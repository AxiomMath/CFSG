module

public import CFSG.Monster.GMS.R433Cover.Algebra
public import CFSG.YGroups.Defs

public section

namespace CFSG.Sporadic.Recognition.YCover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open CFSG.Monster.GMS.R433Cover (IsZ cm sq_eq_of_cube cm_slide cm_swap cube_swap kappa_zero
  eps_zero)
open CFSG.YGroups (yEdges ngen spiderWord)

section Diagram

variable (p q r : ℕ)

@[expose] def adjB (s t : ℕ) : Bool :=
  decide ((s, t) ∈ yEdges p q r) || decide ((t, s) ∈ yEdges p q r)

@[expose] def nonadjB (s t : ℕ) : Bool :=
  decide (s < ngen p q r) && decide (t < ngen p q r) && decide (s ≠ t) && !adjB p q r s t

@[expose] def parentY (c : ℕ) : ℕ := if c = 1 ∨ c = 1 + p ∨ c = 1 + p + q then 0 else c - 1

@[expose] def slideStep (x y : ℕ × ℕ) : Bool :=
  nonadjB p q r x.1 x.2 && nonadjB p q r y.1 y.2 &&
    ((x.1 == y.1 && adjB p q r x.2 y.2) || (x.1 == y.2 && x.2 == y.1))

@[expose] def nonadjPairs : List (ℕ × ℕ) :=
  ((List.range (ngen p q r)).flatMap fun s => (List.range (ngen p q r)).map fun t => (s, t)).filter
    fun x => nonadjB p q r x.1 x.2

@[expose] def slideGrow (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  S ++ (nonadjPairs p q r).filter fun y => !(S.contains y) && S.any fun x => slideStep p q r x y

@[expose] def slideClosure : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, S => S
  | n + 1, S => slideClosure n (slideGrow p q r S)

variable {p q r}

theorem nonadjB_lt {s t : ℕ} (h : nonadjB p q r s t = true) : s < ngen p q r ∧ t < ngen p q r := by
  unfold nonadjB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem nonadjB_ne {s t : ℕ} (h : nonadjB p q r s t = true) : s ≠ t := by
  unfold nonadjB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem mem_nonadjPairs {s t : ℕ} (h : nonadjB p q r s t = true) : (s, t) ∈ nonadjPairs p q r := by
  unfold nonadjPairs
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map]
  obtain ⟨hs, ht⟩ := nonadjB_lt h
  exact ⟨⟨s, hs, t, ht, rfl⟩, h⟩

theorem slideClosure_sound {P : ℕ × ℕ → Prop}
    (hP : ∀ x y, slideStep p q r x y = true → P x → P y) :
    ∀ n (S : List (ℕ × ℕ)), (∀ x ∈ S, P x) → ∀ x ∈ slideClosure p q r n S, P x := by
  intro n
  induction n with
  | zero => intro S hS x hx; exact hS x hx
  | succ n ih =>
    intro S hS x hx
    refine ih (slideGrow p q r S) ?_ x hx
    intro y hy
    unfold slideGrow at hy
    rcases List.mem_append.1 hy with h | h
    · exact hS y h
    · obtain ⟨_, hy2⟩ := List.mem_filter.1 h
      simp only [Bool.and_eq_true, List.any_eq_true] at hy2
      obtain ⟨_, z, hz, hzy⟩ := hy2
      exact hP z y hzy (hS z hz)

structure FlagData (p q r : ℕ) where
  u : ℕ
  v₀ : ℕ
  Fw : List ℕ
  t₁ : ℕ
  t₂ : ℕ
  t₃ : ℕ
  q₁ : ℕ
  q₂ : ℕ
  q₃ : ℕ
  q₄ : ℕ
  parent_edge : ∀ c < ngen p q r, 0 < c →
    parentY p q c < c ∧ (parentY p q c, c) ∈ yEdges p q r
  edges_parent : ∀ e ∈ yEdges p q r, 0 < e.2 ∧ e.2 < ngen p q r ∧ parentY p q e.2 = e.1
  reach : ∀ x ∈ nonadjPairs p q r, x ∈ slideClosure p q r 14 [(u, v₀)]
  base : nonadjB p q r u v₀ = true
  Fw_odd : Fw.length % 2 = 1
  Fw_lt : ∀ c ∈ Fw, c < ngen p q r
  Fw_nonadj : ∀ c ∈ Fw, nonadjB p q r u c = true
  triple : nonadjB p q r t₁ t₂ = true ∧ nonadjB p q r t₁ t₃ = true ∧ nonadjB p q r t₂ t₃ = true
  quad : nonadjB p q r q₁ q₂ = true ∧ nonadjB p q r q₁ q₃ = true ∧ nonadjB p q r q₁ q₄ = true ∧
    nonadjB p q r q₂ q₃ = true ∧ nonadjB p q r q₂ q₄ = true ∧ nonadjB p q r q₃ q₄ = true
  spider_mem : (List.replicate 10 (spiderWord p q)).flatten ∈ CFSG.YGroups.yRels p q r
  spider_lt : ∀ c ∈ spiderWord p q, c < ngen p q r
  even_rels : ∀ w ∈ CFSG.YGroups.yRels p q r, w.length % 2 = 0

end Diagram

section Flags

variable {p q r : ℕ} {E : Type*} [Group E]

theorem FlagData.edges_lt (D : FlagData p q r) {e : ℕ × ℕ} (he : e ∈ yEdges p q r) :
    e.1 < e.2 := by
  obtain ⟨h0, hn, hpar⟩ := D.edges_parent e he
  have := (D.parent_edge e.2 hn h0).1
  rw [hpar] at this
  exact this

theorem edge_cube {g : ℕ → E} (hedge : ∀ e ∈ yEdges p q r, (g e.1 * g e.2) ^ 3 = 1) {s t : ℕ}
    (h : adjB p q r s t = true) : (g s * g t) ^ 3 = 1 := by
  unfold adjB at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact hedge (s, t) h
  · exact cube_swap (hedge (t, s) h)

theorem flags_vanish (D : FlagData p q r) {z : E} (hzc : ∀ g : E, g * z = z * g) (hz2 : z * z = 1)
    {g : ℕ → E} (hedge : ∀ e ∈ yEdges p q r, (g e.1 * g e.2) ^ 3 = 1)
    (hsq : ∀ s < ngen p q r, IsZ z (g s * g s))
    (hcm : ∀ s t, nonadjB p q r s t = true → IsZ z (cm (g s) (g t)))
    (hF : IsZ z ((evalWord g D.Fw) ^ 9))
    (hsp : IsZ z ((evalWord g (spiderWord p q)) ^ 10))
    (hI1 : IsZ z (((evalWord g (spiderWord p q)) ^ 5 * g 0) ^ 3)) {Y : List ℕ}
    (hI2 : IsZ z ((evalWord g Y)⁻¹ * (g D.t₁ * g D.t₂ * g D.t₃) * evalWord g Y *
      (g D.q₁ * g D.q₂ * g D.q₃ * g D.q₄)⁻¹)) :
    (∀ s < ngen p q r, g s * g s = 1) ∧
      (∀ s t, nonadjB p q r s t = true → g s * g t = g t * g s) ∧
      (evalWord g (spiderWord p q)) ^ 10 = 1 := by
  have h0 : 0 < ngen p q r := by unfold ngen; omega
  have hsqeq : ∀ s, s < ngen p q r → g s * g s = g 0 * g 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · rfl
      · obtain ⟨hlt, hmem⟩ := D.parent_edge s hs hpos
        have hpn : parentY p q s < ngen p q r := by omega
        have h1 := sq_eq_of_cube hzc hz2 (hsq (parentY p q s) hpn) (hsq s hs)
          (Or.inl (hedge _ hmem))
        exact h1.symm.trans (ih (parentY p q s) hlt hpn)
  have hslide : ∀ x y : ℕ × ℕ, slideStep p q r x y = true →
      cm (g x.1) (g x.2) = cm (g D.u) (g D.v₀) → cm (g y.1) (g y.2) = cm (g D.u) (g D.v₀) := by
    intro x y hxy hx
    obtain ⟨⟨hnx, hny⟩, h⟩ : (nonadjB p q r x.1 x.2 = true ∧ nonadjB p q r y.1 y.2 = true) ∧
        ((x.1 == y.1 && adjB p q r x.2 y.2) || (x.1 == y.2 && x.2 == y.1)) = true := by
      unfold slideStep at hxy
      simpa only [Bool.and_eq_true] using hxy
    rw [← hx]
    have hcx := hcm _ _ hnx
    have hcy := hcm _ _ hny
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1] at hcy ⊢
      exact (cm_slide hzc hz2 hcx hcy (edge_cube hedge h2)).symm
    · rw [← h1, ← h2] at hcy ⊢
      exact cm_swap hzc hz2 hcx
  have hall : ∀ x ∈ nonadjPairs p q r, cm (g x.1) (g x.2) = cm (g D.u) (g D.v₀) :=
    fun x hx => slideClosure_sound hslide 14 [(D.u, D.v₀)]
      (by intro y hy; simp at hy; subst hy; rfl) x (D.reach x hx)
  have hk : IsZ z (cm (g D.u) (g D.v₀)) := hcm D.u D.v₀ D.base
  have hk1 : cm (g D.u) (g D.v₀) = 1 := by
    refine kappa_zero hzc hz2 (a := g D.u) (g := g) (w := D.Fw) hk ?_ D.Fw_odd hF
    intro c hc
    exact hall (D.u, c) (mem_nonadjPairs (D.Fw_nonadj c hc))
  have hcomm : ∀ s t, nonadjB p q r s t = true → g s * g t = g t * g s := by
    intro s t hst
    have h := hall (s, t) (mem_nonadjPairs hst)
    simp only at h
    rw [hk1] at h
    calc g s * g t = (cm (g s) (g t)) * (g t * g s) := by unfold cm; group
      _ = g t * g s := by rw [h, one_mul]
  obtain ⟨ht12, ht13, ht23⟩ := D.triple
  obtain ⟨hq12, hq13, hq14, hq23, hq24, hq34⟩ := D.quad
  have hA : g 0 * g 0 = 1 := by
    refine eps_zero hzc hz2 (a := g D.t₁) (b := g D.t₂) (c := g D.t₃) (a' := g D.q₁)
      (b' := g D.q₂) (c' := g D.q₃) (d' := g D.q₄) (y := evalWord g Y) (A := g 0 * g 0)
      (hsq 0 h0) (hsqeq _ (nonadjB_lt ht12).1) (hsqeq _ (nonadjB_lt ht12).2)
      (hsqeq _ (nonadjB_lt ht13).2) (hsqeq _ (nonadjB_lt hq12).1) (hsqeq _ (nonadjB_lt hq12).2)
      (hsqeq _ (nonadjB_lt hq13).2) (hsqeq _ (nonadjB_lt hq14).2)
      (hcomm _ _ ht12) (hcomm _ _ ht13) (hcomm _ _ ht23)
      (hcomm _ _ hq12) (hcomm _ _ hq13) (hcomm _ _ hq14) (hcomm _ _ hq23) (hcomm _ _ hq24)
      (hcomm _ _ hq34) hI2
  have hsq1 : ∀ s < ngen p q r, g s * g s = 1 := fun s hs => (hsqeq s hs).trans hA
  refine ⟨hsq1, hcomm, ?_⟩
  have h5 := sq_eq_of_cube hzc hz2 (a := (evalWord g (spiderWord p q)) ^ 5) (b := g 0)
    (by rw [← pow_add]; exact hsp) (hsq 0 h0) hI1
  rw [← pow_add] at h5
  rw [h5, hA]

end Flags

end CFSG.Sporadic.Recognition.YCover
