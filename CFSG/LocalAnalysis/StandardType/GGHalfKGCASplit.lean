module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs

public section

namespace CFSG.StandardType

private lemma ggKGCASplit_add_self {W : Type} [AddCommGroup W] [Module GGKGCF W]
    (x : W) : x + x = 0 := by
  have h : (2 : GGKGCF) = 0 := CharP.cast_eq_zero GGKGCF 2
  calc x + x = (2 : GGKGCF) • x := (two_smul GGKGCF x).symm
    _ = 0 := by rw [h, zero_smul]

private lemma ggKGCASplit_fix_iff
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k : V ≃ₗ[GGKGCF] V} {w : V} :
    w ∈ ggKGCAFix k ↔ (k : V →ₗ[GGKGCF] V) w = w := by
  rw [ggKGCAFix, LinearMap.mem_ker]
  change (k : V →ₗ[GGKGCF] V) w - w = 0 ↔ (k : V →ₗ[GGKGCF] V) w = w
  rw [sub_eq_zero]

private lemma ggKGCASplit_plane_iff
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k : V ≃ₗ[GGKGCF] V} {t : V} :
    t ∈ ggKGCAPlane k ↔
      (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) t) + (k : V →ₗ[GGKGCF] V) t + t = 0 := by
  rw [ggKGCAPlane, LinearMap.mem_ker]
  change (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) t) + (k : V →ₗ[GGKGCF] V) t + t = 0 ↔
      (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) t) + (k : V →ₗ[GGKGCF] V) t + t = 0
  rfl

private lemma ggKGCASplit_field_eq_zero_or_one (a : GGKGCF) : a = 0 ∨ a = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have h' := h (GaloisField.equivZmodP 2 a)
  rcases h' with h0 | h1
  · left
    apply (GaloisField.equivZmodP 2).injective
    simpa using h0
  · right
    apply (GaloisField.equivZmodP 2).injective
    simpa using h1

private lemma ggKGCASplit_hK3
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (k : V ≃ₗ[GGKGCF] V) (hk3 : k ^ 3 = 1) :
    ∀ x : V, (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) x)) = x := by
  intro x
  have h := congrArg (fun e : V ≃ₗ[GGKGCF] V => (e : V → V)) hk3
  have h' : (⇑k)^[3] = id := by simpa [LinearEquiv.coe_pow, LinearEquiv.coe_one] using h
  simpa using congrFun h' x

theorem ggKGCASplit_isCompl
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (k : V ≃ₗ[GGKGCF] V) (hk3 : k ^ 3 = 1) :
    IsCompl (ggKGCAFix k) (ggKGCAPlane k) := by
  have hK3 := ggKGCASplit_hK3 k hk3
  apply IsCompl.of_eq
  · rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf, ggKGCASplit_fix_iff, ggKGCASplit_plane_iff] at hw
    obtain ⟨hfix, hplane⟩ := hw
    rw [hfix] at hplane
    rw [add_assoc, ggKGCASplit_add_self, add_zero] at hplane
    rw [← hfix]
    exact hplane
  · rw [eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨(k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) v) + (k : V →ₗ[GGKGCF] V) v + v,
      ?_, (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) v) + (k : V →ₗ[GGKGCF] V) v, ?_, ?_⟩
    · rw [ggKGCASplit_fix_iff]
      simp only [map_add, hK3]
      abel
    · rw [ggKGCASplit_plane_iff]
      simp only [map_add, hK3]
      abel_nf
      simp [two_zsmul, ggKGCASplit_add_self]
    · abel_nf
      simp [two_zsmul, ggKGCASplit_add_self]

theorem ggKGCASplit_stable
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k g : V ≃ₗ[GGKGCF] V} (hgk : g * k = k * g) :
    (∀ w ∈ ggKGCAFix k, g w ∈ ggKGCAFix k) ∧ (∀ t ∈ ggKGCAPlane k, g t ∈ ggKGCAPlane k) := by
  have hcomm : ∀ x : V, (k : V →ₗ[GGKGCF] V) (g x) =
      g ((k : V →ₗ[GGKGCF] V) x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[GGKGCF] V => e x) hgk
    simpa [LinearEquiv.mul_apply] using h.symm
  constructor
  · intro w hw
    rw [ggKGCASplit_fix_iff] at hw ⊢
    rw [hcomm w, hw]
  · intro t ht
    rw [ggKGCASplit_plane_iff] at ht ⊢
    rw [hcomm t, hcomm ((k : V →ₗ[GGKGCF] V) t)]
    rw [← map_add, ← map_add, ht, map_zero]

theorem ggKGCASplit_plane_ne_bot
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k : V ≃ₗ[GGKGCF] V} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    ggKGCAPlane k ≠ ⊥ := by
  intro hbot
  apply hk1
  have his := ggKGCASplit_isCompl k hk3
  have htop : ggKGCAFix k = ⊤ := by
    have h := his.sup_eq_top
    rwa [hbot, sup_bot_eq] at h
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ ggKGCAFix k := by rw [htop]; exact Submodule.mem_top
  rw [ggKGCASplit_fix_iff] at hv
  simpa using hv

private lemma ggKGCASplit_linIndep {W : Type} [AddCommGroup W] [Module GGKGCF W]
    (φ : W →ₗ[GGKGCF] W) (hφ : φ ^ 2 + φ + 1 = 0) {v : W} (hv : v ≠ 0) :
    LinearIndependent GGKGCF ![v, φ v] := by
  rw [linearIndependent_fin2]
  have hrel : φ (φ v) + φ v + v = 0 := by
    have h := congrArg (fun f : W →ₗ[GGKGCF] W => f v) hφ
    change φ (φ v) + φ v + v = 0 at h
    simpa using h
  change φ v ≠ 0 ∧ ∀ a : GGKGCF, a • φ v ≠ v
  constructor
  · intro h0
    have hv0 : v = 0 := by simpa [h0, ggKGCASplit_add_self] using hrel
    exact hv hv0
  · intro a
    rcases ggKGCASplit_field_eq_zero_or_one a with rfl | rfl
    · intro h
      exact hv (by simpa using h.symm)
    · intro h
      have h' : φ v = v := by simpa using h
      exact hv (by simpa [h', ggKGCASplit_add_self] using hrel)

private lemma ggKGCASplit_neg_eq {W : Type} [AddCommGroup W] [Module GGKGCF W]
    (x : W) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]
  exact ggKGCASplit_add_self x

private lemma ggKGCASplit_comm
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k g : V ≃ₗ[GGKGCF] V} (hgk : g * k = k * g) (x : V) :
    (g : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) x) =
      (k : V →ₗ[GGKGCF] V) ((g : V →ₗ[GGKGCF] V) x) := by
  have h := congrArg (fun e : V ≃ₗ[GGKGCF] V => e x) hgk
  simpa [LinearEquiv.mul_apply] using h

private theorem ggKGCASplit_gen_aux :
    ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module GGKGCF W] [FiniteDimensional GGKGCF W],
      Module.finrank GGKGCF W = n →
      ∀ φ : W →ₗ[GGKGCF] W, φ ^ 2 + φ + 1 = 0 →
        ∃ r : ℕ, Module.finrank GGKGCF W = 2 * r ∧
          ∃ v : Fin r → W,
            Submodule.span GGKGCF (Set.range v ∪ Set.range fun i => φ (v i)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ _ hdim φ hφ
    by_cases hnt : Nontrivial W
    · obtain ⟨v, hv⟩ := exists_ne (0 : W)
      have hrel : ∀ x : W, φ (φ x) + φ x + x = 0 := by
        intro x
        have h := congrArg (fun f : W →ₗ[GGKGCF] W => f x) hφ
        change φ (φ x) + φ x + x = 0 at h
        simpa using h
      let U : Submodule GGKGCF W := Submodule.span GGKGCF (Set.range ![v, φ v])
      have hv_mem : v ∈ U := Submodule.subset_span ⟨0, by simp⟩
      have hφv_mem : φ v ∈ U := Submodule.subset_span ⟨1, by simp⟩
      have hUle : U ≤ Submodule.comap φ U := by
        change Submodule.span GGKGCF (Set.range ![v, φ v]) ≤ Submodule.comap φ U
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        fin_cases i
        · exact hφv_mem
        · have hvv : φ (φ v) = φ v + v := by
            have h := hrel v
            rw [add_assoc] at h
            rw [eq_neg_of_add_eq_zero_left h, ggKGCASplit_neg_eq]
          change φ (φ v) ∈ U
          rw [hvv]
          exact Submodule.add_mem _ hφv_mem hv_mem
      have hlin : LinearIndependent GGKGCF ![v, φ v] := ggKGCASplit_linIndep φ hφ hv
      have hU2 : Module.finrank GGKGCF U = 2 := by
        have h := finrank_span_eq_card hlin
        simpa [U] using h
      let φq : W ⧸ U →ₗ[GGKGCF] W ⧸ U := Submodule.mapQ U U φ hUle
      have hφq : φq ^ 2 + φq + 1 = 0 := by
        apply LinearMap.ext
        intro y
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U y
        have h2 : (φq ^ 2) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ (φ x)) := by
          rw [pow_two]
          change φq (φq (Submodule.Quotient.mk x)) = Submodule.Quotient.mk (φ (φ x))
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
        have h1 : φq (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ x) := by
          rw [Submodule.mapQ_apply]
        rw [LinearMap.add_apply, LinearMap.add_apply, h2, h1]
        change Submodule.Quotient.mk (φ (φ x)) + Submodule.Quotient.mk (φ x) +
          Submodule.Quotient.mk x = 0
        simp only [← Submodule.mkQ_apply]
        rw [← map_add, ← map_add, hrel x, map_zero]
      have hfinq : Module.finrank GGKGCF (W ⧸ U) = n - 2 := by
        have h := Submodule.finrank_quotient_add_finrank U
        rw [hdim, hU2] at h
        omega
      have h2n : 2 ≤ n := by
        have h := Submodule.finrank_le U
        rw [hdim, hU2] at h
        exact h
      have hlt : Module.finrank GGKGCF (W ⧸ U) < n := by omega
      obtain ⟨r', hfin', v', hspan'⟩ :=
        ih (Module.finrank GGKGCF (W ⧸ U)) hlt (W ⧸ U) rfl φq hφq
      choose w hw using fun i => Submodule.Quotient.mk_surjective U (v' i)
      let u : Fin (r' + 1) → W := Fin.cases v w
      have hu0 : u 0 = v := Fin.cases_zero
      have hus : ∀ i, u i.succ = w i := fun i => Fin.cases_succ i
      let S : Submodule GGKGCF W :=
        Submodule.span GGKGCF (Set.range u ∪ Set.range fun i => φ (u i))
      have hUleS : U ≤ S := by
        change Submodule.span GGKGCF (Set.range ![v, φ v]) ≤ S
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        fin_cases i
        · exact Submodule.subset_span (Or.inl ⟨0, hu0⟩)
        · exact Submodule.subset_span (Or.inr ⟨0, by simp [hu0]⟩)
      have hmap : Submodule.map (Submodule.mkQ U) S = ⊤ := by
        rw [eq_top_iff, ← hspan']
        apply Submodule.span_le.mpr
        rintro z (hz | hz)
        · obtain ⟨i, rfl⟩ := hz
          refine ⟨u i.succ, Submodule.subset_span (Or.inl ⟨i.succ, rfl⟩), ?_⟩
          rw [Submodule.mkQ_apply, hus i]
          exact hw i
        · obtain ⟨i, rfl⟩ := hz
          refine ⟨φ (u i.succ), Submodule.subset_span (Or.inr ⟨i.succ, rfl⟩), ?_⟩
          change U.mkQ (φ (u i.succ)) = φq (v' i)
          rw [← hw i, Submodule.mapQ_apply, Submodule.mkQ_apply, hus i]
      have hSU : S ⊔ U = ⊤ := by
        have h := Submodule.comap_map_eq (Submodule.mkQ U) S
        rw [hmap] at h
        rw [Submodule.comap_top, Submodule.ker_mkQ] at h
        exact h.symm
      have hS : S = ⊤ := by
        rw [sup_eq_left.mpr hUleS] at hSU
        exact hSU
      refine ⟨r' + 1, ?_, ?_⟩
      · have h := Submodule.finrank_quotient_add_finrank U
        rw [hfin', hU2] at h
        omega
      · exact ⟨u, hS⟩
    · haveI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
      exact ⟨0, by rw [Module.finrank_zero_of_subsingleton], ⟨Fin.elim0, Subsingleton.elim _ _⟩⟩

private theorem ggKGCASplit_gen {W : Type} [AddCommGroup W] [Module GGKGCF W]
    [FiniteDimensional GGKGCF W] (φ : W →ₗ[GGKGCF] W) (hφ : φ ^ 2 + φ + 1 = 0) :
    ∃ r : ℕ, Module.finrank GGKGCF W = 2 * r ∧
      ∃ v : Fin r → W, Submodule.span GGKGCF (Set.range v ∪ Set.range fun i => φ (v i)) = ⊤ :=
  ggKGCASplit_gen_aux (Module.finrank GGKGCF W) W rfl φ hφ

private lemma ggKGCASplit_plane_stable_self
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (k : V ≃ₗ[GGKGCF] V) :
    ∀ x ∈ ggKGCAPlane k, (k : V →ₗ[GGKGCF] V) x ∈ ggKGCAPlane k := by
  intro x hx
  rw [ggKGCASplit_plane_iff] at hx ⊢
  have h := congrArg (fun y => (k : V →ₗ[GGKGCF] V) y) hx
  simpa [map_add] using h

private noncomputable def ggKGCASplit_restrict
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (k : V ≃ₗ[GGKGCF] V) :
    (ggKGCAPlane k) →ₗ[GGKGCF] (ggKGCAPlane k) :=
  (((k : V →ₗ[GGKGCF] V).comp (ggKGCAPlane k).subtype)).codRestrict (ggKGCAPlane k)
    (fun x => ggKGCASplit_plane_stable_self k x.1 x.2)

private lemma ggKGCASplit_restrict_rel
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (k : V ≃ₗ[GGKGCF] V) :
    ggKGCASplit_restrict k ^ 2 + ggKGCASplit_restrict k + 1 = 0 := by
  ext x
  have hx := x.2
  rw [ggKGCASplit_plane_iff] at hx
  change (k : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) (x : V)) +
      (k : V →ₗ[GGKGCF] V) (x : V) + (x : V) = 0
  exact hx

theorem ggKGCASplit_rank
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k : V ≃ₗ[GGKGCF] V} (hk3 : k ^ 3 = 1) :
    ∃ r : ℕ, Module.finrank GGKGCF (ggKGCAPlane k) = 2 * r := by
  obtain ⟨r, hfin, -⟩ := ggKGCASplit_gen (ggKGCASplit_restrict k) (ggKGCASplit_restrict_rel k)
  exact ⟨r, hfin⟩

theorem ggKGCASplit_card_restrict_le
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {k : V ≃ₗ[GGKGCF] V} (hk3 : k ^ 3 = 1) {r : ℕ}
    (hr : Module.finrank GGKGCF (ggKGCAPlane k) = 2 * r) :
    Nat.card (Set.range fun g : {g : V ≃ₗ[GGKGCF] V // g * k = k * g} =>
      fun t : ggKGCAPlane k => (g.1 t : V)) ≤ Nat.card (ggKGCAPlane k) ^ r := by
  haveI : Finite V := Module.finite_of_finite GGKGCF
  haveI : Finite (ggKGCAPlane k) := Subtype.finite
  obtain ⟨r₀, hfin₀, v, hspan⟩ :=
    ggKGCASplit_gen (ggKGCASplit_restrict k) (ggKGCASplit_restrict_rel k)
  have hr₀ : r₀ = r := by omega
  subst r₀
  let G : Type := {g : V ≃ₗ[GGKGCF] V // g * k = k * g}
  let res : G → (ggKGCAPlane k → V) := fun g t => g.1 t
  have hdet : ∀ (g g' : G), (∀ i : Fin r, (g : V →ₗ[GGKGCF] V) (v i).1 =
      (g' : V →ₗ[GGKGCF] V) (v i).1) →
      ∀ t : ggKGCAPlane k, g.1 t.1 = g'.1 t.1 := by
    intro g g' hagree t
    let F : ggKGCAPlane k →ₗ[GGKGCF] V :=
      ((g : V →ₗ[GGKGCF] V).comp (ggKGCAPlane k).subtype) -
        ((g' : V →ₗ[GGKGCF] V).comp (ggKGCAPlane k).subtype)
    have hSle : Submodule.span GGKGCF (Set.range v ∪
        Set.range fun i => ggKGCASplit_restrict k (v i)) ≤ F.ker := by
      apply Submodule.span_le.mpr
      rintro y (hy | hy)
      · obtain ⟨i, rfl⟩ := hy
        change (g : V →ₗ[GGKGCF] V) (v i).1 - (g' : V →ₗ[GGKGCF] V) (v i).1 = 0
        rw [sub_eq_zero]
        exact hagree i
      · obtain ⟨i, rfl⟩ := hy
        change (g : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) (v i).1) -
            (g' : V →ₗ[GGKGCF] V) ((k : V →ₗ[GGKGCF] V) (v i).1) = 0
        rw [sub_eq_zero, ggKGCASplit_comm g.2, ggKGCASplit_comm g'.2, hagree i]
    have ht : t ∈ Submodule.span GGKGCF (Set.range v ∪
        Set.range fun i => ggKGCASplit_restrict k (v i)) := by
      rw [hspan]; exact Submodule.mem_top
    have ht' := hSle ht
    change (g : V →ₗ[GGKGCF] V) (t : V) - (g' : V →ₗ[GGKGCF] V) (t : V) = 0 at ht'
    rw [sub_eq_zero] at ht'
    exact ht'
  have hmem : ∀ (i : Fin r) (f : Set.range res), f.1 (v i) ∈ ggKGCAPlane k := by
    intro i f
    obtain ⟨g, hg⟩ := f.2
    rw [← hg]
    exact (ggKGCASplit_stable g.2).2 (v i).1 (v i).2
  let Ψ : Set.range res → (Fin r → ggKGCAPlane k) := fun f i => ⟨f.1 (v i), hmem i f⟩
  have hΨinj : Function.Injective Ψ := by
    intro f f' hff'
    apply Subtype.ext
    funext t
    obtain ⟨g, hg⟩ := f.2
    obtain ⟨g', hg'⟩ := f'.2
    have hagree : ∀ i : Fin r, (g : V →ₗ[GGKGCF] V) (v i).1 =
        (g' : V →ₗ[GGKGCF] V) (v i).1 := by
      intro i
      have h := congrArg Subtype.val (congrFun hff' i)
      simp only [Ψ] at h
      rw [← hg, ← hg'] at h
      simpa [res] using h
    have hres := hdet g g' hagree t
    rw [← hg, ← hg']
    exact hres
  have hcard : Nat.card (Set.range res) ≤ Nat.card (Fin r → ggKGCAPlane k) :=
    Nat.card_le_card_of_injective Ψ hΨinj
  rw [Nat.card_fun, Nat.card_fin] at hcard
  exact hcard

end CFSG.StandardType

end
