module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitNine

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130LStarProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Item2130SplitProof
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

@[expose] def SameOn (B : Subgroup G) (x y : G) : Prop :=
  ∀ b ∈ B, x * b * x⁻¹ = y * b * y⁻¹

theorem sameOn_one_iff {B : Subgroup G} {x : G} : SameOn B x 1 ↔ ∀ b ∈ B, x * b * x⁻¹ = b := by
  simp [SameOn]

theorem SameOn.mono {B X : Subgroup G} {x y : G} (h : SameOn B x y) (hXB : X ≤ B) :
    SameOn X x y := fun b hb => h b (hXB hb)

theorem kleinFour_entries : ∀ a b c d : ZMod 3, (!![a, b; c, d] : Mat2) * !![a, b; c, d] = 1 →
    ∀ a' b' c' d' : ZMod 3, (!![a', b'; c', d'] : Mat2) * !![a', b'; c', d'] = 1 →
    (!![a, b; c, d] : Mat2) * !![a', b'; c', d'] = !![a', b'; c', d'] * !![a, b; c, d] →
    (!![a, b; c, d] : Mat2) = 1 ∨ (!![a', b'; c', d'] : Mat2) = 1 ∨
      (!![a, b; c, d] : Mat2) * !![a', b'; c', d'] = 1 ∨ (!![a, b; c, d] : Mat2) = -1 ∨
      (!![a', b'; c', d'] : Mat2) = -1 ∨ (!![a, b; c, d] : Mat2) * !![a', b'; c', d'] = -1 := by
  decide +kernel

theorem kleinFour_mat (S T : Mat2) (hS : S * S = 1) (hT : T * T = 1) (hST : S * T = T * S) :
    S = 1 ∨ T = 1 ∨ S * T = 1 ∨ S = -1 ∨ T = -1 ∨ S * T = -1 := by
  have := kleinFour_entries (S 0 0) (S 0 1) (S 1 0) (S 1 1)
  rw [← Matrix.eta_fin_two S] at this
  have := this hS (T 0 0) (T 0 1) (T 1 0) (T 1 1)
  rw [← Matrix.eta_fin_two T] at this
  exact this hT hST

theorem false_of_kleinFour_GL {S T Γ : GL (Fin 2) (ZMod 3)} (hS : S * S = 1) (hT : T * T = 1)
    (hST : S * T = T * S) (hS1 : S ≠ 1) (hT1 : T ≠ 1) (hST1 : S * T ≠ 1)
    (hΓS : Γ * S * Γ⁻¹ = T) (hΓT : Γ * T * Γ⁻¹ = S * T) : False := by
  have hcen : ∀ x : GL (Fin 2) (ZMod 3), Γ * x * Γ⁻¹ = -1 → x = -1 := by
    intro x hx
    have : x = Γ⁻¹ * (Γ * x * Γ⁻¹) * Γ := by group
    rw [this, hx, mul_neg_one, neg_mul, inv_mul_cancel]
  have hneg : ∀ x : GL (Fin 2) (ZMod 3), x = -1 → Γ * x * Γ⁻¹ = -1 := by
    rintro x rfl
    rw [mul_neg_one, neg_mul, mul_inv_cancel]
  have e : ∀ x : GL (Fin 2) (ZMod 3), x = -1 ↔ ((x : GL (Fin 2) (ZMod 3)) : Mat2) = -1 := by
    intro x
    constructor
    · rintro rfl
      simp
    · intro h
      exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have e1 : ∀ x : GL (Fin 2) (ZMod 3), x = 1 ↔ ((x : GL (Fin 2) (ZMod 3)) : Mat2) = 1 := by
    intro x
    constructor
    · rintro rfl
      simp
    · intro h
      exact Units.ext (by rw [h, Units.val_one])
  have hS' : (S : Mat2) * S = 1 := by rw [← Units.val_mul, hS, Units.val_one]
  have hT' : (T : Mat2) * T = 1 := by rw [← Units.val_mul, hT, Units.val_one]
  have hST' : (S : Mat2) * T = T * S := by rw [← Units.val_mul, hST, Units.val_mul]
  rcases kleinFour_mat _ _ hS' hT' hST' with h | h | h | h | h | h
  · exact hS1 ((e1 S).mpr h)
  · exact hT1 ((e1 T).mpr h)
  · exact hST1 ((e1 _).mpr (by rw [Units.val_mul]; exact h))
  ·
    have hSm : S = -1 := (e S).mpr h
    have hTm : T = -1 := hΓS ▸ hneg S hSm
    apply hST1
    rw [hSm, hTm, neg_one_mul, neg_neg]
  ·
    have hTm : T = -1 := (e T).mpr h
    have h1 : S * T = -1 := hΓT ▸ hneg T hTm
    apply hS1
    rw [hTm, mul_neg_one, neg_eq_iff_eq_neg, neg_neg] at h1
    exact h1
  ·
    have hSTm : S * T = -1 := (e _).mpr (by rw [Units.val_mul]; exact h)
    have h1 : Γ * (S * T) * Γ⁻¹ = S := by
      calc Γ * (S * T) * Γ⁻¹ = (Γ * S * Γ⁻¹) * (Γ * T * Γ⁻¹) := by group
        _ = T * (S * T) := by rw [hΓS, hΓT]
        _ = S * (T * T) := by rw [← mul_assoc, ← hST, mul_assoc]
        _ = S := by rw [hT, mul_one]
    have hSm : S = -1 := h1 ▸ hneg _ hSTm
    apply hT1
    rw [hSm, neg_one_mul, neg_eq_iff_eq_neg] at hSTm
    rw [hSTm, neg_neg]

theorem matB_eq_of_sameOn {k : ℕ} {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    {n m : Subgroup.normalizer (B : Set G)} (h : SameOn B n m) : matB f n = matB f m := by
  apply Units.ext
  ext i j
  have h1 : eltB f (((matB f n : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
      Pi.single j 1) = eltB f (((matB f m : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k)
        (ZMod 3)) *ᵥ Pi.single j 1) := by
    rw [eltB_matB, eltB_matB]
    exact h _ (eltB_mem f _)
  have h2 := congrFun (eltB_injective f h1) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2

theorem sameOn_of_matB_eq {k : ℕ} {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    {n m : Subgroup.normalizer (B : Set G)} (h : matB f n = matB f m) : SameOn B n m := by
  intro b hb
  obtain ⟨v, rfl⟩ := exists_eltB f hb
  rw [← eltB_matB, ← eltB_matB, h]

theorem false_of_kleinFour_nine [Finite G] {X : Subgroup G} (hX : CFSG.Assembly.IsElemAbelian 3 X)
    (h9 : Nat.card X = 9) {s t g : G} (hs : s ∈ Subgroup.normalizer (X : Set G))
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hs2 : SameOn X (s * s) 1) (ht2 : SameOn X (t * t) 1) (hst : SameOn X (s * t) (t * s))
    (hs1 : ¬ SameOn X s 1) (ht1 : ¬ SameOn X t 1) (hst1 : ¬ SameOn X (s * t) 1)
    (hgs : SameOn X (g * s * g⁻¹) t) (hgt : SameOn X (g * t * g⁻¹) (s * t)) : False := by
  obtain ⟨f⟩ := Sec12.exists_coords hX (n := 2) (by rw [h9]; norm_num)
  set N := Subgroup.normalizer (X : Set G)
  let sn : N := ⟨s, hs⟩
  let tn : N := ⟨t, ht⟩
  let gn : N := ⟨g, hg⟩
  have key : ∀ (x y : N), SameOn X x y → matB f x = matB f y := fun x y h =>
    matB_eq_of_sameOn f h
  have key' : ∀ (x y : N), matB f x = matB f y → SameOn X x y := fun x y h =>
    sameOn_of_matB_eq f h
  refine false_of_kleinFour_GL (S := matB f sn) (T := matB f tn) (Γ := matB f gn) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
  · rw [← map_mul, ← map_one (matB f)]
    exact key (sn * sn) 1 hs2
  · rw [← map_mul, ← map_one (matB f)]
    exact key (tn * tn) 1 ht2
  · rw [← map_mul, ← map_mul]
    exact key (sn * tn) (tn * sn) hst
  · intro h
    apply hs1
    exact key' sn 1 (by rw [h, map_one])
  · intro h
    apply ht1
    exact key' tn 1 (by rw [h, map_one])
  · intro h
    apply hst1
    exact key' (sn * tn) 1 (by rw [map_mul, h, map_one])
  · rw [← map_mul, ← map_inv, ← map_mul]
    exact key (gn * sn * gn⁻¹) tn hgs
  · rw [← map_mul, ← map_inv, ← map_mul, ← map_mul]
    exact key (gn * tn * gn⁻¹) (sn * tn) hgt

theorem cube_sameOn_of_unipotent {B X : Subgroup G} {s : G}
    (hX3 : ∀ x ∈ X, x ^ 3 = 1) (hsB : ∀ b ∈ B, s * b * s⁻¹ * b⁻¹ ∈ X)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ = x) : SameOn B (s * s * s) 1 := by
  rw [sameOn_one_iff]
  intro b hb
  obtain ⟨x, hxX, hx⟩ : ∃ x ∈ X, x = s * b * s⁻¹ * b⁻¹ := ⟨_, hsB b hb, rfl⟩
  have h1 : s * b * s⁻¹ = x * b := by rw [hx]; group
  have h2 : s * x * s⁻¹ = x := hsX x hxX
  have h3 : x * (x * x) = 1 := by rw [← pow_three]; exact hX3 x hxX
  calc s * s * s * b * (s * s * s)⁻¹ = s * (s * (s * b * s⁻¹) * s⁻¹) * s⁻¹ := by group
    _ = s * (s * (x * b) * s⁻¹) * s⁻¹ := by rw [h1]
    _ = s * ((s * x * s⁻¹) * (s * b * s⁻¹)) * s⁻¹ := by group
    _ = s * (x * (x * b)) * s⁻¹ := by rw [h2, h1]
    _ = (s * x * s⁻¹) * ((s * x * s⁻¹) * (s * b * s⁻¹)) := by group
    _ = x * (x * (x * b)) := by rw [h2, h1]
    _ = (x * (x * x)) * b := by group
    _ = b := by rw [h3, one_mul]

theorem sameOn_one_of_unipotent {B X : Subgroup G} {s : G}
    (hsB' : s ∈ Subgroup.normalizer (B : Set G)) (hX3 : ∀ x ∈ X, x ^ 3 = 1)
    (hsB : ∀ b ∈ B, s * b * s⁻¹ * b⁻¹ ∈ X) (hsX : ∀ x ∈ X, s * x * s⁻¹ = x)
    (hs2 : SameOn B (s * s) 1) : SameOn B s 1 := by
  have h3 := cube_sameOn_of_unipotent hX3 hsB hsX
  rw [sameOn_one_iff] at h3 hs2 ⊢
  intro b hb
  have hb2 : (s * s)⁻¹ * b * (s * s) ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hsB' hsB')) b).mp hb
    rwa [inv_inv] at this
  have e2 : (s * s)⁻¹ * b * (s * s) = b := by
    have := hs2 _ hb2
    rw [show s * s * ((s * s)⁻¹ * b * (s * s)) * (s * s)⁻¹ = b by group] at this
    exact this.symm
  calc s * b * s⁻¹ = (s * s * s) * ((s * s)⁻¹ * b * (s * s)) * (s * s * s)⁻¹ := by group
    _ = (s * s)⁻¹ * b * (s * s) := h3 _ hb2
    _ = b := e2

theorem SameOn.symm {B : Subgroup G} {x y : G} (h : SameOn B x y) : SameOn B y x :=
  fun b hb => (h b hb).symm

theorem trivQ_of_sameOn {A B : Subgroup G} {x y : G} (h : SameOn A x y) (hy : TrivQ A B y) :
    TrivQ A B x := fun a ha => by
  rw [h a ha]
  exact hy a ha

theorem invQ_of_sameOn {A B : Subgroup G} {x y : G} (h : SameOn A x y) (hy : InvQ A B y) :
    InvQ A B x := fun a ha => by
  rw [h a ha]
  exact hy a ha

structure A4On (B : Subgroup G) (s t g : G) : Prop where
  hs : s ∈ Subgroup.normalizer (B : Set G)
  ht : t ∈ Subgroup.normalizer (B : Set G)
  hg : g ∈ Subgroup.normalizer (B : Set G)
  s2 : SameOn B (s * s) 1
  t2 : SameOn B (t * t) 1
  st : SameOn B (s * t) (t * s)
  s1 : ¬ SameOn B s 1
  t1 : ¬ SameOn B t 1
  st1 : ¬ SameOn B (s * t) 1
  g3 : SameOn B (g * g * g) 1
  gs : SameOn B (g * s * g⁻¹) t
  gt : SameOn B (g * t * g⁻¹) (s * t)

namespace A4On

variable {B : Subgroup G} {s t g : G} (h : A4On B s t g)
include h

omit h in
theorem conj_mem {x b : G} (hx : x ∈ Subgroup.normalizer (B : Set G)) (hb : b ∈ B) :
    x * b * x⁻¹ ∈ B :=
  (Subgroup.mem_normalizer_iff.mp hx b).mp hb

theorem st2 : SameOn B ((s * t) * (s * t)) 1 := by
  rw [sameOn_one_iff]
  intro b hb
  have hc : t * b * t⁻¹ ∈ B := A4On.conj_mem h.ht hb
  have h1 := h.st.symm _ hc
  have h2 : t * t * b * (t * t)⁻¹ = b := by simpa using h.t2 b hb
  have h3 : s * s * b * (s * s)⁻¹ = b := by simpa using h.s2 b hb
  calc s * t * (s * t) * b * (s * t * (s * t))⁻¹
      = s * ((t * s) * (t * b * t⁻¹) * (t * s)⁻¹) * s⁻¹ := by group
    _ = s * ((s * t) * (t * b * t⁻¹) * (s * t)⁻¹) * s⁻¹ := by rw [h1]
    _ = s * s * (t * t * b * (t * t)⁻¹) * (s * s)⁻¹ := by group
    _ = b := by rw [h2, h3]

theorem tst : SameOn B (t * (s * t)) s := by
  intro b hb
  have hc : t * b * t⁻¹ ∈ B := A4On.conj_mem h.ht hb
  have h1 := h.st.symm _ hc
  have h2 : t * t * b * (t * t)⁻¹ = b := by simpa using h.t2 b hb
  calc t * (s * t) * b * (t * (s * t))⁻¹ = (t * s) * (t * b * t⁻¹) * (t * s)⁻¹ := by group
    _ = (s * t) * (t * b * t⁻¹) * (s * t)⁻¹ := h1
    _ = s * (t * t * b * (t * t)⁻¹) * s⁻¹ := by group
    _ = s * b * s⁻¹ := by rw [h2]

theorem gst : SameOn B (g * (s * t) * g⁻¹) s := by
  intro b hb
  have hc : g * t * g⁻¹ * b * (g * t * g⁻¹)⁻¹ ∈ B :=
    A4On.conj_mem (Subgroup.mul_mem _ (Subgroup.mul_mem _ h.hg h.ht) (Subgroup.inv_mem _ h.hg)) hb
  calc g * (s * t) * g⁻¹ * b * (g * (s * t) * g⁻¹)⁻¹
      = (g * s * g⁻¹) * ((g * t * g⁻¹) * b * (g * t * g⁻¹)⁻¹) * (g * s * g⁻¹)⁻¹ := by group
    _ = t * ((s * t) * b * (s * t)⁻¹) * t⁻¹ := by
        rw [h.gt b hb, h.gs _ (by rw [← h.gt b hb]; exact hc)]
    _ = t * (s * t) * b * (t * (s * t))⁻¹ := by group
    _ = s * b * s⁻¹ := h.tst b hb

@[expose] def fixST (B : Subgroup G) (s t : G) : Subgroup G :=
  B ⊓ Subgroup.centralizer ({s, t} : Set G)

omit h in
theorem mem_fixST {y : G} : y ∈ fixST B s t ↔ y ∈ B ∧ s * y * s⁻¹ = y ∧ t * y * t⁻¹ = y := by
  rw [fixST, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; group, by rw [h2]; group⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc s * y = s * y * s⁻¹ * s := by group
        _ = y * s := by rw [h1]
    · calc t * y = t * y * t⁻¹ * t := by group
        _ = y * t := by rw [h2]

theorem fixST_normalized : ∀ x ∈ ({s, t, g} : Set G), ∀ y ∈ fixST B s t,
    x * y * x⁻¹ ∈ fixST B s t := by
  intro x hx y hy
  obtain ⟨hyB, hsy, hty⟩ := mem_fixST.mp hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [hsy]; exact hy
  · rw [hty]; exact hy
  · have hgy : x * y * x⁻¹ ∈ B := A4On.conj_mem h.hg hyB
    have h1 : t * (x * y * x⁻¹) * t⁻¹ = x * y * x⁻¹ := by
      rw [← h.gs _ hgy]
      calc x * s * x⁻¹ * (x * y * x⁻¹) * (x * s * x⁻¹)⁻¹ = x * (s * y * s⁻¹) * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hsy]
    have h2 : (s * t) * (x * y * x⁻¹) * (s * t)⁻¹ = x * y * x⁻¹ := by
      rw [← h.gt _ hgy]
      calc x * t * x⁻¹ * (x * y * x⁻¹) * (x * t * x⁻¹)⁻¹ = x * (t * y * t⁻¹) * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hty]
    refine mem_fixST.mpr ⟨hgy, ?_, h1⟩
    calc s * (x * y * x⁻¹) * s⁻¹ = (s * t) * (t⁻¹ * (x * y * x⁻¹) * t) * (s * t)⁻¹ := by group
      _ = (s * t) * (x * y * x⁻¹) * (s * t)⁻¹ := by
        congr 2
        calc t⁻¹ * (x * y * x⁻¹) * t = t⁻¹ * (t * (x * y * x⁻¹) * t⁻¹) * t := by rw [h1]
          _ = x * y * x⁻¹ := by group
      _ = x * y * x⁻¹ := h2

end A4On

theorem closure_le_normalizer {X : Subgroup G} {s t g : G}
    (hs : s ∈ Subgroup.normalizer (X : Set G)) (ht : t ∈ Subgroup.normalizer (X : Set G))
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.closure ({s, t, g} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hs
  · exact ht
  · exact hg

theorem trivQ_of_quot [Finite G] {B X : Subgroup G} {s t g : G}
    (hQ : QuotHyp B X (Subgroup.closure ({s, t, g} : Set G))) (hg3 : SameOn B (g * g * g) 1)
    (hgs : SameOn B (g * s * g⁻¹) t) (hgt : SameOn B (g * t * g⁻¹) (s * t)) :
    TrivQ B X s ∧ TrivQ B X t := by
  set N := Subgroup.closure ({s, t, g} : Set G)
  have hsN : s ∈ N := Subgroup.subset_closure (by simp)
  have htN : t ∈ N := Subgroup.subset_closure (by simp)
  have hgN : g ∈ N := Subgroup.subset_closure (by simp)
  have hqg : TrivQ B X g := hQ.trivQ_of_pow_odd hgN (j := 1) (fun a ha => by
    have := hg3 a ha
    rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, pow_three']
    simpa using this)
  have conj_invQ : ∀ {x : G}, x ∈ N → InvQ B X x → InvQ B X (g * x * g⁻¹) := fun hx hq =>
    hQ.invQ_mul_of_invQ_trivQ (N.inv_mem hgN) (hQ.invQ_mul_of_trivQ_invQ hx hqg hq)
      (hQ.trivQ_inv hgN hqg)
  have conj_trivQ : ∀ {x : G}, x ∈ N → TrivQ B X x → TrivQ B X (g * x * g⁻¹) := fun hx hq =>
    hQ.trivQ_mul (N.inv_mem hgN) (hQ.trivQ_mul hx hqg hq) (hQ.trivQ_inv hgN hqg)
  have hqs : TrivQ B X s := by
    rcases hQ.trivQ_or_invQ hsN with hq | hq
    · exact hq
    · exfalso
      have h2 : InvQ B X t := invQ_of_sameOn hgs.symm (conj_invQ hsN hq)
      have h3 : TrivQ B X (s * t) := hQ.trivQ_mul_of_invQ htN hq h2
      have h5 : InvQ B X (s * t) := invQ_of_sameOn hgt.symm (conj_invQ htN h2)
      exact hQ.not_trivQ_and_invQ h3 h5
  exact ⟨hqs, trivQ_of_sameOn hgs.symm (conj_trivQ hsN hqs)⟩

theorem A4On.false_of_order_nine [Finite G] {B X : Subgroup G} {s t g : G} (h : A4On B s t g)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h27 : Nat.card B = 27) (hXB : X ≤ B)
    (hX9 : Nat.card X = 9) (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (htX : t ∈ Subgroup.normalizer (X : Set G)) (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    False := by
  have hNB := closure_le_normalizer h.hs h.ht h.hg
  have hNX := closure_le_normalizer hsX htX hgX
  have hQ : QuotHyp B X (Subgroup.closure ({s, t, g} : Set G)) :=
    { elem := hB, le := hXB, card := by rw [h27, hX9], normA := hNB, normB := hNX }
  obtain ⟨hqs, hqt⟩ := trivQ_of_quot hQ h.g3 h.gs h.gt
  have hqst : TrivQ B X (s * t) := hQ.trivQ_mul (Subgroup.subset_closure (by simp)) hqs hqt
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := fun x hx => hB.2 x (hXB hx)
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hXe : CFSG.Assembly.IsElemAbelian 3 X :=
    ⟨⟨⟨fun x y => Subtype.ext (hcommB _ (hXB x.2) _ (hXB y.2))⟩⟩, hX3⟩
  have nontriv : ∀ {x : G}, x ∈ Subgroup.normalizer (B : Set G) → TrivQ B X x →
      SameOn B (x * x) 1 → ¬ SameOn B x 1 → ¬ SameOn X x 1 := fun hx hq hx2 hx1 hX =>
    hx1 (sameOn_one_of_unipotent hx hX3 hq (sameOn_one_iff.mp hX) hx2)
  exact false_of_kleinFour_nine hXe hX9 hsX htX hgX (h.s2.mono hXB) (h.t2.mono hXB)
    (h.st.mono hXB) (nontriv h.hs hqs h.s2 h.s1) (nontriv h.ht hqt h.t2 h.t1)
    (nontriv (Subgroup.mul_mem _ h.hs h.ht) hqst h.st2 h.st1) (h.gs.mono hXB) (h.gt.mono hXB)

theorem mem_normalizer_of_conj_mem [Finite G] {F : Subgroup G} {x : G}
    (h : ∀ y ∈ F, x * y * x⁻¹ ∈ F) : x ∈ Subgroup.normalizer (F : Set G) := by
  have hpow : ∀ k : ℕ, ∀ y ∈ F, x ^ k * y * (x ^ k)⁻¹ ∈ F := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := ih _ (h y hy)
      rwa [show x ^ k * (x * y * x⁻¹) * (x ^ k)⁻¹ = x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ by group]
        at this
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have hk : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hfin.orderOf_pos,
      pow_orderOf_eq_one]
  have := hpow (orderOf x - 1) _ hy
  rwa [← hk, inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem A4On.false_of_order_three [Finite G] {B X : Subgroup G} {s t g : G} (h : A4On B s t g)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h27 : Nat.card B = 27) (hXB : X ≤ B)
    (hX3 : Nat.card X = 3) (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (htX : t ∈ Subgroup.normalizer (X : Set G)) (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    False := by
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hXe : CFSG.Assembly.IsElemAbelian 3 X :=
    ⟨⟨⟨fun x y => Subtype.ext (hcommB _ (hXB x.2) _ (hXB y.2))⟩⟩, fun x hx => hB.2 x (hXB hx)⟩
  have hQ : QuotHyp X ⊥ (Subgroup.closure ({s, t, g} : Set G)) :=
    { elem := hXe, le := bot_le, card := by rw [hX3, Subgroup.card_bot]
      normA := closure_le_normalizer hsX htX hgX
      normB := fun x _ => by
        rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]
        trivial }
  obtain ⟨hqs, hqt⟩ := trivQ_of_quot hQ (h.g3.mono hXB) (h.gs.mono hXB) (h.gt.mono hXB)
  have hfix : ∀ {x : G}, TrivQ X ⊥ x → ∀ y ∈ X, x * y * x⁻¹ = y := fun hq y hy => by
    have := hq y hy
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  set F := A4On.fixST B s t with hF
  have hXF : X ≤ F := fun x hx => A4On.mem_fixST.mpr ⟨hXB hx, hfix hqs x hx, hfix hqt x hx⟩
  have hFB : F ≤ B := inf_le_left
  have hFnorm : ∀ x ∈ ({s, t, g} : Set G), x ∈ Subgroup.normalizer (F : Set G) :=
    fun x hx => mem_normalizer_of_conj_mem (h.fixST_normalized x hx)
  have hsF := hFnorm s (by simp)
  have htF := hFnorm t (by simp)
  have hgF := hFnorm g (by simp)
  have hFcard : Nat.card F = 3 ∨ Nat.card F = 9 := by
    have hdvd : Nat.card F ∣ 3 ^ 3 := by
      rw [show 3 ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le hFB
    have h3 : 3 ∣ Nat.card F := hX3 ▸ Subgroup.card_dvd_of_le hXF
    obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hFk] at h3
      norm_num at h3
    · exact Or.inl hFk
    · exact Or.inr hFk
    · exfalso
      have hFB' : F = B := Subgroup.eq_of_le_of_card_ge hFB (by rw [hFk, h27]; norm_num)
      apply h.s1
      rw [sameOn_one_iff]
      intro b hb
      exact (A4On.mem_fixST.mp (hFB' ▸ hb : b ∈ F)).2.1
  rcases hFcard with hF3 | hF9
  ·
    have hu : s * t ∈ Subgroup.normalizer (B : Set G) := Subgroup.mul_mem _ h.hs h.ht
    set τf : G → G := fun y => y * (s * y * s⁻¹) * (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹)
      with hτf
    have hτB : ∀ y ∈ B, τf y ∈ B := fun y hy =>
      B.mul_mem (B.mul_mem (B.mul_mem hy (A4On.conj_mem h.hs hy)) (A4On.conj_mem h.ht hy))
        (A4On.conj_mem hu hy)
    have hcomm4 : ∀ {a b c d : G}, a ∈ B → b ∈ B → c ∈ B → d ∈ B →
        (a * b * c * d = b * a * d * c) ∧ (a * b * c * d = c * d * a * b) ∧
          (a * b * c * d = a * c * d * b) := by
      intro a b c d ha hb hc hd
      let _ : CommGroup B := { (inferInstance : Group B) with
        mul_comm := fun x y => Subtype.ext (hcommB _ x.2 _ y.2) }
      have key : ∀ x y z w : B, (x * y * z * w = y * x * w * z) ∧
          (x * y * z * w = z * w * x * y) ∧ (x * y * z * w = x * z * w * y) := fun x y z w =>
        ⟨by ac_rfl, by ac_rfl, by ac_rfl⟩
      obtain ⟨k1, k2, k3⟩ := key ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
      exact ⟨congrArg Subtype.val k1, congrArg Subtype.val k2, congrArg Subtype.val k3⟩
    have hss : ∀ y ∈ B, (s * s) * y * (s * s)⁻¹ = y := fun y hy => by simpa using h.s2 y hy
    have htt : ∀ y ∈ B, (t * t) * y * (t * t)⁻¹ = y := fun y hy => by simpa using h.t2 y hy
    have hsst : ∀ y ∈ B, (s * (s * t)) * y * (s * (s * t))⁻¹ = t * y * t⁻¹ := fun y hy => by
      rw [show s * (s * t) * y * (s * (s * t))⁻¹ = (s * s) * (t * y * t⁻¹) * (s * s)⁻¹ by group,
        hss _ (A4On.conj_mem h.ht hy)]
    have hts : ∀ y ∈ B, (t * s) * y * (t * s)⁻¹ = (s * t) * y * (s * t)⁻¹ := fun y hy =>
      (h.st y hy).symm
    have hsts : ∀ y ∈ B, (s * t * s) * y * (s * t * s)⁻¹ = t * y * t⁻¹ := fun y hy => by
      rw [show s * t * s * y * (s * t * s)⁻¹ = s * ((t * s) * y * (t * s)⁻¹) * s⁻¹ by group,
        hts y hy, show s * ((s * t) * y * (s * t)⁻¹) * s⁻¹ = s * (s * t) * y * (s * (s * t))⁻¹ by
          group, hsst y hy]
    have hstt : ∀ y ∈ B, (s * t * t) * y * (s * t * t)⁻¹ = s * y * s⁻¹ := fun y hy => by
      rw [show s * t * t * y * (s * t * t)⁻¹ = s * ((t * t) * y * (t * t)⁻¹) * s⁻¹ by group,
        htt y hy]
    have htst : ∀ y ∈ B, (t * (s * t)) * y * (t * (s * t))⁻¹ = s * y * s⁻¹ := h.tst
    have hτF : ∀ y ∈ B, τf y ∈ F := by
      intro y hy
      have hsy := A4On.conj_mem h.hs hy
      have hty := A4On.conj_mem h.ht hy
      have huy := A4On.conj_mem hu hy
      refine A4On.mem_fixST.mpr ⟨hτB y hy, ?_, ?_⟩
      · calc s * τf y * s⁻¹ = (s * y * s⁻¹) * ((s * s) * y * (s * s)⁻¹) *
              ((s * t) * y * (s * t)⁻¹) * ((s * (s * t)) * y * (s * (s * t))⁻¹) := by
              simp only [hτf]; group
          _ = (s * y * s⁻¹) * y * ((s * t) * y * (s * t)⁻¹) * (t * y * t⁻¹) := by
              rw [hss y hy, hsst y hy]
          _ = τf y := (hcomm4 hsy hy huy hty).1
      · calc t * τf y * t⁻¹ = (t * y * t⁻¹) * ((t * s) * y * (t * s)⁻¹) *
              ((t * t) * y * (t * t)⁻¹) * ((t * (s * t)) * y * (t * (s * t))⁻¹) := by
              simp only [hτf]; group
          _ = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) * y * (s * y * s⁻¹) := by
              rw [hts y hy, htt y hy, htst y hy]
          _ = τf y := (hcomm4 hty huy hy hsy).2.1
    let τ : B →* B := MonoidHom.mk' (fun y => ⟨τf y, hτB y y.2⟩) (by
      intro y z
      apply Subtype.ext
      let _ : CommGroup B := { (inferInstance : Group B) with
        mul_comm := fun x y => Subtype.ext (hcommB _ x.2 _ y.2) }
      have e : ∀ x : G, ∀ a b : B, x * ((a : G) * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) :=
        fun x a b => by group
      have hsy : s * (y : G) * s⁻¹ ∈ B := A4On.conj_mem h.hs y.2
      have hsz : s * (z : G) * s⁻¹ ∈ B := A4On.conj_mem h.hs z.2
      have hty : t * (y : G) * t⁻¹ ∈ B := A4On.conj_mem h.ht y.2
      have htz : t * (z : G) * t⁻¹ ∈ B := A4On.conj_mem h.ht z.2
      have huy : (s * t) * (y : G) * (s * t)⁻¹ ∈ B := A4On.conj_mem hu y.2
      have huz : (s * t) * (z : G) * (s * t)⁻¹ ∈ B := A4On.conj_mem hu z.2
      have key : ∀ y₀ z₀ y₁ z₁ y₂ z₂ y₃ z₃ : B,
          (y₀ * z₀) * (y₁ * z₁) * (y₂ * z₂) * (y₃ * z₃) =
            (y₀ * y₁ * y₂ * y₃) * (z₀ * z₁ * z₂ * z₃) := fun _ _ _ _ _ _ _ _ => by ac_rfl
      have := congrArg Subtype.val (key y z ⟨_, hsy⟩ ⟨_, hsz⟩ ⟨_, hty⟩ ⟨_, htz⟩ ⟨_, huy⟩
        ⟨_, huz⟩)
      simp only [Subgroup.coe_mul] at this
      change τf ((y : G) * z) = τf y * τf z
      simp only [hτf, e s y z, e t y z, e (s * t) y z]
      exact this)
    have hτapp : ∀ y : B, ((τ y : B) : G) = τf y := fun _ => rfl
    have hτFid : ∀ y ∈ F, τf y = y := by
      intro y hy
      obtain ⟨hyB, hsy, hty⟩ := A4On.mem_fixST.mp hy
      have huy : (s * t) * y * (s * t)⁻¹ = y := by
        rw [show s * t * y * (s * t)⁻¹ = s * (t * y * t⁻¹) * s⁻¹ by group, hty, hsy]
      simp only [hτf, hsy, hty, huy]
      calc y * y * y * y = y ^ 3 * y := by rw [pow_three]; simp only [mul_assoc]
        _ = y := by rw [hB.2 y hyB, one_mul]
    set Y : Subgroup G := τ.ker.map B.subtype with hY
    have hYB : Y ≤ B := Subgroup.map_subtype_le _
    have hmemY : ∀ y, y ∈ Y ↔ y ∈ B ∧ τf y = 1 := by
      intro y
      constructor
      · rintro ⟨⟨y', hy'⟩, hk, rfl⟩
        exact ⟨hy', (hτapp _).symm.trans (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))⟩
      · rintro ⟨hy, hτ1⟩
        exact ⟨⟨y, hy⟩, MonoidHom.mem_ker.mpr (Subtype.ext ((hτapp _).trans hτ1)), rfl⟩
    have hYcard : Nat.card Y = 9 := by
      have hYk : Nat.card Y = Nat.card τ.ker :=
        Subgroup.card_map_of_injective B.subtype_injective
      have hrange : Nat.card τ.range ≤ 3 := by
        rw [← hF3]
        have hle : τ.range ≤ F.subgroupOf B := by
          rintro _ ⟨y, rfl⟩
          rw [Subgroup.mem_subgroupOf]
          exact hτF y y.2
        calc Nat.card τ.range ≤ Nat.card (F.subgroupOf B) := Subgroup.card_le_of_le hle
          _ = Nat.card F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
      have hmul : Nat.card τ.ker * Nat.card τ.range = 27 := by
        rw [← Subgroup.index_ker, Subgroup.card_mul_index, h27]
      have hdvd : Nat.card τ.ker ∣ 3 ^ 3 := by
        rw [show 3 ^ 3 = 27 by norm_num, ← hmul]
        exact Dvd.intro _ rfl
      obtain ⟨k, hk, hKk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      have hne : τ.ker ≠ ⊤ := by
        intro htop
        obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
          by_contra hcon
          push Not at hcon
          have : X = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
          rw [this, Subgroup.card_bot] at hX3
          norm_num at hX3
        have hxB := hXB hxX
        have : (⟨x, hxB⟩ : B) ∈ τ.ker := htop ▸ Subgroup.mem_top _
        have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp this)
        rw [hτapp, hτFid x (hXF hxX)] at h1
        exact hx1 h1
      have hkpos : 0 < Nat.card τ.range := Nat.card_pos
      rw [hYk]
      interval_cases k
      · exfalso
        rw [hKk] at hmul
        omega
      · exfalso
        rw [hKk] at hmul
        omega
      · simpa using hKk
      · exfalso
        apply hne
        exact Subgroup.eq_top_of_card_eq _ (by rw [hKk]; simpa [Nat.card_congr] using h27.symm)
    have hYs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
      intro y hy
      obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
      have hsy := A4On.conj_mem h.hs hyB
      have hty := A4On.conj_mem h.ht hyB
      have huy := A4On.conj_mem hu hyB
      refine (hmemY _).mpr ⟨hsy, ?_⟩
      calc τf (s * y * s⁻¹) = (s * y * s⁻¹) * ((s * s) * y * (s * s)⁻¹) *
            ((t * s) * y * (t * s)⁻¹) * ((s * t * s) * y * (s * t * s)⁻¹) := by
            simp only [hτf]; group
        _ = (s * y * s⁻¹) * y * ((s * t) * y * (s * t)⁻¹) * (t * y * t⁻¹) := by
            rw [hss y hyB, hts y hyB, hsts y hyB]
        _ = τf y := (hcomm4 hsy hyB huy hty).1
        _ = 1 := hτ1
    have hYt : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
      intro y hy
      obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
      have hsy := A4On.conj_mem h.hs hyB
      have hty := A4On.conj_mem h.ht hyB
      have huy := A4On.conj_mem hu hyB
      refine (hmemY _).mpr ⟨hty, ?_⟩
      calc τf (t * y * t⁻¹) = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) *
            ((t * t) * y * (t * t)⁻¹) * ((s * t * t) * y * (s * t * t)⁻¹) := by
            simp only [hτf]; group
        _ = (t * y * t⁻¹) * ((s * t) * y * (s * t)⁻¹) * y * (s * y * s⁻¹) := by
            rw [htt y hyB, hstt y hyB]
        _ = τf y := (hcomm4 hty huy hyB hsy).2.1
        _ = 1 := hτ1
    have hYg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
      intro y hy
      obtain ⟨hyB, hτ1⟩ := (hmemY y).mp hy
      have hsy := A4On.conj_mem h.hs hyB
      have hty := A4On.conj_mem h.ht hyB
      have huy := A4On.conj_mem hu hyB
      have hgy := A4On.conj_mem h.hg hyB
      refine (hmemY _).mpr ⟨hgy, ?_⟩
      have e1 : s * (g * y * g⁻¹) * s⁻¹ = g * ((s * t) * y * (s * t)⁻¹) * g⁻¹ := by
        rw [← h.gst _ hgy]
        group
      have e2 : t * (g * y * g⁻¹) * t⁻¹ = g * (s * y * s⁻¹) * g⁻¹ := by
        rw [← h.gs _ hgy]
        group
      have e3 : (s * t) * (g * y * g⁻¹) * (s * t)⁻¹ = g * (t * y * t⁻¹) * g⁻¹ := by
        rw [← h.gt _ hgy]
        group
      calc τf (g * y * g⁻¹) = (g * y * g⁻¹) * (s * (g * y * g⁻¹) * s⁻¹) *
            (t * (g * y * g⁻¹) * t⁻¹) * ((s * t) * (g * y * g⁻¹) * (s * t)⁻¹) := rfl
        _ = g * (y * ((s * t) * y * (s * t)⁻¹) * (s * y * s⁻¹) * (t * y * t⁻¹)) * g⁻¹ := by
            rw [e1, e2, e3]
            group
        _ = g * τf y * g⁻¹ := by rw [(hcomm4 hyB huy hsy hty).2.2]
        _ = 1 := by rw [hτ1]; group
    exact h.false_of_order_nine hB h27 hYB hYcard (mem_normalizer_of_conj_mem hYs)
      (mem_normalizer_of_conj_mem hYt) (mem_normalizer_of_conj_mem hYg)
  · exact h.false_of_order_nine hB h27 hFB hF9 hsF htF hgF

theorem A4On.eq_bot_or_eq [Finite G] {B X : Subgroup G} {s t g : G} (h : A4On B s t g)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h27 : Nat.card B = 27) (hXB : X ≤ B)
    (hsX : s ∈ Subgroup.normalizer (X : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = B := by
  have hdvd : Nat.card X ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le hXB
  obtain ⟨k, hk, hXk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · left
    exact Subgroup.eq_bot_of_card_eq X (by simpa using hXk)
  · exact (h.false_of_order_three hB h27 hXB (by simpa using hXk) hsX htX hgX).elim
  · exact (h.false_of_order_nine hB h27 hXB (by simpa using hXk) hsX htX hgX).elim
  · right
    exact Subgroup.eq_of_le_of_card_ge hXB (by rw [hXk, h27]; norm_num)

end CFSG.RankThree.PartTwo.Sec21.Item2130LStarProof
