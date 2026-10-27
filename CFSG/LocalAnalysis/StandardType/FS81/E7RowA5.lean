module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowA4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

@[expose] def IsAxis (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) (r : Coords 8) : Prop :=
  r ≠ 0 ∧ A *ᵥ r = -r ∧ ∀ w : Coords 8, ∃ c : ZMod 3, A *ᵥ w - w = c • r

set_option maxRecDepth 100000 in
theorem root7_of_axis_e1 {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) :
    ∀ c : ZMod 3, c ≠ 0 → IsRoot7 δ (c • ((-1 : ZMod 3) • Pi.single 1 1 - Pi.single 1 1)) := by
  rcases hδ with rfl | rfl <;> decide +kernel

set_option maxRecDepth 100000 in
theorem root7_of_axis_kl {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) :
    ∀ k l : Fin 8, 2 ≤ k.val → 2 ≤ l.val → k ≠ l → ∀ c ε : ZMod 3, c ≠ 0 → (ε = 1 ∨ ε = -1) →
      IsRoot7 δ (c • (ε • Pi.single l 1 - Pi.single k 1)) := by
  rcases hδ with rfl | rfl <;> decide +kernel

theorem axis_of_hSeven {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) {A : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hA : A ∈ hSeven) {r : Coords 8} (hr : IsAxis A r) : IsRoot7 δ r := by
  obtain ⟨σ, s, hs, ⟨h0, hs0, h1, hp⟩, rfl⟩ := hA
  obtain ⟨hr0, hneg, hrank⟩ := hr
  have hmove : ∃ j : Fin 8, spMat σ s *ᵥ Pi.single j 1 ≠ Pi.single j 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hId : spMat σ s = 1 := matrix_ext_mulVec fun w => by
      rw [Matrix.one_mulVec]
      have hw : w = ∑ j, w j • Pi.single j 1 := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hw, Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mulVec_smul, hall j]
    rw [hId, Matrix.one_mulVec] at hneg
    exact hr0 (eq_zero_of_neg_eq_self hneg.symm)
  obtain ⟨j, hj⟩ := hmove
  obtain ⟨c, hc⟩ := hrank (Pi.single j 1)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hc
    exact hj hc
  have hAj : spMat σ s *ᵥ Pi.single j 1 = s j • Pi.single (σ j) 1 := by
    funext i
    rw [spMat_mulVec, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = σ j
    · subst hi
      simp
    · have : σ.symm i ≠ j := fun e => hi (by rw [← e, Equiv.apply_symm_apply])
      simp [this, hi]
  have hrj : r = c⁻¹ • (s j • Pi.single (σ j) 1 - Pi.single j 1) := by
    rw [← hAj, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hsj := hs j
  by_cases hσj : σ j = j
  ·
    have hsj1 : s j = -1 := by
      rcases hsj with e | e
      · exfalso
        apply hj
        rw [hAj, hσj, e, one_smul]
      · exact e
    have hj1 : j = 1 := by
      by_contra hj1
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [hs0] at hsj1
        exact absurd hsj1 (by decide)
      have hfix : ∀ k, k ≠ j → σ k = k ∧ s k = 1 := by
        intro k hkj
        obtain ⟨d, hd⟩ := hrank (Pi.single k 1)
        have hrk : r k = 0 := by
          rw [hrj, hσj]
          simp [hkj]
        have hk' := congrFun hd k
        rw [spMat_mulVec_single, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hrk, mul_zero,
          sub_eq_zero, mul_one, Pi.single_eq_same] at hk'
        by_cases hσk : σ k = k
        · rw [hσk, Pi.single_eq_same] at hk'
          exact ⟨hσk, hk'⟩
        · exfalso
          rw [Pi.single_apply, if_neg (Ne.symm hσk)] at hk'
          exact absurd hk' (by decide)
      have hprod : ∏ i : Fin 6, s i.succ.succ = -1 := by
        have hjs : ∃ i : Fin 6, i.succ.succ = j := by
          refine ⟨⟨j.val - 2, by omega⟩, ?_⟩
          have hj2 : 2 ≤ j.val := by
            have h0' : j.val ≠ 0 := fun e => hj0 (Fin.ext e)
            have h1' : j.val ≠ 1 := fun e => hj1 (Fin.ext e)
            omega
          ext
          simp
          omega
        obtain ⟨i₀, hi₀⟩ := hjs
        rw [Finset.prod_eq_single i₀]
        · rw [hi₀, hsj1]
        · intro i _ hi
          refine (hfix _ fun e => hi ?_).2
          rw [← hi₀] at e
          exact Fin.succ_injective _ (Fin.succ_injective _ e)
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hprod] at hp
      exact absurd hp (by decide)
    subst hj1
    rw [hrj, hσj, hsj1]
    exact root7_of_axis_e1 hδ _ (inv_ne_zero hc0)
  ·
    have hj2 : 2 ≤ j.val := by
      by_contra hlt
      have : j = 0 ∨ j = 1 := by
        have : j.val = 0 ∨ j.val = 1 := by omega
        rcases this with e | e
        · exact Or.inl (Fin.ext e)
        · exact Or.inr (Fin.ext e)
      rcases this with rfl | rfl
      · exact hσj h0
      · exact hσj h1
    have hl2 : 2 ≤ (σ j).val := by
      by_contra hlt
      have : σ j = 0 ∨ σ j = 1 := by
        have : (σ j).val = 0 ∨ (σ j).val = 1 := by omega
        rcases this with e | e
        · exact Or.inl (Fin.ext e)
        · exact Or.inr (Fin.ext e)
      rcases this with e | e
      · have hj0 : j = 0 := σ.injective (e.trans h0.symm)
        exact hσj (by rw [hj0, h0])
      · have hj1 : j = 1 := σ.injective (e.trans h1.symm)
        exact hσj (by rw [hj1, h1])
    rw [hrj]
    exact root7_of_axis_kl hδ j (σ j) hj2 hl2 (Ne.symm hσj) _ _ (inv_ne_zero hc0) hsj


set_option maxRecDepth 100000 in
theorem card_signs_hSeven :
    (Finset.univ.filter fun s : Fin 8 → ZMod 3 =>
      (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1).card = 64 := by
  decide +kernel

theorem card_hSeven : Nat.card ↥hSeven = 46080 := by
  let P := {f : Equiv.Perm (Fin 8) // ∀ a, ¬ (a ≠ 0 ∧ a ≠ 1) → f a = a}
  let S := {s : Fin 8 → ZMod 3 //
    (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1}
  let F : P × S → Matrix (Fin 8) (Fin 8) (ZMod 3) := fun q => spMat q.1.1 q.2.1
  have hF : Function.Injective F := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, hs⟩⟩ ⟨⟨σ', hσ'⟩, ⟨s', hs'⟩⟩ h
    obtain ⟨h1, h2⟩ := spMat_injective hs.1 h
    subst h1
    subst h2
    rfl
  have hrange : Set.range F = hSeven := by
    ext A
    constructor
    · rintro ⟨⟨⟨σ, hσ⟩, ⟨s, hs, hs0, hp⟩⟩, rfl⟩
      exact ⟨σ, s, hs, ⟨hσ 0 (by simp), hs0, hσ 1 (by simp), hp⟩, rfl⟩
    · rintro ⟨σ, s, hs, ⟨h0, hs0, h1, hp⟩, rfl⟩
      refine ⟨(⟨σ, fun a ha => ?_⟩, ⟨s, hs, hs0, hp⟩), rfl⟩
      rw [not_and_or, not_not, not_not] at ha
      rcases ha with rfl | rfl
      · exact h0
      · exact h1
  have hP : Nat.card P = 720 := by
    rw [← Nat.card_congr (Equiv.Perm.subtypeEquivSubtypePerm fun a : Fin 8 => a ≠ 0 ∧ a ≠ 1),
      Nat.card_perm, Nat.card_eq_fintype_card]
    rfl
  have hS : Nat.card S = 64 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_signs_hSeven
  rw [← hrange, Nat.card_range_of_injective hF, Nat.card_prod, hP, hS]

@[expose] def lineStab1 : Subgroup (GL (Fin 8) (ZMod 3)) where
  carrier := {x | ∃ c : ZMod 3,
    (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1}
  one_mem' := ⟨1, by rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc,
      smul_smul]⟩
  inv_mem' := by
    rintro x ⟨c, hc⟩
    have e := mulVec_inv_mulVec x (Pi.single 1 1)
    rw [hc, Matrix.mulVec_smul] at e
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at e
      have := congrFun e 1
      simp at this
    refine ⟨c⁻¹, ?_⟩
    calc ((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1
        = c⁻¹ • (c • (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
            Pi.single 1 1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • Pi.single 1 1 := by rw [e]

theorem card_H1 (h : CoreHyp X) : Nat.card ↥(X ⊓ fixE0 7 ⊓ lineStab1) = 46080 := by
  rw [← card_hSeven]
  have hmem : ∀ x : ↥(X ⊓ fixE0 7 ⊓ lineStab1),
      ((x : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven := by
    rintro ⟨x, ⟨hxX, hxF⟩, hxL⟩
    exact h.hstab x hxX (mem_fixE0.mp hxF) hxL
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩)
  · intro a b e
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val e
  · rintro ⟨A, hA⟩
    obtain ⟨x, hx, rfl⟩ := h.exists_fix hA
    exact ⟨⟨x, hx, ⟨_, hSeven_mulVec_e1 hA⟩⟩, rfl⟩

theorem exists_conj_mem_hSeven (h : CoreHyp X) {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X ⊓ fixE0 7)
    (hg2 : g * g = 1) : ∃ y ∈ X ⊓ fixE0 7,
      ((y⁻¹ * g * y : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, -, hKH⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two
    (n := 10) (H := ⊥) (L := X ⊓ fixE0 7 ⊓ lineStab1) (by simp) (by rw [card_H1 h]; norm_num)
    bot_le
  have hKX : K ≤ X ⊓ fixE0 7 := hKH.trans inf_le_left
  have hK'card : Nat.card ↥(K.subgroupOf (X ⊓ fixE0 7)) = 2 ^ 10 := by
    rw [← hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have hK'p : IsPGroup 2 ↥(K.subgroupOf (X ⊓ fixE0 7)) := IsPGroup.of_card hK'card
  have hidx : ¬ 2 ∣ (K.subgroupOf (X ⊓ fixE0 7)).index := by
    have e := Subgroup.index_mul_card (K.subgroupOf (X ⊓ fixE0 7))
    rw [hK'card, h.hcard] at e
    have : (K.subgroupOf (X ⊓ fixE0 7)).index = 2835 := by omega
    rw [this]
    decide
  set S := hK'p.toSylow hidx
  set gX : ↥(X ⊓ fixE0 7) := ⟨g, hg⟩
  have hP : IsPGroup 2 ↥(Subgroup.zpowers gX) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simp [gX, pow_two, hg2]
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥(X ⊓ fixE0 7) S Q
  have hgQ : gX ∈ (Q : Subgroup ↥(X ⊓ fixE0 7)) := hPQ (Subgroup.mem_zpowers gX)
  rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hgQ
  obtain ⟨z, hzS, hz⟩ := hgQ
  have hzK : z ∈ K.subgroupOf (X ⊓ fixE0 7) := by
    have : (S : Subgroup ↥(X ⊓ fixE0 7)) = K.subgroupOf (X ⊓ fixE0 7) := IsPGroup.toSylow_coe _ _
    rw [← this]
    exact hzS
  have hzeq : z = y⁻¹ * gX * y := by
    rw [← hz, MulAut.smul_def, MulAut.conj_apply]
    group
  refine ⟨y, y.2, ?_⟩
  have hzL : ((z : ↥(X ⊓ fixE0 7)) : GL (Fin 8) (ZMod 3)) ∈ X ⊓ fixE0 7 ⊓ lineStab1 :=
    hKH (Subgroup.mem_subgroupOf.mp hzK)
  have hval : ((z : ↥(X ⊓ fixE0 7)) : GL (Fin 8) (ZMod 3)) =
      (y : GL (Fin 8) (ZMod 3))⁻¹ * g * y := by
    rw [hzeq]
    rfl
  rw [← hval]
  exact h.hstab _ hzL.1.1 (mem_fixE0.mp hzL.1.2) hzL.2

theorem axis_root_of_X1 (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {g : GL (Fin 8) (ZMod 3)} (hg : g ∈ X ⊓ fixE0 7)
    (hg2 : g * g = 1) {r : Coords 8} (hr : IsAxis (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) r) :
    IsRoot7 δ r := by
  obtain ⟨y, hy, hyH⟩ := exists_conj_mem_hSeven h hg hg2
  obtain ⟨hr0, hneg, hrank⟩ := hr
  have hax : IsAxis ((y⁻¹ * g * y : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))
      (((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ r) := by
    refine ⟨fun e => hr0 ?_, ?_, fun w => ?_⟩
    · have := congrArg (fun v => (y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) e
      simpa [mulVec_mulVec_inv] using this
    · rw [mulVec_gmul, mulVec_gmul, mulVec_mulVec_inv, hneg, Matrix.mulVec_neg]
    · obtain ⟨c, hc⟩ := hrank ((y : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w)
      refine ⟨c, ?_⟩
      rw [mulVec_gmul, mulVec_gmul]
      have e := congrArg
        (fun v => ((y⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) hc
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, mulVec_inv_mulVec] at e
      exact e
  have hroot := axis_of_hSeven hδ hyH hax
  have := orb1_mul hy ((horb _).mpr hroot)
  rw [mulVec_mulVec_inv] at this
  exact (horb r).mp this

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
