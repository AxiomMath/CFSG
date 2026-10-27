module

public import CFSG.RankThree.PartTwo.Sec4.Item413Cases

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item223CensusResProof

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

section Orders

variable {p f : ℕ} {K : Type} [Field K]

theorem card_unitarySU_three' (h : UnitaryFieldData p f K) :
    Nat.card (unitarySU p f K 3) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  norm_num
  ring

theorem card_unitaryPSU_three_mul (h : UnitaryFieldData p f K) :
    Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) = Nat.card (unitarySU p f K 3) := by
  have := h.finite
  rw [← card_unitaryScalars h (by norm_num)]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem su3Poly_lt {q q' : ℕ} (hq : 2 ≤ q) (hqq : q < q') :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) := by
  have h1 : q ^ 3 < q' ^ 3 := Nat.pow_lt_pow_left hqq (by norm_num)
  have h2 : q ^ 2 - 1 ≤ q' ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hqq.le 2) 1
  have h4 : 0 < q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  calc q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q' ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by omega)
        exact Nat.mul_lt_mul_of_pos_right h1 h4
    _ ≤ q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1) := by gcongr

theorem su3Poly_inj {q q' : ℕ} (hq : 2 ≤ q) (hq' : 2 ≤ q')
    (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 + 1)) : q = q' := by
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd h (su3Poly_lt hq hlt).ne
  · exact heq
  · exact absurd h (su3Poly_lt hq' hgt).ne'

theorem two_le_pow_of_unitaryFieldData (h : UnitaryFieldData p f K) : 2 ≤ p ^ f :=
  (h.prime.two_le).trans (Nat.le_self_pow (by have := h.one_le; omega) p)

variable {p' f' : ℕ} {K' : Type} [Field K']

theorem eq_of_unitarySU_three (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p' f' K')
    (e : unitarySU p' f' K' 3 ≃* unitarySU p f K 3) : p' ^ f' = p ^ f := by
  have hc := Nat.card_congr e.toEquiv
  rw [card_unitarySU_three' h, card_unitarySU_three' h'] at hc
  exact su3Poly_inj (two_le_pow_of_unitaryFieldData h') (two_le_pow_of_unitaryFieldData h) hc

theorem eq_of_unitaryPSU_three (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p' f' K')
    (h3 : 3 ∣ p ^ f + 1) (h3' : 3 ∣ p' ^ f' + 1) (e : unitaryPSU h' 3 ≃* unitaryPSU h 3) :
    p' ^ f' = p ^ f := by
  have hc := Nat.card_congr e.toEquiv
  have h1 := card_unitaryPSU_three_mul h
  have h2 := card_unitaryPSU_three_mul h'
  rw [Nat.gcd_eq_left h3, card_unitarySU_three' h] at h1
  rw [Nat.gcd_eq_left h3', card_unitarySU_three' h'] at h2
  exact su3Poly_inj (two_le_pow_of_unitaryFieldData h') (two_le_pow_of_unitaryFieldData h)
    (by rw [← h1, ← h2, hc])

theorem eq_and_eq_of_pow_eq (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p' f' K')
    (hq : p' ^ f' = p ^ f) : p' = p ∧ f' = f :=
  Nat.Prime.pow_inj' h'.prime h.prime (by have := h'.one_le; omega)
    (by have := h.one_le; omega) hq

end Orders

section Field

variable {p f : ℕ} {K K' : Type} [Field K] [Field K'] (ψ : K' ≃+* K)

@[expose] noncomputable def glEquiv3 : GL (Fin 3) K' ≃* GL (Fin 3) K where
  toFun := GeneralLinearGroup.map ψ.toRingHom
  invFun := GeneralLinearGroup.map ψ.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

theorem coe_glEquiv3 (A : GL (Fin 3) K') :
    ((glEquiv3 ψ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ψ.toRingHom.mapMatrix (A : Matrix (Fin 3) (Fin 3) K') :=
  rfl

theorem map_bar_eq (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K') (c : K') :
    ψ (h'.bar c) = h.bar (ψ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem unitary_map (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    {A : Matrix (Fin 3) (Fin 3) K'} (hA : (A.map h'.bar)ᵀ * A = 1) :
    ((ψ.toRingHom.mapMatrix A).map h.bar)ᵀ * ψ.toRingHom.mapMatrix A = 1 := by
  have hcomm : (ψ.toRingHom.mapMatrix A).map h.bar = ψ.toRingHom.mapMatrix (A.map h'.bar) := by
    ext i j
    simp [(map_bar_eq ψ h h' _).symm]
  have ht : (ψ.toRingHom.mapMatrix (A.map h'.bar))ᵀ = ψ.toRingHom.mapMatrix ((A.map h'.bar)ᵀ) := by
    ext i j
    simp
  rw [hcomm, ht, ← map_mul, hA, map_one]

theorem glEquiv3_mem_unitarySU (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    {A : GL (Fin 3) K'} (hA : A ∈ unitarySU p f K' 3) :
    glEquiv3 ψ A ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h'] at hA
  rw [mem_unitarySU_iff h, coe_glEquiv3, ← RingHom.map_det, hA.1, map_one]
  exact ⟨rfl, unitary_map ψ h h' hA.2⟩

theorem glEquiv3_mem_unitaryIsom3 (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    {A : GL (Fin 3) K'} (hA : A ∈ unitaryIsom3 h') :
    glEquiv3 ψ A ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3] at hA ⊢
  rw [coe_glEquiv3]
  exact unitary_map ψ h h' hA

@[expose] noncomputable def suEquiv (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K') :
    unitarySU p f K' 3 ≃* unitarySU p f K 3 where
  toFun g := ⟨glEquiv3 ψ g, glEquiv3_mem_unitarySU ψ h h' g.2⟩
  invFun g := ⟨(glEquiv3 ψ).symm g, by
    have := glEquiv3_mem_unitarySU ψ.symm h' h g.2
    exact this⟩
  left_inv g := Subtype.ext ((glEquiv3 ψ).symm_apply_apply _)
  right_inv g := Subtype.ext ((glEquiv3 ψ).apply_symm_apply _)
  map_mul' g g' := Subtype.ext (map_mul (glEquiv3 ψ) _ _)

@[expose] noncomputable def psuEquiv (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    (hq : 2 < p ^ f) : unitaryPSU h' 3 ≃* unitaryPSU h 3 :=
  (suCenterEquiv h' hq).symm.trans ((Sec4.quotientCenterCongr (suEquiv ψ h h')).trans
    (suCenterEquiv h hq))

theorem psuEquiv_mk (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    (hq : 2 < p ^ f) (g : unitarySU p f K' 3) :
    psuEquiv ψ h h' hq (g : unitaryPSU h' 3) = ((suEquiv ψ h h' g : unitarySU p f K 3) :
      unitaryPSU h 3) :=
  rfl

theorem psuEquiv_symm_mk (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    (hq : 2 < p ^ f) (g : unitarySU p f K 3) :
    (psuEquiv ψ h h' hq).symm (g : unitaryPSU h 3) =
      (((suEquiv ψ h h').symm g : unitarySU p f K' 3) : unitaryPSU h' 3) := by
  apply (psuEquiv ψ h h' hq).injective
  rw [MulEquiv.apply_symm_apply, psuEquiv_mk, MulEquiv.apply_symm_apply]

theorem congr_psuConj_suEquiv (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p f K')
    (hq : 2 < p ^ f) (A : unitaryIsom3 h') :
    MulAut.congr (psuEquiv ψ h h' hq) (psuConj h' A) =
      psuConj h ⟨glEquiv3 ψ A, glEquiv3_mem_unitaryIsom3 ψ h h' A.2⟩ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [psuEquiv_symm_mk, psuConj_mk, psuEquiv_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    change glEquiv3 ψ (A * ((glEquiv3 ψ).symm g) * A⁻¹) =
      glEquiv3 ψ A * g * (glEquiv3 ψ A)⁻¹
    simp only [map_mul, Subgroup.coe_inv, map_inv, MulEquiv.apply_symm_apply]

theorem congr_mem_psuConj_range_suEquiv (h : UnitaryFieldData p f K)
    (h' : UnitaryFieldData p f K') (hq : 2 < p ^ f) {τ : MulAut (unitaryPSU h' 3)}
    (hτ : τ ∈ (psuConj h').range) :
    MulAut.congr (psuEquiv ψ h h' hq) τ ∈ (psuConj h).range := by
  obtain ⟨A, rfl⟩ := hτ
  rw [congr_psuConj_suEquiv]
  exact ⟨_, rfl⟩

end Field

section Inndiag

variable {p f p' f' : ℕ} {K K' : Type} [Field K] [Field K']

theorem congr_mem_psuConj_range_of_eq (h : UnitaryFieldData p f K)
    (h' : UnitaryFieldData p f K') (hq : 2 < p ^ f) (φ : unitaryPSU h' 3 ≃* unitaryPSU h 3)
    {τ : MulAut (unitaryPSU h' 3)} (hτ : τ ∈ (psuConj h').range) :
    MulAut.congr φ τ ∈ (psuConj h).range := by
  have := h.finite
  have := h'.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  let ψ : K' ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h.card, h'.card])
  set Ψ := psuEquiv ψ h h' hq
  set α : MulAut (unitaryPSU h' 3) := φ.trans Ψ.symm
  have hφ : MulAut.congr φ τ = MulAut.congr Ψ (α * τ * α⁻¹) := by
    ext x
    simp [α, MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_def]
  rw [hφ]
  apply congr_mem_psuConj_range_suEquiv
  exact (stdPinnedPSU3_stable (h := h') hq).normal.conj_mem τ hτ α

theorem congr_mem_psuConj_range (h : UnitaryFieldData p f K) (h' : UnitaryFieldData p' f' K')
    (h3 : 3 ∣ p ^ f + 1) (h3' : 3 ∣ p' ^ f' + 1) (hq' : 2 < p' ^ f')
    (φ : unitaryPSU h' 3 ≃* unitaryPSU h 3) {τ : MulAut (unitaryPSU h' 3)}
    (hτ : τ ∈ (psuConj h').range) : MulAut.congr φ τ ∈ (psuConj h).range := by
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_pow_eq h h' (eq_of_unitaryPSU_three h h' h3 h3' φ)
  exact congr_mem_psuConj_range_of_eq h h' hq' φ hτ

theorem centerDescend_congr {S S' : Type} [Group S] [Group S'] (φ : S' ≃* S) (σ : MulAut S') :
    centerDescend S (MulAut.congr φ σ) =
      MulAut.congr (Sec4.quotientCenterCongr φ) (centerDescend S' σ) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [centerDescend_mk]
    have h1 : (Sec4.quotientCenterCongr φ).symm (g : S ⧸ Subgroup.center S) =
        ((φ.symm g : S') : S' ⧸ Subgroup.center S') := by
      apply (Sec4.quotientCenterCongr φ).injective
      rw [MulEquiv.apply_symm_apply]
      change _ = QuotientGroup.mk (φ (φ.symm g))
      rw [MulEquiv.apply_symm_apply]
    rw [h1, centerDescend_mk]
    rfl

theorem centerDescend_congr_mem_psuConj_range (h : UnitaryFieldData p f K)
    (h' : UnitaryFieldData p' f' K') (hq : 2 < p ^ f) (hq' : 2 < p' ^ f')
    (φ : unitarySU p' f' K' 3 ≃* unitarySU p f K 3) {σ : MulAut (unitarySU p' f' K' 3)}
    (hσ : MulAut.congr (suCenterEquiv h' hq') (centerDescend _ σ) ∈ (psuConj h').range) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (MulAut.congr φ σ)) ∈
      (psuConj h).range := by
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_pow_eq h h' (eq_of_unitarySU_three h h' φ)
  set χ : unitaryPSU h' 3 ≃* unitaryPSU h 3 :=
    (suCenterEquiv h' hq').symm.trans ((Sec4.quotientCenterCongr φ).trans (suCenterEquiv h hq))
  have hχ : MulAut.congr (suCenterEquiv h hq) (centerDescend _ (MulAut.congr φ σ)) =
      MulAut.congr χ (MulAut.congr (suCenterEquiv h' hq') (centerDescend _ σ)) := by
    rw [centerDescend_congr]
    ext x
    simp [χ, MulAut.congr_apply]
  rw [hχ]
  exact congr_mem_psuConj_range_of_eq h h' hq χ hσ

end Inndiag

end Item223CensusResProof

end CFSG.RankThree.PartTwo.Sec21
