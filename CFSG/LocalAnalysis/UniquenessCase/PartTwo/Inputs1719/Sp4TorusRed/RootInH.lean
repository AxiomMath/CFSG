module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRootTransport
public import CFSG.ClassicalGroups.Symplectic.Sp4TorusTwoSubgroup
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped Matrix Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem pairRootElt_mem_of_mem_sup {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) {a b : Fin 2 ⊕ Fin 2}
    (hab : a ≠ b) {t : K} (ht : pairRootElt hab t ∈ H ⊔ torus 2 K) : pairRootElt hab t ∈ H := by
  have : Fintype K := Fintype.ofFinite K
  have hcoe : ((H ⊔ torus 2 K : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) =
      (H : Set (StatedSp 2 K)) * (torus 2 K : Set (StatedSp 2 K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H (torus 2 K) hT
  have ht' : pairRootElt hab t ∈
      (H : Set (StatedSp 2 K)) * (torus 2 K : Set (StatedSp 2 K)) := by
    rw [← hcoe]
    exact ht
  obtain ⟨h, hh, d, hd, hx⟩ := Set.mem_mul.mp ht'
  obtain ⟨s, rfl⟩ := hd
  rw [← hx]
  have hsq : (h * torusHom s) * (h * torusHom s) = 1 := by
    rw [hx]
    apply statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_pairRootElt, pairRootMat_mul hab,
      CharTwo.add_self_eq_zero, pairRootMat_zero]
    rfl
  have hmem : torusHom s * h * (torusHom s)⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp (hT (torusHom_mem_torus s)) h).mp hh
  have hdh : torusHom s * h * (torusHom s)⁻¹ =
      h⁻¹ * (torusHom s)⁻¹ * (torusHom s)⁻¹ := by
    have h1 : torusHom s * h * torusHom s = h⁻¹ := by
      have h2 : h * (torusHom s * h * torusHom s) = 1 := by
        rw [← hsq]; group
      calc torusHom s * h * torusHom s = h⁻¹ * (h * (torusHom s * h * torusHom s)) := by group
        _ = h⁻¹ := by rw [h2, mul_one]
    calc torusHom s * h * (torusHom s)⁻¹
        = (torusHom s * h * torusHom s) * ((torusHom s)⁻¹ * (torusHom s)⁻¹) := by group
      _ = h⁻¹ * (torusHom s)⁻¹ * (torusHom s)⁻¹ := by rw [h1, mul_assoc]
  have hd2inv : (torusHom s)⁻¹ * (torusHom s)⁻¹ ∈ H := by
    have h3 : (torusHom s)⁻¹ * (torusHom s)⁻¹ =
        h * (torusHom s * h * (torusHom s)⁻¹) := by rw [hdh]; group
    rw [h3]
    exact H.mul_mem hh hmem
  have hd2 : (torusHom s) ^ 2 ∈ H := by
    have h4 : (torusHom s) ^ 2 = ((torusHom s)⁻¹ * (torusHom s)⁻¹)⁻¹ := by group
    rw [h4]
    exact H.inv_mem hd2inv
  have hpow : (torusHom s) ^ (Nat.card K - 1) = 1 := by
    have hs : s ^ (Nat.card K - 1) = 1 := by
      funext i
      apply Units.ext
      rw [Pi.pow_apply, Pi.one_apply, Units.val_pow_eq_pow_val, Units.val_one]
      have h := FiniteField.pow_card_sub_one_eq_one ((s i : Kˣ) : K) (Units.ne_zero (s i))
      rwa [Nat.card_eq_fintype_card]
    rw [← map_pow, hs, map_one]
  have hq : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hfin : torusHom s ∈ H := by
    have e : torusHom s = ((torusHom s) ^ 2) ^ (Nat.card K / 2) := by
      have e1 : ((torusHom s) ^ 2) ^ (Nat.card K / 2) = (torusHom s) ^ Nat.card K := by
        rw [← pow_mul, Nat.two_mul_div_two_of_even hq]
      rw [e1, show Nat.card K = Nat.card K - 1 + 1 from
        (Nat.sub_one_add_one (Nat.card_pos (α := K)).ne').symm, pow_succ, hpow, one_mul]
    rw [e]
    exact H.pow_mem hd2 _
  exact H.mul_mem hh hfin

omit [Finite K] [CharP K 2] in
theorem conj_torusHom_pairRootElt (u : Fin 2 → Kˣ) {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) (t : K) :
    torusHom u * pairRootElt hab t * (torusHom u)⁻¹ =
      pairRootElt hab (Sp4.diagSp4TorusHomFun u a * (Sp4.diagSp4TorusHomFun u b)⁻¹ * t) := by
  rw [conj_pairRootElt (torusHom u) (isLinePerm_torusHom u) hab t]
  have e1 : (spMat (torusHom u)) a a = Sp4.diagSp4TorusHomFun u a := by
    rw [coe_torusHom, Matrix.diagonal_apply_eq]
    simp [Sp4.diagSp4TorusHomFun]
  have e2 : (spMat ((torusHom u)⁻¹)) b b = (Sp4.diagSp4TorusHomFun u b)⁻¹ := by
    rw [← map_inv, coe_torusHom, Matrix.diagonal_apply_eq]
    rcases b with i | i <;> simp [Sp4.diagSp4TorusHomFun]
  simp only [Equiv.Perm.one_apply, e1, e2]

theorem exists_mem_torus_conj_pairRootElt {a b : Fin 2 ⊕ Fin 2} (hab : a ≠ b) {t s : K}
    (ht : t ≠ 0) (hs : s ≠ 0) :
    ∃ d ∈ torus 2 K, d * pairRootElt hab t * d⁻¹ = pairRootElt hab s := by
  have hc : s / t ≠ 0 := div_ne_zero hs ht
  have hct : ((Units.mk0 (s / t) hc : Kˣ) : K) * t = s := by
    rw [Units.val_mk0, div_mul_cancel₀ s ht]
  rcases a with i | i
  · rcases b with j | j
    ·
      have hji : ¬j = i := fun h => hab (by rw [h])
      refine ⟨torusHom (Sp4.sp4TorusParam i (Units.mk0 (s / t) hc)), torusHom_mem_torus _, ?_⟩
      rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inl,
        Sp4.diagSp4TorusHomFun_sp4TorusParam_inl, if_pos rfl, if_neg hji]
      congr 1
      simp only [Units.val_mk0, inv_one, mul_one]
      exact hct
    ·
      by_cases hji : j = i
      ·
        subst i
        obtain ⟨w, hw⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (s / t)
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hc (by simpa using hw)
        refine ⟨torusHom (Sp4.sp4TorusParam j (Units.mk0 w hw0)), torusHom_mem_torus _, ?_⟩
        rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inl,
          Sp4.diagSp4TorusHomFun_sp4TorusParam_inr, if_pos rfl, if_pos rfl]
        congr 1
        simp only [Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
        rw [← hw]
        exact hct
      ·
        refine ⟨torusHom (Sp4.sp4TorusParam i (Units.mk0 (s / t) hc)), torusHom_mem_torus _, ?_⟩
        rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inl,
          Sp4.diagSp4TorusHomFun_sp4TorusParam_inr, if_pos rfl, if_neg hji]
        congr 1
        simp only [Units.val_mk0, inv_one, mul_one]
        exact hct
  · rcases b with j | j
    ·
      by_cases hji : j = i
      ·
        subst i
        obtain ⟨w, hw⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (s / t)
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hc (by simpa using hw)
        refine ⟨torusHom (Sp4.sp4TorusParam j (Units.mk0 w hw0)⁻¹), torusHom_mem_torus _, ?_⟩
        rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inl,
          Sp4.diagSp4TorusHomFun_sp4TorusParam_inr, if_pos rfl, if_pos rfl]
        congr 1
        simp only [Units.val_inv_eq_inv_val, inv_inv, Units.val_mk0]
        rw [← hw]
        exact hct
      ·
        refine ⟨torusHom (Sp4.sp4TorusParam i (Units.mk0 (s / t) hc)⁻¹), torusHom_mem_torus _, ?_⟩
        rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inl,
          Sp4.diagSp4TorusHomFun_sp4TorusParam_inr, if_pos rfl, if_neg hji]
        congr 1
        simp only [inv_inv, Units.val_mk0, inv_one, mul_one]
        exact hct
    ·
      have hji : ¬j = i := fun h => hab (by rw [h])
      refine ⟨torusHom (Sp4.sp4TorusParam i (Units.mk0 (s / t) hc)⁻¹), torusHom_mem_torus _, ?_⟩
      rw [conj_torusHom_pairRootElt, Sp4.diagSp4TorusHomFun_sp4TorusParam_inr,
        Sp4.diagSp4TorusHomFun_sp4TorusParam_inr, if_pos rfl, if_neg hji]
      congr 1
      simp only [inv_inv, Units.val_mk0, inv_one, mul_one]
      exact hct

theorem exists_root_subgroup_le_of_not_isRootFree {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hX : ¬ IsRootFree (H ⊔ torus 2 K)) :
    ∃ (a b : Fin 2 ⊕ Fin 2) (hab : a ≠ b), ∀ s : K, pairRootElt hab s ∈ H := by
  rw [IsRootFree] at hX
  have hne : ∃ (a b : Fin 2 ⊕ Fin 2) (hab : a ≠ b) (t : K),
      pairRootElt hab t ∈ H ⊔ torus 2 K ∧ t ≠ 0 := by
    by_contra h
    apply hX
    intro a b hab t hmem
    by_contra ht0
    exact h ⟨a, b, hab, t, hmem, ht0⟩
  obtain ⟨a, b, hab, t, ht, ht0⟩ := hne
  refine ⟨a, b, hab, fun s => ?_⟩
  by_cases hs : s = 0
  · subst hs
    have h1 : pairRootElt (a := a) (b := b) hab (0 : K) = 1 :=
      statedSp_ext (by rw [coe_pairRootElt, pairRootMat_zero]; rfl)
    rw [h1]
    exact H.one_mem
  · obtain ⟨d, hdT, hd⟩ := exists_mem_torus_conj_pairRootElt hab ht0 hs
    rw [← hd]
    exact (Subgroup.mem_normalizer_iff.mp (hT hdT) (pairRootElt hab t)).mp
      (pairRootElt_mem_of_mem_sup hT hab ht)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
