module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ThmRA
public import CFSG.Quasithin.Vol2.Ch10Reselect.GLemma
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelOfIv
public import CFSG.Quasithin.Vol2.Ch10Reselect.CardGL

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem false_of_caseIV_lineJ (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) [IsMulCommutative ↥(fsuVM T L I)] [Finite K] (hK4 : 4 ≤ Nat.card K)
    (M : RModel T L I K) {w : Fin 2 → K} (hw0 : w ≠ 0)
    (hw : ∀ (γ : ↥(fsuML T L)) (p : UTilde K), p ∈ linePair K w → actML M γ p ∈ linePair K w)
    (hJfsu : FSU G T L (M.lineJ w)) {x : G} (hx : x ∈ T)
    [IsMulCommutative ↥(fsuVM T L (CFSG.conjugate (M.lineJ w) x))]
    (hiv : Case3_2_6_iv T L (CFSG.conjugate (M.lineJ w) x)) : False := by
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_fsuUL T L I
  have hJ := jData_of_line hfsu hlt hA M hw0 hw
  have hJU : M.lineJ w ≤ fsuUL T L I := UModel.lineJ_le_U M w hLU
  have hfsuJ' := CFSG.Quasithin.Vol2.Ch10.fsu_conjugate hJfsu hx
  obtain ⟨K', hF', hfin', -, hK'4, ⟨M'⟩⟩ := exists_uModel hfsuJ' hiv
  have hVM' : fsuVM T L (CFSG.conjugate (M.lineJ w) x) = fsuV T (M.lineJ w) :=
    (CFSG.Quasithin.Vol2.Ch10.fsuVM_conjugate (I := M.lineJ w) hx).trans
      (hJ.fsuVM_eq h37 h38 ht htn)
  have hV : fsuV T (M.lineJ w) = M.lineJ w ⊔ CFSG.conjugate (M.lineJ w) t :=
    hJ.fsuV_eq h37 h38 ht htn
  have hUL' : fsuUL T L (CFSG.conjugate (M.lineJ w) x) = M.lineJ w :=
    (CFSG.Quasithin.Vol2.Ch10.fsuUL_conjugate (I := M.lineJ w) hx).trans
      (hJ.fsuUL_eq h37 h38 ht htn)
  have hJV' : M.lineJ w ≤ fsuVM T L (CFSG.conjugate (M.lineJ w) x) := by
    rw [hVM', hV]
    exact le_sup_left
  have hV'M : fsuVM T L (CFSG.conjugate (M.lineJ w) x) ≤ fsuVM T L I := by
    rw [hVM', hV]
    exact hJ.sup_le_fsuVM ht
  have hker : M.γ.ker = M'.γ.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hl
      rw [M.γ_ker, Subgroup.mem_centralizer_iff] at hl
      rw [M'.γ_ker, Subgroup.mem_centralizer_iff]
      intro h hh
      exact hl h (hV'M hh)
    · intro hl
      rw [M'.γ_ker, Subgroup.mem_centralizer_iff] at hl
      refine UModel.eq_one_of_centralizes_lineJ M hw0 hLU l ?_
      intro j hj
      have h1 : j * (l : G) = (l : G) * j := hl j (hJV' hj)
      rw [← h1, mul_inv_cancel_right]
  have hcard1 := UModel.card_lineJ M hw0 hLU
  have hcard2 := UModel.card_eq_pow_four M'
  rw [hUL'] at hcard2
  have hsub : (M.lineJ w ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (M.lineJ w) =
      (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (M.lineJ w) := by
    ext j
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨hJU j.2, h.2⟩, fun h => ⟨j.2, h.2⟩⟩
  rw [hsub] at hcard2
  have hcardeq : Nat.card ↥((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
      (M.lineJ w)) * Nat.card K ^ 2 =
      Nat.card ↥((fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf
      (M.lineJ w)) * Nat.card K' ^ 4 :=
    hcard1.symm.trans hcard2
  have hpow : Nat.card K ^ 2 = Nat.card K' ^ 4 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardeq
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K') :=
    card_eq_of_ker_eq M.γ M'.γ M.γ_surj M'.γ_surj hker
  rw [card_SL_two K, card_SL_two K'] at hSL
  have hq : Nat.card K = Nat.card K' ^ 2 := by
    have h2 : Nat.card K ^ 2 = (Nat.card K' ^ 2) ^ 2 := by
      rw [hpow]
      ring
    exact Nat.pow_left_injective (by norm_num) h2
  rw [hq] at hSL
  have h1 : 1 ≤ Nat.card K' ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.card K' ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by omega))
  zify [h1, h2] at hSL
  have h4 : (4 : ℤ) ≤ (Nat.card K' : ℤ) := by exact_mod_cast hK'4
  set x : ℤ := (Nat.card K' : ℤ) with hxdef
  have hfac : (x ^ 2 - 1) * (x ^ 2 * (x ^ 2 + 1) - x) = 0 := by
    linear_combination hSL
  have hA : (0 : ℤ) < x ^ 2 - 1 := by nlinarith
  have hB : (0 : ℤ) < x ^ 2 * (x ^ 2 + 1) - x := by nlinarith
  linarith [mul_pos hA hB]

end CFSG.Quasithin.Vol2.Ch10Reselect
