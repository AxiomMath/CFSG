module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoS34_isQuasisimple_coordBlockSU (hK : Nat.card K = 4) {N : ℕ} {J : Finset (Fin N)}
    (hJ : J.card = 4) : CFSG.IsQuasisimple ↥(coordBlockSU K 2 1 J) := by
  have h4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have e : ↥(coordBlockSU K 2 1 J) ≃* Su K 2 1 J.card :=
    (MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := 2) (f := 1) J)).symm
  have e2 : Su K 2 1 J.card ≃* ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K J.card) :=
    MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) h4 J.card)
  have hunit : CFSG.IsQuasisimple ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K J.card) :=
    CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU
      ⟨Nat.prime_two, le_refl 1, by rw [h4]; norm_num⟩ (by omega) (by
        intro h
        have h1 := congrArg Prod.fst h
        simp only at h1
        omega)
  exact CFSG.IsQuasisimple.of_mulEquiv (e.trans e2) hunit

theorem qTwoS34_center_unitarySU_card (hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K) {n : ℕ} (hn : n = 4) :
    Nat.card ↥(Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K n)) ≤ 3 := by
  subst hn
  have hbot : Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 4) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hz' := CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_le_unitaryScalars hdata 4 hz
    obtain ⟨c, -, hc4, hzc⟩ := CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars.1 hz'
    have hc4' : (c : K) ^ 4 = 1 := by
      have := congrArg Units.val hc4
      simpa using this
    have h2 : (c : K) ^ 2 = 1 := by
      apply (CharTwo.sq_inj).1
      rw [← pow_mul, one_pow]
      exact hc4'
    have h1 : (c : K) = 1 := by
      apply (CharTwo.sq_inj).1
      rw [one_pow]
      exact h2
    have hc : c = 1 := Units.ext h1
    subst hc
    exact Subtype.ext (by simpa using hzc)
  rw [hbot, Subgroup.card_bot]
  norm_num

theorem qTwoS34_center_card_le_three (hK : Nat.card K = 4) {N : ℕ} {J : Finset (Fin N)}
    (hJ : J.card = 4) : Nat.card ↥(Subgroup.center ↥(coordBlockSU K 2 1 J)) ≤ 3 := by
  have h4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have e : ↥(coordBlockSU K 2 1 J) ≃* Su K 2 1 J.card :=
    (MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := 2) (f := 1) J)).symm
  have e2 : Su K 2 1 J.card ≃* ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K J.card) :=
    MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) h4 J.card)
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_refl 1, by rw [h4]; norm_num⟩
  calc Nat.card ↥(Subgroup.center ↥(coordBlockSU K 2 1 J))
      = Nat.card ↥(Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K J.card)) :=
        Nat.card_congr (Subgroup.centerCongr (e.trans e2)).toEquiv
    _ ≤ 3 := qTwoS34_center_unitarySU_card hdata hJ

theorem qTwoS34_card_le_of_ne_top {S : Type} [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple S) (hZ : Nat.card ↥(Subgroup.center S) ≤ 3)
    (hcard : Nat.card S = 25920) {Y : Subgroup S} (hY : Y ≠ ⊤) :
    Nat.card ↥Y ≤ 3240 := by
  classical
  let φ := MulAction.toPermHom S (S ⧸ Y)
  have hker : φ.ker = Y.normalCore := (Subgroup.normalCore_eq_ker Y).symm
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  have hkerne : φ.ker ≠ ⊤ := by
    intro htop
    apply hY
    rw [hker] at htop
    exact top_le_iff.mp (htop ▸ Y.normalCore_le)
  have hkerle : φ.ker ≤ Subgroup.center S :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff S).2.2.1.1 hq) φ.ker hkerne
  have hkercard : Nat.card ↥φ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hkerle).trans hZ
  have h1 : Nat.card S = Nat.card (S ⧸ φ.ker) * Nat.card ↥φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (S ⧸ φ.ker) = Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h3 : Nat.card ↥φ.range ≤ (Nat.card (S ⧸ Y)).factorial := by
    refine (Subgroup.card_le_card_group (H := φ.range)).trans ?_
    rw [Nat.card_perm]
  have h4 : 25920 ≤ (Nat.card (S ⧸ Y)).factorial * 3 := by
    rw [← hcard, h1, h2]
    exact Nat.mul_le_mul h3 hkercard
  have hk : 8 ≤ Nat.card (S ⧸ Y) := by
    by_contra hlt
    push Not at hlt
    have h7 : (Nat.card (S ⧸ Y)).factorial ≤ (7 : ℕ).factorial :=
      Nat.factorial_le (by omega)
    have h5040 : (7 : ℕ).factorial = 5040 := by decide
    omega
  have h5 : Nat.card S = Nat.card (S ⧸ Y) * Nat.card ↥Y :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Y
  have h6 : 8 * Nat.card ↥Y ≤ Nat.card (S ⧸ Y) * Nat.card ↥Y := Nat.mul_le_mul_right _ hk
  omega

theorem qTwoS34_eq_of_card_ge {G : Type} [Group G] [Finite G] {S Y : Subgroup G} (hYS : Y ≤ S)
    (hq : CFSG.IsQuasisimple ↥S) (hZ : Nat.card ↥(Subgroup.center ↥S) ≤ 3)
    (hcard : Nat.card ↥S = 25920) (hY : 7776 ≤ Nat.card ↥Y) : Y = S := by
  by_contra hne
  have hHne : Y.subgroupOf S ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hYS ?_
    intro y hy
    have : (⟨y, hy⟩ : ↥S) ∈ Y.subgroupOf S := by rw [htop]; trivial
    exact this
  have h1 := qTwoS34_card_le_of_ne_top hq hZ hcard hHne
  have h2 : Nat.card ↥(Y.subgroupOf S) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYS).toEquiv
  omega

theorem qTwoS34_sup_eq (hK : Nat.card K = 4) {N : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∪ B).card = 4) :
    coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B = coordBlockSU K 2 1 (A ∪ B) :=
  qTwoS34_eq_of_card_ge
    (sup_le (qTwoS34_coordBlockSU_mono Finset.subset_union_left)
      (qTwoS34_coordBlockSU_mono Finset.subset_union_right))
    (qTwoS34_isQuasisimple_coordBlockSU hK (J := A ∪ B) hAB)
    (qTwoS34_center_card_le_three hK hAB)
    (by rw [qTwoS34_card_coordBlockSU, hAB, qTwoS34_card_Su_four hK])
    (qTwoS34_card_sup_ge hK hA hB hAB)

end CFSG.StandardType.QTwo

end
