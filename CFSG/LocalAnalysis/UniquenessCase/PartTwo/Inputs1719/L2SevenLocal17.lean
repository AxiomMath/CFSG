module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Blueprint.Catalog
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_L27Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsL2Odd Y 7 →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      (∃ X : Subgroup Y, Nat.card X = 3 ∧ Permutes X S ∧
        ¬ X ≤ Subgroup.center Y) ∧
      (∃ X₁ X₂ : Subgroup Y, Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧ X₁ ≠ X₂ ∧
        Permutes X₁ S ∧ Permutes X₂ S ∧ S ⊔ X₁ ⊔ X₂ = ⊤ ∧
        Nonempty (Bar2 (S ⊔ X₁) ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Bar2 (S ⊔ X₂) ≃* Equiv.Perm (Fin 3)))

theorem K_L27Extension : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
    K.Normal → IsL2Odd ↥K 7 →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    K = ⊤ ∨ CFSG.Quasithin.F6.IsPGL2 7 Y := by
  intro Y _ _ K hKn hL2 hcent hidx
  classical
  have : K.Normal := hKn
  obtain ⟨-, F, _, _, hFcard, ⟨eK⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide)
  have hF7 : Nat.card F = 7 := by rw [hFcard, pow_one]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let e' : ↥K ≃* CFSG.GorensteinWalter.PSL2 F :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hoddF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by norm_num, ⟨3, by norm_num⟩, le_rfl, by rw [hF7]; norm_num⟩
  have hcardF : 3 < Nat.card F := by rw [hF7]; norm_num
  have hsimple : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF7]; norm_num)
  have hZPSL : Subgroup.center (CFSG.GorensteinWalter.PSL2 F) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (Subgroup.center (CFSG.GorensteinWalter.PSL2 F)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := CFSG.ABGLocalTools.psl2_exists_not_commute (K := F)
      refine hab (Subgroup.mem_center_iff.mp ?_ b).symm
      rw [h]
      exact Subgroup.mem_top a
  have hZK : Subgroup.center ↥K = ⊥ := by
    have hmap := Subgroup.map_center_eq (f := e')
    rw [hZPSL] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥K) e'.injective).1 hmap
  have hcen : Subgroup.centralizer (K : Set Y) = ⊥ := by
    rw [hcent, hZK]
    simp
  have hker : (MulAut.conjNormal (H := K)).ker = ⊥ := by
    rw [CFSG.LargeEvenClassification.Helpers.conjNormal_ker_eq_centralizer, hcen]
  have hinj : Function.Injective (MulAut.conjNormal (H := K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hKcard : Nat.card ↥K = 168 := card_of_isL2Odd_seven hL2
  have hAut : Nat.card (MulAut ↥K) = 336 := by
    have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hF7 hoddF hcardF
    have h1 : Nat.card (MulAut ↥K) =
        Nat.card (MulAut (CFSG.GorensteinWalter.PSL2 F)) :=
      Nat.card_congr (MulAut.congr e').toEquiv
    have h2 : Nat.card (MulAut (CFSG.GorensteinWalter.PSL2 F)) =
        Nat.card (CFSG.GorensteinWalter.PGL2 F) := by
      rw [← Nat.card_congr (MulEquiv.ofBijective
        (CFSG.GorensteinWalter.pgl2InnerAutPSL2 F hoddF hcardF) hbij).toEquiv]
    rw [h1, h2, CFSG.GorensteinWalter.pgl2_card_formula, hF7]
    norm_num
  obtain ⟨n, hn⟩ := hidx
  have hY : Nat.card Y = 168 * 2 ^ n := by
    rw [← Subgroup.card_mul_index K, hn, hKcard]
  have hle : Nat.card Y ≤ 336 := by
    have h := Nat.card_le_card_of_injective (MulAut.conjNormal (H := K)) hinj
    rwa [hAut] at h
  have hn1 : n ≤ 1 := by
    have h2 : 168 * 2 ^ n ≤ 168 * 2 := by
      rw [show 168 * 2 = 336 by norm_num, ← hY]
      exact hle
    have h3 : 2 ^ n ≤ 2 ^ 1 := by
      simpa using Nat.le_of_mul_le_mul_left h2 (by norm_num)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · left
    rw [h0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  · right
    have hn1' : n = 1 := by omega
    rw [hn1'] at hn
    have hY336 : Nat.card Y = 336 := by rw [hY, hn1']; norm_num
    have hbijφ : Function.Bijective (MulAut.conjNormal (H := K)) :=
      hinj.bijective_of_nat_card_le (by rw [hY336, hAut])
    have hbijP := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hF7 hoddF hcardF
    let eY : Y ≃* MulAut ↥K := MulEquiv.ofBijective _ hbijφ
    let eP : CFSG.GorensteinWalter.PGL2 F ≃* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
      MulEquiv.ofBijective _ hbijP
    have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
        CFSG.Open.StatedScalars (Fin 2) F := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      rfl
    refine ⟨F, inferInstance, inferInstance, hF7, ⟨?_⟩⟩
    exact eY.trans ((MulAut.congr e').trans
      (eP.symm.trans (QuotientGroup.quotientMulEquivOfEq hcs)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end