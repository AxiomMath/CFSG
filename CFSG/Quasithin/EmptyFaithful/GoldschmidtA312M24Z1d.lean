module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z1c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem alt8_nonabelian : ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  have := alternatingGroup.isSimpleGroup (α := Fin 8) (by simp)
  refine Seven.nonabelian_of_card_not_prime ?_
  have : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [this]
  norm_num

theorem isExt_Z1 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z1) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y) := by
  have hperf := Z1_perfect hB hY
  let eR : ↥rho1.range ≃* alternatingGroup (Fin 8) := MulEquiv.subgroupCongr rho1_range
  have hsA : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥rho1.range := (MulEquiv.isSimpleGroup_congr eR).mpr hsA
  have hnab : ∃ a b : ↥rho1.range, a * b ≠ b * a := by
    obtain ⟨a, b, h⟩ := alt8_nonabelian
    exact ⟨eR.symm a, eR.symm b, fun h' => h (by simpa using congrArg eR h')⟩
  have hsurj : Function.Surjective rho1.rangeRestrict := MonoidHom.rangeRestrict_surjective rho1
  have hker : rho1.rangeRestrict.ker = V1.subgroupOf Z1 := by
    rw [MonoidHom.ker_rangeRestrict, rho1_ker.2]
  have hsolv : Group.IsSolvable rho1.rangeRestrict.ker := by
    rw [hker]
    refine isSolvable_of_card_two_pow (n := 4) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe V1_le_Z1).toEquiv, card_V1]
    norm_num
  have hV : IsE2 4 ↥rho1.rangeRestrict.ker := by
    rw [hker]
    exact IsE2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe V1_le_Z1).symm V1_isE2
  have hQ : IsPSL 4 2 1 (↥Z1 ⧸ rho1.rangeRestrict.ker) :=
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight _
      ⟨(QuotientGroup.quotientKerEquivOfSurjective _ hsurj).trans eR⟩
  exact isExt_of_perfect_member hB hY hperf hnab rho1.rangeRestrict hsurj hsolv
    (fun V W _ _ e h => IsE2.of_mulEquiv e h) (fun V W _ _ e h => IsPSL.of_mulEquiv e h) hV hQ

end CFSG.Quasithin.A312M24
