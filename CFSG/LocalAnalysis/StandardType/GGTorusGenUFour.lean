module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCover
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

theorem unitaryCoverAt_of_even
    {n d : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (he : Even d) (hd : 4 ≤ d) :
    UnitaryCoverAt n d K := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK (by omega)
  have : CharP K 2 := hU.charP
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : commutator (unitarySU 2 n K d) = ⊤ := by
    have := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hK hd
    exact Group.IsPerfect.commutator_eq_top
  refine unitaryCoverAt_of_section hperf ?_
  intro E _ _ π hπ hcen
  exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
    hK he hd hq hπ hcen

theorem largeEvenLabelAll_torusGenTableB_uFour_of_two_le
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (htag : lab.tag = .twA ∨ lab.tag = .twD)
    (hl : lab.rank = 3) (hn : 2 ≤ lab.n) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  have hp4 : ¬ p ∣ 4 := not_dvd_four_of_dvd_two_pow_add_one hp (by omega) hpn
  refine largeEvenLabelAll_uFour_of_forall htag hl fun K _ _ hK => ?_
  have hcov : UnitaryCoverAt lab.n 4 K := unitaryCoverAt_of_even hK hn ⟨2, rfl⟩ le_rfl
  have hL : GGTorusLift p (3 - 1) (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ lab.n))) := by
    have h := ggTorusLift_unitary (p := p) (d := 4) hK (by omega) (by norm_num) (by simp) hp hpn
    rwa [ggUnitaryTorusRank, if_neg hp4] at h
  exact ggTorusGenTableB_of_rk (r := 3) hp (by norm_num) hL
    (ggTorusGenTableBRk_PSU_coprime hK (by omega) (by norm_num) hp hpn hp4 hcov)

theorem largeEvenLabelAll_torusGenTableB_uFour
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (htag : lab.tag = .twA ∨ lab.tag = .twD)
    (hl : lab.rank = 3) (hn : 1 ≤ lab.n) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  rcases Nat.lt_or_ge lab.n 2 with h | h
  · exact largeEvenLabelAll_torusGenTableB_uFourTwo hp htag hl (by omega) hpn
  · exact largeEvenLabelAll_torusGenTableB_uFour_of_two_le hp htag hl h hpn

end CFSG.StandardType
