module

public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (jOf jOneOf omegaOneZ)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem omegaOneZ_eq_omegaG (X : Subgroup G) : omegaOneZ X = Sec3.omegaG X := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun x hx => Subgroup.subset_closure ?_
  · rintro x ⟨⟨c, hc, rfl⟩, h2⟩
    refine ⟨c.2, fun y hy => ?_, by rwa [pow_two] at h2⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)).symm
  · obtain ⟨hxX, hcomm, h2⟩ := hx
    refine ⟨⟨⟨x, hxX⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩, ?_⟩
    · exact (hcomm y y.2).symm
    · rwa [pow_two]

omit [Finite G] in
private theorem isElemTwo_iff {A : Subgroup G} :
    Sec3.IsElemTwo A ↔ CFSG.Open.IsElemAbelian 2 A := by
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact hp x hx⟩
  · rintro ⟨hc, hp⟩
    exact ⟨fun a ha b hb => congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
      fun a ha => by rw [← pow_two]; exact hp a ha⟩

private theorem jG_zero_eq (S : Subgroup G) : Sec3.jG S 0 = jOf S := by
  rw [Sec3.jG, sSup_eq_iSup, jOf]
  refine iSup_congr fun A => iSup_congr_Prop ?_ fun _ => rfl
  rw [Sec3.mem_famG, Nat.sub_zero, isElemTwo_iff, CFSG.SectionRank.pRank_coe_eq_openPRank]

omit [Finite G] in
private theorem jG_one_eq_bot (S : Subgroup G) (hm : CFSG.pRank 2 S ≤ 1) : Sec3.jG S 1 = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun A hA => ?_)
  have hcard : Nat.card A = 1 := by
    rw [hA.2.2, show CFSG.pRank 2 S - 1 = 0 by omega, pow_zero]
  exact (Subgroup.card_eq_one.mp hcard).le

private theorem jG_one_eq_jOneOf (S : Subgroup G) (hS : IsPGroup 2 S) (hm : 2 ≤ CFSG.pRank 2 S) :
    Sec3.jG S 1 = jOneOf S := by
  refine le_antisymm (sSup_le fun A hA => ?_) (iSup₂_le fun E hE => ?_)
  · obtain ⟨hAS, hA2, hAcard⟩ := hA
    refine le_iSup₂_of_le A ⟨hAS, isElemTwo_iff.mp hA2, ?_⟩ le_rfl
    rw [hAcard, CFSG.SectionRank.pRank_coe_eq_openPRank]
  · obtain ⟨hES, hEel, hEcard⟩ := hE
    intro x hx
    have hE2 := isElemTwo_iff.mpr hEel
    obtain ⟨j, hj⟩ := (hS.to_le hES).exists_card_eq
    rw [hj, ← CFSG.SectionRank.pRank_coe_eq_openPRank] at hEcard
    have hdvd : 2 ^ (CFSG.pRank 2 S - 1) ∣ Nat.card E :=
      hj ▸ pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hEcard)
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hE2.2 x hx
    have hord : Nat.card (Subgroup.zpowers x) ∣ 2 ^ (CFSG.pRank 2 S - 1) := by
      rw [Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one hx2).trans (dvd_pow_self 2 (by omega))
    obtain ⟨K, hKcard, hxK, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hord
      hdvd (Subgroup.zpowers_le.mpr hx)
    exact Sec3.le_jG (A := K)
      ⟨hKE.trans hES, ⟨fun a ha b hb => hE2.1 a (hKE ha) b (hKE hb),
        fun a ha => hE2.2 a (hKE ha)⟩, hKcard⟩ (hxK (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem fourChar_zero_eq (S : Subgroup G) : Sec18.fourChar S 0 = omegaOneZ S := by
  change (CFSG.omegaOneCenter (⊤ : Subgroup S)).map S.subtype = _
  rw [omegaOneZ_eq_omegaG, Sec3.map_omegaOneCenter, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem fourChar_one_eq (S : Subgroup G) : Sec18.fourChar S 1 = jOf S := by
  change (CFSG.higherElemThompson S 0).map S.subtype = _
  rw [Sec3.map_higherElemThompson, jG_zero_eq]

theorem fourChar_two_eq (S : Subgroup G) (hS : IsPGroup 2 S) (hne : Sec18.fourChar S 2 ≠ ⊥) :
    Sec18.fourChar S 2 = omegaOneZ (jOneOf S) := by
  have h2 : Sec18.fourChar S 2 = Sec3.omegaG (Sec3.jG S 1) := by
    change (CFSG.omegaOneCenter (CFSG.higherElemThompson S 1)).map S.subtype = _
    rw [Sec3.map_omegaOneCenter, Sec3.map_higherElemThompson]
  have hm : 2 ≤ CFSG.pRank 2 S := by
    by_contra hlt
    refine hne ?_
    rw [h2, jG_one_eq_bot S (by omega)]
    exact le_bot_iff.mp (Sec3.omegaG_le _)
  rw [h2, omegaOneZ_eq_omegaG, jG_one_eq_jOneOf S hS hm]

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
