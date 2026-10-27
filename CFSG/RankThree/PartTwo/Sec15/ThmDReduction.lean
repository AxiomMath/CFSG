module

public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof
public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement Pointwise

theorem step153PushCoreR_of_P (hobs : Claim153ObsR) (h146 : Item146S14)
    (hP : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
        ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2),
          S ≤ Subgroup.normalizer (Y : Set G) →
          ((CFSG.Open.pCoreOf 2 (Y ⊔ S) ⊔ S) ⊓ Y) ∈ scriptQ A (lB A)) :
    Step153PushCoreR := by
  intro G _ _ A c L hR Y hY S hS hno
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hobs G A c L hR Y hY S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 (Y ⊔ S) with hT
  set P := (T ⊔ S) ⊓ Y with hPdef
  have hPQ : P ∈ scriptQ A (lB A) := hP G A c L hR Y hY S hS hSY
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hSN : S ≤ n155 A Y := hS.prop.1.2
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_sup_right : S ≤ Y ⊔ S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTS2 : IsPGroup 2 ↥(S ⊔ T) := IsPGroup.to_sup_of_normal_right' hS2 hT2 hST
  have hTS : T ⊔ S = S ⊔ T := sup_comm _ _
  have hTle : T ≤ Y ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPS : T ⊔ S ≤ P ⊔ S := by
    intro x hx
    have hxYS : x ∈ Y ⊔ S := sup_le hTle le_sup_right hx
    have hxm : x ∈ ((Y : Set G) * (S : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y S hSY]
      exact hxYS
    obtain ⟨y, hy, s, hs, rfl⟩ := hxm
    have hyTS : y ∈ T ⊔ S := by
      have := (T ⊔ S).mul_mem hx ((T ⊔ S).inv_mem (Subgroup.mem_sup_right hs))
      simpa using this
    exact (P ⊔ S).mul_mem (Subgroup.mem_sup_left (show y ∈ P from ⟨hyTS, hy⟩))
      (Subgroup.mem_sup_right hs)
  have hSP : S ≤ Subgroup.normalizer (P : Set G) :=
    Late.le_normalizer_inf ((le_sup_right : S ≤ T ⊔ S).trans Subgroup.le_normalizer) hSY
  have hsup : S ⊔ P ∈ scriptQ A (lB A) :=
    Sec14.sup_mem_scriptQ_of_item146 hR.toSec14Std.isE27 (h146 G A c L hR.toSec14Std)
      hS.prop.1.1 hPQ hSP
  have hYN : Y ≤ n155 A Y :=
    (le_oPrimeResidualOf_delta hY.prop.1 Subgroup.le_normalizer).trans Subgroup.le_normalizer
  have hPN : P ≤ n155 A Y := inf_le_right.trans hYN
  have hSPle : S ⊔ P ≤ S ⊔ T := sup_le le_sup_left (inf_le_left.trans (by rw [← hTS]))
  have h2 : IsPGroup 2 ↥(S ⊔ P) := hTS2.to_le hSPle
  have hmem : S ⊔ P ∈ scriptQPi A (lB A) (n155 A Y) (piOf 2) :=
    ⟨⟨hsup, sup_le hSN hPN⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr h2⟩
  have hPS' : S ⊔ P ≤ S := hS.2 hmem le_sup_left
  exact (le_sup_left.trans hPS).trans (sup_le (le_sup_right.trans hPS') le_rfl)

end CFSG.RankThree.PartTwo.Sec15.ThmD
