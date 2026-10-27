module

public import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofModule
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofKFactProof

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item181ThreeProof

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_forall_commute {X : Subgroup G}
    (hF : CFSG.generalizedFitting X = CFSG.pCore 2 X) {x : G} (hxX : x ∈ X)
    (hx : ∀ y ∈ CFSG.Open.pCoreOf 2 X, x * y = y * x) : x ∈ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF
  have hmem : (⟨x, hxX⟩ : X) ∈ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact (hx y ⟨y, hy, rfl⟩).symm
  have h1 := hc hmem
  exact ⟨_, h1, rfl⟩

theorem setting_of {A M H : Subgroup G} (h : Sec18Std G A M) (hH : H ∈ scriptH A M)
    (hF : CFSG.generalizedFitting H = CFSG.pCore 2 H) {s : G}
    (hSeq : CFSG.Open.pCoreOf 2 (H ⊓ M) = Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 H)
    (hrel : (CFSG.Open.pCoreOf 2 H).relIndex (CFSG.Open.pCoreOf 2 (H ⊓ M)) = 2) :
    Setting H (CFSG.Open.pCoreOf 2 H) (CFSG.Open.pCoreOf 2 (H ⊓ M))
      (inSubgroup perfectResidual H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAS : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) :=
    (le_inf hAH (sec18Std_le h)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  refine
    { le_S := by rw [hSeq]; exact le_sup_right
      S_le := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
      isPGroup_S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
      relIndex_eq := hrel
      conj_mem := fun x hx q hq => (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx) q).mp hq
      mem_of_commute := fun x hx hc => mem_pCoreOf_of_forall_commute hF hx hc
      le_of_normal := fun K hKH hKn hK2 =>
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH
          (fun x hx => Sec3.mem_normalizer_of_conj_mem (hKn x hx)) hK2
      L_le := Subgroup.map_subtype_le _
      gen := fun X hLX hSX => ?_ }
  refine le_trans (le_of_eq hH.2.1) ?_
  exact sup_le (sup_le hLX (hAS.trans hSX)) (Subgroup.le_normalizer.trans hSX)

end Item181ThreeProof

open Item181ThreeProof

theorem item181_3_of
    (h1812 : Item181_2)
    (hK : KFacts.KS181GraphFieldModule) : Item181_3 := by
  intro G _ _ A M h H hH hF
  obtain ⟨s, hs, hSeq, hrel⟩ := h1812 G A M h H hH
  have hset := setting_of h hH hF hSeq hrel
  obtain ⟨hMB4, hMB16⟩ := moduleBound_of_kfact hK h hH hs hrel
  exact ⟨hset.part_one hMB4, fun hL => hset.part_two (hMB16 hL)⟩

theorem rank3II_18_1_3_of
    (h1812 : Item181_2) : Item181_3 :=
  item181_3_of h1812 Item181ThreeProof.ks181GraphFieldModule

end CFSG.RankThree.PartTwo.Sec18
