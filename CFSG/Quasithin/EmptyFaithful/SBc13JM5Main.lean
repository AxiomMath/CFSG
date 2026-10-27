module

public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Rank
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Quasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_one_of_commutes (h36 : A36ForSQTK) {X J : Subgroup G} (hX : SQTKGroup ↥X)
    (hJ : J ∈ cComp X) (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) {k : G} (hkX : k ∈ X)
    (hk5 : orderOf k = 5) (hkJ : k ∈ Subgroup.normalizer (J : Set G))
    (hcomm : ∀ x ∈ J, ⁅x, k⁆ ∈ pCoreOf 2 J) : CFSG.Open.pRank 5 J ≤ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJX : J ≤ X := le_of_mem_cComp hJ
  have hnot : k ∉ J :=
    not_mem_of_commutes hX (h36 _ (SQTKHyp.of_sqtkGroup ↥X hX)) hJ hJq hk5 hcomm
  have h1 := pRank_succ_le_of_commutes (p := 5) (by norm_num) hJX hkX hkJ hk5 hnot hcomm
  have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) ≤ 2 := hX.1 5 (by norm_num) (by norm_num)
  rw [pRank_top_subtype] at h2
  omega

end SBc13

end CFSG.Quasithin
