module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModelTorus
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModelG2
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerCentJ
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerE9
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerMarkDiag
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerSemilin
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerConj
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerTriality
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerDich
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerFour
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerTwoMark
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_model
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n) :
    ∃ s₀ : Om8 K, s₀ ^ 3 = 1 ∧ D4Rank.omFixDim s₀ = 2 ∧ (∀ y ∈ centDer s₀, theta y = y) ∧
      ∀ p ∈ Subgroup.centralizer (centDer s₀ : Set (Om8 K)), p * theta p * theta (theta p) = 1 :=
  ⟨sZero, sZero_pow_three, omFixDim_sZero, theta_fix_centDer_sZero hK hn hn3,
    theta_norm_centralizer_centDer_sZero hK hn (theta_fix_centDer_sZero hK hn hn3)
      (centralizer_centDer_facts hK hn hn3 sZero_pow_three omFixDim_sZero).2.1⟩

theorem exists_triality_centralizing
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ γ : MulAut (Om8 K), D4Bstar.IsTriPart 1 γ ∧ γ ^ 3 = 1 ∧ (∀ y ∈ centDer s, γ y = y) ∧
      ∀ p ∈ Subgroup.centralizer (centDer s : Set (Om8 K)), p * γ p * γ (γ p) = 1 :=
  exists_triality_centralizing_of_model
    (fun hx3 hz3 hdx hdz => exists_conj_of_omFixDim_two hK hn hx3 hz3 hdx hdz)
    (exists_model hK hn hn3) hs3 hd

theorem toralOn_false
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {A : Subgroup (MulAut (Om8 K))} {s : Om8 K} {J : Subgroup (Om8 K)}
    (hloc : GGKLocal A (MulAut.conj s) J) (hA : Nat.card A = 3 ^ 3)
    (hd : D4Rank.omFixDim s = 2)
    (hdat : ∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K))
    (hout : ∃ a ∈ A, a ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (htor : ToralOn A s J) : False :=
  toralOn_false_of_leaves (fun hs3 hd hJ => eq_centDer_of_isComponentOf hK hn hn3 hs3 hd hJ)
    (fun hs3 hd => exists_triality_centralizing hK hn hn3 hs3 hd)
    (fun hs3 hd hφ hfix => mem_inner_of_fix_centDer hK hn hn3 hs3 hd hφ hfix)
    hloc hA hd hdat hout htor

theorem ggD4InnerTwoDichInput_holds :
    GGD4InnerTwoDichInput :=
  ggD4InnerTwoDichInput_of_leaves
    (fun _ _ _ _ _ hK hn hn3 _ hs3 hd _ hJ _ hAJ => innDiagOn_of_ggAutsInduceOn hK hn hn3 hs3 hd hJ hAJ)
    (fun _ _ _ _ _ hK hn hn3 _ _ _ hloc hA hd hinn => fixedInCenter_or_toralOn hK hn hn3 hloc hA hd hinn)
    (fun _ _ _ _ _ hK hn hn3 _ _ _ hloc hA hd hdat hout htor =>
      toralOn_false hK hn hn3 hloc hA hd hdat hout htor)

end D4Inner

theorem ggD4OddCentInnerInput_holds :
    GGD4OddCentInnerInput :=
  ggD4OddCentInnerInput_of_om8 D4Inner.ggD4InnerOneInput_holds D4Inner.ggD4InnerFourInput_holds
    D4Inner.ggD4InnerTwoMarkInput_holds D4Inner.ggD4InnerTwoDichInput_holds

end CFSG.StandardType

end
