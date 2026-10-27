module

public import CFSG.Quasithin.H13.A5S136h
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic

@[expose] def Graph1367Lambda2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) → S.Lv ≤ K →
    ∀ α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2), Function.Surjective α →
      (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G)) →
      ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2) →
      (∃ t ∈ S.Tv, ∃ u ∈ unitriangular 4 (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
        α ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α l * u⁻¹)) →
      ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α =
          flagStabilizer 4 (ZMod 2) {2} ∧
        ∀ B : Subgroup G, B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) →
          ¬ B ≤ Subgroup.centralizer (S.WK K : Set G) →
          (B ⊓ Subgroup.centralizer (S.WK K : Set G)).relIndex B <
            (S.WK K ⊓ Subgroup.centralizer (B : Set G)).relIndex (S.WK K)

end CFSG.Quasithin.H13.A5
