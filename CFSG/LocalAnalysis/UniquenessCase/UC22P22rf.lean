module

import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_le_oinf_of_normal_subnormal {S K H : Subgroup G} (hSK : S ≤ K)
    (hN : (S.subgroupOf K).Normal) (hS : Group.IsSolvable ↥S) (hKH : IsSubnormal K H) : S ≤ OInf H := by
  have hSKchain : IsSubnormal S K := IsSubnormal.step hSK hN (IsSubnormal.refl K)
  have hSH : IsSubnormal S H := IsSubnormal.trans hSKchain hKH
  have hSHle : S ≤ H := hSH.le
  have hsub : (S.subgroupOf H).IsSubnormal := hSH.subgroupOf
  haveI := hS
  have hsolv : Group.IsSolvable ↥(S.subgroupOf H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hSHle).symm
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal hsub hsolv
  intro x hx
  exact ⟨⟨x, hSHle hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem uc22p22r_pCoreOf_le_oinf {K H : Subgroup G} (hKH : IsSubnormal K H) : pCoreOf 2 K ≤ OInf H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isNilpotent
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := inferInstance
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 K) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥K) K.subtype K.subtype_injective)
  have hN : ((pCoreOf 2 K).subgroupOf K).Normal := by
    have h : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      unfold pCoreOf
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    rw [h]
    exact CFSG.pCore_normal
  exact uc22p22r_le_oinf_of_normal_subnormal (Subgroup.map_subtype_le _) hN hsolv hKH

theorem uc22p22r_exists_K (D : Data G) (h204 : S20_4 D) (h1930 : H1930 D) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) :
    ∃ L K : Subgroup G, L ∈ calLOf D.T D.M H ∧ K ∈ calC L ∧
      L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ∧ ¬ K ≤ D.M := by
  by_contra hcon
  push Not at hcon
  have hLM : ∀ L ∈ calLOf D.T D.M H, L ≤ D.M := by
    intro L hL
    obtain ⟨K, hK, hLK⟩ := hL.1.2.2.2
    have hKM : K ≤ D.M := hcon L K hL hK hLK
    rw [hLK]
    refine iSup_le fun t => ?_
    rintro _ ⟨k, hk, rfl⟩
    have htM : (t : G) ∈ D.M := D.sylowM.le t.2
    exact D.M.mul_mem (D.M.mul_mem htM (hKM hk)) (D.M.inv_mem htM)
  have hprod := h204 h1930 H hH
  apply hH.2.1
  intro y hy
  have hy' : y ∈ (((⨆ L ∈ calLOf D.T D.M H, L : Subgroup G) : Set G) * ((H ⊓ D.M : Subgroup G) : Set G)) := by
    rw [hprod]
    exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  have haM : a ∈ D.M := (iSup₂_le fun L hL => hLM L hL) ha
  exact D.M.mul_mem haM hb.2

theorem uc22p22r_K_subnormal {D : Data G} {H L K : Subgroup G} (hL : L ∈ calLOf D.T D.M H)
    (hK : K ∈ calC L) : IsSubnormal K H ∧ ⁅K, K⁆ = K :=
  ⟨IsSubnormal.trans hK.1 hL.2, hK.2.1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
