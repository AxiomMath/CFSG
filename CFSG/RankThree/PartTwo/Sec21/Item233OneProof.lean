module

import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G]

namespace Item233One

theorem mem_thetaComponentsIn_of_le [Finite G] {H J : Subgroup G}
    {X : Subgroup (J ⊓ H : Subgroup G)} (hX : IsComponent X) {X₀ : Subgroup G}
    (hX₀ : X₀ ∈ thetaComponentsIn H) (hX₀J : X₀ ≤ J) (hle : X.map (J ⊓ H).subtype ≤ X₀) :
    X.map (J ⊓ H).subtype ∈ thetaComponentsIn H := by
  obtain ⟨hX₀H, hX₀θ⟩ := mem_thetaComponentsIn_iff.mp hX₀
  have hX₀C : X₀ ≤ J ⊓ H := le_inf hX₀J hX₀H
  have hX'H : X.map (J ⊓ H).subtype ≤ H := (Subgroup.map_subtype_le X).trans inf_le_right
  have hXeq : (X.map (J ⊓ H).subtype).subgroupOf (J ⊓ H) = X := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (J ⊓ H).subtype_injective]
  have hsnC : ((X.map (J ⊓ H).subtype).subgroupOf (J ⊓ H)).IsSubnormal := by
    rw [hXeq]
    exact hX.2
  have hsnX₀ : ((X.map (J ⊓ H).subtype).subgroupOf X₀).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hX₀C hsnC
  have hsnH : ((X.map (J ⊓ H).subtype).subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hle hX₀H hsnX₀ hX₀θ.2.1
  have e : X ≃* (X.map (J ⊓ H).subtype).subgroupOf H :=
    (X.equivMapOfInjective (J ⊓ H).subtype (J ⊓ H).subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hX'H).symm
  have hq : IsQuasisimple ((X.map (J ⊓ H).subtype).subgroupOf H) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hX.1
  exact mem_thetaComponentsIn_iff.mpr
    ⟨hX'H, Sec4.mem_thetaComponents_of_isComponent3 ⟨hq, hsnH⟩⟩

theorem iSup_dStar_starOf_le_iGroup (A Z : Subgroup G) :
    (⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ) ≤ iGroup A :=
  iSup_le fun _ => iSup_le fun hψ => iSup_le fun _ => kOf_le_iGroup hψ

theorem not_forall_commute_of_mulEquiv {K : Subgroup G} {m : ℕ}
    (e : Nonempty (K ≃* projSL 2 (GaloisField 2 m))) :
    ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  intro hcomm
  obtain ⟨e⟩ := e
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_mulEquiv_projSL e
  exact hab (Subtype.ext (hcomm a a.2 b b.2))

end Item233One

end CFSG.RankThree.PartTwo.Sec21
