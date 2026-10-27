module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The selected PSL₂ component forces a dihedral Sylow subgroup in `M`

The component-Sylow intersection supplied by Section 4 identifies a Sylow
`2`-subgroup of the selected component inside a Sylow `2`-subgroup of the
maximal subgroup `M`.  Its image in `PSL₂(K)` is noncyclic, because every
Sylow `2`-subgroup of an odd `PSL₂` is dihedral.  Since `M` is a proper
subgroup of the minimal counterexample, its `D`-group trichotomy then turns
this one noncyclic Sylow subgroup into a dihedral model for every Sylow
`2`-subgroup of `M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem psl2_component_sylow_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    ∃ SM : Sylow 2 (↥w.M), ∃ SE : Sylow 2 (↥d.E),
      ((SE : Subgroup d.E).map d.E.subtype =
        ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E) ∧
      ¬ IsCyclic SM := by
  obtain ⟨SM, _hSMcent, SE, hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let P : Sylow 2 Q :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E))
  let PP : Sylow 2 (PSL2 K) :=
    P.mapSurjective (f := e.some.toMonoidHom) e.some.surjective
  have hPPnc : ¬ IsCyclic PP := by
    intro hcyc
    obtain ⟨m, hm, ⟨em⟩⟩ :=
      (psl2_odd_hasDihedralSylowTwo_model K hK) PP
    have hcycD : IsCyclic (DihedralGroup (2 ^ m)) :=
      (MulEquiv.isCyclic em).mp hcyc
    apply (DihedralGroup.not_isCyclic (by
      have hm0 : m ≠ 0 := by omega
      exact (Nat.one_lt_pow hm0 (by norm_num : 1 < (2 : ℕ))).ne.symm) hcycD)
  have hSEnc : ¬ IsCyclic SE := by
    intro hcyc
    have hPcyc : IsCyclic P :=
      isCyclic_of_surjective
        (q.subgroupMap (SE : Subgroup d.E))
        (q.subgroupMap_surjective (SE : Subgroup d.E))
    have hPPcyc : IsCyclic PP :=
      isCyclic_of_surjective
        (e.some.toMonoidHom.subgroupMap (P : Subgroup Q))
        (e.some.toMonoidHom.subgroupMap_surjective (P : Subgroup Q))
    exact hPPnc hPPcyc
  refine ⟨SM, SE, hSEamb, ?_⟩
  intro hSMcyc
  have hSEcyc : IsCyclic SE := by
    let SEmap : Subgroup G := (SE : Subgroup d.E).map d.E.subtype
    let SMamb : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
    have hSEmaple : SEmap ≤ SMamb := by
      change (SE : Subgroup d.E).map d.E.subtype ≤
        (SM : Subgroup w.M).map w.M.subtype
      rw [hSEamb]
      exact inf_le_left
    let eSM : (SM : Subgroup w.M) ≃* SMamb :=
      Subgroup.equivMapOfInjective (SM : Subgroup w.M)
        w.M.subtype w.M.subtype_injective
    have hSMambcyc : IsCyclic SMamb := (MulEquiv.isCyclic eSM).mp hSMcyc
    let : IsCyclic SMamb := hSMambcyc
    have hSEmapcyc : IsCyclic SEmap := Subgroup.isCyclic_of_le hSEmaple
    let eSE : (SE : Subgroup d.E) ≃* SEmap :=
      Subgroup.equivMapOfInjective (SE : Subgroup d.E)
        d.E.subtype d.E.subtype_injective
    exact (MulEquiv.isCyclic eSE).mpr hSEmapcyc
  exact hSEnc hSEcyc

private theorem hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (hSyl : HasCyclicOrDihedralSylowTwo G)
    (hnotcyc : ¬ ∀ S : Sylow 2 G, IsCyclic S) :
    HasDihedralSylowTwo G := by
  push Not at hnotcyc
  rcases hnotcyc with ⟨S, hSnot⟩
  have hSdihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m)) :=
    (hSyl S).resolve_left hSnot
  rcases hSdihedral with ⟨m, hm, ⟨eS⟩⟩
  intro T
  refine ⟨m, hm, ⟨(Sylow.equiv S T).symm.trans eS⟩⟩

/-- In the PSL₂ component branch, the selected maximal subgroup has
dihedral Sylow `2`-subgroups. -/
public theorem secondCase_psl2_hasDihedralSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    HasDihedralSylowTwo (↥w.M) := by
  have hD : IsDGroup w.M :=
    properSubgroups_areDGroups hmin w.M w.M_maximal.ne_top
  have hSyl : HasCyclicOrDihedralSylowTwo (↥w.M) := by
    rcases hD with ⟨hsyl, _⟩ | ⟨hsyl, _⟩ | ⟨hsyl, _⟩
    · exact hsyl
    · exact hsyl
    · exact hsyl
  have hnotcyc : ¬ ∀ S : Sylow 2 (↥w.M), IsCyclic S := by
    intro hall
    obtain ⟨SM, _SE, _hSE, hSM⟩ :=
      psl2_component_sylow_not_cyclic c w d K hK e
    exact hSM (hall SM)
  exact hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic
    hSyl hnotcyc

end CFSG.GorensteinWalter
