module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerPCoreOfFstarPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1

namespace CFSG
end CFSG
open CFSG

/-!
# Promoting a local Sylow subgroup with controlled ZJ normalizer

Let `B` be a maximal subgroup of a finite simple group.  If `F*(B)` is a
`p`-group, `Qd(p)` is not involved in the ambient group, and a Sylow
`p`-subgroup of `B` is nontrivial, then that Sylow subgroup is also ambient
Sylow after mapping along `B.subtype`.  Moreover, the ambient normalizer of
its Glauberman `ZJ` subgroup is exactly `B`.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

open Glauberman

universe u

/-- A nontrivial local Sylow subgroup of a maximal subgroup whose generalized
Fitting subgroup is a `p`-group promotes to an ambient Sylow subgroup, and its
ambient `ZJ` normalizer is the original maximal subgroup. -/
public theorem exists_ambient_sylow_with_zj_normalizer_eq_of_fstar_pgroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hsimple : IsSimpleGroup G)
    (hInvG : ¬ Involved (Qd p) G)
    (B : Subgroup G) (hB : IsCoatom B)
    (hBp : IsPGroup p (generalizedFittingSubgroupOf B))
    (PB : Sylow p (↑B)) (hPBne : (PB : Subgroup (↑B)) ≠ ⊥) :
    ∃ PG : Sylow p G,
      (PG : Subgroup G) =
          section8SubgroupInAmbient (PB : Subgroup (↑B)) ∧
        Subgroup.normalizer
            ((ZJ (G := G) (PG : Subgroup G) : Subgroup G) : Set G) = B := by
  classical
  have hp : p.Prime := Fact.out
  have hInvB : ¬ Involved (Qd p) (↑B) := by
    intro h
    exact hInvG (involved_of_involved_subgroup h)
  have hstableQ :
      pStable p (↑(⊤ : Subgroup (↑B)) ⧸
        (⊥ : Subgroup (↑(⊤ : Subgroup (↑B))))) :=
    (lemma6_3 (p := p) hpodd (G := ↑B)).mp hInvB
      (⊤ : Subgroup (↑B)) (⊥ : Subgroup (⊤ : Subgroup (↑B)))
  let eTopBot :
      (↑(⊤ : Subgroup (↑B)) ⧸
        (⊥ : Subgroup (↑(⊤ : Subgroup (↑B))))) ≃* ↑B :=
    (QuotientGroup.quotientBot
      (G := ↑(⊤ : Subgroup (↑B)))).trans (Subgroup.topEquiv (G := ↑B))
  have hstable : pStable p (↑B) := (pStable_iso eTopBot).mp hstableQ
  have hcent :
      Subgroup.centralizer ((pCore p (↑B) : Subgroup (↑B)) : Set (↑B)) ≤
        pCore p (↑B) :=
    centralizer_pCore_le_of_generalizedFitting_isPGroup B hp hBp
  have hZchar : (ZJ (G := ↑B) (PB : Subgroup (↑B))).Characteristic :=
    Glauberman.TheoremA.theoremA hpodd PB hstable hcent
  let ZB : Subgroup G :=
    section8SubgroupInAmbient (ZJ (G := ↑B) (PB : Subgroup (↑B)))
  have hZBneInt : ZJ (G := ↑B) (PB : Subgroup (↑B)) ≠ ⊥ := by
    simpa [zjCharacteristicFunctor, zjFunctor, ZJ] using
      (zjCharacteristicFunctor p).K_nontrivial
        (PB : Subgroup (↑B)) PB.isPGroup' hPBne
  have hZBne : ZB ≠ ⊥ := by
    intro hbot
    have hpre := (Subgroup.map_eq_bot_iff_of_injective
      (ZJ (G := ↑B) (PB : Subgroup (↑B)))
      (f := B.subtype) B.subtype_injective).mp hbot
    exact hZBneInt hpre
  let : (ZJ (G := ↑B) (PB : Subgroup (↑B))).Characteristic := hZchar
  have hBleNZ : B ≤ Subgroup.normalizer (ZB : Set G) := by
    exact Subgroup.le_normalizer.trans
      (by simpa [ZB, section8SubgroupInAmbient] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := B) (K := ZJ (G := ↑B) (PB : Subgroup (↑B)))))
  have hZBleB : ZB ≤ B := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zB, _hzB, rfl⟩
    exact zB.property
  have hZBnormal : (ZB.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hBleNZ
  have hNZ : Subgroup.normalizer (ZB : Set G) = B :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      hsimple hB hZBleB hZBne hZBnormal
  have hNPleB :
      Subgroup.normalizer
          (section8SubgroupInAmbient (PB : Subgroup (↑B)) : Set G) ≤ B := by
    calc
      Subgroup.normalizer
          (section8SubgroupInAmbient (PB : Subgroup (↑B)) : Set G) ≤
          Subgroup.normalizer (ZB : Set G) := by
        change Subgroup.normalizer
            (section8SubgroupInAmbient (PB : Subgroup (↑B)) : Set G) ≤
          Subgroup.normalizer
            (section8SubgroupInAmbient
              (centerIn (G := ↑B) (thompsonSubgroup (PB : Subgroup (↑B)))) : Set G)
        exact section8_normalizer_centerIn_thompsonSubgroup_le_of_normalizer_sylow
          (G := G) PB
      _ = B := hNZ
  obtain ⟨PG, hPG⟩ :=
    section8SubgroupInAmbient_sylow_of_normalizer_le PB hNPleB
  refine ⟨PG, hPG, ?_⟩
  have hZB_eq : ZB = ZJ (G := G) (PG : Subgroup G) := by
    calc
      ZB = (ZJ (G := ↑B) (PB : Subgroup (↑B))).map B.subtype := rfl
      _ = ZJ (G := G)
          ((PB : Subgroup (↑B)).map B.subtype) := by
        simpa [zjCharacteristicFunctor, zjFunctor, ZJ] using
          ((zjCharacteristicFunctor p).K_map B.subtype
            (PB : Subgroup (↑B))
            (B.subtype_injective.comp PB.toSubgroup.subtype_injective)).symm
      _ = ZJ (G := G) (PG : Subgroup G) := by
        rw [hPG]
        rfl
  simpa [hZB_eq] using hNZ

end CFSG.GorensteinWalter
