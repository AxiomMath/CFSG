module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.DGroupInvariantCommutatorOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorOddCoreTail
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- If an odd-prime subgroup of an ambient group is contained in a D-group
subgroup and invariant under the involution centralizer inside that subgroup,
then its commutator with the involution lies in the ambient q-core. -/
public theorem commutator_le_qCoreOf_of_isDGroup
    {G : Type u} [Group G] [Finite G]
    (B P : Subgroup G) (p : ℕ)
    (hD : IsDGroup B) (hp : p.Prime) (hpodd : Odd p)
    (hPB : P ≤ B) (hPp : IsPGroup p P)
    {t : G} (htB : t ∈ B) (ht : IsInvolution t)
    (hPinv : B ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (P : Set G)) :
    ⁅P, Subgroup.zpowers t⁆ ≤ qCoreOf B p := by
  classical
  let PB : Subgroup B := P.subgroupOf B
  let tB : B := ⟨t, htB⟩
  have hPBp : IsPGroup p PB :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPB).symm
  have htBinv : IsInvolution tB := by
    constructor
    · intro htBone
      exact ht.1 (congrArg Subtype.val htBone)
    · exact Subtype.ext ht.2
  have hPBinv : Subgroup.centralizer ({tB} : Set B) ≤
      Subgroup.normalizer (PB : Set B) := by
    intro c hc
    have hcG : (c : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hcNorm : (c : G) ∈ Subgroup.normalizer (P : Set G) :=
      hPinv ⟨c.property, hcG⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change ((x : G) ∈ P ↔
      (c : G) * (x : G) * (c : G)⁻¹ ∈ P)
    exact (Subgroup.mem_normalizer_iff.mp hcNorm) (x : G)
  have hcommO : ⁅PB, Subgroup.zpowers tB⁆ ≤ pPrimeCore 2 B :=
    commutator_le_pPrimeCore_of_isDGroup
      PB p hD hp hpodd hPBp htBinv hPBinv
  have hcommCore : ⁅PB, Subgroup.zpowers tB⁆ ≤ pCore p B :=
    commutator_le_pCore_of_le_pPrimeCore
      PB p hp hpodd htBinv hPBp hPBinv hcommO
  have hZleB : Subgroup.zpowers t ≤ B := Subgroup.zpowers_le.mpr htB
  have hZsub : (Subgroup.zpowers t).subgroupOf B =
      Subgroup.zpowers tB := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, Subtype.ext ?_⟩
      simpa [tB] using hn
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      exact congrArg Subtype.val hn
  have hcommMap : (⁅PB, Subgroup.zpowers tB⁆).map B.subtype =
      ⁅P, Subgroup.zpowers t⁆ := by
    change (⁅P.subgroupOf B, Subgroup.zpowers tB⁆).map B.subtype =
      ⁅P, Subgroup.zpowers t⁆
    rw [← hZsub]
    exact commutator_subgroupOf_map_eq B (Subgroup.zpowers t) P hZleB hPB
  have hmapLe : (⁅PB, Subgroup.zpowers tB⁆).map B.subtype ≤
      (pCore p B).map B.subtype :=
    Subgroup.map_mono hcommCore
  rw [hcommMap] at hmapLe
  exact hmapLe

end CFSG.GorensteinWalter
