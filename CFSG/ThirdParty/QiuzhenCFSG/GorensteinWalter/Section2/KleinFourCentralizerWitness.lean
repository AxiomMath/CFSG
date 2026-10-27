module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

namespace CFSG
end CFSG
open CFSG

/-!
# A Klein-four fixed-point witness for Theorem 2.6

This is the source's use of coprime-action Fact 1.1(iii).  If a
nonidentity element `t` of a Klein four acts nontrivially enough that
`[P,t]=P`, fixed-point generation supplies another element whose centralizer
in `P` is not contained in `C_P(t)`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Let a Klein four `V` act on an odd-order group `P`.  If the commutator
with `t ∈ V#` is all of `P`, then some `s ∈ V#`, necessarily distinct from
`t`, has `C_P(s) ≰ C_P(t)`. -/
public theorem exists_kleinFour_centralizer_not_le_of_commutator_eq_self
    {G : Type u} [Group G] [Finite G]
    {V P : Subgroup G}
    (hV : IsKleinFour V)
    (hVP : V ≤ Subgroup.normalizer (P : Set G))
    (hPodd : Nat.Coprime 2 (Nat.card (↥P)))
    {t : G} (htV : t ∈ V) (ht1 : t ≠ 1)
    (hPne : P ≠ ⊥)
    (hcomm : ⁅P, Subgroup.zpowers t⁆ = P) :
    ∃ s : G, s ∈ V ∧ s ≠ 1 ∧ s ≠ t ∧
      ¬ (centralizerIn P s ≤ centralizerIn P t) := by
  classical
  let : IsKleinFour (↥V) := hV
  let : IsMulCommutative (↥V) := IsKleinFour.isMulCommutative
  let : CommGroup (↥V) := IsMulCommutative.instCommGroup
  have hV2 : IsPGroup 2 (↥V) := IsPGroup.of_card (n := 2) (by
    simp [IsKleinFour.card_four])
  let : Fact (IsPGroup 2 (↥V)) := ⟨hV2⟩
  let : V.Normalizes P := ⟨hVP⟩
  let : MulDistribMulAction (↥V) (↥P) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer V P hVP
  by_contra hnone
  push Not at hnone
  have hfixed_map_le :
      ∀ v : ↥V, ∀ hv1 : v ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥P)).map P.subtype ≤
          centralizerIn P t := by
    intro v hv1
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥P) =
          (elementCentralizerIn P (v : G)).subgroupOf P := by
      simpa using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn P V hVP v
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥P)).map P.subtype =
          centralizerIn P (v : G) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥P)).map P.subtype =
            ((elementCentralizerIn P (v : G)).subgroupOf P).map P.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn P (v : G) ⊓ P := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn P (v : G) := inf_eq_left.2 inf_le_left
        _ = centralizerIn P (v : G) := rfl
    rw [hfix_map]
    by_cases hvt : (v : G) = t
    · subst hvt
      exact le_rfl
    · exact hnone (v : G) v.2 (by
        intro hvG
        exact hv1 (Subtype.ext hvG)) hvt
  have htop :=
    iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
      (G := ↥P) (A := ↥V) (p := 2) (hG := hPodd)
      (hncyc := IsKleinFour.not_isCyclic)
  have hPleCent : P ≤ centralizerIn P t := by
    have htop_map : (⊤ : Subgroup (↥P)).map P.subtype = P := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := P))
    calc
      P = (⊤ : Subgroup (↥P)).map P.subtype := htop_map.symm
      _ = (⨆ (v : ↥V) (_ : v ≠ 1),
          fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥P)).map P.subtype := by
            simp [htop]
      _ ≤ centralizerIn P t := by
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro v
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro hv1
        exact hfixed_map_le v hv1
  have hPleCentZ :
      P ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have htx : t * x = x * t :=
      Subgroup.mem_centralizer_iff.mp (hPleCent hx).2 t (by simp)
    exact ((show Commute x t from htx.symm).zpow_right n).symm
  have hbot : ⁅P, Subgroup.zpowers t⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hPleCentZ
  exact hPne (hcomm.symm.trans hbot)

end CFSG.GorensteinWalter
