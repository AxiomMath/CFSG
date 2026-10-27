module

public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem pCore_two_bar_H0_eq_bot {M Q Z B : Subgroup G}
    [hN : (Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    pCore 2 ↥(bar M Q (H0 M Z)) = ⊥ := by
  have hZM : Z ≤ M := hc.hyp.Z_normal.1.trans hc.hyp.Q_normal.1
  have hQp : Q.subgroupOf M = pCore 2 ↥M := by
    rw [hc.hyp.hQ]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective (pCore 2 ↥M)
  have hMbar : pCore 2 (Mbar M Q) = ⊥ := by
    have he : Mbar M Q ≃* (↥M ⧸ pCore 2 ↥M) := QuotientGroup.quotientMulEquivOfEq hQp
    have h := CFSG.pCore_map_iso (p := 2) he
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ he.injective).mp h
  have hH0n : ((H0 M Z).subgroupOf M).Normal := by
    have hZsub : (Z.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZM).mpr hc.hyp.Z_normal.2
    have heq : (H0 M Z).subgroupOf M =
        Subgroup.centralizer (Z.subgroupOf M : Set ↥M) := by
      ext m
      rw [Subgroup.mem_subgroupOf]
      change (m : G) ∈ M ⊓ Subgroup.centralizer (Z : Set G) ↔
        m ∈ Subgroup.centralizer (Z.subgroupOf M : Set ↥M)
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, hcent⟩ z hz
        exact Subtype.ext (hcent (z : G) hz)
      · intro hcent
        refine ⟨m.2, ?_⟩
        intro z hz
        exact congrArg Subtype.val (hcent ⟨z, hZM hz⟩ (Subgroup.mem_subgroupOf.mpr hz))
    rw [heq]
    haveI := hZsub
    exact Subgroup.normal_centralizer
  let H := bar M Q (H0 M Z)
  have hH : H.Normal := by
    exact Subgroup.Normal.map hH0n (QuotientGroup.mk' (Q.subgroupOf M))
      (QuotientGroup.mk'_surjective (Q.subgroupOf M))
  haveI := hH
  have hnorm : ((pCore 2 ↥H).map H.subtype).Normal := inferInstance
  have hp : IsPGroup 2 ((pCore 2 ↥H).map H.subtype) :=
    (pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  have hle : (pCore 2 ↥H).map H.subtype ≤ pCore 2 (Mbar M Q) := le_sSup ⟨hnorm, hp⟩
  rw [hMbar, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hle

end CFSG.RankThree.GF2n.Stroth80
