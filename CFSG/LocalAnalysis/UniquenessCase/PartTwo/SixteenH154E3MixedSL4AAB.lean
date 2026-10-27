module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_fpf_of_card_four {Z : Subgroup G} {d : G} (hZcard : Nat.card ↥Z = 4)
    (hd3 : orderOf d = 3)
    (hinv : ∀ z ∈ Z, d * z * d⁻¹ ∈ Z)
    (hnt : ∃ z ∈ Z, d * z * d⁻¹ ≠ z) :
    ∀ z ∈ Z, d * z * d⁻¹ = z → z = 1 := by
  have hmap_le : Z.map (MulAut.conj d : G →* G) ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact hinv z hz
  have hcard : Nat.card ↥(Z.map (MulAut.conj d : G →* G)) = Nat.card ↥Z :=
    Subgroup.card_map_of_injective (f := (MulAut.conj d : G →* G)) (MulAut.conj d).injective
  have hmap_eq : Z.map (MulAut.conj d : G →* G) = Z :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
  have hdN : d ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq
  have hle : Subgroup.zpowers d ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  letI : MulAction (Subgroup.zpowers d) ↥Z :=
    MulAction.compHom _ (Subgroup.inclusion hle)
  have h3grp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd3, pow_one])
  have hfix : MulAction.fixedPoints (Subgroup.zpowers d) ↥Z =
      MulAction.fixedBy ↥Z (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) := by
    ext x
    rw [MulAction.mem_fixedPoints, MulAction.mem_fixedBy]
    constructor
    · intro h; exact h _
    · intro h g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hgj : g = (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) ^ j := by
        ext
        rw [Subgroup.coe_zpow]
        exact hj.symm
      rw [hgj]
      exact MulAction.mem_fixedBy_zpow h j
  have hmod : Nat.card ↥Z ≡
      Nat.card (MulAction.fixedPoints (Subgroup.zpowers d) ↥Z) [MOD 3] :=
    h3grp.card_modEq_card_fixedPoints ↥Z
  rw [hZcard, hfix] at hmod
  have hproper : MulAction.fixedBy ↥Z (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) ⊂
      Set.univ := by
    obtain ⟨z, hz, hzfix⟩ := hnt
    refine ⟨Set.subset_univ _, fun heq => ?_⟩
    have hmem : (⟨z, hz⟩ : ↥Z) ∈
        MulAction.fixedBy ↥Z (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) := heq trivial
    rw [MulAction.mem_fixedBy] at hmem
    exact hzfix (congrArg Subtype.val hmem)
  have hnlt : Nat.card (MulAction.fixedBy ↥Z
      (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)) < 4 := by
    rw [← hZcard]
    simpa using Set.ncard_lt_ncard hproper
  have hn1 : Nat.card (MulAction.fixedBy ↥Z
      (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)) = 1 := by
    have hmod' : Nat.card (MulAction.fixedBy ↥Z
        (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)) % 3 = 1 := by
      have h := hmod
      norm_num [Nat.ModEq] at h
      exact h.symm
    omega
  intro z hz hzfix
  have hmem : (⟨z, hz⟩ : ↥Z) ∈
      MulAction.fixedBy ↥Z (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) := by
    rw [MulAction.mem_fixedBy]
    exact Subtype.ext hzfix
  have h1mem : (⟨1, Z.one_mem⟩ : ↥Z) ∈
      MulAction.fixedBy ↥Z (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) := by
    rw [MulAction.mem_fixedBy]
    rw [MulAction.compHom_smul_def]
    exact smul_one _
  haveI : Subsingleton ↥(MulAction.fixedBy ↥Z
      (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)) :=
    (Finite.card_le_one_iff_subsingleton (α := ↥(MulAction.fixedBy ↥Z
      (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)))).mp (by rw [hn1])
  have heq : (⟨z, hz⟩ : ↥Z) = ⟨1, Z.one_mem⟩ :=
    congrArg Subtype.val (Subsingleton.elim
      (⟨⟨z, hz⟩, hmem⟩ : ↥(MulAction.fixedBy ↥Z
        (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d)))
      ⟨⟨1, Z.one_mem⟩, h1mem⟩)
  exact congrArg Subtype.val heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
