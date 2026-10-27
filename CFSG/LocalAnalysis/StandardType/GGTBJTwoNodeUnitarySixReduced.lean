module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofOne
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.Line63.H5
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.PerfectCentralQuotient

theorem exists_block_unitarySix_reduced_component
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    {G : Type} [Group G] [Finite G]
    {X Bs C J : Subgroup G} {r : ℕ}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hCB : C ≤ Bs)
    (hJ : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G)))
    (hNbar : (redMkB hN).range ≤
      Subgroup.normalizer (((redMkL X).range : Subgroup (RedGrp X)) : Set (RedGrp X)))
    (φ : ↥(unitarySU 2 1 F (r + 1)) →* (redMkL X).range)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma ((redMkL X).range) hNbar).range,
      ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t)
    (hr : 2 ≤ r := by norm_num) :
    ∃ S : Finset (Fin (r + 1)), 2 ≤ S.card ∧
      ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) :
        Subgroup (RedGrp X)) =
      (TableBUE.blockSU (K := F) (n := 1) S).map
        (((redMkL X).range).subtype.comp φ) ∧
      CFSG.Assembly.IsComponentOf
        ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X))
        (((redMkL X).range : Subgroup (RedGrp X)) ⊓
          Subgroup.centralizer
            (((C.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) :
              Subgroup (RedGrp X)) : Set (RedGrp X))) := by
  classical
  let NX : Subgroup G := Subgroup.normalizer (X : Set G)
  let Xbar : Subgroup (RedGrp X) := (redMkL X).range
  let Bbar : Subgroup (RedGrp X) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp X) := (J.subgroupOf NX).map (redMk X)
  let Cbar : Subgroup (RedGrp X) := (C.subgroupOf NX).map (redMk X)
  have hNbar' : Bbar ≤ Subgroup.normalizer (Xbar : Set (RedGrp X)) := hNbar
  have hdiag' : ∀ a ∈ (ggGamma Xbar hNbar').range,
      ∃ t : Fin (r + 1) → F, LineU.ActsDiagU φ a t := hdiag
  have hXbar_image : (X.subgroupOf NX).map (redMk X) = Xbar := by
    dsimp [Xbar]
    rw [redMkL, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hBbar_image : (Bs.subgroupOf NX).map (redMk X) = Bbar := by
    dsimp [Bbar]
    rw [redMkB, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hCsub_le_Bsub : C.subgroupOf NX ≤ Bs.subgroupOf NX := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hCB (Subgroup.mem_subgroupOf.mp hy))
  have hCbar_le_Bbar : (Cbar : Set (RedGrp X)) ⊆ Bbar := by
    intro x hx
    rw [← hBbar_image]
    exact Subgroup.map_mono hCsub_le_Bsub hx
  have hK : (redMk X).ker ≤ X.subgroupOf NX := by
    intro n hn
    exact Subgroup.mem_subgroupOf.mpr ((redMk_eq_one_iff X n).mp hn).1
  have hC3 : IsPGroup 3 (C.subgroupOf NX) := by
    have hC3' : IsPGroup 3 C := (isPGroup_three_of_isElemAbelian hBs).to_le hCB
    exact hC3'.of_equiv (Subgroup.subgroupOfEquivOfLe (hCB.trans hN)).symm
  have hpker3 : ¬ 3 ∣ Nat.card (redMk X).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_ker_redMk X)
    rw [hn]
    intro h
    have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h2
  have hJ_le_X : J ≤ X := hJ.1.trans inf_le_left
  have hX_le_NX : X ≤ NX := Subgroup.le_normalizer
  have hJ_le_NX : J ≤ NX := hJ_le_X.trans hX_le_NX
  have hJcompX : CFSG.Assembly.IsComponentOf (J.subgroupOf X)
      ((X ⊓ Subgroup.centralizer (C : Set G)).subgroupOf X) :=
    ggIsComponentOf_subgroupOf hJ inf_le_left
  have hJqX : CFSG.Assembly.IsQuasisimple (J.subgroupOf X) := hJcompX.2.2
  have hJnotker : ¬ J.subgroupOf NX ≤ (redMk X).ker := by
    intro hker
    apply not_le_center_of_isQuasisimple hJqX
    intro jx hjx
    let j : J := ⟨(jx : G), Subgroup.mem_subgroupOf.mp hjx⟩
    have hjNX : (⟨(j : G), hJ_le_NX j.2⟩ : NX) ∈ J.subgroupOf NX :=
      Subgroup.mem_subgroupOf.mpr j.2
    have htwo : ((j : G)) ∈ twoCenter X :=
      (redMk_eq_one_iff X ⟨(j : G), hJ_le_NX j.2⟩).mp (hker hjNX)
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (htwo.2.1 (x : G) x.2).symm
  have hcentral : Xbar ⊓ Subgroup.centralizer (Cbar : Set (RedGrp X)) =
      ((X ⊓ Subgroup.centralizer (C : Set G)).subgroupOf NX).map (redMk X) := by
    dsimp [Cbar]
    rw [← hXbar_image]
    have hmap := CFSG.LocalAnalysis.GLTheoremA.I2611.map_inf_centralizer_of_isPGroup
      (p := 3) (ψ := redMk X) Nat.prime_three hpker3 hK hC3
    change (X.subgroupOf NX).map (redMk X) ⊓
        Subgroup.centralizer (((C.subgroupOf NX).map (redMk X) : Subgroup (RedGrp X)) :
          Set (RedGrp X)) =
      ((X ⊓ Subgroup.centralizer (C : Set G)).subgroupOf NX).map (redMk X)
    rw [hmap]
    congr 1
    rw [CFSG.centralizer_subgroupOf_eq C NX (hCB.trans hN)]
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  have hJsub : CFSG.Assembly.IsComponentOf (J.subgroupOf NX)
      ((X ⊓ Subgroup.centralizer (C : Set G)).subgroupOf NX) :=
    ggIsComponentOf_subgroupOf hJ (inf_le_left.trans hX_le_NX)
  have hJbarComp : CFSG.Assembly.IsComponentOf Jbar
      (Xbar ⊓ Subgroup.centralizer (Cbar : Set (RedGrp X))) := by
    have h := isComponentOf_map_of_not_le_ker (redMk X) hJsub hJnotker
    rw [hcentral]
    exact h
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component
    (p := 3) (r := r) (f := 1) (G := RedGrp X)
    hr (by norm_num : 1 ≤ 1) (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (isElemAbelian_redB hN hBs) hNbar' (by simpa using hF) hM hdiag'
    hCbar_le_Bbar hJbarComp
  exact ⟨S, hS2, hJblock, hJbarComp⟩

theorem exists_block_unitarySix_reduced
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    {G : Type} [Group G] [Finite G]
    {X Bs C J : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hCB : C ≤ Bs)
    (hJ : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G)))
    {lab : LargeEvenLabel} (hJLab : GGHasLabel lab (J ⧸ Subgroup.center J))
    (hNbar : (redMkB hN).range ≤
      Subgroup.normalizer (((redMkL X).range : Subgroup (RedGrp X)) : Set (RedGrp X)))
    (φ : ↥(unitarySU 2 1 F 6) →* (redMkL X).range)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma ((redMkL X).range) hNbar).range,
      ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t) :
    ∃ S : Finset (Fin 6), 2 ≤ S.card ∧
      ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) :
        Subgroup (RedGrp X)) =
        (TableBUE.blockSU (K := F) (n := 1) S).map
          (((redMkL X).range).subtype.comp φ) ∧
      CFSG.Assembly.IsQuasisimple
        ↥((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) ∧
      GGHasLabel lab
        (↥((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X)) ⧸
          Subgroup.center ↥((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X))) := by
  classical
  let NX : Subgroup G := Subgroup.normalizer (X : Set G)
  let Jbar : Subgroup (RedGrp X) := (J.subgroupOf NX).map (redMk X)
  obtain ⟨S, hS2, hJblock, hJbarComp⟩ :=
    exists_block_unitarySix_reduced_component hF hBs hN hCB hJ hNbar φ hM hdiag
  have hJ_le_X : J ≤ X := hJ.1.trans inf_le_left
  have hJ_le_NX : J ≤ NX := hJ_le_X.trans Subgroup.le_normalizer
  have hJperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  let fJfull : ↥J →* RedGrp X := (redMk X).comp (Subgroup.inclusion hJ_le_NX)
  have hfJfull_range : fJfull.range = Jbar := by
    dsimp [Jbar, fJfull]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let fJ : ↥J →* Jbar := fJfull.codRestrict Jbar (fun j => by
    rw [← hfJfull_range]
    exact ⟨j, rfl⟩)
  have hfJ_surj : Function.Surjective fJ := by
    intro y
    have hy : (y : RedGrp X) ∈ fJfull.range := by
      rw [hfJfull_range]
      exact y.2
    rcases MonoidHom.mem_range.mp hy with ⟨j, hj⟩
    exact ⟨j, Subtype.ext hj⟩
  have hfJ_ker : fJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj1 : fJfull j = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      simpa [fJ] using h
    have htwo : ((j : G)) ∈ twoCenter X :=
      (redMk_eq_one_iff X (Subgroup.inclusion hJ_le_NX j)).mp hj1
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    exact (htwo.2.1 (j' : G) (hJ_le_X j'.2)).symm
  have eJ : (↥J ⧸ Subgroup.center ↥J) ≃*
      (↥Jbar ⧸ Subgroup.center Jbar) :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence fJ hfJ_surj hfJ_ker
  have hJbarLab : GGHasLabel lab (Jbar ⧸ Subgroup.center Jbar) :=
    ggHasLabel_of_mulEquiv eJ hJLab
  exact ⟨S, hS2, hJblock, hJbarComp.2.2, hJbarLab⟩

theorem exists_blockSU_unitarySix_reduced
    (hRig : GGLabelRigidInput)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    {G : Type} [Group G] [Finite G]
    {X Bs C J : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hCB : C ≤ Bs)
    (hJ : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer (C : Set G)))
    (hJLab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J))
    (hNbar : (redMkB hN).range ≤
      Subgroup.normalizer (((redMkL X).range : Subgroup (RedGrp X)) : Set (RedGrp X)))
    (φ : ↥(unitarySU 2 1 F 6) →* (redMkL X).range)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma ((redMkL X).range) hNbar).range,
      ∃ t : Fin 6 → F, LineU.ActsDiagU φ a t) :
    ∃ S : Finset (Fin 6), S.card = 4 ∧
      ((J.subgroupOf (Subgroup.normalizer (X : Set G))).map (redMk X) :
        Subgroup (RedGrp X)) =
      (TableBUE.blockSU (K := F) (n := 1) S).map
        (((redMkL X).range).subtype.comp φ) := by
  classical
  obtain ⟨S, hS2, hJblock, hJq, hJbarLab⟩ :=
    exists_block_unitarySix_reduced hF hBs hN hCB hJ hJLab hNbar φ hM hdiag
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by
    rw [hF]
    norm_num
  have hΛ3 : LargeEvenInLambda2 ⟨.twA, 3, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have hBq : CFSG.Assembly.IsQuasisimple
      ↥((TableBUE.blockSU (K := F) (n := 1) S).map
        (((redMkL X).range).subtype.comp φ)) := by
    exact hJblock ▸ hJq
  have hker : (((redMkL X).range).subtype.comp φ).ker ≤
      Subgroup.center ↥(unitarySU 2 1 F 6) :=
    UnitTB.ker_comp_subtype_le_center hM
  have hScard : S.card = 4 := by
    have h := card_eq_of_blockSU_label (r := 5) (f := 1)
      hRig hF' (by norm_num) hker hS2 hBq hΛ3 (hJblock ▸ hJbarLab)
    simpa using h
  exact ⟨S, hScard, hJblock⟩

end CFSG.StandardType

end
