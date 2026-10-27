module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.RankThree.PartTwo.KFacts.K71PSU3
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.KFacts.K71Item89
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open CFSG.RankThree.PartTwo.Sec4
  CFSG.GH74.GLS.IVK

theorem gffa2_unitary_derived_equiv {K : Type} [Field K] {n m : ℕ} (h : UnitaryFieldData 2 n K)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (hnm : n = 3 * m) (hm : 2 ≤ m) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = (2 ^ m) ^ 2 ∧
      Nonempty (↥⁅ggAutFixedSubgroup (psuField h σ), ggAutFixedSubgroup (psuField h σ)⁆ ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m))) := by
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hf0m : f₀ = m := by omega
  subst f₀
  have hcardm : Nat.card (fixedField σ) = (2 ^ m) ^ 2 := by
    rw [hcard, show 2 * m = m * 2 from by omega, pow_mul]
  have h₀ : UnitaryFieldData 2 m (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  let G : Subgroup (GL (Fin 3) (fixedField σ)) := glPi false 3 (2 ^ m) (fixedField σ)
  let S : Subgroup (GL (Fin 3) (fixedField σ)) := unitarySU 2 m (fixedField σ) 3
  let Φ : ↥G →* unitaryPSU h 3 := puHom h hf h₀ hbar
  have hq₀ : 2 < 2 ^ m := by
    have h : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
    norm_num at h
    omega
  have hSG : S ≤ G :=
    slPi_le_glPi (π := false) (n := 3) (p := 2) (f := m) (K := fixedField σ)
      (hπ := fun _ => h₀)
  have hperfS : Group.IsPerfect S := isPerfect_unitarySU_three h₀ hq₀
  have hcomm_GG : ⁅G, G⁆ = S := by
    refine le_antisymm (commutator_glPi_false_le h₀) ?_
    calc S = ⁅S, S⁆ := (Subgroup.isPerfect_iff.mp hperfS).symm
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hSG hSG
  have hcomm_sub : commutator G = S.subgroupOf G := by
    rw [← ggCommutator_subgroupOf G, hcomm_GG]
  let Ψ : ↥S →* unitaryPSU h 3 := Φ.comp (Subgroup.inclusion hSG)
  have hfix : ggAutFixedSubgroup (psuField h σ) = Φ.range := by
    ext y
    rw [mem_ggAutFixedSubgroup]
    exact (mem_range_puHom_iff h hf h₀ hbar y).symm
  have hcomm_phi : ⁅Φ.range, Φ.range⁆ = Ψ.range := by
    calc ⁅Φ.range, Φ.range⁆
        = ⁅(⊤ : Subgroup ↥G).map Φ, (⊤ : Subgroup ↥G).map Φ⁆ := by
            rw [← MonoidHom.range_eq_map Φ]
      _ = (⁅(⊤ : Subgroup ↥G), (⊤ : Subgroup ↥G)⁆).map Φ :=
            (Subgroup.map_commutator (f := Φ) (H₁ := ⊤) (H₂ := ⊤)).symm
      _ = (commutator ↥G).map Φ := rfl
      _ = (S.subgroupOf G).map Φ := by rw [hcomm_sub]
      _ = ((Subgroup.inclusion hSG).range).map Φ := by rw [Subgroup.inclusion_range hSG]
      _ = Ψ.range := (MonoidHom.range_comp Φ (Subgroup.inclusion hSG)).symm
  have hker_eq : Ψ.ker = unitaryScalars h₀ 3 := by
    have h1 : Φ.ker = (StatedScalars (Fin 3) (fixedField σ)).subgroupOf G :=
      ker_puHom h hf h₀ hbar
    ext x
    change Φ (Subgroup.inclusion hSG x) = 1 ↔ x ∈ unitaryScalars h₀ 3
    rw [← MonoidHom.mem_ker, h1, Subgroup.mem_subgroupOf,
      unitaryScalars_eq h₀ (by norm_num : 1 ≤ 3), Subgroup.mem_subgroupOf]
    exact Iff.rfl
  let e1 : ↥⁅ggAutFixedSubgroup (psuField h σ), ggAutFixedSubgroup (psuField h σ)⁆ ≃*
      ↥Ψ.range := MulEquiv.subgroupCongr (by rw [hfix]; exact hcomm_phi)
  let e2 : ↥Ψ.range ≃* ↥S ⧸ Ψ.ker := (QuotientGroup.quotientKerEquivRange Ψ).symm
  let e3 : ↥S ⧸ Ψ.ker ≃* unitaryPSU h₀ 3 := QuotientGroup.quotientMulEquivOfEq hker_eq
  let e4 : unitaryPSU h₀ 3 ≃* StatedProj (StatedSU 3 (2 ^ m) (fixedField σ)) :=
    unitaryPSUEquiv h₀ (by norm_num : 1 ≤ 3)
  refine ⟨fixedField σ, inferInstance, h₀.finite, hcardm, ⟨?_⟩⟩
  exact e1.trans (e2.trans (e3.trans e4))

theorem gffa2_unitary_simple_nonab {K₀ : Type} [Field K₀] [Finite K₀] {m : ℕ} (hm : 2 ≤ m)
    (hK₀ : Nat.card K₀ = (2 ^ m) ^ 2) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m))) ∧
      ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m)), a * b ≠ b * a := by
  have hq₀ : 2 < 2 ^ m := by
    have h : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
    norm_num at h
    omega
  have hne : (3, 2 ^ m) ≠ (3, 2) := by
    intro hh
    have h2 : 2 ^ m = 2 := by simpa using congrArg Prod.snd hh
    omega
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K₀ 2 m hK₀ 3
      (by norm_num) hne
  refine ⟨hsimple, ?_⟩
  by_contra h
  push Not at h
  haveI : Nontrivial (LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m))) :=
    hsimple.toNontrivial
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m))) := by
    haveI : Group.IsPerfect (LargeEvenSUGroup (Fin 3) K₀ (2 ^ m)) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K₀) (p := 2) (f := m) hK₀
        (n := 3) (by norm_num) hne
    infer_instance
  exact Group.IsPerfect.not_isMulCommutative _ (IsMulCommutative.of_comm fun a b => h a b)

end CFSG.StandardType
