module

public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusPSL2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
public import CFSG.GroupTheory.QuasisimplePSolvable

public section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Pointwise

private theorem exists_inner_action_lift
    {H X Γ : Type} [Group H] [Group X] [Group Γ]
    (ι : H →* Γ) (hι : Function.Injective ι) (hZ : Subgroup.center H = ⊥)
    (φ : X →* Γ)
    (hact : ∀ x : X, ∃ h : H, ∀ a : H,
      φ x * ι a * (φ x)⁻¹ = ι (h * a * h⁻¹)) :
    ∃ ρ : X →* H, ∀ x a, φ x * ι a * (φ x)⁻¹ = ι (ρ x * a * (ρ x)⁻¹) := by
  classical
  let f : X → H := fun x => (hact x).choose
  have hf : ∀ x a, φ x * ι a * (φ x)⁻¹ = ι (f x * a * (f x)⁻¹) :=
    fun x => (hact x).choose_spec
  have hc := CFSG.mulAut_conj_injective hZ
  let ρ : X →* H :=
    { toFun := f
      map_one' := by
        apply hc
        ext a
        apply hι
        simpa only [MulAut.conj_apply, MulAut.one_apply, map_one, one_mul, mul_one, inv_one] using
          (hf 1 a).symm
      map_mul' := by
        intro x y
        apply hc
        ext a
        apply hι
        change ι (f (x * y) * a * (f (x * y))⁻¹) =
          ι ((f x * f y) * a * (f x * f y)⁻¹)
        calc ι (f (x * y) * a * (f (x * y))⁻¹)
            = φ (x * y) * ι a * (φ (x * y))⁻¹ := (hf (x * y) a).symm
          _ = φ x * (φ y * ι a * (φ y)⁻¹) * (φ x)⁻¹ := by rw [map_mul]; group
          _ = ι (f x * (f y * a * (f y)⁻¹) * (f x)⁻¹) := by rw [hf y a, hf]
          _ = ι ((f x * f y) * a * (f x * f y)⁻¹) := by congr 1; group }
  exact ⟨ρ, hf⟩


variable {τ : Tag} {Ω : Type} [Field Ω] {r₁ r₂ r₃ : Fin τ.rank → ℤ}
  (hc12 : ∀ A B : SL2 Ω, Commute (rootSL2 τ Ω r₁ A) (rootSL2 τ Ω r₂ B))
  (hc13 : ∀ A C : SL2 Ω, Commute (rootSL2 τ Ω r₁ A) (rootSL2 τ Ω r₃ C))
  (hc23 : ∀ B C : SL2 Ω, Commute (rootSL2 τ Ω r₂ B) (rootSL2 τ Ω r₃ C))
  (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)

include hc12 hc13 hc23 h₁ h₂ h₃

theorem mem_torusGroup_of_centralizes_three_rootSL2
    [IsAlgClosed Ω]
    {g : ModGL τ Ω}
    (hg : g ∈ torusGroup τ Ω ⊔ rootSpan τ Ω (threeRootSet r₁ r₂ r₃))
    (hcomm₁ : ∀ A, g * rootSL2 τ Ω r₁ A = rootSL2 τ Ω r₁ A * g)
    (hcomm₂ : ∀ B, g * rootSL2 τ Ω r₂ B = rootSL2 τ Ω r₂ B * g)
    (hcomm₃ : ∀ C, g * rootSL2 τ Ω r₃ C = rootSL2 τ Ω r₃ C * g) :
    g ∈ torusGroup τ Ω := by
  obtain ⟨b, A, B, C, rfl⟩ := exists_decomp hc12 hc13 hc23 h₁ h₂ h₃ hg
  obtain ⟨e₁, e₂, e₃⟩ := conj_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃ b A B C
  have key {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) (D : SL2 Ω)
      (he : ∀ U, (rootDiagUnit τ b *
        (rootSL2 τ Ω r₁ A * rootSL2 τ Ω r₂ B * rootSL2 τ Ω r₃ C)) * rootSL2 τ Ω r U *
        (rootDiagUnit τ b * (rootSL2 τ Ω r₁ A * rootSL2 τ Ω r₂ B * rootSL2 τ Ω r₃ C))⁻¹ =
        rootSL2 τ Ω r (conjSL (diagUnitOne (rootChar b r) * SpecialLinearGroup.toGL D) U))
      (hc : ∀ U, (rootDiagUnit τ b *
        (rootSL2 τ Ω r₁ A * rootSL2 τ Ω r₂ B * rootSL2 τ Ω r₃ C)) * rootSL2 τ Ω r U =
        rootSL2 τ Ω r U * (rootDiagUnit τ b *
          (rootSL2 τ Ω r₁ A * rootSL2 τ Ω r₂ B * rootSL2 τ Ω r₃ C))) :
      rootSL2 τ Ω r D ∈ torusGroup τ Ω := by
    have hfix : ∀ U, conjSL (diagUnitOne (rootChar b r) * SpecialLinearGroup.toGL D) U = U := by
      intro U
      apply rootSL2_injective_of_field (τ := τ) (K := Ω) r
      rw [← he U, hc U, mul_inv_cancel_right]
    have ht : rootDiagUnit τ b * rootSL2 τ Ω r D ∈ torusGroup τ Ω :=
      mem_torusGroup_of_centralizes_rootSL2 hr
        ⟨rootDiagUnit τ b, rootDiagUnit_mem_torusGroup b, rootSL2 τ Ω r D, ⟨D, rfl⟩, rfl⟩
        fun U => by
          have h := conj_rootSL2_torus_mul hr b D U
          rw [hfix U] at h
          exact mul_inv_eq_iff_eq_mul.mp h
    have h := (torusGroup τ Ω).mul_mem
      ((torusGroup τ Ω).inv_mem (rootDiagUnit_mem_torusGroup b)) ht
    simpa only [inv_mul_cancel_left] using h
  exact (torusGroup τ Ω).mul_mem (rootDiagUnit_mem_torusGroup b)
    ((torusGroup τ Ω).mul_mem ((torusGroup τ Ω).mul_mem
      (key h₁ A e₁ hcomm₁) (key h₂ B e₂ hcomm₂)) (key h₃ C e₃ hcomm₃))

theorem le_torusGroup_of_perfect_threePrime_threeA1
    [IsAlgClosed Ω] [CharP Ω 2]
    {K : Type} [Field K] [Finite K] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (φ : Y →* ModGL τ Ω)
    (hφ : φ.range ≤ torusGroup τ Ω ⊔ rootSpan τ Ω (threeRootSet r₁ r₂ r₃))
    (hY3 : ¬ 3 ∣ Nat.card Y) : φ.range ≤ torusGroup τ Ω := by
  have hZ : Subgroup.center (SL2 Ω) = ⊥ := by
    rw [← scalars_eq_center, CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot]
  have hproj : Function.Injective (proj 2 Ω) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot]
  have hinner {r : Fin τ.rank → ℤ}
      (hin : ∀ y : Y, ∃ D : SL2 Ω, ∀ U,
        φ y * rootSL2 τ Ω r U * (φ y)⁻¹ = rootSL2 τ Ω r (D * U * D⁻¹)) :
      ∀ y U, φ y * rootSL2 τ Ω r U = rootSL2 τ Ω r U * φ y := by
    obtain ⟨ρ, hρ⟩ := exists_inner_action_lift (rootSL2 τ Ω r)
      (rootSL2_injective_of_field (τ := τ) (K := Ω) r) hZ φ hin
    have hρone : ∀ y, ρ y = 1 := fun y => hproj (by
      simpa only [MonoidHom.comp_apply, map_one] using
        CFSG.RankThree.PartTwo.Sec6.BThreeCensus.map_eq_one_of_perfect_threePrime_projectiveSL_two_algebraic
          (K := K) ((proj 2 Ω).comp ρ) hY3 y)
    intro y U
    have h := hρ y U
    rw [hρone y, one_mul, inv_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hact : ∀ y : Y, ∃ D₁ D₂ D₃ : SL2 Ω,
      (∀ U, φ y * rootSL2 τ Ω r₁ U * (φ y)⁻¹ = rootSL2 τ Ω r₁ (D₁ * U * D₁⁻¹)) ∧
      (∀ U, φ y * rootSL2 τ Ω r₂ U * (φ y)⁻¹ = rootSL2 τ Ω r₂ (D₂ * U * D₂⁻¹)) ∧
      (∀ U, φ y * rootSL2 τ Ω r₃ U * (φ y)⁻¹ = rootSL2 τ Ω r₃ (D₃ * U * D₃⁻¹)) := by
    intro y
    obtain ⟨b, A, B, C, he⟩ := exists_decomp hc12 hc13 hc23 h₁ h₂ h₃ (hφ ⟨y, rfl⟩)
    obtain ⟨e₁, e₂, e₃⟩ := conj_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃ b A B C
    obtain ⟨D₁, hD₁⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sl2_conjSL
      (diagUnitOne (rootChar b r₁) * SpecialLinearGroup.toGL A)
    obtain ⟨D₂, hD₂⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sl2_conjSL
      (diagUnitOne (rootChar b r₂) * SpecialLinearGroup.toGL B)
    obtain ⟨D₃, hD₃⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sl2_conjSL
      (diagUnitOne (rootChar b r₃) * SpecialLinearGroup.toGL C)
    refine ⟨D₁, D₂, D₃, ?_, ?_, ?_⟩
    · intro U; rw [he, e₁ U, hD₁ U]
    · intro U; rw [he, e₂ U, hD₂ U]
    · intro U; rw [he, e₃ U, hD₃ U]
  have hcomm₁ := hinner fun y => let ⟨D₁, _, _, h₁, _, _⟩ := hact y; ⟨D₁, h₁⟩
  have hcomm₂ := hinner fun y => let ⟨_, D₂, _, _, h₂, _⟩ := hact y; ⟨D₂, h₂⟩
  have hcomm₃ := hinner fun y => let ⟨_, _, D₃, _, _, h₃⟩ := hact y; ⟨D₃, h₃⟩
  rintro _ ⟨y, rfl⟩
  exact mem_torusGroup_of_centralizes_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃
    (hφ ⟨y, rfl⟩) (hcomm₁ y) (hcomm₂ y) (hcomm₃ y)

theorem isSolvable_of_threeA1_and_complement_derived
    [IsAlgClosed Ω] [CharP Ω 2]
    {K : Type} [Field K] [Finite K] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    {G : Type} [Group G] [Finite G]
    (φ : G →* ModGL τ Ω)
    (hφ : φ.range ≤ torusGroup τ Ω ⊔ rootSpan τ Ω (threeRootSet r₁ r₂ r₃))
    (hker : φ.ker ≤ Subgroup.center G)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator G)) : Group.IsSolvable G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  rw [Group.isSolvable_iff_commutator_lt]
  intro Y hY
  refine lt_of_le_of_ne (Subgroup.commutator_le.2 ?_) ?_
  · intro a ha b hb
    rw [_root_.commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  · intro hperf
    have : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hperf
    have hYle : Y ≤ _root_.commutator G := by
      rw [← Subgroup.commutator_eq_self (H := Y), _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    have hY3 : ¬ 3 ∣ Nat.card Y := Nat.prime_three.coprime_iff_not_dvd.mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect
        (CFSG.hasNormalPComplement_of_le 3 hYle hNPC))
    let ψ : Y →* ModGL τ Ω := φ.comp Y.subtype
    have hψT : ψ.range ≤ torusGroup τ Ω :=
      le_torusGroup_of_perfect_threePrime_threeA1 hc12 hc13 hc23 h₁ h₂ h₃ (K := K) ψ
        (by rintro _ ⟨y, rfl⟩; exact hφ ⟨(y : G), rfl⟩) hY3
    have hψs : Group.IsSolvable ψ.range := Group.isSolvable_of_comm fun x y => by
      obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hψT x.2)
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hψT y.2)
      apply Subtype.ext
      change (x : ModGL τ Ω) * (y : ModGL τ Ω) = (y : ModGL τ Ω) * (x : ModGL τ Ω)
      rw [ha, hb, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
        ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm a b]
    have hψk : Group.IsSolvable ψ.ker := Group.isSolvable_of_comm fun x y => by
      apply Subtype.ext
      apply Subtype.ext
      exact ((Subgroup.mem_center_iff.mp (hker x.2)) (y : Y)).symm
    have hYs : Group.IsSolvable Y := Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
    exact hY (CFSG.RankThree.PartTwo.Sec6.BThreeCensus.eq_bot_of_isPerfect_of_isSolvable
      inferInstance hYs)

end CFSG.RankThree.PartOne.KE
