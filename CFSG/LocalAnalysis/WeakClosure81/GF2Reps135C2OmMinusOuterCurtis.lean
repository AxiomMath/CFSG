module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.RepresentationTheory.FixedBaseChange
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LieType.RootSystem
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

omit [Finite K] [CharP K 2] in
private theorem omMinus_two_isAbsolutelyIrreducible {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2) :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ := by
  classical
  have : ρ.IsIrreducible := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  rw [CFSG.Theory.Representation.isAbsolutelyIrreducible_iff_surjective]
  have hcard : Nat.card (CFSG.Theory.Representation.End ρ) = 2 := by
    change Nat.card (ρ →ₗ ρ) = 2
    rw [Nat.card_congr
      (CFSG.Theory.Representation.RepMap.equivLinearMapAsModule (ρ := ρ) (σ := ρ)).toEquiv]
    exact hE
  have : Nontrivial V := hρ.1
  have : Finite (CFSG.Theory.Representation.End ρ) :=
    (Nat.card_ne_zero.mp (by rw [hcard]; norm_num)).2
  let : Fintype (CFSG.Theory.Representation.End ρ) := Fintype.ofFinite _
  have hcard' : Fintype.card (ZMod 2) = Fintype.card (CFSG.Theory.Representation.End ρ) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard')).mp
    (algebraMap (ZMod 2) (CFSG.Theory.Representation.End ρ)).injective

private theorem omMinus_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

private theorem omMinus_two_eq_of_smul {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {x y : V} {a : ZMod 2} (hx : x = a • y) (hx0 : x ≠ 0) : x = y := by
  have ha : a ≠ 0 := fun h => hx0 (by rw [hx, h, zero_smul])
  rw [hx, omMinus_two_eq_one_of_ne_zero ha, one_smul]

theorem omMinus_two_exists_isCurtisType_of_card_end {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2) :
    ∃ (y : V) (χ : spinGroup (quadMinus 4 K b c) → ZMod 2) (μ : Fin 3 → ZMod 2),
      (o8mDatum hirrQ).IsCurtisType ρ y χ μ ∧ ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1 := by
  classical
  let D := o8mDatum hirrQ
  let k := AlgebraicClosure (ZMod 2)
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    finite_group (isFiniteType_cartanB 3)
  have hρk : IsSimpleRep (CFSG.Theory.Representation.extendScalars k ρ) :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff _).mp
      ((omMinus_two_isAbsolutelyIrreducible hρ hE).irreducible_of_extension ρ k)
  have hdim : Module.finrank (ZMod 2) (D.fixU ρ) = 1 := by
    change Module.finrank (ZMod 2) (fixSub ρ D.U) = 1
    rw [← CFSG.Theory.Representation.finrank_fixSub_extendScalars (F' := k) ρ D.U]
    exact D.finrank_fixU (SmallO8mCurtis.curtisDatum_splitOver (K := K) (k := k) hirrQ) hρk
  obtain ⟨⟨y, hy⟩, hy0', hspan⟩ := finrank_eq_one_iff'.mp hdim
  have hy0 : y ≠ 0 := fun h => hy0' (Subtype.ext h)
  have hline : ∀ x ∈ D.fixU ρ, ∃ a : ZMod 2, x = a • y := fun x hx => by
    obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hHy : ∀ h ∈ D.H, ρ h y = y := by
    intro h hh
    obtain ⟨a, ha⟩ := hline _ (D.act_H_mem_fixU ρ hh hy)
    refine omMinus_two_eq_of_smul ha fun h0 => hy0 ?_
    rw [← ρ.inv_self_apply h y, h0, map_zero]
  let μ : Fin 3 → ZMod 2 := fun s => if D.heckeT ρ s y = y then 1 else 0
  have hμ : ∀ s, D.heckeT ρ s y = μ s • y := by
    intro s
    obtain ⟨a, ha⟩ := hline _ (D.heckeT_mem_fixU ρ s hy)
    by_cases h0 : D.heckeT ρ s y = 0
    · have hne : ¬ (0 : V) = y := fun h => hy0 h.symm
      simp [μ, h0, hne]
    · have h1 := omMinus_two_eq_of_smul ha h0
      simp [μ, h1]
  refine ⟨y, fun _ => 1, μ, ⟨hy, hy0, fun h hh => by rw [hHy h hh, one_smul], hμ⟩,
    fun _ _ => rfl⟩

theorem omMinus_two_intertwiner_fix {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : spinGroup (quadMinus 4 K b c) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ)
    (β : spinGroup (quadMinus 4 K b c) →* spinGroup (quadMinus 4 K b c))
    (hβ2 : ∀ g, β (β g) = g) (hβU : ∀ u ∈ (o8mDatum hirrQ).U, β u ∈ (o8mDatum hirrQ).U)
    (j : V ≃ₗ[ZMod 2] V) (hj : ∀ g v, j (ρ g (j.symm v)) = ρ (β g) v) :
    j y = y := by
  have hjy : j y ∈ (o8mDatum hirrQ).fixU ρ := by
    intro u hu
    have h1 := hj (β u) (j y)
    rw [LinearEquiv.symm_apply_apply, ht.1 (β u) (hβU u hu), hβ2] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := (o8mDatum hirrQ).fixU_eq_smul hρ ht hjy
  exact omMinus_two_eq_of_smul ha fun h0 => ht.2.1 (j.injective (h0.trans (map_zero j).symm))

theorem omMinus_two_mu_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) {y : V} {χ : spinGroup (quadMinus 4 K b c) → ZMod 2}
    {μ : Fin 3 → ZMod 2} (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ)
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨β, hβ⟩ := (o8mDatum hirrQ).iso_of_isCurtisType hρ
    (omMinus_isSimpleRep_trivial (k := ZMod 2) _) ht
    (isCurtisType_omMinus_two_trivial (hirrQ := hirrQ) hχ)
  obtain ⟨g, hg⟩ := hρ1
  refine hg (LinearMap.ext fun v => β.injective ?_)
  rw [hβ g v, Representation.trivial_apply, Module.End.one_apply]

theorem omMinus_two_mu_ne_natural (hK : Nat.card K = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    (hρ : IsSimpleRep ρ)
    (hnat : ¬ ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v)
    {y : V} {χ : spinGroup (quadMinus 4 K b c) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    μ ≠ fun s => if s.val = 0 then 1 else 0 := by
  rintro rfl
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hK
  let φ : K →+* ZMod 2 := (FiniteField.ringEquivOfCardEq hcard).toRingHom
  let : Algebra K (ZMod 2) := φ.toAlgebra
  obtain ⟨β, hβ⟩ := (o8mDatum hirrQ).iso_of_isCurtisType hρ
    (SmallO8mCurtis.naturalRep_isSimple (by norm_num : 4 ≤ 4) hirrQ φ) ht
    (isCurtisType_omMinus_two_natural (hirrQ := hirrQ) hK φ hχ)
  have : Nontrivial V := hρ.1
  obtain ⟨w, hw⟩ : ∃ w : V, w ≠ 0 := exists_ne 0
  let : DistribMulAction (spinGroup (quadMinus 4 K b c)) V :=
    { smul := fun g w => ρ g w
      one_smul := fun w => by change ρ 1 w = w; rw [map_one]; rfl
      mul_smul := fun g h w => by change ρ (g * h) w = ρ g (ρ h w); rw [map_mul]; rfl
      smul_zero := fun g => map_zero (ρ g)
      smul_add := fun g w w' => map_add (ρ g) w w' }
  refine hnat (CFSG.LieType.SpecialLinear.exists_addHom_of_extend (fun g => mat 4 g)
    β.toLinearMap.toAddMonoidHom (fun h => hw (β.injective
      ((DFunLike.congr_fun h w).trans (map_zero β).symm))) fun g w => ?_)
  have h := hβ g w
  rw [SmallO8mCurtis.naturalRep_apply] at h
  exact h

end CFSG.LocalAnalysis.WeakClosure81
