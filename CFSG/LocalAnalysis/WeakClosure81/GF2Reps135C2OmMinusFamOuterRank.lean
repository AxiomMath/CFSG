module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamAut
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamReflDatum
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOuterInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamCTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOrbit
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.IndepRank
import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem omfor_finrank_conj {G k U : Type} [Group G] [Field k] [AddCommGroup U]
    [Module k U] (σ : Representation k G U) (g : G) {f f' : U →ₗ[k] U}
    (h : ∀ v, σ g (f v) = f' (σ g v)) :
    Module.finrank k (LinearMap.range (f' - 1)) = Module.finrank k (LinearMap.range (f - 1)) :=
  CFSG.HardMathSupport.GuralnickMalle.finrank_range_sub_one_eq_of_intertwines
    (LinearEquiv.ofLinear (σ g) (σ g⁻¹) (LinearMap.ext fun v => σ.self_inv_apply g v)
      (LinearMap.ext fun v => σ.inv_self_apply g v)) f f' h

private theorem omfor_finrank_range_sub_le {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    [Module.Finite k U] {A S S' : U →ₗ[k] U} (hA : Function.Surjective A)
    (hS : S' ∘ₗ A = A ∘ₗ S) :
    Module.finrank k (LinearMap.range (S' - S)) ≤
      2 * Module.finrank k (LinearMap.range (A - 1)) := by
  have h1 : LinearMap.range ((S' - S) ∘ₗ A) = LinearMap.range (S' - S) :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hA)
  have h2 : (S' - S) ∘ₗ A = (A - 1) ∘ₗ S - S ∘ₗ (A - 1) := by
    rw [LinearMap.sub_comp, hS]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.End.one_apply, map_sub]
    abel
  have h3 : LinearMap.range ((A - 1) ∘ₗ S - S ∘ₗ (A - 1)) ≤
      LinearMap.range (A - 1) ⊔ (LinearMap.range (A - 1)).map S := by
    intro w hw
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _))
  rw [← h1, h2]
  have h4 := Submodule.finrank_mono h3
  have h5 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (A - 1))
    ((LinearMap.range (A - 1)).map S)
  have h6 := Submodule.finrank_map_le S (LinearMap.range (A - 1))
  omega

theorem omMinus_two_outer_four_le_of_isCurtisType (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n)
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k] [CharP k 2] {U : Type}
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    {σ : Representation k (spinGroup (quadMinus n K b c)) U} (hσ : IsSimpleRep σ) {y : U}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).IsCurtisType σ y χ μ)
    {j : Fin (n - 1)} (hj : j.val ≠ 0)
    (hsep : μ j = (SmallO8mCurtis.curtisDatum n (by omega) hirrQ).dScalar χ j) (T : U →ₗ[k] U)
    {h : spinGroup (quadMinus n K b c)} (hh : h * omMinusReflAut n (by omega) hirrQ h = 1)
    (hT : ∀ (g : spinGroup (quadMinus n K b c)) (u : U),
      T (σ g u) = σ (h * omMinusReflAut n (by omega) hirrQ g * h⁻¹) (T u)) :
    4 ≤ Module.finrank k (LinearMap.range (T - 1)) := by
  have hn4 : 4 ≤ n := by omega
  have ht' : (SmallO8mCurtis.curtisDatum n hn4 hirrQ).IsCurtisType σ y χ μ := ht
  have hh' : h * omMinusReflAut n hn4 hirrQ h = 1 := hh
  have hT' : ∀ (g : spinGroup (quadMinus n K b c)) (u : U),
      T (σ g u) = σ (h * omMinusReflAut n hn4 hirrQ g * h⁻¹) (T u) := hT
  obtain ⟨g₂, x₂, hx₂, hg₂⟩ := exists_conj_shortPosHom_planeOne_eq_nW (b := b) (c := c) hn4 hirrQ
  have h7 : 7 ≤ Module.finrank k (LinearMap.range
      (σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x₂) - 1)) :=
    omMinus_seven_le_rank_negLastTwo hn hirrQ hσ ht hj hsep hx₂
  obtain ⟨g, hg⟩ := omMinus_exists_conj_reflAut_eq_nW hn4 hirrQ hh'
  set T₁ : U →ₗ[k] U := σ g ∘ₗ T ∘ₗ σ g⁻¹ with hT₁def
  have hrank : Module.finrank k (LinearMap.range (T₁ - 1)) =
      Module.finrank k (LinearMap.range (T - 1)) :=
    omfor_finrank_conj σ g fun v => by
      rw [hT₁def, LinearMap.comp_apply, LinearMap.comp_apply, Representation.inv_self_apply]
  have hT₁ : ∀ (a : spinGroup (quadMinus n K b c)) (u : U),
      T₁ (σ a u) = σ (g * h * omMinusReflAut n hn4 hirrQ g⁻¹ * omMinusReflAut n hn4 hirrQ a *
        (g * h * omMinusReflAut n hn4 hirrQ g⁻¹)⁻¹) (T₁ u) := by
    intro a u
    have e1 : σ g⁻¹ (σ a u) = σ (g⁻¹ * a * g) (σ g⁻¹ u) := by
      rw [act_mul, act_mul, mul_inv_cancel_right]
    rw [hT₁def, LinearMap.comp_apply, LinearMap.comp_apply, e1, hT', LinearMap.comp_apply,
      LinearMap.comp_apply, act_mul, act_mul]
    congr 2
    simp only [map_mul, map_inv]
    group
  rw [← hrank]
  rcases hg with hz | ⟨x, π, hxr, hπ, hπ0, hπ1, hz⟩
  ·
    rw [hz] at hT₁
    simp only [one_mul, inv_one, mul_one] at hT₁
    have hker : ∀ (a : spinGroup (quadMinus n K b c)), ∀ u ∈ LinearMap.ker T₁,
        σ a u ∈ LinearMap.ker T₁ := by
      intro a u hu
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hT₁, hu, map_zero]
    rcases hσ.2 _ hker with hk | hk
    · have hsurj : Function.Surjective T₁ :=
        LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hk)
      have hu₀ := omMinusReflAut_shortPosHom_mul_inv hK hn4 hirrQ
      set z₀ := shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd ![(0 : K), 1])
        with hz₀
      set u₀ := shortPosHom n hirrQ ⟨n - 2, by omega⟩ (Multiplicative.ofAdd (planeOne : Fin 2 → K))
        with hu₀def
      have hcomm : σ (omMinusReflAut n hn4 hirrQ z₀) ∘ₗ T₁ = T₁ ∘ₗ σ z₀ :=
        LinearMap.ext fun v => (hT₁ z₀ v).symm
      have h2 := omfor_finrank_range_sub_le hsurj hcomm
      have hsub : σ u₀ - 1 = (σ (omMinusReflAut n hn4 hirrQ z₀) - σ z₀) ∘ₗ σ z₀⁻¹ := by
        rw [← hu₀]
        refine LinearMap.ext fun v => ?_
        rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sub_apply, act_mul,
          Representation.self_inv_apply, Module.End.one_apply]
      have hle : LinearMap.range (σ u₀ - 1) ≤
          LinearMap.range (σ (omMinusReflAut n hn4 hirrQ z₀) - σ z₀) := by
        rw [hsub]
        exact LinearMap.range_comp_le_range _ _
      have hconj : Module.finrank k (LinearMap.range
          (σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x₂) - 1)) =
          Module.finrank k (LinearMap.range (σ u₀ - 1)) :=
        omfor_finrank_conj σ g₂ fun v => by
          rw [← hg₂, act_mul, act_mul, inv_mul_cancel_right]
      have h8 := Submodule.finrank_mono hle
      omega
    ·
      have hT0 : T₁ = 0 := LinearMap.ker_eq_top.mp hk
      have htop : LinearMap.range (T₁ - 1) = ⊤ := by
        rw [hT0, zero_sub, LinearMap.range_neg]
        exact LinearMap.range_eq_top.mpr fun v => ⟨v, rfl⟩
      have h8 := Submodule.finrank_le
        (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x₂) - 1))
      rw [htop, finrank_top]
      omega
  ·
    rw [hz] at hT₁
    have hfix : σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x)⁻¹ (T₁ y) ∈
        (SmallO8mCurtis.curtisDatum n hn4 hirrQ).fixU σ := by
      rw [CurtisDatum.mem_fixU]
      intro u hu
      have h1 := hT₁ (omMinusReflAut n hn4 hirrQ u) y
      rw [(CurtisDatum.mem_fixU _ _).mp ht'.1 _ (omMinusReflAut_mem_U hn4 hirrQ hu),
        omMinusReflAut_apply_apply] at h1
      conv_rhs => rw [h1]
      rw [act_mul, act_mul]
      congr 2
      group
    obtain ⟨l, hl⟩ := CurtisDatum.fixU_eq_smul _ hσ ht' hfix
    have hTy : T₁ y = l • σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x) y := by
      have h1 := congrArg (σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW x)) hl
      rwa [Representation.self_inv_apply, map_smul] at h1
    have hshape : ∀ w, ∃ a : k, T₁ (σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW w) y) =
        a • σ ((SmallO8mCurtis.curtisDatum n hn4 hirrQ).nW (x * w)) y := by
      intro w
      obtain ⟨t, htH, htw⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_mul
        (SmallO8mCurtis.curtisDatum n hn4 hirrQ) x w
      refine ⟨l * χ t, ?_⟩
      rw [hT₁, omMinusReflAut_nW, hTy, map_smul, act_mul, inv_mul_cancel_right, htw, ← act_mul,
        ht'.2.2.1 t htH, map_smul, smul_smul]
    exact omMinus_four_le_rank_of_map_shapeA hn hirrQ hσ ht hj hsep hxr hπ hπ0 hπ1 T₁ hshape

end CFSG.LocalAnalysis.WeakClosure81
