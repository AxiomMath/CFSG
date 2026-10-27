module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpTwelveLin
import CFSG.LargeExtraspecial.DW2AOutOrth
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
import CFSG.Open.StatedZModTwo
import CFSG.RankThree.PartOne.K159.BorelSp
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open

theorem center_eq_bot_of_twelve
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (h : StatedClassicalModel (K ⧸ center K) .PSp 6 2 1 ∨
      StatedClassicalModel (K ⧸ center K) .POmegaPlus 6 2 1 ∨
      StatedClassicalModel (K ⧸ center K) .POmegaMinus 6 2 1) : center K = ⊥ := by
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  have hM : ∀ {S : Type} [Group S], (K ⧸ center K ≃* S) →
      Nat.card (griessHopfMultiplier S) = 1 → center K = ⊥ := fun e h1 => by
    have := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e
    rw [h1, Nat.dvd_one] at this
    exact Subgroup.card_eq_one.1 this
  rcases h with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, b, c, hirr, ⟨e⟩⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hF])
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier
      (n := 6) (f := 1) hF le_rfl (by norm_num) (by omega)
    refine hM e ?_
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hF]
    norm_num
  · obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier
        (n := 6) (by norm_num) hF (by rw [hF, pow_one])
    refine hM e ?_
    rw [Nat.card_congr eM.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod]
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  · obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaMinus_two_hopfMultiplier
        (n := 6) (by norm_num) hirr hF (by rw [hF, pow_one])
    refine hM e ?_
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    norm_num

theorem pumpUpAut_map_config {F V : Type} [Field F] [AddCommGroup V] [Module F V] {K : Type}
    [Group K] [Finite K] {W Wk : Subgroup K} {ζ ξ : MulAut K} {Q A : Subgroup (MulAut K)}
    (h : PumpUpAut W Wk ζ ξ Q A) (hZ : center K = ⊥) {z : K} (hζ : ζ = MulAut.conj z)
    (φ : K →* (V ≃ₗ[F] V)) (hφ : Function.Injective φ) :
    φ z ^ 3 = 1 ∧ φ z ≠ 1 ∧ IsSimpleGroup (W.map φ) ∧ Nat.card (W.map φ) = 13685760 ∧
      (∀ w ∈ W.map φ, w * φ z = φ z * w) ∧
      IsComponentOf (W.map φ) (φ.range ⊓ Subgroup.centralizer {φ z}) ∧
      (∀ g ∈ φ.range, orderOf g = 3 → (∀ w ∈ W.map φ, g * w = w * g) → g * φ z = φ z * g →
        g ∈ Subgroup.zpowers (φ z)) := by
  classical
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [← hZ, mem_center_iff]
    intro b
    have hb := congrArg (fun α : MulAut K => α b) ((MonoidHom.mem_ker).1 ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at hb
    calc b * a = a * b * a⁻¹ * a := by rw [hb]
      _ = a * b := by group
  have hWcl : StatedClassicalModel W .PSU 5 2 1 := by
    obtain ⟨-, hc | ⟨h0, -⟩⟩ := h.W_model
    · exact hc
    · omega
  haveI : IsSimpleGroup W := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hWcl
  have hWc : Nat.card W = 13685760 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hWcl
  let eW : W ≃* W.map φ := W.equivMapOfInjective φ hφ
  have hzW : ∀ w ∈ W, z * w = w * z := fun w hw => by
    have h1 : ζ w = w := mem_autFix.1 (h.W_comp.1 hw)
    rw [hζ, MulAut.conj_apply] at h1
    calc z * w = z * w * z⁻¹ * z := by group
      _ = w * z := by rw [h1]
  have hfix : autFix ζ = Subgroup.centralizer {z} := by
    ext k
    rw [mem_autFix, hζ, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      calc k * z = z * k * z⁻¹ * z := by rw [hk]
        _ = z * k := by group
    · intro hk
      rw [← hk]
      group
  refine ⟨?_, ?_, MulEquiv.isSimpleGroup eW.symm, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow]
    have h3 : MulAut.conj (z ^ 3) = 1 := by rw [map_pow, ← hζ, h.ζ_cube]
    rw [hconj (h3.trans (map_one _).symm), map_one]
  · intro h1
    apply h.ζ_ne
    rw [hζ, hφ (h1.trans (map_one φ).symm), map_one]
  · rw [← Nat.card_congr eW.toEquiv, hWc]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hzW w hw]
  · have hc := hfix ▸ h.W_comp
    have hcomp : IsComponentOf (W.map φ) ((Subgroup.centralizer {z}).map φ) :=
      ⟨Subgroup.map_mono hc.1, hc.2.1.map φ,
        CFSG.ComponentClassification.Components.quasisimple_of_equiv
          (W.equivMapOfInjective φ hφ).symm hc.2.2⟩
    convert hcomp using 1
    ext g
    simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨k, rfl⟩, hg⟩
      exact ⟨k, hφ (by rw [map_mul, map_mul]; exact hg), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, by rw [← map_mul, ← map_mul, hk]⟩
  · rintro _ ⟨k, rfl⟩ hk3 hkW hkz
    have hord : orderOf k = 3 := by rwa [orderOf_injective φ hφ] at hk3
    have hkW' : ∀ w ∈ W, k * w = w * k := fun w hw => hφ (by
      rw [map_mul, map_mul]
      exact hkW _ ⟨w, hw, rfl⟩)
    have hkz' : k * z = z * k := hφ (by rw [map_mul, map_mul]; exact hkz)
    have hsc : MulAut.conj k ∈ A := h.selfcent k hord fun α hα => by
      obtain ⟨w, hw, β, hβ, rfl⟩ := h.A_gen α hα
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβ
      rw [hζ, ← map_zpow, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
      have hc : z ^ n * k = k * z ^ n := ((Commute.zpow_left (hkz'.symm : Commute z k) n)).eq
      rw [hc, mul_inv_cancel_right, ← hkW' w hw, mul_inv_cancel_right]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (h.A_fixW _ hsc fun w hw => by
      rw [MulAut.conj_apply, hkW' w hw, mul_inv_cancel_right])
    rw [hζ, ← map_zpow] at hn
    rw [← hconj hn, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ n

private theorem exists_sp_model {K : Type} [Group K] (hZ : center K = ⊥)
    (h : StatedClassicalModel (K ⧸ center K) .PSp 6 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ φ : K →* ((Fin 6 ⊕ Fin 6 → F) ≃ₗ[F] (Fin 6 ⊕ Fin 6 → F)), Function.Injective φ ∧
        φ.range = TauCeti.BilinForm.isometryGroup (Matrix.toBilin' (Matrix.J (Fin 6) F)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨eSp⟩ := CFSG.RankThree.PartOne.K159.nonempty_isometryGroup_mulEquiv_statedSp
    (Matrix.toBilin' (Matrix.J (Fin 6) F))
    CFSG.ClassicalInvolution.Models.SymplecticPairs.isAlt_toBilin'_J
    CFSG.ClassicalInvolution.Models.SymplecticPairs.nondegenerate_toBilin'_J (m := 6)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
  have hS : (StatedScalars (Fin 6 ⊕ Fin 6) F).subgroupOf (StatedSp 6 F) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hF2, Subgroup.bot_subgroupOf]
  let e₁ : StatedProj (StatedSp 6 F) ≃* StatedSp 6 F :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  let eK : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let ψ := eK.trans (e.trans (e₁.trans eSp.symm))
  refine ⟨F, inferInstance, inferInstance, hF2, (Subgroup.subtype _).comp ψ.toMonoidHom,
    (Subgroup.subtype_injective _).comp ψ.injective, ?_⟩
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    exact (ψ k).2
  · intro hg
    exact ⟨ψ.symm ⟨g, hg⟩, by simp⟩

private theorem exists_omegaPlus_model {K : Type} [Group K] (hZ : center K = ⊥)
    (h : StatedClassicalModel (K ⧸ center K) .POmegaPlus 6 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ φ : K →* ((Fin 6 ⊕ Fin 6 → F) ≃ₗ[F] (Fin 6 ⊕ Fin 6 → F)), Function.Injective φ ∧
        φ.range = CFSG.RankThree.Classical2.orthDerived
          (CFSG.LieType.Universal.Spin.quadPlus 6 F) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hcoe := CFSG.LieType.Universal.Spin.coe_quadPlus 6 F
  have hv : ∃ v, (CFSG.LieType.Universal.Spin.quadPlus 6 F) v ≠ 0 := by
    refine ⟨Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1, ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply, Finset.sum_eq_single (0 : Fin 6)]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hS := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hcoe hv
  let e₁ : StatedProj (StatedOmega (StatedQuadPlus 6 F)) ≃* StatedOmega (StatedQuadPlus 6 F) :=
    (QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot
  let e₂ := CFSG.RankThree.PartOne.statedOmegaOrthEquiv hcoe
  let eK : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let ψ := eK.trans (e.trans (e₁.trans e₂))
  refine ⟨F, inferInstance, inferInstance, hF2, (Subgroup.subtype _).comp ψ.toMonoidHom,
    (Subgroup.subtype_injective _).comp ψ.injective, ?_⟩
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    exact (ψ k).2
  · intro hg
    exact ⟨ψ.symm ⟨g, hg⟩, by simp⟩

private theorem isPGroup_outer_twelve {L : Type} [Group L]
    (h : StatedClassicalModel L .PSp 6 2 1 ∨ StatedClassicalModel L .POmegaPlus 6 2 1) :
    IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) := by
  rcases h with h | h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have h1 :=
      (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
        Nat.prime_two le_rfl (by norm_num : 3 ≤ 6) hF).1
    refine IsPGroup.of_card (n := 0) ?_
    rw [pow_zero, Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact Nat.dvd_one.1 (by simpa using h1)
  · exact CFSG.LargeExtraspecial.DW.isPGroup_outer_POmegaPlus (by norm_num) (Or.inl ⟨by decide, h⟩)

theorem pumpUpTwelveInput_holds :
    PumpUpTwelveInput := by
  intro K _ _ W Wk ζ ξ Q A h hmodel
  have hcl : StatedClassicalModel (K ⧸ center K) .PSp 6 2 1 ∨
      StatedClassicalModel (K ⧸ center K) .POmegaPlus 6 2 1 := by
    rcases hmodel with ⟨-, hc | ⟨h0, -⟩⟩ | ⟨-, hc | ⟨h0, -⟩⟩
    · exact Or.inl hc
    · omega
    · exact Or.inr hc
    · omega
  have hZ : center K = ⊥ :=
    center_eq_bot_of_twelve h.quasi (hcl.elim Or.inl fun hc => Or.inr (Or.inl hc))
  let eK : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hout : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    (isPGroup_outer_twelve hcl).of_equiv
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eK).symm
  obtain ⟨z, hz⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hout (by decide) h.ζ_cube
  rcases hcl with hc | hc
  · obtain ⟨F, _, _, hF, φ, hφ, hrange⟩ := exists_sp_model hZ hc
    obtain ⟨hz3, hz1, hWs, hWc, -, hcomp, hKF⟩ := pumpUpAut_map_config h hZ hz.symm φ hφ
    rw [hrange] at hcomp hKF
    have hzB : φ z ∈ TauCeti.BilinForm.isometryGroup (Matrix.toBilin' (Matrix.J (Fin 6) F)) :=
      hrange ▸ ⟨z, rfl⟩
    haveI := hWs
    exact false_of_twelve_sp_config hF
      (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
      CFSG.ClassicalInvolution.Models.SymplecticPairs.isAlt_toBilin'_J
      CFSG.ClassicalInvolution.Models.SymplecticPairs.nondegenerate_toBilin'_J hzB hz3 hz1 hWc
      hcomp hKF
  · obtain ⟨F, _, _, hF, φ, hφ, hrange⟩ := exists_omegaPlus_model hZ hc
    obtain ⟨hz3, hz1, hWs, hWc, -, hcomp, hKF⟩ := pumpUpAut_map_config h hZ hz.symm φ hφ
    rw [hrange] at hcomp hKF
    have hzΩ : φ z ∈ CFSG.RankThree.Classical2.orthDerived
        (CFSG.LieType.Universal.Spin.quadPlus 6 F) := hrange ▸ ⟨z, rfl⟩
    haveI := hWs
    exact false_of_twelve_orth_config hF
      (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 F)
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F 6) hzΩ hz3 hz1 hWc hcomp hKF

end CFSG.GGQ2Prime
