module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPairsF4
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2F4Outer
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcPeriodic
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.ReductionArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc CFSG.SeitzReduction


variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

private theorem w135c2_f4_direct_data (hctx : Is135Context Y L) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .F4 n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ Nat.card K = 2 ^ f ∧ Nonempty (adjointGroup .F4 K ≃* ↥L) := by
  classical
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hX := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hlie (by decide)
  obtain ⟨K, hKfield, hKfinite, hK, ⟨e0⟩⟩ := hX.2
  let : Field K := hKfield
  let : Finite K := hKfinite
  have hn : 1 ≤ f := hX.1.2.1
  have hK2 : Nat.card K = 2 ^ f := hK
  have hKchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hK2
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_F4 hq (w135_odd_card_center hctx) hn hK2 e0
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* adjointGroup .F4 K :=
    e0.trans (adjointQuotientEquiv .F4 K)
  let fn : ↥L →* adjointGroup .F4 K :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Bijective fn := by
    refine ⟨fun x y hxy => ?_, eS.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y :=
      eS.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  exact ⟨K, hKfield, hKfinite, hKchar, hn, hK2, ⟨(MulEquiv.ofBijective fn hf).symm⟩⟩

theorem w135c2_four_le_mQuot_f4_direct (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .F4 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  obtain ⟨K, hKfield, hKfinite, hKchar, hn, hK2, ⟨ι⟩⟩ := w135c2_f4_direct_data hctx hlie
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : CharP K 2 := hKchar
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hirr := w135c2_x1IsIrrOn_of_ctx hctx
  obtain ⟨δ, m, k, hkfield, hkfinite, hkchar, hAlg, ρ, hδ, hρ, hρinj, hfix⟩ :=
    w135c2_periodic_fix hW' hirr ι hn hK2
  let : Field k := hkfield
  let : Finite k := hkfinite
  let : CharP k 2 := hkchar
  let : Algebra K k := hAlg
  by_cases htL : t ∈ L
  ·
    let g : adjointGroup .F4 K := ι.symm ⟨t, htL⟩
    have hιg : ι g = ⟨t, htL⟩ := ι.apply_symm_apply _
    have hcoe : ((ι g : ↥L) : MulAut W) = t := by rw [hιg]
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      omega
    have h2 : (⟨t, htL⟩ : ↥L) ^ 2 = 1 := by
      refine Subtype.ext ?_
      simpa [Subgroup.coe_pow, ht2] using pow_orderOf_eq_one t
    have hg2 : g ^ 2 = 1 := by
      apply ι.injective
      rw [map_pow, hιg, map_one]
      exact h2
    have hg1 : g ≠ 1 := by
      intro h
      apply ht1
      rw [← hcoe, h, map_one]
      rfl
    obtain ⟨ψ, F, hF, hψ⟩ := exists_mulAut_eq_f4DescProd hg2 hg1
    let ρ' : Representation k (adjointGroup .F4 K) (Fin m → k) :=
      ρ.comp ψ.symm.toMonoidHom
    have hρ' : IsSimpleRep ρ' :=
      (isSimpleRep_comp_iff ρ (f := ψ.symm.toMonoidHom) ψ.symm.surjective).2 hρ
    have hinj' : Function.Injective ρ' := fun a b hab =>
      ψ.symm.injective (hρinj hab)
    have hframe : 4 ≤ Module.finrank k (LinearMap.range (ρ' (ψ g) - 1)) :=
      f4_four_le_finrank_frame hn hK2 hρ' hinj' hF (ψ g) hψ
    have hρ'g : ρ' (ψ g) = ρ g := by
      change ρ (ψ.symm (ψ g)) = ρ g
      exact congrArg ρ (ψ.symm_apply_apply g)
    have h4 : 4 ≤ δ * Module.finrank k (LinearMap.range (ρ g - 1)) := by
      have h := Nat.mul_le_mul hδ hframe
      rw [hρ'g] at h
      simpa using h
    rw [← hcoe, hfix g]
    exact h4
  ·
    obtain ⟨α, hα2, hαout, hbound⟩ :=
      w135c2_exists_outer_aut hW hctx ι htY ht2 htL
    obtain ⟨ψ, x, d₁, d₄, hψ⟩ := f4_exists_inv_mul_eq_frame hn hK2 α hα2 hαout
    let ρ' : Representation k (adjointGroup .F4 K) (Fin m → k) :=
      ρ.comp ψ.symm.toMonoidHom
    have hρ' : IsSimpleRep ρ' :=
      (isSimpleRep_comp_iff ρ (f := ψ.symm.toMonoidHom) ψ.symm.surjective).2 hρ
    have hinj' : Function.Injective ρ' := fun a b hab =>
      ψ.symm.injective (hρinj hab)
    let z0 : adjointGroup .F4 K := ψ ((α x)⁻¹ * x)
    have hframe : 7 ≤ Module.finrank k (LinearMap.range (ρ' z0 - 1)) :=
      f4_seven_le_finrank_outer_frame hn hK2 hρ' hinj' d₁ d₄ z0 hψ
    have hρ'z : ρ' z0 = ρ ((α x)⁻¹ * x) := by
      change ρ (ψ.symm (ψ ((α x)⁻¹ * x))) = ρ ((α x)⁻¹ * x)
      exact congrArg ρ (ψ.symm_apply_apply ((α x)⁻¹ * x))
    have hframe' : 7 ≤
        Module.finrank k (LinearMap.range (ρ ((α x)⁻¹ * x) - 1)) := by
      rw [← hρ'z]
      exact hframe
    have h7 : 7 ≤ δ * Module.finrank k
        (LinearMap.range (ρ ((α x)⁻¹ * x) - 1)) := by
      have h := Nat.mul_le_mul hδ hframe'
      simpa using h
    have hm := hbound x
    rw [hfix ((α x)⁻¹ * x)] at hm
    have h2 : 7 ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := le_trans h7 hm
    omega

end CFSG.LocalAnalysis.WeakClosure81
