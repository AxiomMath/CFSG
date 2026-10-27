module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix (exists_eq_conj_statedSp)
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap spMap_injective spMap_surjective)

theorem isSpn_six_one_exists_eq_conj {X : Type} [Group X] (hX : IsSpn X 6 1) (α : MulAut X) :
    ∃ x : X, α = MulAut.conj x := by
  obtain ⟨-, K, instK, instFin, hK, ⟨e₀⟩⟩ := hX
  letI : Field K := instK
  letI : Finite K := instFin
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using hK
  let eK : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hK'
  let e₁ : ↥(StatedSp 3 K) ≃* ↥(StatedSp 3 (ZMod 2)) :=
    (MulEquiv.ofBijective (spMap (n := 3) eK.toRingHom)
      ⟨spMap_injective _, spMap_surjective eK⟩).symm
  let e : X ≃* ↥(StatedSp 3 (ZMod 2)) := e₀.trans e₁
  obtain ⟨g, hg⟩ := exists_eq_conj_statedSp ((e.symm.trans α).trans e)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h := congrArg (fun γ : MulAut ↥(StatedSp 3 (ZMod 2)) => γ (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private lemma coe_trans_subgroupCongr {G : Type*} [Group G] {H K : Subgroup G}
    (f : G →* G) (hf : Function.Injective f) (h : H.map f = K) (x : H) :
    (((H.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr h)) x : G) = f x := by
  simp only [MulEquiv.trans_apply, Subgroup.coe_equivMapOfInjective_apply,
    MulEquiv.subgroupCongr_apply]

theorem c8_eq_of_map_conj_eq {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hC : RSp6SpinCent) {H M : Subgroup (MulAut W)} (hH : IsSpn ↥H 6 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 8) (hirr : IsIrrOn H ⊤ ⊥) (hHM : H ≤ M)
    (hN : ∀ φ ∈ M, H.map (MulAut.conj φ).toMonoidHom = H) : M = H := by
  refine le_antisymm ?_ hHM
  intro φ hφ
  let f : MulAut W →* MulAut W := (MulAut.conj φ).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj φ).injective
  have hf_apply : ∀ x : MulAut W, f x = φ * x * φ⁻¹ := by
    intro x
    dsimp only [f]
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  set α : MulAut ↥H :=
    (H.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hN φ hφ)) with hα
  obtain ⟨ℓ, hℓ⟩ := isSpn_six_one_exists_eq_conj hH α
  have hcoe : ∀ x : ↥H, ((α x : ↥H) : MulAut W) = φ * (x : MulAut W) * φ⁻¹ := by
    intro x
    rw [hα, coe_trans_subgroupCongr f hf (hN φ hφ) x, hf_apply]
  have hconj : ∀ x : ↥H,
      φ * (x : MulAut W) * φ⁻¹ = (ℓ : MulAut W) * (x : MulAut W) * (ℓ : MulAut W)⁻¹ := by
    intro x
    have h := congrArg (fun γ : ↥H => ((γ : MulAut W))) (MulEquiv.congr_fun hℓ x)
    rw [hcoe x] at h
    simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
  set c : MulAut W := (ℓ : MulAut W)⁻¹ * φ with hc
  have hcomm : ∀ x ∈ H, c * x = x * c := by
    intro x hx
    have h := hconj ⟨x, hx⟩
    simp only [Subgroup.coe_mk] at h
    calc c * x = (ℓ : MulAut W)⁻¹ * (φ * x * φ⁻¹) * φ := by rw [hc]; group
      _ = x * c := by rw [h, hc]; group
  have hc1 : c = 1 := hC W hW H hH hrk hirr c hcomm
  have hφℓ : φ = (ℓ : MulAut W) := by
    have h1 : (ℓ : MulAut W)⁻¹ * φ = 1 := by rw [← hc1, hc]
    exact (inv_mul_eq_one.mp h1).symm
  rw [hφℓ]
  exact ℓ.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
