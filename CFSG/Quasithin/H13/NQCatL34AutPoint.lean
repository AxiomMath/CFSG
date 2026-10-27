module

public import CFSG.Quasithin.H13.NQCatL34AutModel
public import CFSG.Quasithin.Recognition.HSTypeFactAut
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers

public section

namespace CFSG.Quasithin.H13.NQCat.L34Aut

open MulAction Module CFSG.Fischer CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)

section Dim

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem finrank_eq_of_natCard_eq {W W' : Submodule K (Fin n → K)}
    (h : Nat.card W = Nat.card W') : finrank K W = finrank K W' := by
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := ↥W')
  rw [h1, h2] at h
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) h

theorem finrank_map_mulVecLin_gl (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    finrank K (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) = finrank K W := by
  refine finrank_eq_of_natCard_eq ?_
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) := fun v w h => by
    have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) h
    simpa [mulVec_mulVec] using h1
  have e : Nat.card ↥(W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) =
      Nat.card ↑((mulVecLin (A : Matrix (Fin n) (Fin n) K)) '' (W : Set (Fin n → K))) := by
    rw [← Submodule.map_coe]
    rfl
  rw [e, Nat.card_image_of_injective hinj]
  rfl

theorem finrank_coordImage (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    finrank K (coordImage σ W) = finrank K W := by
  refine finrank_eq_of_natCard_eq (Nat.card_congr
    { toFun := fun v => ⟨fun i => σ.symm ((v : Fin n → K) i), v.2⟩
      invFun := fun w => ⟨fun i => σ ((w : Fin n → K) i), coord_mem_coordImage w.2⟩
      left_inv := fun v => Subtype.ext (by funext i; simp)
      right_inv := fun w => Subtype.ext (by funext i; simp) })

end Dim

section Transport

variable {n : ℕ} {K : Type*} [Field K]

theorem map_projStabilizer_conjAut (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (conjAut n K A).toMonoidHom =
      projStabilizer (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) :=
  (standard_automorphism_transport (n := n) (K := K)).2.2.2.2.2.2.1 A W

theorem map_projStabilizer_fieldAut (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (fieldAut n K σ).toMonoidHom = projStabilizer (coordImage σ W) :=
  (standard_automorphism_transport (n := n) (K := K)).2.2.2.2.2.2.2.1 σ W

theorem map_projStabilizer_dualAut (W : Submodule K (Fin n → K)) :
    (projStabilizer W).map (dualAut n K).toMonoidHom = projStabilizer (dotOrth W) :=
  (standard_automorphism_transport (n := n) (K := K)).2.2.2.2.2.2.2.2.1 W

theorem map_mul_toMonoidHom' {G : Type*} [Group G] (X : Subgroup G) (e f : MulAut G) :
    X.map (e * f).toMonoidHom = (X.map f.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

end Transport

section Model

variable {k : Type} [Field k] [Finite k]

theorem eq_of_projStabilizer_eq [CharP k 2] {W W' : Submodule k (Fin 3 → k)}
    (hW : 1 ≤ finrank k W ∧ finrank k W < 3) (hW' : 1 ≤ finrank k W' ∧ finrank k W' < 3)
    (h : projStabilizer W = projStabilizer W') : W = W' :=
  (maximal_parabolics (K := k) 2 (by norm_num)).2.1 (bot_lt_and_lt_top_of_finrank hW.1 hW.2)
    (bot_lt_and_lt_top_of_finrank hW'.1 hW'.2) h

theorem pointStab_aut_cases (hk : Nat.card k = 4) {L : Submodule k (Fin 3 → k)}
    (hL : finrank k L = 1) {β : MulAut (projectiveSL 3 k)} (hβ : β * β = 1)
    (hβL : (projStabilizer L).map β.toMonoidHom = projStabilizer L) :
    (∃ d ∈ projStabilizer L, β = MulAut.conj d) ∨
      ∃ w : projectiveSL 3 k, orderOf w = 7 ∧ β w = w := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have hL' : ∀ H : GL (Fin 3) k, finrank k (L.map (mulVecLin (H : Matrix (Fin 3) (Fin 3) k))) = 1 :=
    fun H => (finrank_map_mulVecLin_gl H L).trans hL
  rcases involution_cases_card hk hσ hβ with ⟨d, rfl⟩ | ⟨⟨H, rfl⟩, hcard⟩ | ⟨⟨H, rfl⟩, -⟩ |
    ⟨⟨H, rfl⟩, -⟩
  ·
    left
    refine ⟨d, ?_, rfl⟩
    obtain ⟨A, rfl⟩ := proj_surjective 3 k d
    rw [map_conj_projStabilizer] at hβL
    have hdim : finrank k (L.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) k))) = 1 :=
      hL' (SpecialLinearGroup.toGL A)
    exact proj_mem_projStabilizer_iff.2 (mem_stabilizer.2
      (eq_of_projStabilizer_eq ⟨hdim.ge, by omega⟩ ⟨hL.ge, by omega⟩ hβL))
  ·
    right
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autFixed (conjAut 3 k H *
      fieldAut 3 k (frobeniusEquiv k 2) * (conjAut 3 k H)⁻¹))) 7 (by rw [hcard]; norm_num)
    exact ⟨w, by rw [← Subgroup.orderOf_coe] at hw; exact hw, mem_autFixed.1 w.2⟩
  ·
    exfalso
    rw [map_mul_toMonoidHom', map_mul_toMonoidHom', ← map_inv, map_projStabilizer_conjAut,
      map_projStabilizer_dualAut, map_projStabilizer_conjAut] at hβL
    have h1 := eq_of_projStabilizer_eq ?_ ⟨hL.ge, by omega⟩ hβL
    · have h2 := congrArg (fun W : Submodule k (Fin 3 → k) => finrank k W) h1
      rw [finrank_map_mulVecLin_gl, finrank_dotOrth, hL' H⁻¹, hL] at h2
      omega
    · rw [finrank_map_mulVecLin_gl, finrank_dotOrth, hL' H⁻¹]
      omega
  ·
    exfalso
    rw [betaAut, map_mul_toMonoidHom', map_mul_toMonoidHom', ← map_inv, map_projStabilizer_conjAut,
      map_mul_toMonoidHom', map_projStabilizer_dualAut, map_projStabilizer_fieldAut,
      map_projStabilizer_conjAut] at hβL
    have h1 := eq_of_projStabilizer_eq ?_ ⟨hL.ge, by omega⟩ hβL
    · have h2 := congrArg (fun W : Submodule k (Fin 3 → k) => finrank k W) h1
      rw [finrank_map_mulVecLin_gl, finrank_coordImage, finrank_dotOrth, hL' H⁻¹, hL] at h2
      omega
    · rw [finrank_map_mulVecLin_gl, finrank_coordImage, finrank_dotOrth, hL' H⁻¹]
      omega

end Model

theorem factAutL34_holds :
    HSType.FactAutL34 := by
  intro β hβ hβP
  obtain ⟨Ψ, hΨ1, -⟩ := exists_m22Zero_equiv
  have hβs : ∀ x, β.symm x = β x := fun x => by
    rw [MulEquiv.symm_apply_eq, hβ]
  set β' : MulAut (projectiveSL 3 F4) := Ψ.symm.trans (β.trans Ψ) with hβ'def
  have hβ'apply : ∀ y, β' y = Ψ (β (Ψ.symm y)) := fun y => rfl
  have hβ'2 : β' * β' = 1 := by
    ext y
    rw [MulAut.mul_apply, hβ'apply, hβ'apply, MulEquiv.symm_apply_apply, hβ,
      MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hβ'L : (projStabilizer (flagSpace 3 F4 1)).map β'.toMonoidHom =
      projStabilizer (flagSpace 3 F4 1) := by
    ext y
    rw [Subgroup.mem_map_equiv]
    have h1 : β'.symm y = Ψ (β (Ψ.symm y)) := by
      change Ψ (β.symm (Ψ.symm y)) = _
      rw [hβs]
    rw [h1, ← hΨ1, ← hβP, hΨ1, MulEquiv.apply_symm_apply]
  have hF1 : finrank F4 (flagSpace 3 F4 1) = 1 := finrank_flagSpace (by norm_num)
  have hcard : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  rcases pointStab_aut_cases hcard hF1 hβ'2 hβ'L with ⟨d, hd, hdβ⟩ | ⟨w, hw7, hwβ⟩
  · left
    refine ⟨Ψ.symm d, (hΨ1 _).2 (by rw [MulEquiv.apply_symm_apply]; exact hd), fun x => ?_⟩
    apply Ψ.injective
    have h1 : β' (Ψ x) = d * Ψ x * d⁻¹ := by rw [hdβ]; rfl
    rw [hβ'apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · right
    refine ⟨Ψ.symm w, by rw [MulEquiv.orderOf_eq]; exact hw7, ?_⟩
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply]
    exact (hβ'apply w).symm.trans hwβ

end CFSG.Quasithin.H13.NQCat.L34Aut
