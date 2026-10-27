module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaElementary
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour

public section

open scoped Matrix commutatorElement
open QuadraticMap

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

theorem kf9_exists_ne_zero_ne_one (K : Type) [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun b : Bool => cond b (1 : K) 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [h x hx]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have hB : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  omega

theorem kf9_commutator_quadPlus (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 2 K),
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 2 K)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup
        (CFSG.LieType.Universal.Spin.quadPlus 2 K) := by
  obtain ⟨c, hc0, hc1⟩ := kf9_exists_ne_zero_ne_one K h4
  exact CFSG.RankThree.GF2n.Stroth80.Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1

theorem kf9_commSpace_toLinEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (A : GL ι K) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) =
      LinearMap.range (Matrix.mulVecLin ((A : Matrix ι ι K) - 1)) := by
  show LinearMap.range ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A :
    (ι → K) →ₗ[K] (ι → K)) - 1) = _
  congr 1
  apply LinearMap.ext
  intro v
  simp [Matrix.sub_mulVec]

theorem kf9_dickson_of_form {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)} {f : (ι → K) → K} (hf : ⇑Q = f)
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Fintype.card ι)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q) :
    DicksonNatFor K f := by
  subst hf
  intro A hA _
  rw [CFSG.ClassicalGroups.Orthogonal.mem_statedOmega_iff_mem_elementaryGroup rfl hE]
  have hdim : 4 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact h4
  have hO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
      exact hA v
  have hiff : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q ↔
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    ⟨fun h => CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup hQ h,
      fun h => CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le hQ hdim h⟩
  rw [hiff, CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup, and_iff_right hO,
    kf9_commSpace_toLinEquiv]
  rfl

theorem dicksonNat_holds : DicksonNatStatement := by
  unfold DicksonNatStatement ForBothSigns
  intro K _ _ _ h4K
  refine ⟨kf9_dickson_of_form (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K)
    (by simp) (kf9_commutator_quadPlus K h4K), fun b c hirr =>
    kf9_dickson_of_form (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (by simp) (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
        le_rfl hirr)⟩

@[expose] def kf9Quad {K : Type} [Field K] (S : QSpace K) : QuadraticForm K S.E where
  toFun := S.Qf
  toFun_smul := fun a x => by simp only [S.Qf_smul, smul_eq_mul]; ring
  exists_companion' := ⟨S.B, S.Qf_add⟩

theorem kf9Quad_apply {K : Type} [Field K] (S : QSpace K) (x : S.E) :
    kf9Quad S x = S.Qf x :=
  rfl

theorem dicksonSpace_holds : DicksonSpaceStatement := by
  unfold DicksonSpaceStatement
  intro K _ _ _ h4K S h8 _ V hV hV4
  have hB : polarBilin (kf9Quad S) = S.B := by
    ext x y
    rw [polarBilin_apply_apply]
    simp only [QuadraticMap.polar, kf9Quad_apply]
    rw [S.Qf_add]
    ring
  have hQ : (polarBilin (kf9Quad S)).Nondegenerate := by
    rw [hB]
    exact KFLin.B_nondegenerate S
  have h4 : 4 ≤ Module.finrank K S.E := by omega
  have hE :=
    CFSG.RankThree.GF2n.Stroth80.Classify.commutator_orthogonalGroup_eq_elementaryGroup_of_plusTwo
      (fun K _ _ _ h => kf9_commutator_quadPlus K h) (kf9Quad S) h4K hQ h4
  have hO : S.O = TauCeti.QuadraticMap.orthogonalGroup (kf9Quad S) := by
    ext g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    simp only [kf9Quad_apply]
    exact Iff.rfl
  have hΩ : S.Ω = CFSG.ClassicalGroups.Orthogonal.elementaryGroup (kf9Quad S) := by
    rw [← hE]
    show ⁅S.O, S.O⁆ = _
    rw [hO]
  have hU : ∀ x ∈ V, kf9Quad S x = 0 := fun x hx => by
    rw [kf9Quad_apply]
    exact hV x hx
  have hUdim : 2 * Module.finrank K V = Module.finrank K S.E := by omega
  have hVle : ∀ g : S.E ≃ₗ[K] S.E, (∀ v, v ∈ V ↔ g v ∈ V) →
      V ≤ V.map (g : S.E →ₗ[K] S.E) := by
    intro g hg v hv
    have hw : g.symm v ∈ V :=
      (hg (g.symm v)).mpr (by rw [LinearEquiv.apply_symm_apply]; exact hv)
    exact ⟨g.symm v, hw, LinearEquiv.apply_symm_apply g v⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hgO, hgV⟩ := hg
    rw [hΩ]
    have hgQ : g ∈ TauCeti.QuadraticMap.orthogonalGroup (kf9Quad S) := by
      rw [← hO]
      exact hgO
    have hker := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_sub_finrank_inf_map
      hQ hU hUdim hgQ
    rw [inf_eq_left.mpr (hVle g hgV), Nat.sub_self, Nat.cast_zero] at hker
    apply CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le hQ h4
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
    exact ⟨hgQ, ZMod.natCast_eq_zero_iff_even.mp hker.symm⟩
  · rw [hΩ] at hg
    have hgΩ := CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup hQ hg
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hgΩ
    have hker := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_sub_finrank_inf_map
      hQ hU hUdim hgΩ.1
    have h0 : ((Module.finrank K V - Module.finrank K ↥(V ⊓ V.map (g : S.E →ₗ[K] S.E)) : ℕ) :
        ZMod 2) = 0 := by
      rw [hker]
      exact ZMod.natCast_eq_zero_iff_even.mpr hgΩ.2
    have hev := ZMod.natCast_eq_zero_iff_even.mp h0
    have hle : Module.finrank K ↥(V ⊓ V.map (g : S.E →ₗ[K] S.E)) ≤ Module.finrank K V :=
      Submodule.finrank_mono inf_le_left
    rw [Nat.even_iff] at hev ⊢
    omega

end CFSG.RankThree.GF2n.Smith81.Smith23E1
