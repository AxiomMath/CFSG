module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommEmbeddedTau
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Defs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Use

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem model3_center_eq_U (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hM : Model3Sub (Ytor φ i) (Vtor φ t i i) (Nat.card K)) :
    Vtor φ t i i ⊓ centralizer (Vtor φ t i i : Set G) = U φ i := by
  have hUV : U φ i ≤ Vtor φ t i i :=
    (RootStandard.V_inf_C hS.fc i hS.ne_bot hS.eq_bot).symm.le.trans inf_le_left
  have hVT : Vtor φ t i i ≤ Tplus φ t i := inf_le_left.trans hH.normal_M.1
  have hUC : U φ i ≤ centralizer (Vtor φ t i i : Set G) := by
    intro x hx
    rw [← hH.center_Tplus] at hx
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    rw [mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨v, hVT hv⟩)
  have hUZ : U φ i ≤ Vtor φ t i i ⊓ centralizer (Vtor φ t i i : Set G) := le_inf hUV hUC
  have hcard : Nat.card ↥(Vtor φ t i i ⊓ centralizer (Vtor φ t i i : Set G)) ≤
      Nat.card ↥(U φ i) := by
    rw [hM.card_center, RootAxisTwoCore.card_U φ i]
  exact (Subgroup.eq_of_le_of_card_ge hUZ hcard).symm

theorem model3_use_M_eq {K : Type} [Field K] [CharP K 2] :
    ((RootStandard.upperSL (1 : K) * (FullCenterWeyl.swapSL⁻¹ * RootStandard.upperSL (1 : K) *
      FullCenterWeyl.swapSL) : SL₂ K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    FullCenterWeyl.coe_swapSL]
  have e : ((RootStandard.upperSL (1 : K) : SL₂ K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 1; 0, 1] := rfl
  rw [e, Matrix.adjugate_fin_two_of]
  simp [Matrix.mul_fin_two, CharTwo.neg_eq, h2]

theorem model3_use_M_order {K : Type} [Field K] [CharP K 2] :
    (RootStandard.upperSL (1 : K) * (FullCenterWeyl.swapSL⁻¹ * RootStandard.upperSL (1 : K) *
      FullCenterWeyl.swapSL) : SL₂ K) ^ 3 = 1 ∧
    (RootStandard.upperSL (1 : K) * (FullCenterWeyl.swapSL⁻¹ * RootStandard.upperSL (1 : K) *
      FullCenterWeyl.swapSL) : SL₂ K) ≠ 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hM := model3_use_M_eq (K := K)
  constructor
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hM]
    rw [pow_succ, pow_succ, pow_one]
    simp [Matrix.mul_fin_two, h2, Matrix.one_fin_two]
  · intro h
    have := congrArg (fun A : SL₂ K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [hM] at this

theorem sixK_k4a_of_model3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hM : Model3Sub (Ytor φ i) (Vtor φ t i i) (Nat.card K)) : K4aConcl φ i := by
  intro x hx hxx
  obtain ⟨y, hy, hyx⟩ := hM.involution x hx hxx
  exact ⟨y, hy, by rwa [model3_center_eq_U hS hH hM] at hyx⟩

theorem sixEmb_e2_of_model3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (he1 : EmbE1Concl φ i) (hM : Model3Sub (Ytor φ i) (Vtor φ t i i) (Nat.card K)) :
    EmbGenConcl φ t i := by
  have hZ := model3_center_eq_U hS hH hM
  have hτY : embTau φ i ∈ Ytor φ i := RootStandard.S_le_Y (φ := φ) i he1
  have hnot : ¬ IsPGroup 2 ↥(U φ i ⊔
      (U φ i).map (MulAut.conj (embTau φ i)⁻¹).toMonoidHom) := by
    intro hP
    have haU : RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) ∈ U φ i := by
      rw [RootStandard.rootHom_apply, ← RootStandard.rootCoord_eq_rootSLHom]
      exact RootAxisTwoCore.coordG_mem φ i 1
    have hτ : RootStandard.rootHom φ i FullCenterWeyl.swapSL = embTau φ i :=
      sixEmb_e1_aux_coe φ i
    have hbU : (embTau φ i)⁻¹ * RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) *
        embTau φ i ∈ (U φ i).map (MulAut.conj (embTau φ i)⁻¹).toMonoidHom :=
      ⟨_, haU, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have hgA := Subgroup.mul_mem_sup haU hbU
    have hg : RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) *
        ((embTau φ i)⁻¹ * RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) *
          embTau φ i) =
        RootStandard.rootHom φ i (RootStandard.upperSL (1 : K) *
          (FullCenterWeyl.swapSL⁻¹ * RootStandard.upperSL (1 : K) * FullCenterWeyl.swapSL)) := by
      rw [map_mul, map_mul, map_mul, map_inv, hτ]
    obtain ⟨h3, h1⟩ := model3_use_M_order (K := K)
    set g := RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) *
        ((embTau φ i)⁻¹ * RootStandard.rootHom φ i (RootStandard.upperSL (1 : K)) *
          embTau φ i) with hgdef
    have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, h3, map_one]
    have hg1 : g ≠ 1 := by
      rw [hg]
      intro h
      exact h1 (RootStandard.rootHom_injective φ i (by rw [h, map_one]))
    obtain ⟨k, hk⟩ := hP ⟨g, hgA⟩
    have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf g ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg3) (orderOf_dvd_of_pow_eq_one hk')
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
    exact hg1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
  exact (hM.generation (embTau φ i) hτY (by rwa [hZ])).symm

end Use

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
