module


public import CFSG.RankThree.GF2n.Stroth80.Sec714NotTwelve
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Open
open CFSG.GroupTheory.WeirSylow
open scoped commutatorElement

theorem nondegenerate_polarBilin_of_model {H : Type} [Group H] {QF V : Subgroup H} {K : Type}
    [Field K] {γ : H → K} (M₀ : Tim79.QuadModel QF V K γ) :
    LinearMap.Nondegenerate (QuadraticMap.polarBilin M₀.toQuadraticForm) := by
  have hanti : ∀ a b, M₀.B a b = - M₀.B b a := fun a b => by
    have h := M₀.alt (a + b)
    simp only [map_add, LinearMap.add_apply, M₀.alt] at h
    linear_combination h
  refine ⟨fun x hx => M₀.nondeg x (fun f => ?_), fun y hy => M₀.nondeg y (fun f => ?_)⟩
  · have h := hx f
    simpa [QuadraticMap.polarBilin_apply_apply, Tim79.QuadModel.polar_toQuadraticForm] using h
  · have h := hy f
    simp only [QuadraticMap.polarBilin_apply_apply, Tim79.QuadModel.polar_toQuadraticForm] at h
    rw [hanti, h, neg_zero]

@[expose] def DicksonOmegaPlusFourStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (hQ : LinearMap.Nondegenerate (QuadraticMap.polarBilin (quadPlus 4 K))),
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus 4 K) hQ ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆


theorem quadraticPlusType_of_dickson (hD : DicksonOmegaPlusFourStatement) :
    QuadraticPlusTypeStatement := by
  intro H _ K _ _ QF V γ M₀ Γ hchar hfin hΓO hΓiso
  haveI := hchar
  have hQ := nondegenerate_polarBilin_of_model M₀
  have hdim : Module.finrank K M₀.E = 2 * 4 := hfin
  rcases exists_isometry_quadPlus_or_quadMinus M₀.toQuadraticForm hQ (by norm_num) hdim with
    hplus | ⟨b, c, hirr, hminus⟩
  · obtain ⟨e⟩ := hplus
    exact ⟨e.toLinearEquiv, fun v => e.map_app v⟩
  · exfalso
    obtain ⟨e⟩ := hminus
    have he : ∀ v, quadMinus 4 K b c (e.toLinearEquiv v) = M₀.toQuadraticForm v :=
      fun v => e.map_app v
    have hmap := map_orthogonalGroup_stroth714Conj M₀.toQuadraticForm (quadMinus 4 K b c)
      e.toLinearEquiv he
    have hsub : Γ.map (stroth714ConjEquiv e.toLinearEquiv).toMonoidHom ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
      rw [← hmap]
      exact Subgroup.map_mono hΓO
    have hdvd := Subgroup.card_dvd_of_le hsub
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _)] at hdvd
    obtain ⟨φ0⟩ := hΓiso
    have hcardΓ : Nat.card Γ = Nat.card (StatedOmega (StatedQuadPlus 4 K)) :=
      Nat.card_congr φ0.toEquiv
    have hcardSO := natCard_statedOmega_eq_omega 4 (StatedQuadPlus 4 K) (coe_quadPlus 4 K)
    rw [commutator_orthogonalGroup_quadPlus (by norm_num : 3 ≤ 4)] at hcardSO
    have hQ4 := nondegenerate_polarBilin_quadPlus 4 K
    have hΩE : CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus 4 K) hQ4 =
        elementaryGroup (quadPlus 4 K) :=
      le_antisymm ((hD K hQ4).trans (commutator_orthogonalGroup_quadPlus (by norm_num)).le)
        (elementaryGroup_le_omegaGroup hQ4)
    rw [← hΩE] at hcardSO
    have hidx := Subgroup.relIndex_mul_card
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadPlus 4 K) hQ4)
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))
    rw [inf_eq_left.mpr (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le _ hQ4),
      CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hQ4] at hidx
    have hOp : ((Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) : ℕ) : ℤ) =
        2 * (Nat.card K : ℤ) ^ 12 * ((Nat.card K : ℤ) ^ 4 - 1) *
          ∏ i ∈ Finset.Icc 1 3, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
      natCard_orthogonalGroup_quadPlus (K := K) 3
    have hOm : ((Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) : ℕ) : ℤ) =
        2 * (Nat.card K : ℤ) ^ 12 * ((Nat.card K : ℤ) ^ 4 + 1) *
          ∏ i ∈ Finset.Icc 1 3, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
      natCard_orthogonalGroup_quadMinus (K := K) hirr 3
    have hidxZ : (2 : ℤ) * (Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadPlus 4 K) hQ4) : ℤ) =
        (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) : ℤ) := by
      exact_mod_cast hidx
    have hΓΩ : Nat.card Γ = Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadPlus 4 K) hQ4) := hcardΓ.trans hcardSO
    have hdvdZ : (Nat.card ↥Γ : ℤ) ∣
        (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdvd
    set q : ℤ := (Nat.card K : ℤ) with hq
    have hq2 : (2 : ℤ) ≤ q := by
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2 : 2 ≤ Nat.card K := h1
      rw [hq]
      exact_mod_cast h2
    set P : ℤ := ∏ i ∈ Finset.Icc 1 3, ((q ^ 2) ^ i - 1) with hP
    have hPpos : 0 < P := by
      apply Finset.prod_pos
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have h4 : (4 : ℤ) ≤ q ^ 2 := by nlinarith
      have h5 : q ^ 2 ≤ (q ^ 2) ^ i := le_self_pow₀ (by linarith) (by omega)
      linarith
    have h2X : (2 : ℤ) * (Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadPlus 4 K) hQ4) : ℤ) = 2 * (q ^ 12 * (q ^ 4 - 1) * P) := by
      rw [hidxZ, hOp]
      ring
    have hX : (Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadPlus 4 K) hQ4) : ℤ) = q ^ 12 * (q ^ 4 - 1) * P :=
      mul_left_cancel₀ two_ne_zero h2X
    have hΓZ : (Nat.card ↥Γ : ℤ) = q ^ 12 * (q ^ 4 - 1) * P := by
      rw [show (Nat.card ↥Γ : ℤ) = (Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadPlus 4 K) hQ4) : ℤ) by exact_mod_cast hΓΩ, hX]
    rw [hΓZ, hOm] at hdvdZ
    have hne : q ^ 12 * P ≠ 0 := (mul_pos (pow_pos (by linarith) 12) hPpos).ne'
    have hdiv : (q ^ 12 * P) * (q ^ 4 - 1) ∣ (q ^ 12 * P) * (2 * (q ^ 4 + 1)) := by
      have e1 : q ^ 12 * (q ^ 4 - 1) * P = (q ^ 12 * P) * (q ^ 4 - 1) := by ring
      have e2 : 2 * q ^ 12 * (q ^ 4 + 1) * P = (q ^ 12 * P) * (2 * (q ^ 4 + 1)) := by ring
      rw [e1, e2] at hdvdZ
      exact hdvdZ
    have hdiv' := (mul_dvd_mul_iff_left hne).mp hdiv
    have h4 : (q ^ 4 - 1) ∣ 4 := by
      have h := dvd_sub hdiv' (dvd_mul_left (q ^ 4 - 1) 2)
      have e : 2 * (q ^ 4 + 1) - 2 * (q ^ 4 - 1) = 4 := by ring
      rwa [e] at h
    have hle : q ^ 4 - 1 ≤ 4 := Int.le_of_dvd (by norm_num) h4
    have hq4' : (4 : ℤ) ≤ q ^ 2 := by nlinarith
    have h16 : (16 : ℤ) ≤ q ^ 4 := by
      have e4 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
      have hm : (4 : ℤ) * 4 ≤ q ^ 2 * q ^ 2 := mul_le_mul hq4' hq4' (by norm_num) (by linarith)
      rw [e4]
      linarith
    linarith

end CFSG.RankThree.GF2n.Stroth80
