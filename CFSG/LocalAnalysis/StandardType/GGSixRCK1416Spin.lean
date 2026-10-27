module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.ClassicalGroups.Orthogonal.EichlerCentralizerScalar
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rck1416_gf2_eq_zero_or_one (a : GaloisField 2 1) : a = 0 ∨ a = 1 := by
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 one_ne_zero
  have hcard' : Fintype.card (GaloisField 2 1) = 2 := by
    rwa [← Nat.card_eq_fintype_card]
  by_contra hc
  push Not at hc
  have h3 : ({0, 1, a} : Finset (GaloisField 2 1)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hc.2
    · simpa using Ne.symm hc.1
  have hle := Finset.card_le_univ ({0, 1, a} : Finset (GaloisField 2 1))
  rw [hcard'] at hle
  omega

private theorem center_spinGroup_eq_bot_of_spinAction {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hrange : (Spin.spinAction Q).range =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (hinj : Function.Injective (Spin.spinAction Q))
    (P : CFSG.ClassicalGroups.Orthogonal.HypPair Q) {w : V}
    (hwP : w ∈ P.perp) (hQw : Q w ≠ 0) (hF : ∀ a : K, a = 0 ∨ a = 1) :
    Subgroup.center (spinGroup Q) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  let Y : V →+ V := ((Spin.spinAction Q c : V →ₗ[K] V)).toAddMonoidHom
  have he : ∀ w' ∈ P.perp, ∀ x,
      Y (CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' x) =
        CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' (Y x) := by
    intro w' hw' x
    obtain ⟨s, hs⟩ : ∃ s : spinGroup Q, Spin.spinAction Q s =
        CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' := by
      change CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' ∈ (Spin.spinAction Q).range
      rw [hrange]
      exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup Q P.e w'
    have hcs : c * s = s * c := (Subgroup.mem_center_iff.mp hc s).symm
    calc Y (CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' x)
        = Spin.spinAction Q c (CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' x) := rfl
      _ = Spin.spinAction Q c (Spin.spinAction Q s x) := by rw [hs]
      _ = Spin.spinAction Q (c * s) x := by rw [map_mul]; rfl
      _ = Spin.spinAction Q (s * c) x := by rw [hcs]
      _ = Spin.spinAction Q s (Spin.spinAction Q c x) := by rw [map_mul]; rfl
      _ = CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' (Spin.spinAction Q c x) := by
            rw [hs]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler Q P.e w' (Y x) := rfl
  have hf : ∀ w' ∈ P.perp, ∀ x,
      Y (CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' x) =
        CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' (Y x) := by
    intro w' hw' x
    obtain ⟨s, hs⟩ : ∃ s : spinGroup Q, Spin.spinAction Q s =
        CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' := by
      change CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' ∈ (Spin.spinAction Q).range
      rw [hrange]
      exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup Q P.f w'
    have hcs : c * s = s * c := (Subgroup.mem_center_iff.mp hc s).symm
    calc Y (CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' x)
        = Spin.spinAction Q c (CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' x) := rfl
      _ = Spin.spinAction Q c (Spin.spinAction Q s x) := by rw [hs]
      _ = Spin.spinAction Q (c * s) x := by rw [map_mul]; rfl
      _ = Spin.spinAction Q (s * c) x := by rw [hcs]
      _ = Spin.spinAction Q s (Spin.spinAction Q c x) := by rw [map_mul]; rfl
      _ = CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' (Spin.spinAction Q c x) := by
            rw [hs]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler Q P.f w' (Y x) := rfl
  obtain ⟨μ, hμ⟩ := CFSG.ClassicalGroups.Orthogonal.exists_eq_smul_of_commute_eichler
    hQ P ⟨w, hwP, hQw⟩ Y he hf
  have hsq : μ * μ = 1 := by
    have h := Spin.map_spinAction Q c w
    rw [show Spin.spinAction Q c w = Y w from rfl, hμ w,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq] at h
    refine mul_right_cancel₀ hQw ?_
    calc μ * μ * Q w = μ ^ 2 * Q w := by rw [pow_two]
      _ = 1 * Q w := by rw [h, one_mul]
  have hμ1 : μ = 1 := by
    rcases hF μ with h0 | h1
    · rw [h0, zero_mul] at hsq
      exact absurd hsq zero_ne_one
    · exact h1
  have hYeq : Spin.spinAction Q c = 1 := by
    refine LinearEquiv.ext fun x => ?_
    rw [show Spin.spinAction Q c x = Y x from rfl, hμ x, hμ1, one_smul]
    rfl
  exact hinj (by rw [hYeq, map_one])

theorem rck1416_quadPlus_facts {n : ℕ} (hn : 3 ≤ n) :
    (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 1))).Nondegenerate ∧
      Function.Injective (Spin.spinAction (Spin.quadPlus n (GaloisField 2 1))) ∧
      (Spin.spinAction (Spin.quadPlus n (GaloisField 2 1))).range =
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadPlus n (GaloisField 2 1)) ∧
      Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 1))) = ⊥ ∧
      Module.finrank (GaloisField 2 1) (Fin n ⊕ Fin n → GaloisField 2 1) = 2 * n := by
  have hnd : (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 1))).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (n := n) (K := GaloisField 2 1)
  have hrange : (Spin.spinAction (Spin.quadPlus n (GaloisField 2 1))).range =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadPlus n (GaloisField 2 1)) :=
    Spin.range_spinAction_quadPlus (n := n) (K := GaloisField 2 1) hn
  have hinj : Function.Injective (Spin.spinAction (Spin.quadPlus n (GaloisField 2 1))) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Spin.ker_spinMatrix]
    exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharTwo.two_eq_zero)
  have hcenter : Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 1))) = ⊥ := by
    let P : CFSG.ClassicalGroups.Orthogonal.HypPair
        (Spin.quadPlus n (GaloisField 2 1)) :=
      CFSG.ClassicalGroups.Orthogonal.plusPair (GaloisField 2 1) ⟨0, by omega⟩
    let P₁ : CFSG.ClassicalGroups.Orthogonal.HypPair
        (Spin.quadPlus n (GaloisField 2 1)) :=
      CFSG.ClassicalGroups.Orthogonal.plusPair (GaloisField 2 1) ⟨1, by omega⟩
    let w : Fin n ⊕ Fin n → GaloisField 2 1 := P₁.e + P₁.f
    have horth : P.Orth P₁ :=
      CFSG.ClassicalGroups.Orthogonal.plusPair_orth (by simp [Fin.ext_iff])
    have hwP : w ∈ P.perp := by
      dsimp only [w]
      rw [CFSG.ClassicalGroups.Orthogonal.HypPair.mem_perp]
      constructor
      · rw [QuadraticMap.polar_add_right, horth.ee, horth.ef, add_zero]
      · rw [QuadraticMap.polar_add_right, horth.fe, horth.ff, add_zero]
    have hQw : Spin.quadPlus n (GaloisField 2 1) w ≠ 0 := by
      have h1 : Spin.quadPlus n (GaloisField 2 1) w = 1 := by
        dsimp only [w]
        rw [QuadraticMap.map_add (Spin.quadPlus n (GaloisField 2 1)), P₁.Q_e, P₁.Q_f,
          P₁.polar_ef]
        norm_num
      rw [h1]
      exact one_ne_zero
    exact center_spinGroup_eq_bot_of_spinAction hnd hrange hinj P hwP hQw
      rck1416_gf2_eq_zero_or_one
  have hfin : Module.finrank (GaloisField 2 1)
      (Fin n ⊕ Fin n → GaloisField 2 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  exact ⟨hnd, hinj, hrange, hcenter, hfin⟩

theorem rck1416_quadMinus_facts {n : ℕ} (hn : 3 ≤ n) :
    (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
        (minusCoeffs 2 1).2)).Nondegenerate ∧
      Function.Injective (Spin.spinAction (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) ∧
      (Spin.spinAction (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
        (minusCoeffs 2 1).2)).range =
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadMinus n (GaloisField 2 1)
          (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) ∧
      Subgroup.center (spinGroup (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
        (minusCoeffs 2 1).2)) = ⊥ ∧
      Module.finrank (GaloisField 2 1) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1) =
        2 * n := by
  have hnd : (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := n) (K := GaloisField 2 1)
      (minusCoeffs_irr 2 1)
  have hV : 5 ≤ Module.finrank (GaloisField 2 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1) := by
    have hfr : Module.finrank (GaloisField 2 1)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1) = 2 * n := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hfr]
    omega
  have horth : (CFSG.ClassicalGroups.Orthogonal.minusPair (n := n) (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 ⟨0, by omega⟩).Orth
      (CFSG.ClassicalGroups.Orthogonal.minusPair (n := n) (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 ⟨1, by omega⟩) :=
    CFSG.ClassicalGroups.Orthogonal.minusPair_orth (by simp [Fin.ext_iff])
  have hrange : (Spin.spinAction (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)).range =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) :=
    Spin.range_spinAction_eq_elementaryGroup hnd hV horth
  have hinj : Function.Injective (Spin.spinAction (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Spin.ker_spinMatrix]
    exact Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 1) CharTwo.two_eq_zero
  have hcenter : Subgroup.center (spinGroup (Spin.quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) = ⊥ := by
    let P : CFSG.ClassicalGroups.Orthogonal.HypPair (Spin.quadMinus n (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) :=
      CFSG.ClassicalGroups.Orthogonal.minusPair (GaloisField 2 1)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 ⟨0, by omega⟩
    let w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1 :=
      Pi.single (Sum.inr (Sum.inr 0)) 1
    have hwP : w ∈ P.perp := by
      dsimp only [P, w]
      rw [CFSG.ClassicalGroups.Orthogonal.HypPair.mem_perp,
        CFSG.ClassicalGroups.Orthogonal.minusPair_e,
        CFSG.ClassicalGroups.Orthogonal.minusPair_f]
      constructor
      · rw [QuadraticMap.polar_comm, Spin.polar_quadMinus_single_inl]
        simp
      · rw [QuadraticMap.polar_comm, Spin.polar_quadMinus_single_inr_inl]
        simp
    have hQw : Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
        (minusCoeffs 2 1).2 w ≠ 0 := by
      have h1 : Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
          (minusCoeffs 2 1).2 w = 1 := by
        dsimp only [w]
        rw [Spin.quadMinus_apply]
        simp
      rw [h1]
      exact one_ne_zero
    exact center_spinGroup_eq_bot_of_spinAction hnd hrange hinj P hwP hQw
      rck1416_gf2_eq_zero_or_one
  have hfin : Module.finrank (GaloisField 2 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact ⟨hnd, hinj, hrange, hcenter, hfin⟩

end CFSG.StandardType.RCKC1
