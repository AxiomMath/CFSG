module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent

public section

namespace CFSG.LocalAnalysis

namespace SymplecticFourOuterSquare

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique
open scoped commutatorElement

theorem map_residual {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    (Setup.X7b.residual H).map e.toMonoidHom = Setup.X7b.residual H' := by
  ext x
  simp only [Setup.X7b.residual, Subgroup.mem_map, Subgroup.mem_iInf]
  constructor
  · rintro ⟨y, hy, rfl⟩ k
    rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective k]
    exact ⟨y, hy k, rfl⟩
  · intro hx
    refine ⟨e.symm x, fun k => ?_, by simp⟩
    have := hx k
    rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective k] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : y = e.symm x := by rw [← hyx]; simp
    rwa [← this]

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem minorAut_w : minorAut K (uElt 1 1 1 1) = uElt 1 1 1 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply antiSp_ext
  rw [glMat_minorAut, glMat_uElt, minorMap_uMat]
  congr 1 <;> first | ring1 | linear_combination h2

theorem minorAut_pow_w (n : ℕ) : (minorAut K ^ n) (uElt 1 1 1 1) = uElt 1 1 1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, minorAut_w, ih]

omit [Finite K] in
theorem w_sq : (uElt (1 : K) 1 1 1) ^ 2 = uElt 0 1 1 0 := by
  rw [sq, uElt_mul_self]
  congr 1 <;> ring

theorem minorAut_mem_antiUnipotent {g : antiSp K} (hg : g ∈ antiUnipotent K) :
    minorAut K g ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  refine ⟨d, c + a * b + a ^ 2 * d, b ^ 2 + a * b * d + c * d, a ^ 2, antiSp_ext ?_⟩
  rw [glMat_minorAut, glMat_uElt, minorMap_uMat, glMat_uElt]

theorem minorAut_pow_mem_antiUnipotent (n : ℕ) {g : antiSp K} (hg : g ∈ antiUnipotent K) :
    (minorAut K ^ n) g ∈ antiUnipotent K := by
  induction n generalizing g with
  | zero => exact hg
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply]
    exact ih (minorAut_mem_antiUnipotent hg)

theorem center_square_mem_residual
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hz : uElt (0 : K) 1 1 0 ∈ fixedSubgroup (minorAut K ^ n)) :
    (⟨uElt 0 1 1 0, hz⟩ : fixedSubgroup (minorAut K ^ n)) ∈
      Setup.X7b.residual (fixedSubgroup (minorAut K ^ n)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · by_cases hm2 : 2 ≤ m
    · obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed (by omega) hK
      have := hcp
      let _ : Fintype k := Fintype.ofFinite k
      let e : antiSp k ≃* fixedSubgroup (minorAut K ^ (2 * m)) :=
        (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
      have : Group.IsPerfect (antiSp k) :=
        antiSp_isPerfect (by rw [← Nat.card_eq_fintype_card]; exact hcard) hm2
      have hperf : Group.IsPerfect (fixedSubgroup (minorAut K ^ (2 * m))) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      rw [residual_eq_top_of_perfect hperf]
      exact Subgroup.mem_top _
    · have hm1 : m = 1 := by omega
      subst hm1
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have hρx : minorAut K (uElt 1 0 0 0) = uElt 0 0 0 1 := by
        apply antiSp_ext
        rw [glMat_minorAut, glMat_uElt, minorMap_uMat]
        congr 1 <;> ring1
      have hρy : minorAut K (uElt 0 0 0 1) = uElt 1 0 0 0 := by
        apply antiSp_ext
        rw [glMat_minorAut, glMat_uElt, minorMap_uMat]
        congr 1 <;> ring1
      have hx0 : uElt (1 : K) 0 0 0 ∈ fixedSubgroup (minorAut K ^ (2 * 1)) := by
        rw [mem_fixedSubgroup, mul_one, sq, MulAut.mul_apply, hρx, hρy]
      have hy0 : uElt (0 : K) 0 0 1 ∈ fixedSubgroup (minorAut K ^ (2 * 1)) := by
        rw [mem_fixedSubgroup, mul_one, sq, MulAut.mul_apply, hρy, hρx]
      have hcomm : ⁅(⟨uElt 1 0 0 0, hx0⟩ : fixedSubgroup (minorAut K ^ (2 * 1))),
          (⟨uElt 0 0 0 1, hy0⟩ : fixedSubgroup (minorAut K ^ (2 * 1)))⁆ =
            (⟨uElt 0 1 1 0, hz⟩ : fixedSubgroup (minorAut K ^ (2 * 1))) := by
        apply Subtype.ext
        change uElt (1 : K) 0 0 0 * uElt 0 0 0 1 * (uElt 1 0 0 0)⁻¹ * (uElt 0 0 0 1)⁻¹ =
          uElt 0 1 1 0
        rw [uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
        congr 1 <;> first | ring1 | linear_combination h2
      obtain ⟨k, hcp, lift, hcard, hinj, hrange⟩ := exists_even_fixed (m := 1) le_rfl hK
      have := hcp
      let _ : Fintype k := Fintype.ofFinite k
      have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hcard, pow_one]
      let ε : ZMod 2 ≃+* k := ZMod.ringEquivOfPrime k Nat.prime_two hk'
      have hJ : antiSp (ZMod 2) = CFSG.ComponentClassification.PresentationLocal.sympFour := by
        ext g
        rfl
      let e : fixedSubgroup (minorAut K ^ (2 * 1)) ≃*
          CFSG.ComponentClassification.PresentationLocal.sympFour :=
        ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
          ((antiSpCongr ε.symm).trans (MulEquiv.subgroupCongr hJ))
      have hcm : (commutator (fixedSubgroup (minorAut K ^ (2 * 1)))).map e.toMonoidHom =
          commutator CFSG.ComponentClassification.PresentationLocal.sympFour := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ e.surjective]
      have : Group.IsPerfect
          (commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
        CFSG.ComponentClassification.PresentationLocal.isPerfect_commutator_sympFour
      let f : commutator CFSG.ComponentClassification.PresentationLocal.sympFour ≃*
          commutator (fixedSubgroup (minorAut K ^ (2 * 1))) :=
        ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hcm)).symm
      have hperf : Group.IsPerfect (commutator (fixedSubgroup (minorAut K ^ (2 * 1)))) :=
        Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
      have hstable : derivedSeries (fixedSubgroup (minorAut K ^ (2 * 1))) (1 + 1) =
          derivedSeries (fixedSubgroup (minorAut K ^ (2 * 1))) 1 := by
        rw [derivedSeries_succ, derivedSeries_one]
        exact commutator_self_of_perfect _ hperf
      rw [residual_eq_of_stable hstable, derivedSeries_one, ← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · have hm : 1 ≤ m := by omega
    have hperf : Group.IsPerfect (fixedSubgroup (minorAut K ^ (2 * m + 1))) := by
      have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup m K) :=
        (CFSG.LieType.Ree.suzuki_perfect hm hK).2
      exact Group.IsPerfect.ofSurjective (f := (fixedSubgroupEtaEquiv hK).symm.toMonoidHom)
        (fixedSubgroupEtaEquiv hK).symm.surjective
    rw [residual_eq_top_of_perfect hperf]
    exact Subgroup.mem_top _

end SymplecticFourOuterSquare

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.QuasithinUnique SymplecticFourOuterSquare in
open CFSG.ComponentClassification.OuterAutomorphisms (inner) in
theorem even_symplectic_four_outer_involution_fixed_central_square
    {K : Type} [Field K]
    [CharP K 2] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (θ : MulAut (antiSp K)) (hθ : θ * θ = 1) (hθinn : θ ∉ inner (antiSp K)) :
    ∃ P : Subgroup (antiSp K), IsSylowTwoOf P ⊤ ∧ P.map θ.toMonoidHom = P ∧
      ∃ w ∈ P, θ w = w ∧ orderOf w = 4 ∧ (∀ h ∈ P, w ^ 2 * h = h * w ^ 2) ∧
        w ^ 2 ∈ (Setup.X7b.residual (fixedSubgroup θ)).map (fixedSubgroup θ).subtype ∧
        w ^ 2 ≠ 1 ∧
        ∀ (φ : P ≃* antiUnipotent K) (hz : w ^ 2 ∈ P), ∃ b c : K, b ≠ 0 ∧ c ≠ 0 ∧
          ((φ ⟨w ^ 2, hz⟩ : antiUnipotent K) : antiSp K) = uElt 0 b c 0 := by
  obtain ⟨c, rfl⟩ := outer_involution_conj hn hK θ hθ hθinn
  set Ψ : MulAut (antiSp K) := MulAut.conj c with hΨ
  set θ₀ : MulAut (antiSp K) := minorAut K ^ n with hθ₀
  set w₀ : antiSp K := uElt 1 1 1 1 with hw₀
  have hθw₀ : θ₀ w₀ = w₀ := minorAut_pow_w n
  have hz₀ : w₀ ^ 2 = uElt 0 1 1 0 := w_sq
  have hz₀ne : uElt (0 : K) 1 1 0 ≠ 1 := by
    rw [← uElt_zero_eq_one]
    intro h
    exact one_ne_zero (uElt_inj h).2.1
  have hθapp : ∀ x, (Ψ * θ₀ * Ψ⁻¹) (Ψ x) = Ψ (θ₀ x) := by
    intro x
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  have hT := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  set P : Subgroup (antiSp K) := (antiUnipotent K).map Ψ.toMonoidHom with hP
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, hT.2.1.map _, ?_⟩
    have h0 : ¬ 2 ∣ (antiUnipotent K).index := by
      have := hT.2.2
      change ¬ 2 ∣ (antiUnipotent K).relIndex ⊤ at this
      rwa [Subgroup.relIndex_top_right] at this
    change ¬ 2 ∣ P.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hP]
    have h1 := Subgroup.index_map_equiv (H := antiUnipotent K) Ψ
    rw [show ((Ψ : antiSp K ≃* antiSp K) : antiSp K →* antiSp K) = Ψ.toMonoidHom from rfl] at h1
    rw [h1]
    exact h0
  have hPinv : P.map (Ψ * θ₀ * Ψ⁻¹).toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨θ₀ u, minorAut_pow_mem_antiUnipotent n hu, ?_⟩
      exact (hθapp u).symm
    · have hinj : Function.Injective (Ψ * θ₀ * Ψ⁻¹).toMonoidHom := (Ψ * θ₀ * Ψ⁻¹).injective
      rw [Subgroup.card_map_of_injective hinj]
  have hwP : Ψ w₀ ∈ P := ⟨w₀, ⟨1, 1, 1, 1, rfl⟩, rfl⟩
  have hwfix : (Ψ * θ₀ * Ψ⁻¹) (Ψ w₀) = Ψ w₀ := by rw [hθapp, hθw₀]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hw₀ord : orderOf w₀ = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w₀) (by
      rw [pow_one, hz₀]
      exact hz₀ne) (by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hz₀, sq, uElt_mul]
      rw [← uElt_zero_eq_one]
      congr 1 <;> first | ring1 | linear_combination h2)
    simpa using h
  have hword : orderOf (Ψ w₀) = 4 :=
    (orderOf_injective Ψ.toMonoidHom Ψ.injective w₀).trans hw₀ord
  have hwsq : (Ψ w₀) ^ 2 = Ψ (uElt 0 1 1 0) := by rw [← map_pow, hz₀]
  refine ⟨P, hPsyl, hPinv, Ψ w₀, hwP, hwfix, hword, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨u, hu, rfl⟩
    rw [hwsq]
    change Ψ (uElt 0 1 1 0) * Ψ u = Ψ u * Ψ (uElt 0 1 1 0)
    rw [← map_mul, ← map_mul, antiUnipotentCenter_comm ⟨1, 1, rfl⟩ hu]
  ·
    have hz₀H : uElt (0 : K) 1 1 0 ∈ fixedSubgroup θ₀ := by
      rw [mem_fixedSubgroup, ← hz₀, map_pow, hθw₀]
    have hres := center_square_mem_residual hn hK hz₀H
    let e := fixedSubgroupConjEquiv Ψ θ₀
    have he : ((e ⟨uElt 0 1 1 0, hz₀H⟩ : fixedSubgroup (Ψ * θ₀ * Ψ⁻¹)) : antiSp K) =
        Ψ (uElt 0 1 1 0) := rfl
    rw [hwsq, ← he, ← map_residual e]
    exact ⟨e ⟨uElt 0 1 1 0, hz₀H⟩, ⟨⟨uElt 0 1 1 0, hz₀H⟩, hres, rfl⟩, rfl⟩
  · rw [hwsq]
    intro h
    apply hz₀ne
    apply Ψ.injective
    rw [h, map_one]
  · intro φ hz
    have hsq : (⟨(Ψ w₀) ^ 2, hz⟩ : P) = (⟨Ψ w₀, hwP⟩ : P) * ⟨Ψ w₀, hwP⟩ := by
      apply Subtype.ext
      show (Ψ w₀) ^ 2 = Ψ w₀ * Ψ w₀
      exact sq _
    have hne : ((φ ⟨(Ψ w₀) ^ 2, hz⟩ : antiUnipotent K) : antiSp K) ≠ 1 := by
      intro h
      have h1 : φ ⟨(Ψ w₀) ^ 2, hz⟩ = 1 := Subtype.ext h
      rw [← map_one φ] at h1
      have h2 := congrArg Subtype.val (φ.injective h1)
      apply hz₀ne
      apply Ψ.injective
      rw [← hwsq, map_one]
      exact h2
    refine (isSquare_iff _ hne).mp ⟨(φ ⟨Ψ w₀, hwP⟩ : antiSp K), (φ ⟨Ψ w₀, hwP⟩).2, ?_⟩
    rw [hsq, map_mul, Subgroup.coe_mul]

end CFSG.LocalAnalysis
