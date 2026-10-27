module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowZ3FieldCore
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterUni
public import CFSG.RankThree.PartTwo.Sec4.RonanK432R2
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.KFacts
open Matrix

namespace Z3Field

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem exists_proj_matrix_U (τ : K ≃+* K) (H : unitaryIsom3 h) (g : unitarySU p f K 3) :
    ∃ Y : unitarySU p f K 3,
      (psuConj h H * psuField h τ * (psuConj h H)⁻¹) (unitaryProj h 3 g) = unitaryProj h 3 Y ∧
      (Y : GL (Fin 3) K) = (H : GL (Fin 3) K) *
        frobGL τ ((H : GL (Fin 3) K)⁻¹ * (g : GL (Fin 3) K) * (H : GL (Fin 3) K)) *
          (H : GL (Fin 3) K)⁻¹ := by
  refine ⟨suConj h H (suField h τ (suConj h H⁻¹ g)), ?_, ?_⟩
  · rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply]
    change psuConj h H (psuField h τ (psuConj h H⁻¹ (g : unitaryPSU h 3))) = _
    rw [psuConj_mk, psuField_mk, psuConj_mk]
    rfl
  · rw [coe_suConj, coe_suField, coe_suConj]
    simp only [Subgroup.coe_inv, inv_inv]
    rfl

theorem exists_scalar_of_fix_U (τ : K ≃+* K) (H : unitaryIsom3 h) (ζ : Kˣ)
    {X : unitarySU p f K 3} (hX : (X : GL (Fin 3) K) = diagUnits ζ ζ⁻¹ 1)
    (hfix : (psuConj h H * psuField h τ * (psuConj h H)⁻¹) (unitaryProj h 3 X) =
      unitaryProj h 3 X) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧
      (H : GL (Fin 3) K) * frobGL τ ((H : GL (Fin 3) K)⁻¹ * diagUnits ζ ζ⁻¹ 1 * (H : GL (Fin 3) K)) *
        (H : GL (Fin 3) K)⁻¹ = diagUnits ζ ζ⁻¹ 1 * GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨Y, hY1, hY2⟩ := exists_proj_matrix_U τ H X
  rw [hY1] at hfix
  have hmem : X⁻¹ * Y ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hfix, inv_mul_cancel]
  obtain ⟨c, -, hc3, hc⟩ := mem_unitaryScalars.mp hmem
  refine ⟨c, hc3, ?_⟩
  have hY : (Y : GL (Fin 3) K) = (X : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    calc (Y : GL (Fin 3) K) = ((X * (X⁻¹ * Y) : unitarySU p f K 3) : GL (Fin 3) K) := by
          rw [mul_inv_cancel_left]
      _ = _ := by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hc]; rfl
  rw [hY2, hX] at hY
  exact hY

theorem conj_mem_psuConj_range (s : unitaryPSU h 3) : MulAut.conj s ∈ (psuConj h).range := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 s
  exact ⟨_, (conj_mk_eq_psuConj g).symm⟩

theorem not_autWeaklyClosed_of_field_U [Finite K] (hPi : PiField false p f K) (hq2 : 2 < p ^ f)
    (h3f : 3 ∣ f) {k : ℕ} (hk : p ^ (f / 3) = 3 * k + 2) {σ : MulAut (unitaryPSU h 3)}
    (hσ : σ ^ 3 = 1)
    (hout : σ ∉ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range)
    (hD : σ ∉ (psuConj h).range) : ¬ AutWeaklyClosed σ := by
  intro hw
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = (3 * k + 1) * (3 * k + 3) := ⟨_, rfl⟩
  have hm3 : m % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨(3 * k + 1) * (k + 1), by rw [hmdef]; ring⟩
  have hm0 : 0 < m := by rw [hmdef]; positivity
  have hm1 : m + 1 = (3 * k + 2) ^ 2 := by rw [hmdef]; ring
  have hq : p ^ f = (3 * k + 2) ^ 3 := by rw [← hk, ← pow_mul, Nat.div_mul_cancel h3f]
  have hKc : Nat.card K = (m + 1) ^ 3 := by
    have h6 : 2 * f = f / 3 * 6 := by omega
    rw [h.card, h6, pow_mul, hk, hm1, ← pow_mul]
  have hmf : p ^ (2 * f / 3) = m + 1 := by
    rw [show 2 * f / 3 = f / 3 * 2 by omega, pow_mul, hk, hm1]
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_three_pow hKc hm3 hm0
  have hζq : ζ ^ (p ^ f + 1) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hζ, hq, hmdef]
    exact three_pow_succ_dvd_cube_add_one k
  have hroot : ∀ u : Kˣ, u ^ (p ^ f + 1) = 1 → u ∈ rootsOfUnity (qSubPi false (p ^ f)) K :=
    fun u hu => (mem_rootsOfUnity _ _).mpr hu
  have hmemGU : diagUnits ζ ζ⁻¹ 1 ∈ glPi false 3 (p ^ f) K :=
    diagUnits_mem_glPi hPi (hroot ζ hζq) (hroot ζ⁻¹ (by rw [inv_pow, hζq, inv_one]))
      (hroot 1 (one_pow _))
  have hmemSU : (diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
    (mem_unitarySU_iff h).mpr ⟨det_diagUnits_inv ζ, (mem_glPi_false h).mp hmemGU⟩
  obtain ⟨X, hX⟩ : ∃ X : unitarySU p f K 3, (X : GL (Fin 3) K) = diagUnits ζ ζ⁻¹ 1 :=
    ⟨⟨_, hmemSU⟩, rfl⟩
  have hXN : X ^ (3 ^ (padicValNat 3 m + 1)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hX,
      diagUnits_pow_eq_one (by rw [← hζ]; exact pow_orderOf_eq_one ζ)]
    rfl
  have hR : IsPGroup 3 (Subgroup.zpowers (unitaryProj h 3 X)) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hXN, map_one])
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.center_unitaryPSU_three h hq2
  obtain ⟨s, hs⟩ := r2_exists_conj_fixes hZ hσ hout hw hR
  have hfix := hs (unitaryProj h 3 X) (Subgroup.mem_zpowers _)
  have hD' : MulAut.conj s * σ * (MulAut.conj s)⁻¹ ∉ (psuConj h).range := by
    intro hmem
    apply hD
    have hc : MulAut.conj s ∈ (psuConj h).range := conj_mem_psuConj_range s
    have := mul_mem (mul_mem (inv_mem hc) hmem) hc
    simpa [mul_assoc] using this
  obtain ⟨τ, hτ, H, hσ'⟩ := unitary_order_three_field_descent hq2 _ (r2_conj_pow_three hσ s) hD'
  rw [hσ'] at hfix
  obtain ⟨c, hc3, hcore⟩ := exists_scalar_of_fix_U τ H ζ hX hfix
  obtain ⟨hc, hc1⟩ := core_gl τ H ζ c hcore
  have hcone : c = 1 := eq_one_of_pow_three (one_le_padicValNat_three hm3 hm0) hζ hc3 hc
  obtain ⟨hne1, hne2⟩ :=
    frob_moves_zeta hPi.prime (by have := hPi.one_le; omega) h.card hmf hm3 hm0 hζ hτ
  rcases hc1 hcone with h' | h'
  · exact hne1 h'
  · exact hne2 h'

end Z3Field

open Z3Field

theorem outerRow_unitaryPSU_three_of_frobenius {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hPi : PiField false p f K) (hq : ModThree false (p ^ f))
    (hq2 : 2 < p ^ f) (h3f : 3 ∣ f) {k : ℕ} (hk : p ^ (f / 3) = 3 * k + 2) :
    OuterRow (unitaryPSU h 3) := by
  intro _ σ hσ hout hw
  by_cases hD : σ ∈ (psuConj h).range
  · obtain ⟨A, rfl⟩ := hD
    refine (L3Outer.not_autWeaklyClosed_of_diagonal hPi hq (psuConj h) (unitaryIsom3 h).subtype
      (fun g => L3Outer.psuConj_eq_one_iff g)
      (fun g => (mem_glPi_false h).mpr (mem_unitaryIsom3.mp g.2))
      (fun g hg => L3Outer.psuConj_mem_range_conj_of_slPi h g hg)
      (fun t ht => ⟨⟨t, mem_unitaryIsom3.mpr ((mem_slPi_false h).mp ht).2⟩, rfl⟩) (y := A)
      ?_ ?_) hw
    · intro hA
      obtain ⟨c, hc⟩ := hA
      exact hout (by rw [psuConj_eq_one_of_coe_eq_scalar hc.symm]; exact one_mem _)
    · refine mk_eq_one_iff_mem_statedScalars.mp ((L3Outer.psuConj_eq_one_iff (A ^ 3)).mp ?_)
      rw [map_pow]
      exact hσ
  · exact not_autWeaklyClosed_of_field_U (h := h) hPi hq2 h3f hk hσ hout hD hw

theorem outerRow_projSU_three_two_pow_of_three_dvd {n : ℕ} (hn : 1 ≤ n) (hodd : n % 2 = 1)
    (h3 : n % 3 = 0) : OuterRow (projSU 3 2 n) := by
  have hPi : PiField false 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, by
      rw [GaloisField.card 2 (2 * n) (by omega)]
      change 2 ^ (2 * n) = (2 ^ n) ^ 2
      rw [← pow_mul, mul_comm]⟩
  have hq : ModThree false (2 ^ n) := two_pow_mod_three_of_odd (Nat.odd_iff.mpr hodd)
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr : 2 ^ (n / 3) % 3 = 2 := two_pow_mod_three_of_odd (Nat.odd_iff.mpr (by omega))
  obtain ⟨e⟩ := nonempty_unitaryPSU_mulEquiv_projSU hPi.unitary
  exact OuterRow.of_mulEquiv e
    (outerRow_unitaryPSU_three_of_frobenius hPi.unitary hPi hq (by omega) (by omega)
      (k := 2 ^ (n / 3) / 3) (by omega))

theorem rowOf_seven_SU3_of_odd_of_three_dvd : ∀ n : ℕ, 1 ≤ n → n % 2 = 1 → n % 3 = 0 →
    RowOf (projSU 3 2 n) := by
  intro n hn hodd h3 S _ _ _ _ ⟨eS⟩
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSU_three_two_pow_of_odd (Nat.odd_iff.mpr hodd),
      outerRow_projSU_three_two_pow_of_three_dvd hn hodd h3⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
