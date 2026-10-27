module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartTwo.Sec3.Sims321Action
import CFSG.RankThree.PartTwo.Sec3.Sims321Singer
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.PartTwo.Sec20

open scoped MatrixGroups

section Model

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ}

theorem exists_conjAut_mul_dualAut (hn : Odd n)
    (β : MulAut (projectiveSL 3 (GaloisField 2 n))) (hβ : β * β = 1)
    (hinner : ∀ g, β ≠ MulAut.conj g) :
    ∃ A : GL (Fin 3) (GaloisField 2 n),
      β = conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n) := by
  set F := GaloisField 2 n
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hβeq
    obtain ⟨B, hB⟩ := Res7.exists_pow_conjAut_mul_fieldAut A σ 2
    rw [← hβeq, pow_two, hβ] at hB
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (σ ^ 2) hB.symm
    have hσ : σ = 1 := Res7.eq_one_of_pow_two_pow_eq_one hn (a := 1) (by rwa [pow_one])
    rw [hσ, map_one, mul_one] at hβeq
    obtain ⟨y, hy⟩ := Res7.exists_conj_eq_conjAut_of_cube A (Res7.exists_cube_galoisField hn)
    exact absurd (hβeq.trans hy) (hinner y)
  ·
    rw [pow_one] at hβeq
    have hsq : β ^ 2 = conjAut 3 F (A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut 3 F (σ * σ) := by
      rw [← conjAut_mul_fieldAut_mul]
      have h1 : β ^ 2 = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
          dualAut 3 F * (dualAut 3 F * fieldAut 3 F σ * dualAut 3 F)) := by
        rw [hβeq, pow_two]
        calc _ = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
              fieldAut 3 F σ * dualAut 3 F) := by group
          _ = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A *
              (dualAut 3 F * dualAut 3 F) * fieldAut 3 F σ * dualAut 3 F) := by
            rw [hδδ]
            group
          _ = _ := by group
      rw [h1, htrans.2.2.2.2.1, htrans.2.2.2.2.2.1]
    rw [pow_two, hβ] at hsq
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hsq.symm
    have hσ : σ = 1 := Res7.eq_one_of_pow_two_pow_eq_one hn (a := 1) (by
      rw [pow_one, pow_two]
      exact hσ1)
    exact ⟨A, by rw [hβeq, hσ, map_one, mul_one]⟩

end Model

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_inverted_ppd_projectiveSL_odd {n : ℕ} (hn : Odd n)
    (β : MulAut (projectiveSL 3 (GaloisField 2 n))) (hβ : β * β = 1)
    (hinner : ∀ g, β ≠ MulAut.conj g) :
    ∃ (r : ℕ) (x : projectiveSL 3 (GaloisField 2 n)), r.Prime ∧ r ∣ 2 ^ (3 * n) - 1 ∧
      (∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) ∧ orderOf x = r ∧ β x = x⁻¹ := by
  classical
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  obtain ⟨A, hA⟩ := exists_conjAut_mul_dualAut hn β hβ hinner
  have hA2 : (conjAut 3 (GaloisField 2 n) A * dualAut 3 (GaloisField 2 n)) ^ 2 = 1 := by
    rw [← hA, pow_two, hβ]
  obtain ⟨B, hBs, hB⟩ := Sec3.Sims321.exists_symm_of_sq_eq_one hn A hA2
  obtain ⟨r, hr, hr3, hrk⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (3 * n)
    (by omega) (by obtain ⟨k, rfl⟩ := hn; omega)
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n hn0
  obtain ⟨g, hgr, hginv⟩ := Sec3.Sims321.exists_inverted_of_symm hcard (Nat.pos_of_ne_zero hn0)
    hr hr3 hrk B hBs
  refine ⟨r, proj 3 (GaloisField 2 n) g, hr, hr3, hrk, ?_, ?_⟩
  · rw [orderOf_injective (proj 3 (GaloisField 2 n)) (Sec3.Sims321.proj_injective_of_odd hn) g,
      hgr]
  · rw [hA, hB, Sec3.Sims321.conjAut_mul_dualAut_proj, hginv, map_inv]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
noncomputable def slThreeEquivProjSL {n : ℕ} (hn : Odd n) :
    SL(3, GaloisField 2 n) ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n) :=
  (MulEquiv.ofBijective (proj 3 (GaloisField 2 n))
    ⟨Sec3.Sims321.proj_injective_of_odd hn, proj_surjective 3 _⟩).trans
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)).symm

section Transport

private def InvertedPPD (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ β : MulAut G, β * β = 1 → (∀ g, β ≠ MulAut.conj g) →
    ∃ (r : ℕ) (x : G), r.Prime ∧ r ∣ 2 ^ (3 * n) - 1 ∧
      (∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) ∧ orderOf x = r ∧ β x = x⁻¹

private theorem InvertedPPD.of_mulEquiv {n : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : InvertedPPD n H) : InvertedPPD n G := by
  intro β hβ hinner
  have hinner' : ∀ g : H, MulAut.congr e β ≠ MulAut.conj g := by
    intro g hg
    refine hinner (e.symm g) (MulEquiv.ext fun x => e.injective ?_)
    have := congrArg (fun α : MulAut H => α (e x)) hg
    simpa [MulAut.congr_apply] using this
  obtain ⟨r, y, hr, hr3, hrk, hy, hβy⟩ :=
    h (MulAut.congr e β) (by rw [← map_mul, hβ, map_one]) hinner'
  refine ⟨r, e.symm y, hr, hr3, hrk, by rw [MulEquiv.orderOf_eq, hy], e.injective ?_⟩
  simpa [MulAut.congr_apply] using hβy

end Transport

theorem exists_inverted_ppd_projSL3_odd {n : ℕ} (hn : Odd n)
    (β : MulAut ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) (hβ : β * β = 1)
    (hinner : ∀ g, β ≠ MulAut.conj g) :
    ∃ (r : ℕ) (x : ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))), r.Prime ∧
      r ∣ 2 ^ (3 * n) - 1 ∧ (∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) ∧
      orderOf x = r ∧ β x = x⁻¹ :=
  InvertedPPD.of_mulEquiv (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
    (exists_inverted_ppd_projectiveSL_odd hn) β hβ hinner

end CFSG.RankThree.PartTwo.Sec20
