module

public import CFSG.Quasithin.Background.GoldschmidtRankOneTwoTrans
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem exists_statedProj_equiv_psu {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ (σ : F ≃+* F) (hσ : Function.Involutive σ), Nat.card {x : F // σ x = x} = 2 ^ n ∧
      Nonempty (StatedProj (StatedSU 3 (2 ^ n) F) ≃*
        ProjectiveSpecialUnitaryMatrixGroup (RankTwoShapes.antidiagonalHermitianForm σ hσ)) := by
  obtain ⟨σ, hσq, hσ, hfix⟩ := RankTwoShapes.exists_quadraticFrobenius F n hn hF
  obtain ⟨P, hP⟩ := External.huppert_II_10_4_b_standard_hermitian_basis
    (RankTwoShapes.identityHermitianForm σ hσ) (2 ^ n) hF hfix
  obtain ⟨e⟩ := RankTwoShapes.nonempty_projectiveSpecialUnitary_equiv_of_gram
    (RankTwoShapes.identityHermitianForm σ hσ) (RankTwoShapes.antidiagonalHermitianForm σ hσ) P
    rfl hP
  refine ⟨σ, hσ, hfix, ⟨(RankTwoShapes.statedProjEquivMap _).trans
    ((MulEquiv.subgroupCongr ?_).trans e)⟩⟩
  have hs : (StatedSU 3 (2 ^ n) F : Subgroup (GL (Fin 3) F)) =
      (RankTwoShapes.identityHermitianForm σ hσ).specialSubgroup :=
    RankTwoShapes.statedSU_eq_specialSubgroup (2 ^ n) σ hσ hσq
  rw [hs]

theorem isRankOneSylowCyclic_of_nine_points {G Ω : Type*} [Group G] (ρ : G →* Equiv.Perm Ω)
    (pinf : Ω) (hinj : Function.Injective ρ)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, ρ g a = c ∧ ρ g b = d)
    (hΩ : Nat.card Ω = 9) (hG : Nat.card G = 72) (hU : Nat.card (pointStab ρ pinf) = 8) :
    IsRankOneSylowCyclic G := by
  have hfinG : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hfinΩ : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have hne : ∃ a b : Ω, a ≠ b := by
    have h1 : 1 < Nat.card Ω := by rw [hΩ]; norm_num
    obtain ⟨a, b, hab⟩ := (Finite.one_lt_card_iff_nontrivial.mp h1).exists_pair_ne
    exact ⟨a, b, hab⟩
  have hp : IsPGroup 2 (pointStab ρ pinf) := IsPGroup.of_card (n := 3) (by rw [hU]; norm_num)
  have hidx : (pointStab ρ pinf).index = 9 := by
    have hm := (pointStab ρ pinf).card_mul_index
    rw [hU, hG] at hm
    omega
  have hnt : pointStab ρ pinf ≠ ⊥ := by
    intro hbot
    have := hU
    rw [hbot, Subgroup.card_bot] at this
    omega
  exact isRankOneSylowCyclic_of_two_transitive ρ h2 hne hinj pinf hp
    (by rw [hidx]; norm_num) hnt

theorem isRankOneSylowCyclic_statedProj_one (hF : Nat.card F = (2 ^ 1) ^ 2) :
    IsRankOneSylowCyclic (StatedProj (StatedSU 3 (2 ^ 1) F)) := by
  obtain ⟨σ, hσ, hfix, ⟨e⟩⟩ := exists_statedProj_equiv_psu (n := 1) one_ne_zero hF
  refine IsRankOneSylowCyclic.of_mulEquiv e.symm ?_
  have H := External.huppert_II_10_12 (RankTwoShapes.antidiagonalHermitianForm σ hσ) (2 ^ 1) hF
    hfix rfl
  dsimp only at H
  obtain ⟨hΩ, ρ, pinf, hinj, -, hUcard, -, h2, hGcard, -⟩ := H
  refine isRankOneSylowCyclic_of_nine_points ρ pinf hinj h2 ?_ ?_ ?_
  · rw [hΩ]
    norm_num
  · rw [hGcard]
    norm_num
  · change Nat.card ↥(Subgroup.comap ρ _) = 8
    rw [hUcard]
    norm_num

end CFSG.Quasithin
