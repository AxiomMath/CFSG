module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem not_isQuasisimple_of_isOmegaPlus_four {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a)
    (h : IsOmegaPlus X 4 a) : ¬ CFSG.Open.IsQuasisimple X := by
  intro hq
  have hcardX : Nat.card X = (2 ^ a * (4 ^ a - 1)) ^ 2 := Om8Excl.card_isOmegaPlus_four ha h
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  change X ≃* StatedProj (StatedOmega (StatedQuadPlus 2 K)) at e
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  obtain ⟨e2⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
  let f : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* X :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp e2.toMonoidHom)
  have hf_surj : Function.Surjective f :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp e2.surjective)
  have hcardD : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) = (2 ^ a * (4 ^ a - 1)) ^ 2 := by
    rw [Nat.card_prod,
      Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_two, hcard, ← sq]
    congr 2
    rw [show (4 : ℕ) ^ a = (2 ^ a) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have hf_inj : Function.Injective f :=
    (hf_surj.bijective_of_nat_card_le (by rw [hcardD, hcardX])).1
  let N₁ : Subgroup X :=
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map (f.comp (MonoidHom.inl _ _))
  let N₂ : Subgroup X :=
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map (f.comp (MonoidHom.inr _ _))
  have hmul (u v : Matrix.SpecialLinearGroup (Fin 2) K) :
      f (u, 1) * f (1, v) = f (1, v) * f (u, 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hmul u v
  have hsup : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨u, v⟩, rfl⟩ := hf_surj x
    have hx : f (u, v) = f (u, 1) * f (1, v) := by
      rw [← map_mul]
      congr 1
      ext <;> simp
    rw [hx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ (Subgroup.mem_top u))
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_top v))
  have hnc : ∃ u v : Matrix.SpecialLinearGroup (Fin 2) K, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_not_commutative_aux (k := K) hcon
  have h₁ : ∃ x ∈ N₁, ∃ y ∈ N₁, x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hnc
    refine ⟨f (u, 1), Subgroup.mem_map_of_mem _ (Subgroup.mem_top u),
      f (v, 1), Subgroup.mem_map_of_mem _ (Subgroup.mem_top v), ?_⟩
    intro hxy
    refine huv ?_
    have h2 : f (u * v, 1) = f (v * u, 1) := by
      rw [← map_mul, ← map_mul] at hxy
      simpa using hxy
    exact (Prod.ext_iff.mp (hf_inj h2)).1
  have h₂ : ∃ x ∈ N₂, ∃ y ∈ N₂, x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hnc
    refine ⟨f (1, u), Subgroup.mem_map_of_mem _ (Subgroup.mem_top u),
      f (1, v), Subgroup.mem_map_of_mem _ (Subgroup.mem_top v), ?_⟩
    intro hxy
    refine huv ?_
    have h2 : f (1, u * v) = f (1, v * u) := by
      rw [← map_mul, ← map_mul] at hxy
      simpa using hxy
    exact (Prod.ext_iff.mp (hf_inj h2)).2
  exact uc22p20g_not_quasisimple_of_commuting hq hsup hcomm h₁ h₂

theorem exists_tensor_of_isOmegaPlus_eight {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hW : Conc4_136W A t L)
    (hΩ : IsOmegaPlus ↥L 4 3) :
    ∃ K : Subgroup (MulAut W), IsComponentOf K A ∧ ∃ g ∈ A,
      K ≠ K.map (MulAut.conj g).toMonoidHom ∧ L = K ⊔ K.map (MulAut.conj g).toMonoidHom ∧
        UC22.IsL2 ↥K 3 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 3 := by
  have hcard : Nat.card ↥L = 254016 :=
    (Om8Excl.card_isOmegaPlus_four (by norm_num) hΩ).trans (by norm_num)
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases hW.2.2 with h1 | ⟨K, hK, g, hg, hne, hL, hc⟩ | h3 | h4
  ·
    obtain ⟨p, hp, hLp, -⟩ := h1
    haveI : Fact p.Prime := ⟨hp⟩
    have hpG : IsPGroup p ↥(pCoreOf p A) :=
      (CFSG.pCore_isPGroup (p := p) (G := ↥A)).map A.subtype
    have hpL : IsPGroup p ↥L := hpG.to_le hLp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpL
    have h2dvd : 2 ∣ p ^ k := by rw [← hk, hcard]; norm_num
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        ((Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2dvd)).symm
    have h3dvd : 3 ∣ 2 ^ k := by
      have h' : 3 ∣ Nat.card ↥L := by rw [hcard]; norm_num
      rwa [hk, hp2] at h'
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three) h3dvd) (by norm_num)
  · rcases hc with ⟨-, hT⟩ | ⟨-, hT⟩ | ⟨hK8, hT⟩
    ·
      obtain ⟨F, _, _, hF, π, hπ⟩ := hT
      haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
      have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
      haveI : Finite ↥(StatedSL 3 F) := inferInstance
      have hle : Nat.card ↥L ≤ Nat.card (↥(StatedSL 3 F) × ↥(StatedSL 3 F)) :=
        Nat.card_le_card_of_surjective (π : ↥(StatedSL 3 F) × ↥(StatedSL 3 F) → ↥L) hπ.1
      rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hF2] at hle
      norm_num at hle
      omega
    ·
      obtain ⟨F, _, _, hF, π, hπ⟩ := hT
      haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
      have hF2 : Nat.card F = 4 := by rw [hF]; norm_num
      haveI : Finite ↥(StatedSL 2 F) := inferInstance
      have hle : Nat.card ↥L ≤ Nat.card (↥(StatedSL 2 F) × ↥(StatedSL 2 F)) :=
        Nat.card_le_card_of_surjective (π : ↥(StatedSL 2 F) × ↥(StatedSL 2 F) → ↥L) hπ.1
      rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two, hF2] at hle
      norm_num at hle
      omega
    ·
      exact ⟨K, by simpa using hK, g, hg, hne, hL, hK8, hT⟩
  ·
    exact (not_isQuasisimple_of_isOmegaPlus_four (by norm_num) hΩ h3.1.2.2).elim
  ·
    exact (not_isQuasisimple_of_isOmegaPlus_four (by norm_num) hΩ h4.2.2.1.2.2).elim

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
