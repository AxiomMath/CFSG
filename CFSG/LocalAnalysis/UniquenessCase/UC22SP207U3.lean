module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Coxeter
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Datum
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChIJK CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.GH74.GLS.SP
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg.CentralExt.SUBruhat
open Subgroup (center)

theorem uc22sp207_hasCentralLongest_U3 {X : Type} [Group X] {n : ℕ} (h : IsU3 X n) :
    HasCentralLongest X := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hFf, hFfin, hF, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP F 2 := burnsideI2BN_charP_of_card hp (f := n * 2) (by omega) (by rw [hF, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hσ := unitaryInvolution_involutive hF
  have hsub : Subsingleton (Fin (rootDatum hF 3).rank) := inferInstanceAs (Subsingleton (Fin 1))
  have hSU : HasCentralLongest (SU (unitaryInvolution F 2 n) 3) :=
    uc22sp207_hasCentralLongest_of_datum (D := rootDatum hF 3) (n := levelWeyl hσ ζ)
      (H := levelTorus (unitaryInvolution F 2 n)) (isCTGroupDatum hF 3 (by omega) ζ hζ)
      (steinbergExtras hF 3 (by omega) ζ hζ) (bruhatExtras hF (by omega) ζ hζ) (by
        rintro ⟨x, hx⟩
        have hidb := idBelow_of_mem_iSup hσ 1
          {γ | γ ∈ roots (isFiniteType_cartan 3) (divisible 3) ∧ 0 < ht γ}
          (fun γ hγ => by have := hγ.2; omega) hx
        obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := 2) (lvl 1)
          (M := mat (unitaryInvolution F 2 n) 3 x) hidb
        refine ⟨k, Subtype.ext (mat_injective (σ := unitaryInvolution F 2 n) (n := 3) ?_)⟩
        simpa [map_pow] using hk) (by
        have hT : ∀ y ∈ (⨆ i, levelTorus (unitaryInvolution F 2 n) i :
            Subgroup (SU (unitaryInvolution F 2 n) 3)), y ^ (Nat.card F - 1) = 1 := by
          intro y hy
          obtain ⟨t, ht⟩ : ∃ t : Fin 3 → F,
              mat (unitaryInvolution F 2 n) 3 y = Matrix.diagonal t :=
            Subgroup.iSup_induction _ hy
              (C := fun y => ∃ t : Fin 3 → F,
                mat (unitaryInvolution F 2 n) 3 y = Matrix.diagonal t)
              (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
              ⟨1, by rw [map_one]; exact Matrix.diagonal_one.symm⟩
              (fun y z ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ =>
                ⟨d₁ * d₂, by rw [map_mul, h₁, h₂, Matrix.diagonal_mul_diagonal]; rfl⟩)
          have hdet : ∏ a, t a = 1 := by
            have := y.2.1
            rwa [← mat_apply (σ := unitaryInvolution F 2 n) (n := 3), ht,
              Matrix.det_diagonal] at this
          have hne : ∀ a, t a ≠ 0 := fun a h0 => by
            have := Finset.prod_eq_zero (Finset.mem_univ a) h0
            rw [hdet] at this
            exact one_ne_zero this
          have : Fintype F := Fintype.ofFinite F
          refine mat_injective (σ := unitaryInvolution F 2 n) (n := 3) ?_
          rw [map_pow, ht, Matrix.diagonal_pow, map_one]
          have hd1 : t ^ (Nat.card F - 1) = 1 := by
            funext a
            rw [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card]
            exact FiniteField.pow_card_sub_one_eq_one _ (hne a)
          rw [hd1]
          simp
        exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
          (burnsideI2BN_not_dvd_card_sub_one hp
            (hF ▸ dvd_pow (dvd_pow_self 2 (by omega : n ≠ 0)) two_ne_zero)))
      (uc22sp207_exists_central_longest_of_subsingleton _)
  exact ((hSU.of_mulEquiv (equivStatedSU hF 3)).statedProj).of_mulEquiv e.symm

theorem uc22sp207_hasCentralLongest_SU3 {X : Type} [Group X] [Finite X]
    (hodd : ¬ 2 ∣ Nat.card (center X)) {n : ℕ} (h : IsSU3 X n) : HasCentralLongest X := by
  refine (uc22sp207_hasCentralLongest_U3 h.2).comap (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ?_
  rwa [QuotientGroup.ker_mk']

end CFSG.LocalAnalysis.UniquenessCase.UC22
