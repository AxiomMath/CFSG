module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.KF1923L3Par

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

theorem kfl3_map_pow3 {P : Type} [Group P] (θ : MulAut P) (H : Subgroup P) :
    H.map ((θ ^ 3 : MulAut P) : P →* P) =
      ((H.map (θ : P →* P)).map (θ : P →* P)).map (θ : P →* P) := by
  rw [pow_succ, pow_two, Sec20.Res7.map_mulAut_mul, Sec20.Res7.map_mulAut_mul]

theorem kfl3Two_holds : KFL3Two := by
  intro X _ _ hL P hP α hk hg
  obtain ⟨n, hn, ⟨e₀⟩⟩ := hL
  obtain ⟨k, hk⟩ := hk
  obtain ⟨g, hg⟩ := hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : X ≃* projectiveSL 3 (GaloisField 2 n) :=
    e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)) with he
  obtain ⟨W, hW, hWP⟩ := kfl3_stab_of_isMax_map e hP
  have hβk : (MulAut.congr e α) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hβP : (projStabilizer W).map
      (MulAut.congr e α : MulAut (projectiveSL 3 (GaloisField 2 n))).toMonoidHom =
        (projStabilizer W).map (MulAut.conj (e g)).toMonoidHom := by
    rw [← hWP, kfl3_map_congr, hg, kfl3_map_conj_map]
  obtain ⟨A, σ, ε, hε, hform⟩ :=
    (automorphism_generation (K := GaloisField 2 n) (n := 3) le_rfl).2 (MulAut.congr e α)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hform
    obtain ⟨B, hB⟩ := Sec20.Res7.exists_pow_conjAut_mul_fieldAut A σ (2 ^ k)
    rw [← hform, hβk] at hB
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (σ ^ 2 ^ k) hB.symm
    have hσ : σ = 1 := Sec20.Res7.eq_one_of_pow_two_pow_eq_one hn hσ1
    rw [hσ, map_one, mul_one] at hform
    obtain ⟨y, hy⟩ :=
      Sec20.Res7.exists_conj_eq_conjAut_of_cube A (Sec20.Res7.exists_cube_galoisField hn)
    refine (kfl3_mem_inner_congr e α).mpr ?_
    rw [hform, hy]
    exact ⟨y, rfl⟩
  ·
    exfalso
    rw [pow_one] at hform
    obtain ⟨U, hU, hUd, hUβ⟩ := kfl3_flip_step A σ hW
    rw [← hform] at hUβ
    obtain ⟨h₀, hh₀⟩ := proj_surjective 3 (GaloisField 2 n) (e g)
    rw [← hh₀, kfl3_stab_conj_proj] at hβP
    have hV := kfl3_proper_map (Matrix.SpecialLinearGroup.toGL h₀) hW
    have hUV := kfl3_stab_inj hU hV (hUβ.symm.trans hβP)
    have hfin := kfl3_finrank_eq hUV
    rw [hUd, kfl3_finrank_map] at hfin
    obtain ⟨h1, h2⟩ := (Sec20.Res7.bot_lt_lt_top_iff W).mp hW
    omega

theorem kfl3Aut3_holds : KFL3Aut3 := by
  intro X _ _ hL α hα hα3
  obtain ⟨n, hn, ⟨e₀⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : X ≃* projectiveSL 3 (GaloisField 2 n) :=
    e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)) with he
  have hβ3 : (MulAut.congr e α) ^ 3 ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL 3 (GaloisField 2 n)) := by
    rw [← map_pow]
    exact (kfl3_mem_inner_congr e (α ^ 3)).mp hα3
  obtain ⟨A, σ, ε, hε, hform⟩ :=
    (automorphism_generation (K := GaloisField 2 n) (n := 3) le_rfl).2 (MulAut.congr e α)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hform
    obtain ⟨y, hy⟩ :=
      Sec20.Res7.exists_conj_eq_conjAut_of_cube A (Sec20.Res7.exists_cube_galoisField hn)
    rw [hform] at hβ3
    obtain ⟨y₃, hy₃⟩ := hβ3
    obtain ⟨h₀, hh₀⟩ := proj_surjective 3 (GaloisField 2 n) y₃
    obtain ⟨B, hB⟩ := Sec20.Res7.exists_pow_conjAut_mul_fieldAut A σ 3
    rw [hB, ← hh₀, ← conjAut_toGL] at hy₃
    have hcomp : conjAut 3 (GaloisField 2 n) ((Matrix.SpecialLinearGroup.toGL h₀)⁻¹ * B) *
        fieldAut 3 (GaloisField 2 n) (σ ^ 3) = 1 := by
      calc conjAut 3 (GaloisField 2 n) ((Matrix.SpecialLinearGroup.toGL h₀)⁻¹ * B) *
            fieldAut 3 (GaloisField 2 n) (σ ^ 3)
          = conjAut 3 (GaloisField 2 n) ((Matrix.SpecialLinearGroup.toGL h₀)⁻¹) *
              (conjAut 3 (GaloisField 2 n) B * fieldAut 3 (GaloisField 2 n) (σ ^ 3)) := by
            rw [map_mul, mul_assoc]
        _ = conjAut 3 (GaloisField 2 n) ((Matrix.SpecialLinearGroup.toGL h₀)⁻¹) *
              conjAut 3 (GaloisField 2 n) (Matrix.SpecialLinearGroup.toGL h₀) := by
            rw [← hy₃]
        _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    obtain ⟨hτ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hcomp
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hform
      exact hα ((kfl3_mem_inner_congr e α).mpr (by rw [hform, hy]; exact ⟨y, rfl⟩))
    have hfσ : fieldAut 3 (GaloisField 2 n) σ ≠ 1 := by
      intro h
      apply hσ1
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) 1 σ
        (by rw [map_one, one_mul]; exact h)).1
    have hf3 : fieldAut 3 (GaloisField 2 n) σ ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
    have hβX3 : MulAut.congr e.symm (fieldAut 3 (GaloisField 2 n) σ) ^ 3 = 1 := by
      rw [← map_pow, hf3, map_one]
    have hβXne : MulAut.congr e.symm (fieldAut 3 (GaloisField 2 n) σ) ≠ 1 := by
      intro h
      apply hfσ
      apply (MulAut.congr e.symm).injective
      rw [h, map_one]
    refine ⟨e.symm y, MulAut.congr e.symm (fieldAut 3 (GaloisField 2 n) σ),
      orderOf_eq_prime hβX3 hβXne, ?_⟩
    calc α = MulAut.congr e.symm (MulAut.congr e α) := (kfl3_congr_back e α).symm
      _ = MulAut.congr e.symm (conjAut 3 (GaloisField 2 n) A *
            fieldAut 3 (GaloisField 2 n) σ) := by rw [hform]
      _ = MulAut.congr e.symm (MulAut.conj y * fieldAut 3 (GaloisField 2 n) σ) := by
            rw [hy]
      _ = MulAut.congr e.symm (MulAut.conj y) *
            MulAut.congr e.symm (fieldAut 3 (GaloisField 2 n) σ) := map_mul _ _ _
      _ = MulAut.conj (e.symm y) * MulAut.congr e.symm (fieldAut 3 (GaloisField 2 n) σ) := by
            rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  ·
    exfalso
    rw [pow_one] at hform
    rw [hform] at hβ3
    obtain ⟨y₃, hy₃⟩ := hβ3
    obtain ⟨h₀, hh₀⟩ := proj_surjective 3 (GaloisField 2 n) y₃
    have hW0f : Module.finrank (GaloisField 2 n) (flagSpace 3 (GaloisField 2 n) 1) = 1 :=
      finrank_flagSpace (by norm_num)
    have hW0 : ⊥ < flagSpace 3 (GaloisField 2 n) 1 ∧
        flagSpace 3 (GaloisField 2 n) 1 < ⊤ :=
      kfl3_proper_of_finrank (by omega) (by omega)
    obtain ⟨U1, hU1, hd1, hU1θ⟩ := kfl3_flip_step A σ hW0
    obtain ⟨U2, hU2, hd2, hU2θ⟩ := kfl3_flip_step A σ hU1
    obtain ⟨U3, hU3, hd3, hU3θ⟩ := kfl3_flip_step A σ hU2
    have h3 := kfl3_map_pow3 (conjAut 3 (GaloisField 2 n) A * fieldAut 3 (GaloisField 2 n) σ *
      dualAut 3 (GaloisField 2 n)) (projStabilizer (flagSpace 3 (GaloisField 2 n) 1))
    rw [hU1θ, hU2θ, hU3θ] at h3
    have h4 : (projStabilizer (flagSpace 3 (GaloisField 2 n) 1)).map
        (MulAut.conj (proj 3 (GaloisField 2 n) h₀)).toMonoidHom = projStabilizer U3 := by
      rw [hh₀, hy₃]
      exact h3
    rw [kfl3_stab_conj_proj] at h4
    have hUV := kfl3_stab_inj (kfl3_proper_map (Matrix.SpecialLinearGroup.toGL h₀) hW0) hU3 h4
    have hfin := kfl3_finrank_eq hUV
    rw [kfl3_finrank_map] at hfin
    omega

end CFSG.RankThree.PartTwo.Late
