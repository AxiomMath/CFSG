module

public import CFSG.Fischer.F4
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLevelCount
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (torusSU diagU ent)

private def rhoTFrame_lg (u : F4ˣ) : ZMod 3 :=
  if u = 1 then 0 else if (u : F4) = F4.ω then 1 else 2

private theorem rhoTFrame_lg_mul : ∀ a b : F4ˣ, rhoTFrame_lg (a * b) = rhoTFrame_lg a +
    rhoTFrame_lg b := by decide

private theorem rhoTFrame_lg_inj : ∀ a b : F4ˣ, rhoTFrame_lg a = rhoTFrame_lg b → a = b := by
  decide

private theorem rhoTFrame_lg_surj : ∀ t : ZMod 3, ∃ u : F4ˣ, rhoTFrame_lg u = t := by decide

private theorem rhoTFrame_lg_one : rhoTFrame_lg 1 = 0 := by decide

private theorem rhoTFrame_exists_unit : ∃ u : F4ˣ, u ^ 3 = 1 ∧ u ^ 2 ≠ 1 := by
  have h1 : (F4.ω : F4) ^ 3 = 1 := by decide
  have h3 : (F4.ω : F4) ^ 2 ≠ 1 := by decide
  have h0 : (F4.ω : F4) ≠ 0 := by decide
  refine ⟨Units.mk0 F4.ω h0, Units.ext (by simpa using h1), fun h => h3 ?_⟩
  simpa using congrArg Units.val h

private theorem rhoTFrame_isDiag_of_mem {g : GL (Fin 6) F4} (hg : g ∈ torusSU 3 6 F4) :
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).IsDiag := by
  obtain ⟨d, -, -, rfl⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.1 hg
  exact CFSG.RankThree.PartOne.KFU.isDiag_diagU d

private theorem rhoTFrame_perm_of_normalizes {M : GL (Fin 6) F4}
    (hM : ∀ d ∈ torusSU 3 6 F4, M * d * M⁻¹ ∈ torusSU 3 6 F4)
    (hM' : ∀ d ∈ torusSU 3 6 F4, M⁻¹ * d * M ∈ torusSU 3 6 F4) :
    ∃ π : Equiv.Perm (Fin 6), (∀ i, ent M (π i) i ≠ 0) ∧ (∀ i k, ent M k i ≠ 0 → k = π i) ∧
      ∀ g ∈ torusSU 3 6 F4, ∀ i, ent (M * g * M⁻¹) (π i) (π i) = ent g i i := by
  obtain ⟨u, hu3, hu2⟩ := rhoTFrame_exists_unit
  exact CFSG.RankThree.PartOne.KFU.exists_perm_of_normalizes (torusSU 3 6 F4)
    (fun g hg => rhoTFrame_isDiag_of_mem hg)
    (fun i j hij => CFSG.RankThree.PartOne.KFU.torusSU_char_distinct hu3 hu2 hij) hM hM'

private theorem rhoTFrame_shift {M : GL (Fin 6) F4} {π : Equiv.Perm (Fin 6)}
    (hπ : ∀ i, ent M (π i) i ≠ 0) {wd : Fin 6 → F4ˣ} {c : F4}
    (hc : ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      (M : Matrix (Fin 6) (Fin 6) F4) = c • ((M : Matrix (Fin 6) (Fin 6) F4) *
        ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))) (k : Fin 6) :
    (wd (π k) : F4) = c * wd k := by
  have h1 := congrFun (congrFun hc (π k)) k
  simp only [CFSG.RankThree.PartOne.KFU.diagU_val, Matrix.diagonal_mul, Matrix.smul_apply,
    Matrix.mul_diagonal, smul_eq_mul] at h1
  exact mul_right_cancel₀ (hπ k) (h1.trans (by ring))

private theorem rhoTFrame_conj_eq_of_perm {M N : GL (Fin 6) F4} {π : Equiv.Perm (Fin 6)}
    (hM : ∀ d ∈ torusSU 3 6 F4, M * d * M⁻¹ ∈ torusSU 3 6 F4)
    (hN : ∀ d ∈ torusSU 3 6 F4, N * d * N⁻¹ ∈ torusSU 3 6 F4)
    (hMπ : ∀ g ∈ torusSU 3 6 F4, ∀ i, ent (M * g * M⁻¹) (π i) (π i) = ent g i i)
    (hNπ : ∀ g ∈ torusSU 3 6 F4, ∀ i, ent (N * g * N⁻¹) (π i) (π i) = ent g i i)
    {d : GL (Fin 6) F4} (hd : d ∈ torusSU 3 6 F4) : M * d * M⁻¹ = N * d * N⁻¹ := by
  have hdM := rhoTFrame_isDiag_of_mem (hM d hd)
  have hdN := rhoTFrame_isDiag_of_mem (hN d hd)
  apply Units.ext
  ext k l
  by_cases hkl : k = l
  · subst hkl
    obtain ⟨i, rfl⟩ := π.surjective k
    exact (hMπ d hd i).trans (hNπ d hd i).symm
  · rw [hdM hkl, hdN hkl]

theorem rhoTFrame_pattern_core {ι : Type} (T : Finset ι) (hT : 120 ≤ T.card)
    (M : ι → GL (Fin 6) F4)
    (hM : ∀ i ∈ T, ∀ d ∈ torusSU 3 6 F4, M i * d * (M i)⁻¹ ∈ torusSU 3 6 F4)
    (hM' : ∀ i ∈ T, ∀ d ∈ torusSU 3 6 F4, (M i)⁻¹ * d * M i ∈ torusSU 3 6 F4)
    (wd : Fin 6 → F4ˣ)
    (hw : ∀ i ∈ T, ∃ c : F4, c ≠ 0 ∧
      ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (M i : Matrix (Fin 6) (Fin 6) F4) = c • ((M i : Matrix (Fin 6) (Fin 6) F4) *
          ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)))
    (hinj : ∀ i ∈ T, ∀ j ∈ T,
      (∀ d ∈ torusSU 3 6 F4, M i * d * (M i)⁻¹ = M j * d * (M j)⁻¹) → i = j) :
    (∃ c : F4ˣ, ∀ k, wd k = c) ∨
      ∃ (k₀ : Fin 6) (c u : F4ˣ), u ≠ 1 ∧ ∀ k, wd k = if k = k₀ then c * u else c := by
  classical
  have hex : ∀ i, ∃ π : Equiv.Perm (Fin 6), i ∈ T →
      ((∀ l, ent (M i) (π l) l ≠ 0) ∧
        ∀ g ∈ torusSU 3 6 F4, ∀ l, ent (M i * g * (M i)⁻¹) (π l) (π l) = ent g l l) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨π, h1, -, h3⟩ := rhoTFrame_perm_of_normalizes (hM i hi) (hM' i hi)
      exact ⟨π, fun _ => ⟨h1, h3⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose π hπ using hex
  have hinjOn : Set.InjOn π (T : Set ι) := by
    intro i hi j hj hij
    refine hinj i hi j hj fun d hd => ?_
    refine rhoTFrame_conj_eq_of_perm (hM i hi) (hM j hj) (hπ i hi).2 ?_ hd
    rw [hij]
    exact (hπ j hj).2
  have hcard : 120 ≤ (T.image π).card := by
    rw [Finset.card_image_of_injOn hinjOn]
    exact hT
  have hv : ∀ p ∈ T.image π, ∃ c : ZMod 3,
      ∀ k, rhoTFrame_lg (wd (p k)) = rhoTFrame_lg (wd k) + c := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨c, hc0, hc⟩ := hw i hi
    refine ⟨rhoTFrame_lg (Units.mk0 c hc0), fun k => ?_⟩
    have hk : wd (π i k) = Units.mk0 c hc0 * wd k :=
      Units.ext (rhoTFrame_shift (hπ i hi).1 hc k)
    rw [hk, rhoTFrame_lg_mul, add_comm]
  rcases eq_const_or_single_of_le_card (v := fun k => rhoTFrame_lg (wd k)) hcard hv with
    ⟨c, hc⟩ | ⟨i₀, c, s, hs, hvs⟩
  · left
    exact ⟨wd 0, fun k => rhoTFrame_lg_inj _ _ ((hc k).trans (hc 0).symm)⟩
  · right
    obtain ⟨cu, hcu⟩ := rhoTFrame_lg_surj c
    obtain ⟨uu, huu⟩ := rhoTFrame_lg_surj s
    refine ⟨i₀, cu, uu, fun h => hs ?_, fun k => rhoTFrame_lg_inj _ _ ?_⟩
    · rw [← huu, h, rhoTFrame_lg_one]
    · rw [hvs k]
      by_cases hk : k = i₀
      · simp [hk, rhoTFrame_lg_mul, hcu, huu]
      · simp [hk, hcu]

end CFSG.GGQ2Prime
