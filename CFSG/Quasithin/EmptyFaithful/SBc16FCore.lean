module

public import CFSG.Quasithin.EmptyFaithful.SBc16FDec
import CFSG.Quasithin.EmptyFaithful.SBc16FSyl
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.Quasithin

namespace SBc16

theorem transvection_pow_five : ∀ (i j : Fin 2) (c : ZMod 5), i ≠ j →
    (Matrix.transvection i j c : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 5 = 1 := by
  decide +kernel

theorem det_one_mem {K : Subgroup GL25} (hK : ∀ x : GL25, IsFive x → x ∈ K) :
    ∀ g : GL25, (g : Matrix (Fin 2) (Fin 2) (ZMod 5)).det = 1 → g ∈ K := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcl : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) (ZMod 5) →
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) (ZMod 5) →
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ≤
      K.comap (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* GL25) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    show Matrix.SpecialLinearGroup.toGL t.toSpecialLinearGroup ∈ K
    by_cases h1 : Matrix.SpecialLinearGroup.toGL t.toSpecialLinearGroup = 1
    · rw [h1]
      exact K.one_mem
    · refine hK _ ⟨?_, h1⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact transvection_pow_five t.i t.j t.c t.hij
  intro g hg
  have hmem : g ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* GL25).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact Units.ext hg
  obtain ⟨s, rfl⟩ := hmem
  exact hle (hcl ▸ Subgroup.mem_top s)

theorem card_det_ker :
    Nat.card (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker = 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := ZMod 5)
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv).toEquiv] at h
  have hu : Nat.card (ZMod 5)ˣ = 4 := by
    rw [Nat.card_units]
    simp
  rw [hu, card_GL25] at h
  omega

theorem exists_pow_mul_of_normal {K : Subgroup GL25} {u : GL25} (huK : u ∈ K) (hu : orderOf u = 5)
    (hnorm : (Subgroup.zpowers (⟨u, huK⟩ : K)).Normal) {g : GL25} (hg : g ∈ K) :
    ∃ k : ℕ, k < 5 ∧ g * u = u ^ k * g := by
  have h1 := hnorm.conj_mem ⟨u, huK⟩ (Subgroup.mem_zpowers _) ⟨g, hg⟩
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hz' : u ^ z = g * u * g⁻¹ := congrArg Subtype.val hz
  refine ⟨(z % 5).toNat, by omega, ?_⟩
  have h5 : u ^ ((z % 5).toNat) = u ^ z := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have := zpow_mod_orderOf u z
    rw [hu] at this
    simpa using this
  rw [h5, hz']
  group

theorem core_dvd (K : Subgroup GL25) (σ τ u : GL25) (hσK : σ ∈ K) (hτK : τ ∈ K) (huK : u ∈ K)
    (hu : orderOf u = 5)
    (hσ00 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1)
    (hσ01 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0)
    (hσ10 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0)
    (hσ11 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1)
    (hτ00 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = 0)
    (hτ11 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 0)
    (hτ01 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ≠ 0)
    (hτ10 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0) :
    16 ∣ Nat.card K := by
  have hFive : IsFive u := isFive_of_orderOf_eq_five hu
  have hmove : ¬ (Subgroup.zpowers (⟨u, huK⟩ : K)).Normal := fun hnorm =>
    not_both_normalize hσ00 hσ01 hσ10 hσ11 hτ00 hτ11 hτ01 hτ10 hFive
      ⟨exists_pow_mul_of_normal huK hu hnorm hσK, exists_pow_mul_of_normal huK hu hnorm hτK⟩
  have hall : ∀ x : GL25, IsFive x → x ∈ K := by
    intro x hx
    have := all_isFive_mem_range K.subtype (Subgroup.subtype_injective K) ⟨u, huK⟩ hFive hmove x hx
    simpa using this
  have hker : (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker ≤ K := by
    intro g hg
    refine det_one_mem hall g ?_
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    simpa using this
  have h120 : 120 ∣ Nat.card K := card_det_ker ▸ Subgroup.card_dvd_of_le hker
  have h480 : Nat.card K ∣ 480 := card_GL25 ▸ Subgroup.card_subgroup_dvd_card K
  have hne : Nat.card K ≠ 120 := by
    intro h
    have hKer : (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker = K :=
      Subgroup.eq_of_le_of_card_ge hker (by rw [h, card_det_ker])
    have hσ : σ ∈ (Matrix.GeneralLinearGroup.det : GL25 →* (ZMod 5)ˣ).ker := hKer ▸ hσK
    have hdet : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)).det = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hσ)
      simpa using this
    rw [Matrix.det_fin_two, hσ00, hσ01, hσ10, hσ11] at hdet
    revert hdet
    decide
  obtain ⟨m, hm⟩ := h120
  have hm4 : m ∣ 4 := by
    have h : 120 * m ∣ 120 * 4 := by
      rw [← hm]
      simpa using h480
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hm_le : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
  interval_cases m
  · exact absurd (by simpa using hm) Nat.card_pos.ne'
  · exact absurd (by omega) hne
  · rw [hm]
    norm_num
  · exact absurd hm4 (by norm_num)
  · rw [hm]
    norm_num

end SBc16

end CFSG.Quasithin
