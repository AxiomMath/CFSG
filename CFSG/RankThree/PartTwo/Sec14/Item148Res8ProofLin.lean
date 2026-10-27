module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinFix
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSubfieldCore
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof (subfieldProj subfieldProj_proj
  subfieldProj_injective)

variable {K : Type} [Field K]

theorem smul_mem_scalars {ζ : K} (hζ : ζ ^ 3 = 1) {A B : SpecialLinearGroup (Fin 3) K}
    (h : (B : Matrix (Fin 3) (Fin 3) K) = ζ • (A : Matrix (Fin 3) (Fin 3) K)) :
    A⁻¹ * B ∈ scalars 3 K := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  refine ⟨Units.mk0 ζ hζ0, Units.ext (by simpa using hζ), ?_⟩
  have hAi : ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have : ((A⁻¹ * A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  show ((A⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (ζ : K)
  rw [h, Matrix.mul_smul, hAi, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

variable [Finite K] [CharP K 2]

theorem overgroup_subfieldProj {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {n : ℕ} (hn : 2 ≤ n) (hF₀ : Nat.card (fixedField σ) = 2 ^ n) (hq : 2 ^ n % 3 = 1)
    (H : Subgroup (projectiveSL 3 K)) (hH : (subfieldProj σ).range ≤ H) :
    H = ⊤ ∨ (H ≤ Subgroup.normalizer ((subfieldProj σ).range : Set (projectiveSL 3 K)) ∧
      Nat.card H ∣ 3 * Nat.card (subfieldProj σ).range) := by
  set F₀ := fixedField σ with hF₀def
  have hK : Nat.card K = 2 ^ (3 * n) := by
    have h1 := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hF₀, ← pow_mul, mul_comm] at h1
    exact h1.symm
  have hσfix : ∀ x ∈ F₀, σ x = x := fun x hx => (CFSG.GH74.GLS.IVK.mem_fixedField_iff σ x).mp hx
  set P₀ := (subfieldProj σ).range with hP₀
  set ι := SpecialLinearGroup.map (n := Fin 3) F₀.subtype with hι
  set Ĥ := H.comap (proj 3 K) with hĤ
  have hιĤ : ι.range ≤ Ĥ := by
    rintro _ ⟨A, rfl⟩
    show proj 3 K (ι A) ∈ H
    rw [hι, ← subfieldProj_proj]
    exact hH ⟨_, rfl⟩
  have hFtr : ∀ (i j : Fin 3) (hij : i ≠ j) (a : K), a ∈ F₀ →
      SpecialLinearGroup.transvection hij a ∈ Ĥ := by
    intro i j hij a ha
    apply hιĤ
    exact ⟨SpecialLinearGroup.transvection hij ⟨a, ha⟩, map_subtype_transvection F₀ hij ⟨a, ha⟩⟩
  have hq2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  rcases rootSet_dichotomy Ĥ F₀ hq2 hF₀ (by rw [hK, pow_mul']) hFtr with hS | hall
  swap
  ·
    left
    have htop : Ĥ = ⊤ := by
      rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := K),
        Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      exact hall i j hij c
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := proj_surjective 3 K x
    have : g ∈ Ĥ := htop ▸ Subgroup.mem_top g
    exact this
  right
  have hsemi := fun (h : SpecialLinearGroup (Fin 3) K) (hh : h ∈ Ĥ) =>
    exists_map_eq_smul F₀ hn hF₀ hK Ĥ hιĤ hS σ hσfix hh
  have hfixed : ∀ g : SpecialLinearGroup (Fin 3) K, SpecialLinearGroup.map σ.toRingHom g = g →
      proj 3 K g ∈ P₀ := by
    intro g hg
    obtain ⟨A, hA⟩ := CFSG.RankThree.PartTwo.KFacts.exists_sl_map_subtype_eq hg
    exact ⟨proj 3 F₀ A, by rw [subfieldProj_proj, hA]⟩
  have hιfix : ∀ A : SpecialLinearGroup (Fin 3) F₀,
      SpecialLinearGroup.map σ.toRingHom (ι A) = ι A := by
    intro A
    apply Subtype.ext
    ext r c
    show σ ((A : Matrix (Fin 3) (Fin 3) F₀) r c : K) = ((A : Matrix (Fin 3) (Fin 3) F₀) r c : K)
    exact hσfix _ ((A : Matrix (Fin 3) (Fin 3) F₀) r c).2
  have hconj : ∀ h ∈ Ĥ, ∀ g : SpecialLinearGroup (Fin 3) K,
      SpecialLinearGroup.map σ.toRingHom g = g →
      SpecialLinearGroup.map σ.toRingHom (h * g * h⁻¹) = h * g * h⁻¹ := by
    intro h hh g hg
    obtain ⟨ζ, hζ3, hζ⟩ := hsemi h hh
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ3
    rw [map_mul, map_mul, hg, map_inv]
    apply Subtype.ext
    have hinv : ((SpecialLinearGroup.map σ.toRingHom h)⁻¹ : SpecialLinearGroup (Fin 3) K) =
        h⁻¹ * (SpecialLinearGroup.map σ.toRingHom h * h⁻¹)⁻¹ := by group
    set hM := (h : Matrix (Fin 3) (Fin 3) K)
    set hiM := ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    set sM := ((SpecialLinearGroup.map σ.toRingHom h : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
    set siM := (((SpecialLinearGroup.map σ.toRingHom h)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
    have hsi : sM * siM = 1 := by
      have : ((SpecialLinearGroup.map σ.toRingHom h * (SpecialLinearGroup.map σ.toRingHom h)⁻¹ :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [mul_inv_cancel]; rfl
      exact this
    have hih : hM * hiM = 1 := by
      have : ((h * h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [mul_inv_cancel]; rfl
      exact this
    have hsiM : siM = ζ⁻¹ • hiM := by
      have e : sM * (ζ⁻¹ • hiM) = 1 := by
        rw [hζ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hζ0, one_smul, hih]
      calc siM = siM * (sM * (ζ⁻¹ • hiM)) := by rw [e, Matrix.mul_one]
        _ = (siM * sM) * (ζ⁻¹ • hiM) := by rw [Matrix.mul_assoc]
        _ = ζ⁻¹ • hiM := by
            have : siM * sM = 1 := by
              have : (((SpecialLinearGroup.map σ.toRingHom h)⁻¹ *
                  SpecialLinearGroup.map σ.toRingHom h : SpecialLinearGroup (Fin 3) K) :
                  Matrix (Fin 3) (Fin 3) K) = 1 := by
                rw [inv_mul_cancel]; rfl
              exact this
            rw [this, Matrix.one_mul]
    show sM * (g : Matrix (Fin 3) (Fin 3) K) * siM = hM * g * hiM
    rw [hsiM, hζ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  have hconjP : ∀ x ∈ H, ∀ y ∈ P₀, x * y * x⁻¹ ∈ P₀ := by
    intro x hx y hy
    obtain ⟨h, rfl⟩ := proj_surjective 3 K x
    obtain ⟨y₀, rfl⟩ := hy
    obtain ⟨A, rfl⟩ := proj_surjective 3 F₀ y₀
    rw [subfieldProj_proj, ← map_inv, ← map_mul, ← map_mul]
    exact hfixed _ (hconj h hx _ (hιfix A))
  have hnorm : H ≤ Subgroup.normalizer (P₀ : Set (projectiveSL 3 K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconjP x hx y
    · intro hy
      have := hconjP x⁻¹ (H.inv_mem hx) _ hy
      simpa [mul_assoc] using this
  refine ⟨hnorm, ?_⟩
  have hcube : ∀ x ∈ H, x ^ 3 ∈ P₀ := by
    intro x hx
    obtain ⟨h, rfl⟩ := proj_surjective 3 K x
    rw [← map_pow]
    obtain ⟨ζ, hζ3, hζ⟩ := hsemi h hx
    apply hfixed
    rw [map_pow]
    apply Subtype.ext
    show ((SpecialLinearGroup.map σ.toRingHom h : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) ^ 3 = ((h : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) ^ 3
    rw [hζ, smul_pow, hζ3, one_smul]
  have hfix : H ≤ (fieldAut 3 K σ).toMonoidHom.eqLocus (MonoidHom.id (projectiveSL 3 K)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := proj_surjective 3 K x
    obtain ⟨ζ, hζ3, hζ⟩ := hsemi h hx
    show fieldAut 3 K σ (proj 3 K h) = proj 3 K h
    rw [fieldAut_proj, proj_eq_proj_iff]
    have := smul_mem_scalars (A := SpecialLinearGroup.map σ.toRingHom h) (B := h)
      (ζ := ζ⁻¹) (by rw [inv_pow, hζ3, inv_one]) (by
        have hζ0 : ζ ≠ 0 := by
          rintro rfl
          simp at hζ3
        rw [hζ, smul_smul, inv_mul_cancel₀ hζ0, one_smul])
    exact this
  have hP₀card : Nat.card P₀ = Nat.card (projectiveSL 3 F₀) :=
    (Nat.card_congr (MonoidHom.ofInjective (subfieldProj_injective σ)).toEquiv).symm
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) F₀) = 3 * Nat.card P₀ := by
    rw [hP₀card, card_projectiveSL, card_scalars_eq_gcd F₀ (by norm_num), hF₀]
    have hg : Nat.gcd 3 (2 ^ n - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hg]
    have hdvd : 3 ∣ Nat.card (SpecialLinearGroup (Fin 3) F₀) := by
      have h3 := card_scalars_eq_gcd F₀ (n := 3) (by norm_num)
      rw [hF₀, hg] at h3
      have := Subgroup.card_subgroup_dvd_card (scalars 3 F₀)
      rwa [h3] at this
    exact (Nat.mul_div_cancel' hdvd).symm
  have hle : Nat.card H ≤ 3 * Nat.card P₀ := by
    rw [← hSL]
    exact (Subgroup.card_le_of_le hfix).trans
      (CFSG.RankThree.PartTwo.Sec14.Item148Res5.card_eqLocus_fieldAut_le σ)
  set P₀' := P₀.subgroupOf H with hP₀'
  have hcardP₀' : Nat.card P₀' = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hidx := Subgroup.card_mul_index P₀'
  rw [hcardP₀'] at hidx
  have hpos : 0 < Nat.card P₀ := Nat.card_pos
  have hidx3 : P₀'.index ≤ 3 := by
    by_contra hcon
    have hcon : 3 < P₀'.index := Nat.lt_of_not_le hcon
    have : 3 * Nat.card P₀ < Nat.card H := by
      rw [← hidx]
      nlinarith
    omega
  have hidx2 : P₀'.index ≠ 2 := by
    intro h2
    have hall : ∀ x : H, x ∈ P₀' := by
      intro x
      have hsq := Subgroup.sq_mem_of_index_two h2 x
      have hcb : x ^ 3 ∈ P₀' := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hcube x x.2
      have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
      rw [this]
      exact P₀'.mul_mem hcb (P₀'.inv_mem hsq)
    have htop : P₀' = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at h2
    omega
  have hidx0 : P₀'.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rw [← hidx]
  interval_cases h : P₀'.index
  · omega
  · rw [mul_one]
    exact Dvd.intro_left 3 rfl
  · omega
  · rw [mul_comm]

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
