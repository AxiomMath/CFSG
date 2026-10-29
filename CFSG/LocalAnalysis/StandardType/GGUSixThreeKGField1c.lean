module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGField1

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

open Polynomial
open Module
open scoped BigOperators

variable {K : Type} [Field K]

private lemma one_add_add_sq_eq_zero {r : K} (hr : r ^ 3 = 1) (hr1 : r ≠ 1) :
    1 + r + r ^ 2 = 0 := by
  have h : (1 + r + r ^ 2) * (1 - r) = 0 := by
    have e : (1 + r + r ^ 2) * (1 - r) = 1 - r ^ 3 := by ring
    rw [e, hr, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hr1

private lemma exists_pow_cube_root {r q : K} (hr : r ^ 3 = 1) (hr1 : r ≠ 1)
    (hq : q ^ 3 = 1) : ∃ k : ℕ, r ^ k = q := by
  have hsum := one_add_add_sq_eq_zero hr hr1
  have h : (q - 1) * (q - r) * (q - r ^ 2) = 0 := by
    have e : (q - 1) * (q - r) * (q - r ^ 2)
        = q ^ 3 - (1 + r + r ^ 2) * q ^ 2 + (r + r ^ 2 + r ^ 3) * q - r ^ 3 := by ring
    have hr2 : r + r ^ 2 + 1 = 0 := by linear_combination hsum
    rw [e, hsum, hq, hr, hr2]
    ring
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ⟨0, by rw [pow_zero, sub_eq_zero.mp h2]⟩
    · exact ⟨1, by rw [pow_one, sub_eq_zero.mp h2]⟩
  · exact ⟨2, by rw [sub_eq_zero.mp h1]⟩

section Decomp

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private lemma ker_aeval_X_sub_C (f : Module.End K V) (a : K) :
    (aeval f (X - C a)).ker = f.eigenspace a := by
  simp only [Module.End.eigenspace, Module.End.genEigenspace_one, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one]

private lemma coprime_sub_C {a b : K} (h : a ≠ b) :
    IsCoprime (X - C a : K[X]) (X - C b) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.mpr h))

private lemma eigenspace_sup_eq_top (f : Module.End K V) (hf : f ^ 3 = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    f.eigenspace 1 ⊔ f.eigenspace ζ ⊔ f.eigenspace (ζ ^ 2) = ⊤ := by
  have hfac : (X ^ 3 - 1 : K[X]) = (X - C 1) * (X - C ζ) * (X - C (ζ ^ 2)) := by
    have h := X_pow_sub_C_eq_prod hζ (α := (1 : K)) (a := (1 : K)) (by norm_num) (by norm_num)
    simpa [Finset.prod_range_succ, map_one] using h
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h23 := hζ.dvd_of_pow_eq_one 2 h
    norm_num at h23
  have hζne : ζ ≠ ζ ^ 2 := fun h => by
    have h2 : ζ ^ 2 = ζ ^ 1 := by rw [pow_one]; exact h.symm
    exact absurd (hζ.pow_inj (by norm_num) (by norm_num) h2) (by norm_num)
  have hc1 : IsCoprime (X - C 1) (X - C ζ) := coprime_sub_C hζ1.symm
  have hc2 : IsCoprime (X - C 1) (X - C (ζ ^ 2)) := coprime_sub_C (fun h => hζ2 h.symm)
  have hc3 : IsCoprime (X - C ζ) (X - C (ζ ^ 2)) := coprime_sub_C hζne
  have hc12 : IsCoprime ((X - C 1) * (X - C ζ)) (X - C (ζ ^ 2)) := hc2.mul_left hc3
  have hsup1 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc1
  have hsup2 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc12
  rw [← ker_aeval_X_sub_C f 1, ← ker_aeval_X_sub_C f ζ, ← ker_aeval_X_sub_C f (ζ ^ 2),
    hsup1, hsup2]
  have hprod : ((X - C 1) * (X - C ζ)) * (X - C (ζ ^ 2)) = X ^ 3 - 1 := by
    rw [← hfac]
  rw [hprod]
  have hzero : aeval f (X ^ 3 - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hf, sub_self]
  rw [hzero, LinearMap.ker_zero]

private lemma finrank_eigenspace_sum (f : Module.End K V) (hf : f ^ 3 = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    finrank K (f.eigenspace 1) + finrank K (f.eigenspace ζ)
      + finrank K (f.eigenspace (ζ ^ 2)) = finrank K V := by
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h23 := hζ.dvd_of_pow_eq_one 2 h
    norm_num at h23
  have hζne : ζ ≠ ζ ^ 2 := fun h => by
    have h2 : ζ ^ 2 = ζ ^ 1 := by rw [pow_one]; exact h.symm
    exact absurd (hζ.pow_inj (by norm_num) (by norm_num) h2) (by norm_num)
  have hc1 : IsCoprime (X - C 1) (X - C ζ) := coprime_sub_C hζ1.symm
  have hc2 : IsCoprime (X - C 1) (X - C (ζ ^ 2)) := coprime_sub_C (fun h => hζ2 h.symm)
  have hc3 : IsCoprime (X - C ζ) (X - C (ζ ^ 2)) := coprime_sub_C hζne
  have hc12 : IsCoprime ((X - C 1) * (X - C ζ)) (X - C (ζ ^ 2)) := hc2.mul_left hc3
  have hd12 : Disjoint (f.eigenspace 1) (f.eigenspace ζ) := by
    have h := Polynomial.disjoint_ker_aeval_of_isCoprime f hc1
    rwa [ker_aeval_X_sub_C, ker_aeval_X_sub_C] at h
  have hd3 : Disjoint (f.eigenspace 1 ⊔ f.eigenspace ζ) (f.eigenspace (ζ ^ 2)) := by
    have h := Polynomial.disjoint_ker_aeval_of_isCoprime f hc12
    rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc1,
      ker_aeval_X_sub_C, ker_aeval_X_sub_C, ker_aeval_X_sub_C] at h
    exact h
  have htop := eigenspace_sup_eq_top f hf hζ
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace 1) (f.eigenspace ζ)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace 1 ⊔ f.eigenspace ζ)
    (f.eigenspace (ζ ^ 2))
  have hi1 : f.eigenspace 1 ⊓ f.eigenspace ζ = ⊥ := disjoint_iff.mp hd12
  have hi3 : (f.eigenspace 1 ⊔ f.eigenspace ζ) ⊓ f.eigenspace (ζ ^ 2) = ⊥ := disjoint_iff.mp hd3
  rw [hi1] at h1
  rw [hi3, htop] at h2
  have hbot : finrank K (⊥ : Submodule K V) = 0 := Submodule.finrank_eq_zero.mpr rfl
  have htop' : finrank K (⊤ : Submodule K V) = finrank K V :=
    (Submodule.topEquiv (R := K) (M := V)).finrank_eq
  rw [hbot] at h1
  rw [hbot, htop'] at h2
  omega

private lemma genEigenspace_one_iSup_eq_top (h : Module.End K V) (hh : h ^ 3 = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    (⨆ μ : K, (h.genEigenspace μ) (1 : ℕ∞)) = ⊤ := by
  have htop := eigenspace_sup_eq_top h hh hζ
  have heig : (⨆ μ : K, h.eigenspace μ) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← htop]
    exact sup_le (sup_le (le_iSup _ 1) (le_iSup _ ζ)) (le_iSup _ (ζ ^ 2))
  simpa only [Module.End.eigenspace] using heig

private lemma exists_smul_on_invariant_eigenspace (f h M : Module.End K V)
    [FiniteDimensional K V] (hf : f ^ 3 = 1) (hh : h ^ 3 = 1) (hfh : h * f = f * h)
    {l : K} (hM : M ^ 3 = algebraMap K (Module.End K V) l) (hl : ∀ c : K, c ^ 3 ≠ l)
    (hMf : M * f = f * M) (hMh : M * h = h * M)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {c : K}
    (hc : finrank K (f.eigenspace c) = 3) :
    ∃ d : K, d ^ 3 = 1 ∧ ∀ v ∈ f.eigenspace c, h v = d • v := by
  have hE : ∀ v ∈ f.eigenspace c, h v ∈ f.eigenspace c := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h2 : (f * h) v = (h * f) v := by rw [hfh]
    rw [Module.End.mul_apply, Module.End.mul_apply] at h2
    rw [h2, hv, map_smul]
  have hEbot : f.eigenspace c ≠ ⊥ := by
    intro hbot
    rw [hbot] at hc
    simp at hc
  have hgen := genEigenspace_one_iSup_eq_top h hh hζ
  have hEq : f.eigenspace c
      = ⨆ μ : K, f.eigenspace c ⊓ (h.genEigenspace μ) (1 : ℕ∞) :=
    Submodule.eq_iSup_inf_genEigenspace (1 : ℕ∞) hE hgen
  have hex : ∃ μ : K, f.eigenspace c ⊓ (h.genEigenspace μ) 1 ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hEbot
    rw [hEq]
    exact iSup_eq_bot.mpr hcon
  obtain ⟨μ, hμ⟩ := hex
  have hMW : ∀ v ∈ f.eigenspace c ⊓ (h.genEigenspace μ) 1,
      M v ∈ f.eigenspace c ⊓ (h.genEigenspace μ) 1 := by
    intro v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have h2 : (f * M) v = (M * f) v := by rw [hMf]
      rw [Module.End.mul_apply, Module.End.mul_apply] at h2
      rw [h2, hv.1, map_smul]
    · have hv2 : h v = μ • v := Module.End.mem_eigenspace_iff.mp hv.2
      rw [Module.End.mem_eigenspace_iff]
      have h2 : (h * M) v = (M * h) v := by rw [hMh]
      rw [Module.End.mul_apply, Module.End.mul_apply] at h2
      rw [h2, hv2, map_smul]
  have hμ3 : μ ^ 3 = 1 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    rw [Submodule.mem_inf] at hv
    have hvμ : h v = μ • v := Module.End.mem_eigenspace_iff.mp hv.2
    have hpow : ∀ n : ℕ, (h ^ n) v = μ ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hvμ, smul_smul, pow_succ]
    have h3 := hpow 3
    rw [hh] at h3
    have hzero : (μ ^ 3 - 1) • v = 0 := by
      have hv1 : μ ^ 3 • v = v := by rw [← h3]; simp
      rw [sub_smul, one_smul, hv1, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  have hle : finrank K ↥(f.eigenspace c ⊓ (h.genEigenspace μ) 1) ≤ 3 := by
    rw [← hc]
    exact Submodule.finrank_mono inf_le_left
  have hdvd : 3 ∣ finrank K ↥(f.eigenspace c ⊓ (h.genEigenspace μ) 1) :=
    three_dvd_finrank_of_invariant hl hM _ hMW
  have hpos : 0 < finrank K ↥(f.eigenspace c ⊓ (h.genEigenspace μ) 1) :=
    Nat.pos_of_ne_zero fun h0 => hμ (Submodule.finrank_eq_zero.mp h0)
  have heq : finrank K ↥(f.eigenspace c ⊓ (h.genEigenspace μ) 1) = 3 := by
    obtain ⟨a, ha⟩ := hdvd
    omega
  have hWeq : f.eigenspace c ⊓ (h.genEigenspace μ) 1 = f.eigenspace c :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hc])
  refine ⟨μ, hμ3, ?_⟩
  intro v hv
  have hv' : v ∈ h.eigenspace μ := by
    have : v ∈ f.eigenspace c ⊓ (h.genEigenspace μ) 1 := by rw [hWeq]; exact hv
    rw [Submodule.mem_inf] at this
    exact this.2
  exact Module.End.mem_eigenspace_iff.mp hv'

end Decomp

section Match

variable {V : Type*} [AddCommGroup V] [Module K V]

private lemma exists_scalar_pow_of_two_eigenspaces {f h : Module.End K V}
    {U W : Submodule K V} {a b : K} (hU : U ⊔ W = ⊤) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a ≠ b) (hfU : ∀ v ∈ U, f v = a • v) (hfW : ∀ v ∈ W, f v = b • v)
    (hhU : ∃ d : K, d ^ 3 = 1 ∧ ∀ v ∈ U, h v = d • v)
    (hhW : ∃ e : K, e ^ 3 = 1 ∧ ∀ v ∈ W, h v = e • v) :
    ∃ (c : K) (k : ℕ), c ^ 3 = 1 ∧ h = (c • 1) * f ^ k := by
  obtain ⟨d, hd, hhd⟩ := hhU
  obtain ⟨e, he, hhe⟩ := hhW
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at ha; exact one_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hb; exact one_ne_zero hb.symm
  have hd0 : d ≠ 0 := by rintro rfl; rw [zero_pow (by norm_num)] at hd; exact one_ne_zero hd.symm
  have hr3 : (a * b⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hb, inv_one, ha, mul_one]
  have hr1 : a * b⁻¹ ≠ 1 := by
    intro hh
    apply hab
    calc a = (a * b⁻¹) * b := by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
      _ = 1 * b := by rw [hh]
      _ = b := one_mul b
  have hq3 : (d * e⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, he, inv_one, hd, mul_one]
  obtain ⟨k, hkq⟩ := exists_pow_cube_root hr3 hr1 hq3
  have hkq' : b ^ k * (a ^ k)⁻¹ = e * d⁻¹ := by
    have h := congrArg Inv.inv hkq
    rw [mul_pow, inv_pow, mul_inv, inv_inv, mul_inv, inv_inv] at h
    rw [mul_comm ((a ^ k)⁻¹) (b ^ k), mul_comm d⁻¹ e] at h
    exact h
  have hckb : (d * (a ^ k)⁻¹) * b ^ k = e := by
    rw [mul_assoc, mul_comm ((a ^ k)⁻¹) (b ^ k), hkq', ← mul_assoc, mul_comm d e, mul_assoc,
      mul_inv_cancel₀ hd0, mul_one]
  have hfpowU : ∀ n : ℕ, ∀ v ∈ U, (f ^ n) v = a ^ n • v := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply, ih v hv, map_smul, hfU v hv, smul_smul, pow_succ]
  have hfpowW : ∀ n : ℕ, ∀ v ∈ W, (f ^ n) v = b ^ n • v := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply, ih v hv, map_smul, hfW v hv, smul_smul, pow_succ]
  refine ⟨d * (a ^ k)⁻¹, k, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm k 3, pow_mul, ha, one_pow, inv_one, hd, mul_one]
  · apply LinearMap.ext
    intro v
    rcases Submodule.mem_sup.mp (hU ▸ Submodule.mem_top (x := v)) with ⟨u, hu, w, hw, rfl⟩
    rw [map_add, map_add]
    congr 1
    · rw [hhd u hu, show (((d * (a ^ k)⁻¹) • 1) * f ^ k) u
          = (d * (a ^ k)⁻¹) • ((f ^ k) u) from by
            rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply],
        hfpowU k u hu, smul_smul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k ha0), mul_one]
    · rw [hhe w hw, show (((d * (a ^ k)⁻¹) • 1) * f ^ k) w
          = (d * (a ^ k)⁻¹) • ((f ^ k) w) from by
            rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply],
        hfpowW k w hw, smul_smul, hckb]

end Match

private lemma toLin'_scalar_eq_algebraMap (a : K) :
    Matrix.toLin' (Matrix.scalar (Fin 6) a : Matrix (Fin 6) (Fin 6) K) =
      algebraMap K (Module.End K (Fin 6 → K)) a := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [show (Matrix.scalar (Fin 6) a : Matrix (Fin 6) (Fin 6) K) = a • 1 by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]]
  rw [map_smul, Matrix.toLin'_one]
  rfl

private lemma eq_scalar_mul_pow_of_end {A B : GL (Fin 6) K} {c : K} {k : ℕ}
    (hc : c ^ 3 = 1)
    (h : (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K) : Module.End K (Fin 6 → K)) =
      (c • 1) * (Matrix.toLin' (B : Matrix (Fin 6) (Fin 6) K)) ^ k) :
    ∃ (c' : Kˣ) (k : ℕ), A = GeneralLinearGroup.scalar (Fin 6) c' * B ^ k := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hc
    exact one_ne_zero hc.symm
  refine ⟨Units.mk0 c hc0, k, ?_⟩
  refine Units.ext ?_
  have hmat : (A : Matrix (Fin 6) (Fin 6) K) =
      Matrix.scalar (Fin 6) c * (B : Matrix (Fin 6) (Fin 6) K) ^ k := by
    apply (LinearEquiv.injective Matrix.toLin')
    rw [Matrix.toLin'_mul, Matrix.toLin'_pow, ← Module.End.mul_eq_comp]
    rw [toLin'_scalar_eq_algebraMap, Algebra.algebraMap_eq_smul_one, ← h]
  rw [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hmat

theorem exists_eq_scalar_mul_pow_of_commute {M g g' : GL (Fin 6) K} {l ζ : Kˣ}
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) (hM : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hζ : IsPrimitiveRoot ζ 3) (hg3 : g ^ 3 = 1) (hg3' : g' ^ 3 = 1) (hgM : g * M = M * g)
    (hg'M : g' * M = M * g') (hgg' : g * g' = g' * g) (hgs : g ∉ LargeEvenScalars (Fin 6) K) :
    ∃ (c : Kˣ) (k : ℕ), g' = GeneralLinearGroup.scalar (Fin 6) c * g ^ k := by
  have hζK : IsPrimitiveRoot (ζ : K) 3 := by
    refine ⟨?_, ?_⟩
    · have h := hζ.pow_eq_one
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    · intro m hm
      apply hζ.dvd_of_pow_eq_one
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hm
  set f : Module.End K (Fin 6 → K) := Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K) with hfdef
  set f' : Module.End K (Fin 6 → K) := Matrix.toLin' (g' : Matrix (Fin 6) (Fin 6) K) with hf'def
  set M' : Module.End K (Fin 6 → K) := Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K) with hMdef
  have hgm : (g : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hg'm : (g' : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3', Units.val_one]
  have hMm : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 = Matrix.scalar (Fin 6) (l : K) := by
    rw [← Units.val_pow_eq_pow_val, hM]
    exact GeneralLinearGroup.coe_scalar l
  have hf3 : f ^ 3 = 1 := by
    rw [hfdef, ← Matrix.toLin'_pow, hgm, Matrix.toLin'_one]; rfl
  have hf'3 : f' ^ 3 = 1 := by
    rw [hf'def, ← Matrix.toLin'_pow, hg'm, Matrix.toLin'_one]; rfl
  have hM'3 : M' ^ 3 = algebraMap K (Module.End K (Fin 6 → K)) (l : K) := by
    rw [hMdef, ← Matrix.toLin'_pow, hMm, toLin'_scalar_eq_algebraMap]
  have hmul : ∀ A B : Matrix (Fin 6) (Fin 6) K,
      (Matrix.toLin' A : Module.End K (Fin 6 → K)) * Matrix.toLin' B =
        Matrix.toLin' (A * B) := by
    intro A B
    rw [Module.End.mul_eq_comp, Matrix.toLin'_mul]
  have hMf : M' * f = f * M' := by
    rw [hfdef, hMdef, hmul, hmul]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul, hgM]
  have hMf' : M' * f' = f' * M' := by
    rw [hf'def, hMdef, hmul, hmul]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul, hg'M]
  have hff' : f * f' = f' * f := by
    rw [hfdef, hf'def, hmul, hmul]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul, hgg']
  have hlK : ∀ c : K, c ^ 3 ≠ (l : K) := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hc
      exact l.ne_zero hc.symm
    exact hl (Units.mk0 c hc0) (Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc))
  have hV6 : finrank K (Fin 6 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hdsum : finrank K (f.eigenspace 1) + finrank K (f.eigenspace (ζ : K))
      + finrank K (f.eigenspace ((ζ : K) ^ 2)) = 6 := by
    rw [finrank_eigenspace_sum f hf3 hζK, hV6]
  have hM_inv (c : K) : ∀ v ∈ f.eigenspace c, M' v ∈ f.eigenspace c := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h2 : (f * M') v = (M' * f) v := by rw [hMf]
    rw [Module.End.mul_apply, Module.End.mul_apply] at h2
    rw [h2, hv, map_smul]
  have hdiv1 : 3 ∣ finrank K (f.eigenspace 1) :=
    three_dvd_finrank_of_invariant hlK hM'3 _ (hM_inv 1)
  have hdiv2 : 3 ∣ finrank K (f.eigenspace (ζ : K)) :=
    three_dvd_finrank_of_invariant hlK hM'3 _ (hM_inv (ζ : K))
  have hdiv3 : 3 ∣ finrank K (f.eigenspace ((ζ : K) ^ 2)) :=
    three_dvd_finrank_of_invariant hlK hM'3 _ (hM_inv ((ζ : K) ^ 2))
  have hnscalar : ∀ a : K, a ^ 3 = 1 → f ≠ algebraMap K (Module.End K (Fin 6 → K)) a := by
    intro a ha hcontra
    apply hgs
    rw [CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at ha
      exact one_ne_zero ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    have hmat : Matrix.scalar (Fin 6) a = (g : Matrix (Fin 6) (Fin 6) K) := by
      apply (LinearEquiv.injective Matrix.toLin')
      rw [toLin'_scalar_eq_algebraMap, ← hfdef]
      exact hcontra.symm
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hmat
  have hζ23 : ((ζ : K) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hζK.pow_eq_one, one_pow]
  have htopE : f.eigenspace 1 ≠ ⊤ := by
    intro htop
    refine hnscalar 1 (one_pow 3) ?_
    apply LinearMap.ext
    intro v
    have hv : v ∈ f.eigenspace 1 := by rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv
  have htopE2 : f.eigenspace (ζ : K) ≠ ⊤ := by
    intro htop
    refine hnscalar (ζ : K) hζK.pow_eq_one ?_
    apply LinearMap.ext
    intro v
    have hv : v ∈ f.eigenspace (ζ : K) := by rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv
  have htopE3 : f.eigenspace ((ζ : K) ^ 2) ≠ ⊤ := by
    intro htop
    refine hnscalar ((ζ : K) ^ 2) hζ23 ?_
    apply LinearMap.ext
    intro v
    have hv : v ∈ f.eigenspace ((ζ : K) ^ 2) := by rw [htop]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [Module.algebraMap_end_apply]
    exact hv
  have hd1lt : finrank K (f.eigenspace 1) ≠ 6 := fun h =>
    htopE (Submodule.eq_top_of_finrank_eq (by rw [h, hV6]))
  have hd2lt : finrank K (f.eigenspace (ζ : K)) ≠ 6 := fun h =>
    htopE2 (Submodule.eq_top_of_finrank_eq (by rw [h, hV6]))
  have hd3lt : finrank K (f.eigenspace ((ζ : K) ^ 2)) ≠ 6 := fun h =>
    htopE3 (Submodule.eq_top_of_finrank_eq (by rw [h, hV6]))
  have hone : (finrank K (f.eigenspace 1) ≠ 0 ∧ finrank K (f.eigenspace (ζ : K)) ≠ 0)
      ∨ (finrank K (f.eigenspace 1) ≠ 0 ∧ finrank K (f.eigenspace ((ζ : K) ^ 2)) ≠ 0)
      ∨ (finrank K (f.eigenspace (ζ : K)) ≠ 0
        ∧ finrank K (f.eigenspace ((ζ : K) ^ 2)) ≠ 0) := by
    obtain ⟨a1, ha1⟩ := hdiv1
    obtain ⟨a2, ha2⟩ := hdiv2
    obtain ⟨a3, ha3⟩ := hdiv3
    rw [ha1] at hd1lt
    rw [ha2] at hd2lt
    rw [ha3] at hd3lt
    rw [ha1, ha2, ha3] at hdsum
    omega
  have hζ2 : ((ζ : K) ^ 2) ^ 3 = 1 := hζ23
  have h1neζ : (1 : K) ≠ ζ := (hζK.ne_one (by norm_num)).symm
  have h1neζ2 : (1 : K) ≠ (ζ : K) ^ 2 := by
    intro hcon
    have h := hζK.dvd_of_pow_eq_one 2 hcon.symm
    norm_num at h
  have hζneζ2 : (ζ : K) ≠ (ζ : K) ^ 2 := by
    intro hcon
    have h2 : (ζ : K) ^ 2 = (ζ : K) ^ 1 := by rw [pow_one]; exact hcon.symm
    exact absurd (hζK.pow_inj (by norm_num) (by norm_num) h2) (by norm_num)
  rcases hone with ⟨hn1, hn2⟩ | ⟨hn1, hn3⟩ | ⟨hn2, hn3⟩
  · have hd1 : finrank K (f.eigenspace 1) = 3 := by
      obtain ⟨a1, ha1⟩ := hdiv1; omega
    have hd2 : finrank K (f.eigenspace (ζ : K)) = 3 := by
      obtain ⟨a2, ha2⟩ := hdiv2; omega
    have hb3 : f.eigenspace ((ζ : K) ^ 2) = ⊥ := by
      have : finrank K (f.eigenspace ((ζ : K) ^ 2)) = 0 := by
        obtain ⟨a3, ha3⟩ := hdiv3; omega
      exact Submodule.finrank_eq_zero.mp this
    have hU : f.eigenspace 1 ⊔ f.eigenspace (ζ : K) = ⊤ := by
      have h := eigenspace_sup_eq_top f hf3 hζK
      rw [hb3, sup_bot_eq] at h; exact h
    obtain ⟨d, hd3, hhd⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd1
    obtain ⟨e, he3, hhe⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd2
    obtain ⟨c, k, hc3, heq⟩ := exists_scalar_pow_of_two_eigenspaces hU (one_pow 3) hζK.pow_eq_one
      h1neζ (fun v hv => Module.End.mem_eigenspace_iff.mp hv)
      (fun v hv => Module.End.mem_eigenspace_iff.mp hv) ⟨d, hd3, hhd⟩ ⟨e, he3, hhe⟩
    exact eq_scalar_mul_pow_of_end hc3 heq
  · have hd1 : finrank K (f.eigenspace 1) = 3 := by
      obtain ⟨a1, ha1⟩ := hdiv1; omega
    have hd3 : finrank K (f.eigenspace ((ζ : K) ^ 2)) = 3 := by
      obtain ⟨a3, ha3⟩ := hdiv3; omega
    have hb2 : f.eigenspace (ζ : K) = ⊥ := by
      have : finrank K (f.eigenspace (ζ : K)) = 0 := by
        obtain ⟨a2, ha2⟩ := hdiv2; omega
      exact Submodule.finrank_eq_zero.mp this
    have hU : f.eigenspace 1 ⊔ f.eigenspace ((ζ : K) ^ 2) = ⊤ := by
      have h := eigenspace_sup_eq_top f hf3 hζK
      rw [hb2, sup_bot_eq] at h; exact h
    obtain ⟨d, hd, hhd⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd1
    obtain ⟨e, he, hhe⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd3
    obtain ⟨c, k, hc3, heq⟩ := exists_scalar_pow_of_two_eigenspaces hU (one_pow 3) hζ2 h1neζ2
      (fun v hv => Module.End.mem_eigenspace_iff.mp hv)
      (fun v hv => Module.End.mem_eigenspace_iff.mp hv) ⟨d, hd, hhd⟩ ⟨e, he, hhe⟩
    exact eq_scalar_mul_pow_of_end hc3 heq
  · have hd2 : finrank K (f.eigenspace (ζ : K)) = 3 := by
      obtain ⟨a2, ha2⟩ := hdiv2; omega
    have hd3 : finrank K (f.eigenspace ((ζ : K) ^ 2)) = 3 := by
      obtain ⟨a3, ha3⟩ := hdiv3; omega
    have hb1 : f.eigenspace 1 = ⊥ := by
      have : finrank K (f.eigenspace 1) = 0 := by
        obtain ⟨a1, ha1⟩ := hdiv1; omega
      exact Submodule.finrank_eq_zero.mp this
    have hU : f.eigenspace (ζ : K) ⊔ f.eigenspace ((ζ : K) ^ 2) = ⊤ := by
      have h := eigenspace_sup_eq_top f hf3 hζK
      rw [hb1, bot_sup_eq] at h; exact h
    obtain ⟨d, hd, hhd⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd2
    obtain ⟨e, he, hhe⟩ :=
      exists_smul_on_invariant_eigenspace f f' M' hf3 hf'3 hff'.symm hM'3 hlK hMf hMf' hζK hd3
    obtain ⟨c, k, hc3, heq⟩ := exists_scalar_pow_of_two_eigenspaces hU hζK.pow_eq_one hζ2 hζneζ2
      (fun v hv => Module.End.mem_eigenspace_iff.mp hv)
      (fun v hv => Module.End.mem_eigenspace_iff.mp hv) ⟨d, hd, hhd⟩ ⟨e, he, hhe⟩
    exact eq_scalar_mul_pow_of_end hc3 heq

end CFSG.StandardType.UnitSixThreeKG

end
