module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

section Scalar

theorem coe_scalar_eq_smul (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  rfl

theorem det_scalar_three (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (c : K) ^ 3 := by
  rw [coe_scalar_eq_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

theorem pow_three_eq_one_of_conj_eq_scalar_mul {g y : GL (Fin 3) K} {c : Kˣ}
    (h : g * y * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * y) : c ^ 3 = 1 := by
  have hd := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) h
  simp only [Units.val_mul, Matrix.det_mul] at hd
  rw [det_scalar_three] at hd
  have hg : (g : Matrix (Fin 3) (Fin 3) K).det * ((g⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hy : (y : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have h1 : (c : K) ^ 3 = 1 := by
    have : (y : Matrix (Fin 3) (Fin 3) K).det * ((c : K) ^ 3 - 1) = 0 := by
      linear_combination -hd + (y : Matrix (Fin 3) (Fin 3) K).det * hg
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hy)
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])

theorem trace_eq_zero_of_conj_eq_scalar_mul {g y : GL (Fin 3) K} {c : Kˣ} (hc : c ≠ 1)
    (h : g * y * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * y) :
    (y : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  have ht := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).trace) h
  simp only [Units.val_mul] at ht
  rw [Matrix.trace_units_conj, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul] at ht
  have hc' : (c : K) ≠ 1 := fun h1 => hc (Units.ext h1)
  have : ((c : K) - 1) * (y : Matrix (Fin 3) (Fin 3) K).trace = 0 := by linear_combination -ht
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc')

end Scalar

section Heisenberg

variable {ζ : Kˣ} {y₁ y₂ : GL (Fin 3) K}

theorem zpow_conj_eq (h : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) (b : ℤ) :
    y₁ * y₂ ^ b * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ b) * y₂ ^ b := by
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) ζ) y₂ :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ y₂).symm
  have h1 : (MulAut.conj y₁) (y₂ ^ b) = (GeneralLinearGroup.scalar (Fin 3) ζ * y₂) ^ b := by
    rw [map_zpow, MulAut.conj_apply, h]
  rw [MulAut.conj_apply] at h1
  rw [h1, hc.mul_zpow, map_zpow]

theorem conj_zpow_eq (h : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) (a : ℤ) :
    y₂ * y₁ ^ a * y₂⁻¹ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ (-a)) * y₁ ^ a := by
  have h' : y₂ * y₁ * y₂⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₁ := by
    have hc := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ y₂
    rw [map_inv]
    calc y₂ * y₁ * y₂⁻¹ = (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ *
        (GeneralLinearGroup.scalar (Fin 3) ζ * y₂) * y₁ * y₂⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ * (y₁ * y₂ * y₁⁻¹) * y₁ * y₂⁻¹ := by rw [h]
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ * y₁ := by group
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) y₁ :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ y₁).symm
  have h1 : (MulAut.conj y₂) (y₁ ^ a) = (GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₁) ^ a := by
    rw [map_zpow, MulAut.conj_apply, h']
  rw [MulAut.conj_apply] at h1
  rw [h1, hc.mul_zpow, map_zpow, map_inv, _root_.inv_zpow']

theorem trace_zpow_mul_zpow_eq_zero (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (h : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) {a b : ℤ}
    (hab : ¬ (3 ∣ a ∧ 3 ∣ b)) :
    ((y₁ ^ a * y₂ ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hpow : ∀ n : ℤ, ζ ^ n = 1 ↔ 3 ∣ n := fun n => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]
    norm_cast
  by_cases ha : 3 ∣ a
  · have hb : ¬ 3 ∣ b := fun hb => hab ⟨ha, hb⟩
    refine trace_eq_zero_of_conj_eq_scalar_mul (g := y₁) (c := ζ ^ b)
      (fun h1 => hb ((hpow b).mp h1)) ?_
    calc y₁ * (y₁ ^ a * y₂ ^ b) * y₁⁻¹ = y₁ ^ a * (y₁ * y₂ ^ b * y₁⁻¹) := by group
      _ = y₁ ^ a * (GeneralLinearGroup.scalar (Fin 3) (ζ ^ b) * y₂ ^ b) := by
          rw [zpow_conj_eq h]
      _ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ b) * (y₁ ^ a * y₂ ^ b) := by
          rw [← mul_assoc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ζ ^ b)
            (y₁ ^ a)).eq, mul_assoc]
  · refine trace_eq_zero_of_conj_eq_scalar_mul (g := y₂) (c := ζ ^ (-a))
      (fun h1 => ha (by simpa using (hpow (-a)).mp h1)) ?_
    calc y₂ * (y₁ ^ a * y₂ ^ b) * y₂⁻¹ = (y₂ * y₁ ^ a * y₂⁻¹) * y₂ ^ b := by group
      _ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ (-a)) * y₁ ^ a * y₂ ^ b := by
          rw [conj_zpow_eq h]
      _ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ (-a)) * (y₁ ^ a * y₂ ^ b) := by group

theorem linearIndependent_heis (h3 : (3 : K) ≠ 0) (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (h : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    LinearIndependent K (fun ij : Fin 3 × Fin 3 =>
      ((y₁ ^ (ij.1 : ℤ) * y₂ ^ (ij.2 : ℤ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc kl
  set v : Fin 3 × Fin 3 → Matrix (Fin 3) (Fin 3) K := fun ij =>
    ((y₁ ^ (ij.1 : ℤ) * y₂ ^ (ij.2 : ℤ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hv
  have htr : ∀ ij : Fin 3 × Fin 3, (((y₁ ^ (kl.1 : ℤ) * y₂ ^ (kl.2 : ℤ))⁻¹ : GL (Fin 3) K) *
      v ij).trace = (if ij = kl then 3 else 0 : K) := by
    intro ij
    have hcyc : (((y₁ ^ (kl.1 : ℤ) * y₂ ^ (kl.2 : ℤ))⁻¹ : GL (Fin 3) K) * v ij).trace =
        ((y₁ ^ ((ij.1 : ℤ) - kl.1) * y₂ ^ ((ij.2 : ℤ) - kl.2) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).trace := by
      rw [hv]
      simp only
      rw [← Units.val_mul, _root_.mul_inv_rev]
      have e : y₂ ^ (-(kl.2 : ℤ)) * y₁ ^ (-(kl.1 : ℤ)) * (y₁ ^ (ij.1 : ℤ) * y₂ ^ (ij.2 : ℤ)) =
          y₂ ^ (-(kl.2 : ℤ)) * (y₁ ^ ((ij.1 : ℤ) - kl.1) * y₂ ^ (ij.2 : ℤ)) := by
        rw [sub_eq_add_neg, _root_.zpow_add]
        group
      rw [← _root_.zpow_neg, ← _root_.zpow_neg, e, Units.val_mul, Matrix.trace_mul_comm,
        ← Units.val_mul]
      congr 2
      rw [mul_assoc, ← _root_.zpow_add]
      simp only [sub_eq_add_neg]
    rw [hcyc]
    split_ifs with hij
    · subst hij
      simp
    · refine trace_zpow_mul_zpow_eq_zero hζ1 hζ3 h fun ⟨h1, h2⟩ => hij ?_
      have e1 : ij.1 = kl.1 := by
        have := ij.1.isLt
        have := kl.1.isLt
        omega
      have e2 : ij.2 = kl.2 := by
        have := ij.2.isLt
        have := kl.2.isLt
        omega
      exact Prod.ext e1 e2
  have hsum := congrArg (fun M : Matrix (Fin 3) (Fin 3) K =>
    (((y₁ ^ (kl.1 : ℤ) * y₂ ^ (kl.2 : ℤ))⁻¹ : GL (Fin 3) K) * M).trace) hc
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_zero, Matrix.trace_zero] at hsum
  rw [Finset.sum_eq_single kl (fun ij _ hij => by
    have := htr ij
    simp only [hij, ↓reduceIte, hv] at this
    rw [this, mul_zero]) (fun h => absurd (Finset.mem_univ kl) h)] at hsum
  have := htr kl
  simp only [↓reduceIte, hv] at this
  rw [this] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right h3

theorem mem_statedScalars_of_commute_heis (h3 : (3 : K) ≠ 0) (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (h : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) {r : GL (Fin 3) K}
    (hr1 : r * y₁ = y₁ * r) (hr2 : r * y₂ = y₂ * r) : r ∈ StatedScalars (Fin 3) K := by
  classical
  have hlin := linearIndependent_heis h3 hζ1 hζ3 h
  have hspan := hlin.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_matrix, Module.finrank_self]
    simp)
  have hcomm : ∀ M ∈ Submodule.span K (Set.range (fun ij : Fin 3 × Fin 3 =>
      ((y₁ ^ (ij.1 : ℤ) * y₂ ^ (ij.2 : ℤ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))),
      (r : Matrix (Fin 3) (Fin 3) K) * M = M * r := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ij, rfl⟩ := hx
      have hc : Commute r (y₁ ^ (ij.1 : ℤ) * y₂ ^ (ij.2 : ℤ)) :=
        (Commute.zpow_right hr1 _).mul_right (Commute.zpow_right hr2 _)
      rw [← Units.val_mul, ← Units.val_mul, hc.eq]
    | zero => rw [Matrix.mul_zero, Matrix.zero_mul]
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]
  rw [hspan] at hcomm
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := (r : Matrix (Fin 3) (Fin 3) K))
    fun i j _ => (hcomm _ Submodule.mem_top).symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hd := congrArg Matrix.det ha
    rw [map_zero, Matrix.det_zero] at hd
    exact (r.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hd.symm
  refine mem_statedScalars_of_eq_smul ?_ ha0
  rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Heisenberg

section Inner

variable {p f : ℕ} {π : Bool}

theorem exists_inner_of_det_eq_cube (hK : PiField π p f K) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) {μ : Kˣ} (hμ : GeneralLinearGroup.scalar (Fin 3) μ ∈
      glPi π 3 (p ^ f) K) (hdet : (y : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3) :
    ∃ l ∈ slPi π 3 (p ^ f) K, (∃ z : Kˣ, y = l * GeneralLinearGroup.scalar (Fin 3) z) ∧
      ∀ m : GL (Fin 3) K, y * m * y⁻¹ = l * m * l⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set l := y * (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ with hl
  have hlH : l ∈ glPi π 3 (p ^ f) K := mul_mem hy (inv_mem hμ)
  have hldet : (l : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hl, Units.val_mul, Matrix.det_mul, ← map_inv, det_scalar_three, hdet,
      Units.val_inv_eq_inv_val, inv_pow, mul_inv_cancel₀ (pow_ne_zero 3 μ.ne_zero)]
  have hlS : l ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨hlH, hldet⟩
  refine ⟨l, hlS, ⟨μ, by rw [hl, inv_mul_cancel_right]⟩, fun m => ?_⟩
  have hc := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ m
  rw [hl]
  calc y * m * y⁻¹ = y * (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ *
      (GeneralLinearGroup.scalar (Fin 3) μ * m) * y⁻¹ := by group
    _ = y * (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ *
      (m * GeneralLinearGroup.scalar (Fin 3) μ) * y⁻¹ := by rw [hc.eq]
    _ = _ := by group

theorem exists_det_eq_cube_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) {l : GL (Fin 3) K}
    (hl : l ∈ slPi π 3 (p ^ f) K) (hyl : ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹) :
    ∃ μ : Kˣ, GeneralLinearGroup.scalar (Fin 3) μ ∈ glPi π 3 (p ^ f) K ∧
      y = l * GeneralLinearGroup.scalar (Fin 3) μ ∧
      (y : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hzc : l⁻¹ * y ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
    have := hyl m hm
    calc l⁻¹ * y * m = l⁻¹ * (y * m * y⁻¹) * y := by group
      _ = l⁻¹ * (l * m * l⁻¹) * y := by rw [this]
      _ = m * (l⁻¹ * y) := by group
  obtain ⟨μ, hμ⟩ := hzc
  have hyl' : y = l * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ, mul_inv_cancel_left]
  refine ⟨μ, ?_, hyl', ?_⟩
  · rw [hμ]
    exact mul_mem (inv_mem (slPi_le_glPi hπ hl)) hy
  · have hldet : (l : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hl).2
    rw [hyl', Units.val_mul, Matrix.det_mul, hldet, one_mul, det_scalar_three]

end Inner

section Common

theorem eigenProj_commute {τ : K} {y z : Matrix (Fin 3) (Fin 3) K} (hc : y * z = z * y)
    (k : Fin 3) : eigenProj τ y k * z = z * eigenProj τ y k := by
  have hc2 : y ^ 2 * z = z * y ^ 2 := by
    rw [sq, mul_assoc, hc, ← mul_assoc, hc, mul_assoc]
  unfold eigenProj
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, hc, hc2]

theorem exists_common_eigenbasis {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0)
    {y₁ y₂ : Matrix (Fin 3) (Fin 3) K} (hy₁ : y₁ ^ 3 = 1) (hy₂ : y₂ ^ 3 = 1)
    (hc : y₁ * y₂ = y₂ * y₁) :
    ∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧ ∀ i,
      (∃ k : Fin 3, y₁ *ᵥ b i = τ ^ (k : ℕ) • b i) ∧
        ∃ l : Fin 3, y₂ *ᵥ b i = τ ^ (l : ℕ) • b i := by
  classical
  set S : Set (Fin 3 → K) := Set.range fun klj : Fin 3 × Fin 3 × Fin 3 =>
    (eigenProj τ y₁ klj.1 * eigenProj τ y₂ klj.2.1) *ᵥ Pi.single klj.2.2 1 with hS
  have hSeig : ∀ w ∈ S, (∃ k : Fin 3, y₁ *ᵥ w = τ ^ (k : ℕ) • w) ∧
      ∃ l : Fin 3, y₂ *ᵥ w = τ ^ (l : ℕ) • w := by
    rintro _ ⟨⟨k, l, j⟩, rfl⟩
    refine ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
    · dsimp only
      rw [Matrix.mulVec_mulVec, ← mul_assoc, mul_eigenProj hτ hy₁, Matrix.smul_mul,
        Matrix.smul_mulVec]
    · dsimp only
      rw [Matrix.mulVec_mulVec, ← mul_assoc, ← eigenProj_commute hc k, mul_assoc,
        mul_eigenProj hτ hy₂, Matrix.mul_smul, Matrix.smul_mulVec]
  have hspan : Submodule.span K S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ j, v j • (Pi.single j (1 : K) : Fin 3 → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hj : (Pi.single j (1 : K) : Fin 3 → K) =
        ∑ k, ∑ l, (eigenProj τ y₁ k * eigenProj τ y₂ l) *ᵥ (Pi.single j 1 : Fin 3 → K) := by
      simp only [← Matrix.sum_mulVec, ← Finset.mul_sum, ← Finset.sum_mul,
        sum_eigenProj hτ hτ1 h3, Matrix.one_mul, Matrix.one_mulVec]
    rw [hj]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      Submodule.subset_span ⟨(k, l, j), rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K S
  have hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin 3 → K)) := by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan, hspan]
  set B := Module.Basis.mk hbli hbtop
  have hfin : Finite b := Module.Finite.finite_basis B
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = 3 := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨B', B'.linearIndependent, fun i => ?_⟩
  have hmem : B' i ∈ S := by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact hbS (Subtype.mem _)
  exact hSeig _ hmem

theorem exists_smul_of_commute_regular {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    {z y : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} (hd : Function.Injective d)
    (hz : ∀ i, z *ᵥ b i = d i • b i) (hc : y * z = z * y) (i : Fin 3) :
    ∃ c : K, y *ᵥ b i = c • b i := by
  classical
  have hspan : Submodule.span K (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (by simp)
  set B := Module.Basis.mk hb hspan.ge
  have hyb := B.sum_repr (y *ᵥ b i)
  have hBb : ∀ j, B j = b j := fun j => Module.Basis.mk_apply _ _ j
  simp only [hBb] at hyb
  have hzy : z *ᵥ (y *ᵥ b i) = d i • (y *ᵥ b i) := by
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul]
  refine ⟨B.repr (y *ᵥ b i) i, ?_⟩
  have hcoef : ∀ j, j ≠ i → B.repr (y *ᵥ b i) j = 0 := by
    intro j hji
    have h1 : z *ᵥ (y *ᵥ b i) = ∑ j, (B.repr (y *ᵥ b i) j * d j) • b j := by
      conv_lhs => rw [← hyb]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, hz, smul_smul]
    have h2 : d i • (y *ᵥ b i) = ∑ j, (B.repr (y *ᵥ b i) j * d i) • b j := by
      conv_lhs => rw [← hyb]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    have h12 := hzy
    rw [h1, h2] at h12
    have h0 : ∑ j, (B.repr (y *ᵥ b i) j * (d j - d i)) • b j = 0 := by
      simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, h12, sub_self]
    have hrep := (Fintype.linearIndependent_iff.mp hb) _ h0 j
    have hdj : d j ≠ d i := fun h => hji (hd h)
    exact (mul_eq_zero.mp hrep).resolve_right (sub_ne_zero.mpr hdj)
  conv_lhs => rw [← hyb]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hcoef j hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h)]

theorem exists_injective_combination (k l : Fin 3 → Fin 3)
    (h : ∀ i j : Fin 3, (∃ c : Fin 3, ∀ r, i * k r + j * l r = c) → i = 0 ∧ j = 0) :
    ∃ i j : Fin 3, Function.Injective fun r => i * k r + j * l r := by
  revert k l
  decide

end Common

section Kummer

open Polynomial

theorem exists_eq_tau_pow_of_commute_irred {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ℓ : K}
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = ℓ • 1)
    {m : Matrix (Fin 3) (Fin 3) K} (hm : m * y = y * m) (hm3 : m ^ 3 = 1) :
    ∃ j : Fin 3, m = τ ^ (j : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  obtain ⟨e, rfl⟩ := (mem_range_cubeHom hℓ hy m).mpr hm
  have he3 : e ^ 3 = 1 := cubeHom_injective hℓ hy (by rw [map_pow, hm3, map_one])
  have hs := one_add_tau_add_sq hτ hτ1
  have hfac : (e - 1) * (e - algebraMap K (cubeField ℓ) τ) *
      (e - algebraMap K (cubeField ℓ) (τ ^ 2)) = 0 := by
    have h1 : (e - 1) * (e - algebraMap K (cubeField ℓ) τ) *
        (e - algebraMap K (cubeField ℓ) (τ ^ 2)) =
        e ^ 3 - algebraMap K (cubeField ℓ) (1 + τ + τ ^ 2) * e ^ 2 +
          algebraMap K (cubeField ℓ) (τ + τ ^ 2 + τ ^ 3) * e - algebraMap K _ (τ ^ 3) := by
      simp only [map_add, map_pow, map_one]
      ring
    have h2 : τ + τ ^ 2 + τ ^ 3 = 0 := by linear_combination τ * hs
    rw [h1, hs, h2, hτ, he3, map_zero, map_one]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · refine ⟨0, ?_⟩
      rw [sub_eq_zero.mp h, map_one, Fin.val_zero, pow_zero, one_smul]
    · refine ⟨1, ?_⟩
      rw [sub_eq_zero.mp h, AlgHom.commutes, Fin.val_one, pow_one,
        Algebra.algebraMap_eq_smul_one]
  · refine ⟨2, ?_⟩
    rw [sub_eq_zero.mp h, AlgHom.commutes, Fin.val_two, Algebra.algebraMap_eq_smul_one]

theorem exists_mul_pow_mem_statedScalars_of_irred (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y y' : GL (Fin 3) K}
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) (hc : y' * y = y * y')
    (hy' : y' ^ 3 ∈ StatedScalars (Fin 3) K) :
    ∃ k : Fin 3, y' * y ^ (k : ℕ) ∈ StatedScalars (Fin 3) K := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨w, -, -, hw⟩ := exists_w_linear hτ hτ1 hℓ hy
  set t : Kˣ := Units.mk0 τ hτ0 with ht
  have ht3 : t ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, ht, Units.val_mk0, hτ, Units.val_one])
  have ht1 : t ≠ 1 := fun h1 => hτ1 (by rw [← Units.val_mk0 hτ0, ← ht, h1, Units.val_one])
  set S := GeneralLinearGroup.scalar (Fin 3) t with hS
  have hwy : w * y * w⁻¹ = S * y := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hw, hS, coe_scalar_eq_smul, ht,
      Units.val_mk0, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hpoly : ∀ M N : Matrix (Fin 3) (Fin 3) K, M * y = y * M → N * y = y * N →
      M * N = N * M := by
    intro M N hM hN
    obtain ⟨e₁, rfl⟩ := (mem_range_cubeHom hℓ hy M).mpr hM
    obtain ⟨e₂, rfl⟩ := (mem_range_cubeHom hℓ hy N).mpr hN
    rw [← map_mul, ← map_mul, mul_comm]
  have hy'inv : y'⁻¹ * y = y * y'⁻¹ := by
    calc y'⁻¹ * y = y'⁻¹ * (y * y') * y'⁻¹ := by group
      _ = y'⁻¹ * (y' * y) * y'⁻¹ := by rw [hc]
      _ = y * y'⁻¹ := by group
  set X := w * y' * w⁻¹ with hX
  have hXy : X * y = y * X := by
    have h1 : X * (S * y) = (S * y) * X := by
      rw [← hwy, hX]
      calc w * y' * w⁻¹ * (w * y * w⁻¹) = w * (y' * y) * w⁻¹ := by group
        _ = w * (y * y') * w⁻¹ := by rw [hc]
        _ = w * y * w⁻¹ * (w * y' * w⁻¹) := by group
    have hcs : X * S = S * X := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t X).eq
    have h2 : S * (X * y) = S * (y * X) := by
      calc S * (X * y) = X * (S * y) := by rw [← mul_assoc, ← hcs, mul_assoc]
        _ = (S * y) * X := h1
        _ = S * (y * X) := by rw [mul_assoc]
    exact mul_left_cancel h2
  have hXy' : X * y'⁻¹ = y'⁻¹ * X := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    refine hpoly _ _ ?_ ?_
    · have := congrArg Units.val hXy
      rw [hX] at this
      simpa only [Units.val_mul] using this
    · simpa only [Units.val_mul] using congrArg Units.val hy'inv
  have hmy : ((X * y'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * y =
      y * ((X * y'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc X * y'⁻¹ * y = X * (y'⁻¹ * y) := by group
      _ = X * (y * y'⁻¹) := by rw [hy'inv]
      _ = (X * y) * y'⁻¹ := by group
      _ = (y * X) * y'⁻¹ := by rw [hXy]
      _ = y * (X * y'⁻¹) := by group
  obtain ⟨c, hc3⟩ := hy'
  have hX3 : X ^ 3 = y' ^ 3 := by
    have h1 := map_pow (MulAut.conj w) y' 3
    simp only [MulAut.conj_apply] at h1
    rw [hX, ← h1, ← hc3, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c w).eq,
      mul_inv_cancel_right]
  have hm3 : (X * y'⁻¹) ^ 3 = 1 := by
    rw [(Commute.mul_pow hXy' 3), hX3, inv_pow, mul_inv_cancel]
  obtain ⟨j, hj⟩ := exists_eq_tau_pow_of_commute_irred hτ hτ1 hℓ hy hmy
    (by rw [← Units.val_pow_eq_pow_val, hm3, Units.val_one])
  have hwy' : X = GeneralLinearGroup.scalar (Fin 3) (t ^ (j : ℕ)) * y' := by
    have h1 : X * y'⁻¹ = GeneralLinearGroup.scalar (Fin 3) (t ^ (j : ℕ)) := Units.ext (by
      rw [hj, coe_scalar_eq_smul, Units.val_pow_eq_pow_val, ht, Units.val_mk0])
    calc X = X * y'⁻¹ * y' := by group
      _ = _ := by rw [h1]
  set k : Fin 3 := -j with hk
  have hwyk : w * y ^ (k : ℕ) * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) (t ^ (k : ℕ)) *
      y ^ (k : ℕ) := by
    have := zpow_conj_eq hwy ((k : ℕ) : ℤ)
    simpa only [zpow_natCast] using this
  have htk : t ^ (j : ℕ) * t ^ (k : ℕ) = 1 := by
    rw [← pow_add]
    have hmod : ((j : ℕ) + (k : ℕ)) % 3 = 0 := by
      rw [← Fin.val_add, hk]
      simp
    rw [← Nat.mod_add_div ((j : ℕ) + (k : ℕ)) 3, hmod, zero_add, pow_mul, ht3, one_pow]
  refine ⟨k, mem_statedScalars_of_commute_heis h3 ht1 ht3 hwy ?_ ?_⟩
  ·
    have hcs := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (t ^ (k : ℕ)) y'
    have key : w * (y' * y ^ (k : ℕ)) * w⁻¹ = y' * y ^ (k : ℕ) := by
      calc w * (y' * y ^ (k : ℕ)) * w⁻¹ = X * (w * y ^ (k : ℕ) * w⁻¹) := by rw [hX]; group
        _ = GeneralLinearGroup.scalar (Fin 3) (t ^ (j : ℕ)) * y' *
            (GeneralLinearGroup.scalar (Fin 3) (t ^ (k : ℕ)) * y ^ (k : ℕ)) := by
            rw [hwy', hwyk]
        _ = GeneralLinearGroup.scalar (Fin 3) (t ^ (j : ℕ)) *
            (y' * GeneralLinearGroup.scalar (Fin 3) (t ^ (k : ℕ))) * y ^ (k : ℕ) := by group
        _ = GeneralLinearGroup.scalar (Fin 3) (t ^ (j : ℕ) * t ^ (k : ℕ)) *
            (y' * y ^ (k : ℕ)) := by rw [hcs.eq, map_mul]; group
        _ = y' * y ^ (k : ℕ) := by rw [htk, map_one, one_mul]
    calc y' * y ^ (k : ℕ) * w = (w * (y' * y ^ (k : ℕ)) * w⁻¹) * w := by rw [key]
      _ = w * (y' * y ^ (k : ℕ)) := by group
  ·
    calc y' * y ^ (k : ℕ) * y = y' * y * y ^ (k : ℕ) := by
          rw [mul_assoc, ← pow_succ, pow_succ', mul_assoc]
      _ = y * y' * y ^ (k : ℕ) := by rw [hc]
      _ = y * (y' * y ^ (k : ℕ)) := by group

end Kummer

section Classification

theorem exists_scalar_of_mk_mul_comm {y y' : GL (Fin 3) K}
    (h : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) * y' = y' * y) :
    ∃ c : Kˣ, y * y' * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * y' := by
  have h1 : y * y' * y⁻¹ * y'⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩

theorem pow_three_mem_of_mk {y : GL (Fin 3) K}
    (h : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ^ 3 = 1) :
    y ^ 3 ∈ StatedScalars (Fin 3) K := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, h]

theorem eq_zero_of_pow_mul_pow_eq_one {Q : Type*} [Group Q] {x₁ x₂ : Q} (h1 : x₁ ≠ 1)
    (h13 : x₁ ^ 3 = 1) (h2 : x₂ ∉ Subgroup.zpowers x₁) (h23 : x₂ ^ 3 = 1) {i j : Fin 3}
    (h : x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) = 1) : i = 0 ∧ j = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x₁ = 3 := orderOf_eq_prime h13 h1
  have hj : j = 0 := by
    by_contra hj
    apply h2
    have hxj : x₂ ^ (j : ℕ) ∈ Subgroup.zpowers x₁ := by
      have : x₂ ^ (j : ℕ) = (x₁ ^ (i : ℕ))⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_mem (Subgroup.npow_mem_zpowers _ _)
    fin_cases j
    · exact absurd rfl hj
    · simpa using hxj
    · have : x₂ = (x₂ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h23, one_mul]
      rw [this]
      exact pow_mem (by simpa using hxj) 2
  subst hj
  rw [Fin.val_zero, pow_zero, mul_one] at h
  refine ⟨?_, rfl⟩
  have := orderOf_dvd_of_pow_eq_one h
  rw [hord] at this
  have hi := i.isLt
  ext
  simp only [Fin.val_zero]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
  · exact h0
  · exact absurd (Nat.le_of_dvd h0 this) (by omega)

theorem eq_of_mulVec_eq_of_linearIndependent {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b) {M N : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ r, M *ᵥ b r = N *ᵥ b r) : M = N := by
  have hu := isUnit_colMat hb
  have hMN : M * colMat b = N * colMat b := by
    ext i r
    have := congrFun (h r) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, colMat, of_apply]
    exact this
  exact hu.mul_left_inj.mp hMN

theorem exists_normalized {y : GL (Fin 3) K} {ℓ : Kˣ}
    (hy : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) ℓ) {μ : K} (hμ : μ ^ 3 = ℓ) :
    ∃ m : Kˣ, ((y * GeneralLinearGroup.scalar (Fin 3) m : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact ℓ.ne_zero (by rw [← hμ]; ring)
  refine ⟨(Units.mk0 μ hμ0)⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ y).mul_pow,
    hy, ← map_pow, ← map_mul]
  have : ℓ * (Units.mk0 μ hμ0)⁻¹ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
      inv_pow, hμ, mul_inv_cancel₀ (Units.ne_zero ℓ), Units.val_one]
  rw [this, map_one, Units.val_one]

theorem card_le_nine_of_heis (h3 : (3 : K) ≠ 0)
    (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E) {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) : Nat.card E ≤ 9 := by
  classical
  have hζ3 := pow_three_eq_one_of_conj_eq_scalar_mul hζ
  have hF : ∀ x : E, ∃ c : rootsOfUnity 3 K × rootsOfUnity 3 K,
      x.1.out * y₁ * x.1.out⁻¹ = GeneralLinearGroup.scalar (Fin 3) (c.1 : Kˣ) * y₁ ∧
        x.1.out * y₂ * x.1.out⁻¹ = GeneralLinearGroup.scalar (Fin 3) (c.2 : Kˣ) * y₂ := by
    intro x
    have hx : (x.1.out : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
      rw [QuotientGroup.out_eq']
      exact x.2
    obtain ⟨c₁, hc₁⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hx _ hy₁)
    obtain ⟨c₂, hc₂⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hx _ hy₂)
    exact ⟨(⟨c₁, (mem_rootsOfUnity 3 c₁).mpr (pow_three_eq_one_of_conj_eq_scalar_mul hc₁)⟩,
      ⟨c₂, (mem_rootsOfUnity 3 c₂).mpr (pow_three_eq_one_of_conj_eq_scalar_mul hc₂)⟩),
      hc₁, hc₂⟩
  choose F hF using hF
  have hinj : Function.Injective F := by
    intro x x' hxx'
    obtain ⟨h1, h2⟩ := hF x
    obtain ⟨h1', h2'⟩ := hF x'
    rw [hxx'] at h1 h2
    set r := x.1.out⁻¹ * x'.1.out with hr
    have hr1 : r * y₁ = y₁ * r := by
      have e : x'.1.out * y₁ * x'.1.out⁻¹ = x.1.out * y₁ * x.1.out⁻¹ := by rw [h1, h1']
      calc r * y₁ = x.1.out⁻¹ * (x'.1.out * y₁ * x'.1.out⁻¹) * x'.1.out := by rw [hr]; group
        _ = x.1.out⁻¹ * (x.1.out * y₁ * x.1.out⁻¹) * x'.1.out := by rw [e]
        _ = y₁ * r := by rw [hr]; group
    have hr2 : r * y₂ = y₂ * r := by
      have e : x'.1.out * y₂ * x'.1.out⁻¹ = x.1.out * y₂ * x.1.out⁻¹ := by rw [h2, h2']
      calc r * y₂ = x.1.out⁻¹ * (x'.1.out * y₂ * x'.1.out⁻¹) * x'.1.out := by rw [hr]; group
        _ = x.1.out⁻¹ * (x.1.out * y₂ * x.1.out⁻¹) * x'.1.out := by rw [e]
        _ = y₂ * r := by rw [hr]; group
    have hrs := mem_statedScalars_of_commute_heis h3 hζ1 hζ3 hζ hr1 hr2
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' x.1, ← QuotientGroup.out_eq' x'.1, QuotientGroup.eq]
    exact hrs
  calc Nat.card E ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective F hinj
    _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 3 * 3 := by
        have : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
        exact Nat.mul_le_mul this this

theorem card_le_nine_of_frame (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hexp : ∀ x ∈ E, x ^ 3 = 1) {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E →
      ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i) : Nat.card E ≤ 9 := by
  classical
  have hb0 : ∀ i, b i ≠ 0 := fun i => hb.ne_zero i
  have hF : ∀ x : E, ∃ c : Fin 3 → Kˣ, ∀ i,
      ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = (c i : K) • b i := by
    intro x
    have hx : (x.1.out : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
      rw [QuotientGroup.out_eq']
      exact x.2
    choose c hc using hd _ hx
    have hc0 : ∀ i, c i ≠ 0 := by
      intro i h0
      have := hc i
      rw [h0, zero_smul] at this
      have hinj := (Matrix.mulVec_injective_iff_isUnit (A := ((x.1.out : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))).mpr (x.1.out.isUnit)
      exact hb0 i (hinj (by rw [this, Matrix.mulVec_zero]))
    exact ⟨fun i => Units.mk0 (c i) (hc0 i), fun i => by rw [Units.val_mk0, hc i]⟩
  choose c hc using hF
  have hratio : ∀ x : E, ∀ i, (c x i / c x 0) ^ 3 = 1 := by
    intro x i
    have hx : (x.1.out : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E := by
      rw [QuotientGroup.out_eq']
      exact x.2
    obtain ⟨ℓ, hℓ⟩ := pow_three_mem_of_mk (hexp _ hx)
    have hcube : ∀ j, ((c x j : K)) ^ 3 = ℓ := by
      intro j
      have hpow : ∀ n : ℕ, (((x.1.out ^ n : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ b j =
          (c x j : K) ^ n • b j := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, one_smul, Units.val_one, Matrix.one_mulVec]
        | succ n ih =>
          rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hc x j, Matrix.mulVec_smul, ih,
            smul_smul, pow_succ, mul_comm]
      have h1 := hpow 3
      rw [← hℓ, coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      have h2 : (((c x j : K)) ^ 3 - ℓ) • b j = 0 := by rw [sub_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (hb0 j))
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, div_pow, hcube, hcube, div_self
      (Units.ne_zero ℓ), Units.val_one]
  let F : E → rootsOfUnity 3 K × rootsOfUnity 3 K := fun x =>
    (⟨c x 1 / c x 0, (mem_rootsOfUnity 3 _).mpr (hratio x 1)⟩,
      ⟨c x 2 / c x 0, (mem_rootsOfUnity 3 _).mpr (hratio x 2)⟩)
  have hinj : Function.Injective F := by
    intro x x' hxx'
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx'
    obtain ⟨h1, h2⟩ := hxx'
    set lam : Kˣ := c x 0 / c x' 0 with hlam
    have key : ∀ {a b a' b' : Kˣ}, a / b = a' / b' → a = b / b' * a' := by
      intro a b a' b' h
      apply Units.ext
      have h' := congrArg Units.val h
      simp only [Units.val_div_eq_div_val] at h'
      rw [Units.val_mul, Units.val_div_eq_div_val]
      have hb := b.ne_zero
      have hb' := b'.ne_zero
      rw [show (a : K) = a' / b' * b by rw [← h', div_mul_cancel₀ _ hb]]
      ring
    have hall : ∀ i, c x i = lam * c x' i := by
      intro i
      fin_cases i
      · show c x 0 = lam * c x' 0
        rw [hlam, div_mul_cancel]
      · exact key h1
      · exact key h2
    have heq : ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((x'.1.out * GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      apply eq_of_mulVec_eq_of_linearIndependent hb
      intro i
      calc ((x.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i
          = ((lam * c x' i : Kˣ) : K) • b i := by rw [hc x i, hall i]
        _ = ((x'.1.out : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by
            rw [coe_scalar_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
              hc x' i, smul_smul, Units.val_mul]
        _ = _ := by rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' x.1, ← QuotientGroup.out_eq' x'.1, Units.ext heq,
      QuotientGroup.mk_mul]
    have : ((GeneralLinearGroup.scalar (Fin 3) lam : GL (Fin 3) K) :
        GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨lam, rfl⟩
    rw [this, mul_one]
  calc Nat.card E ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective F hinj
    _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 3 * 3 := by
        have : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
        exact Nat.mul_le_mul this this

theorem exists_independent_of_three_lt_card {Q : Type*} [Group Q] (E : Subgroup Q)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : 3 < Nat.card E) :
    ∃ x₁ ∈ E, x₁ ≠ 1 ∧ ∃ x₂ ∈ E, x₂ ∉ Subgroup.zpowers x₁ := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨x₁, hx₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨x₁, x₁.2, fun h => hx₁1 (Subtype.ext h), ?_⟩
  by_contra hall
  push Not at hall
  have hle : E ≤ Subgroup.zpowers (x₁ : Q) := fun x hx => hall x hx
  have hfo : IsOfFinOrder (x₁ : Q) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hexp _ x₁.2⟩
  have : Finite (Subgroup.zpowers (x₁ : Q)) := hfo.finite_zpowers
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf (x₁ : Q) ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hexp _ x₁.2)
  omega

theorem tau_pow_injective {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Function.Injective fun a : Fin 3 => τ ^ (a : ℕ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hord : orderOf (Units.mk0 τ hτ0) = 3 := orderOf_eq_prime
    (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one]))
    (fun h => hτ1 (by rw [← Units.val_mk0 hτ0, h, Units.val_one]))
  intro a b hab
  have h1 : (Units.mk0 τ hτ0) ^ (a : ℕ) = (Units.mk0 τ hτ0) ^ (b : ℕ) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0]; exact hab)
  have := pow_injOn_Iio_orderOf (by rw [hord]; exact a.isLt) (by rw [hord]; exact b.isLt) h1
  exact Fin.ext this

theorem tau_pow_mul_fin {τ : K} (hτ : τ ^ 3 = 1) (a b : Fin 3) :
    (τ ^ (a : ℕ)) ^ (b : ℕ) = τ ^ ((b * a : Fin 3) : ℕ) := by
  rw [← pow_mul, Fin.val_mul]
  conv_lhs => rw [← Nat.mod_add_div ((a : ℕ) * b) 3]
  rw [pow_add, pow_mul, hτ, one_pow, mul_one, mul_comm]

theorem frame_or_heis (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : 3 < Nat.card E) :
    (∃ b : Fin 3 → (Fin 3 → K), LinearIndependent K b ∧ (∀ y : GL (Fin 3) K,
        (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E →
          ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i) ∧
        ∃ z : GL (Fin 3) K, (z : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧
          ∃ d : Fin 3 → K, Function.Injective d ∧
            ∀ i, (z : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) ∨
      (∃ y₁ y₂ : GL (Fin 3) K, (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧
        (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧ ∃ ζ : Kˣ, ζ ≠ 1 ∧
          y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) := by
  classical
  by_cases hnab : ∃ y₁ y₂ : GL (Fin 3) K, (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧
      (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E ∧ y₁ * y₂ ≠ y₂ * y₁
  · right
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := hnab
    obtain ⟨ζ, hζ⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hy₁ _ hy₂)
    refine ⟨y₁, y₂, hy₁, hy₂, ζ, fun h1 => hne ?_, hζ⟩
    rw [h1, map_one, one_mul] at hζ
    calc y₁ * y₂ = y₁ * y₂ * y₁⁻¹ * y₁ := by group
      _ = y₂ * y₁ := by rw [hζ]
  left
  push Not at hnab
  obtain ⟨x₁, hx₁, hx₁1, x₂, hx₂, hx₂n⟩ := exists_independent_of_three_lt_card E hexp hcard
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective x₁
  obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective x₂
  have h12 := hnab y₁ y₂ hx₁ hx₂
  obtain ⟨ℓ₁, hℓ₁⟩ := pow_three_mem_of_mk (hexp _ hx₁)
  obtain ⟨ℓ₂, hℓ₂⟩ := pow_three_mem_of_mk (hexp _ hx₂)
  have hy₁c : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ₁ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hℓ₁, coe_scalar_eq_smul]
  have hy₂c : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ₂ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hℓ₂, coe_scalar_eq_smul]
  have hy₁s : y₁ ∉ StatedScalars (Fin 3) K := fun h =>
    hx₁1 ((QuotientGroup.eq_one_iff _).mpr h)
  by_cases hs₁ : ∃ μ : K, μ ^ 3 = ℓ₁
  swap
  · exfalso
    push Not at hs₁
    obtain ⟨k, hk⟩ := exists_mul_pow_mem_statedScalars_of_irred h3 hτ hτ1 hs₁ hy₁c
      (hnab y₂ y₁ hx₂ hx₁) ⟨ℓ₂, hℓ₂⟩
    apply hx₂n
    have h1 : ((y₂ * y₁ ^ (k : ℕ) : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
        1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (Subgroup.npow_mem_zpowers _ _)
  obtain ⟨μ₁, hμ₁⟩ := hs₁
  obtain ⟨m₁, hm₁⟩ := exists_normalized hℓ₁.symm hμ₁
  set z₁ := ((y₁ * GeneralLinearGroup.scalar (Fin 3) m₁ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hz₁
  have hz₁s : ∀ c : K, z₁ ≠ c • 1 := by
    intro c hc
    apply hy₁s
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hd := congrArg Matrix.det hc
      rw [zero_smul, Matrix.det_zero] at hd
      exact ((y₁ * GeneralLinearGroup.scalar (Fin 3) m₁).isUnit.map
        (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero hd
    have h1 : y₁ * GeneralLinearGroup.scalar (Fin 3) m₁ ∈ StatedScalars (Fin 3) K :=
      mem_statedScalars_of_eq_smul hc hc0
    have h2 : y₁ = y₁ * GeneralLinearGroup.scalar (Fin 3) m₁ *
        (GeneralLinearGroup.scalar (Fin 3) m₁)⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem ⟨m₁, rfl⟩)
  by_cases hs₂ : ∃ μ : K, μ ^ 3 = ℓ₂
  swap
  · exfalso
    push Not at hs₂
    obtain ⟨b, hb, hk⟩ := exists_eigenbasis hτ hτ1 h3 hm₁
    obtain ⟨k, hk0⟩ := hk 0
    set W := LinearMap.ker (Matrix.toLin' (z₁ - τ ^ (k : ℕ) • 1)) with hW
    have hWinv : ∀ v ∈ W, (y₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
      intro v hv
      rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
      have hc : z₁ * y₂ = y₂ * z₁ := by
        rw [hz₁, ← Units.val_mul, ← Units.val_mul]
        congr 1
        rw [mul_assoc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar m₁ y₂).symm.eq,
          ← mul_assoc, h12, mul_assoc]
      have e : (z₁ - τ ^ (k : ℕ) • 1) * (y₂ : Matrix (Fin 3) (Fin 3) K) =
          (y₂ : Matrix (Fin 3) (Fin 3) K) * (z₁ - τ ^ (k : ℕ) • 1) := by
        rw [Matrix.sub_mul, hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul,
          Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rcases eq_bot_or_eq_top_of_invariant hs₂ hy₂c hWinv with hbot | htop
    · have h0 : b 0 ∈ W := by
        rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, hk0,
          Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
      rw [hbot, Submodule.mem_bot] at h0
      exact hb.ne_zero 0 h0
    · apply hz₁s (τ ^ (k : ℕ))
      have h1 : ∀ v : Fin 3 → K, (z₁ - τ ^ (k : ℕ) • 1) *ᵥ v = 0 := by
        intro v
        have : v ∈ W := htop ▸ Submodule.mem_top
        rwa [hW, LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have h2 : z₁ - τ ^ (k : ℕ) • 1 = 0 := by
        ext i j
        have := congrFun (h1 (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      exact sub_eq_zero.mp h2
  obtain ⟨μ₂, hμ₂⟩ := hs₂
  obtain ⟨m₂, hm₂⟩ := exists_normalized hℓ₂.symm hμ₂
  set z₂ := ((y₂ * GeneralLinearGroup.scalar (Fin 3) m₂ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hz₂
  have hcz : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E →
      ∀ {g : GL (Fin 3) K} {m : Kˣ}, (g : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E →
        (y : Matrix (Fin 3) (Fin 3) K) * ((g * GeneralLinearGroup.scalar (Fin 3) m :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((g * GeneralLinearGroup.scalar (Fin 3) m : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * y := by
    intro y hy g m hg
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [← mul_assoc, hnab y g hy hg, mul_assoc,
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar m y).eq, mul_assoc]
  have hz12 : z₁ * z₂ = z₂ * z₁ := by
    rw [hz₁, hz₂]
    have := hcz (y₁ * GeneralLinearGroup.scalar (Fin 3) m₁) (by
      rw [QuotientGroup.mk_mul]
      have : ((GeneralLinearGroup.scalar (Fin 3) m₁ : GL (Fin 3) K) :
          GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨m₁, rfl⟩
      rw [this, mul_one]
      exact hx₁) (m := m₂) hx₂
    exact this
  obtain ⟨b, hb, hkl⟩ := exists_common_eigenbasis hτ hτ1 h3 hm₁ hm₂ hz12
  have hk' := fun r => (hkl r).1
  have hl' := fun r => (hkl r).2
  choose k hk using hk'
  choose l hl using hl'
  have hpowvec : ∀ (i j : Fin 3) (r : Fin 3), (z₁ ^ (i : ℕ) * z₂ ^ (j : ℕ)) *ᵥ b r =
      τ ^ ((i * k r + j * l r : Fin 3) : ℕ) • b r := by
    intro i j r
    have hp1 : ∀ n : ℕ, z₁ ^ n *ᵥ b r = (τ ^ (k r : ℕ)) ^ n • b r := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ, mul_comm]
    have hp2 : ∀ n : ℕ, z₂ ^ n *ᵥ b r = (τ ^ (l r : ℕ)) ^ n • b r := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ, mul_comm]
    rw [← Matrix.mulVec_mulVec, hp2, Matrix.mulVec_smul, hp1, smul_smul, tau_pow_mul_fin hτ,
      tau_pow_mul_fin hτ, ← tau_pow_fin_add hτ, add_comm]
  have hind : ∀ i j : Fin 3, (∃ c : Fin 3, ∀ r, i * k r + j * l r = c) → i = 0 ∧ j = 0 := by
    rintro i j ⟨c, hc⟩
    have hz : z₁ ^ (i : ℕ) * z₂ ^ (j : ℕ) = τ ^ (c : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      apply eq_of_mulVec_eq_of_linearIndependent hb
      intro r
      rw [hpowvec, hc r, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    have hsc : (y₁ * GeneralLinearGroup.scalar (Fin 3) m₁) ^ (i : ℕ) *
        (y₂ * GeneralLinearGroup.scalar (Fin 3) m₂) ^ (j : ℕ) ∈ StatedScalars (Fin 3) K :=
      mem_statedScalars_of_eq_smul (by rw [Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, ← hz₁, ← hz₂, hz]) (pow_ne_zero _ hτ0)
    have h1 : ((((y₁ * GeneralLinearGroup.scalar (Fin 3) m₁) ^ (i : ℕ) *
        (y₂ * GeneralLinearGroup.scalar (Fin 3) m₂) ^ (j : ℕ) : GL (Fin 3) K) :
          GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hsc
    have hm1 : ((GeneralLinearGroup.scalar (Fin 3) m₁ : GL (Fin 3) K) :
        GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨m₁, rfl⟩
    have hm2 : ((GeneralLinearGroup.scalar (Fin 3) m₂ : GL (Fin 3) K) :
        GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨m₂, rfl⟩
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hm1, hm2, mul_one] at h1
    exact eq_zero_of_pow_mul_pow_eq_one hx₁1 (hexp _ hx₁) hx₂n (hexp _ hx₂) h1
  obtain ⟨i₀, j₀, hinj⟩ := exists_injective_combination k l hind
  have hd : Function.Injective fun r => τ ^ ((i₀ * k r + j₀ * l r : Fin 3) : ℕ) :=
    (tau_pow_injective hτ hτ1).comp hinj
  have hm1 : ((GeneralLinearGroup.scalar (Fin 3) m₁ : GL (Fin 3) K) :
      GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨m₁, rfl⟩
  have hm2 : ((GeneralLinearGroup.scalar (Fin 3) m₂ : GL (Fin 3) K) :
      GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨m₂, rfl⟩
  refine ⟨b, hb, fun y hy r => ?_, (y₁ * GeneralLinearGroup.scalar (Fin 3) m₁) ^ (i₀ : ℕ) *
    (y₂ * GeneralLinearGroup.scalar (Fin 3) m₂) ^ (j₀ : ℕ), ?_, _, hd, fun r => ?_⟩
  rotate_left
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, hm1, hm2, mul_one, mul_one]
    exact mul_mem (pow_mem hx₁ _) (pow_mem hx₂ _)
  · rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hz₁, ← hz₂]
    exact hpowvec i₀ j₀ r
  refine exists_smul_of_commute_regular hb hd (hpowvec i₀ j₀) ?_ r
  have c1 : (y : Matrix (Fin 3) (Fin 3) K) * z₁ = z₁ * y := by rw [hz₁]; exact hcz y hy hx₁
  have c2 : (y : Matrix (Fin 3) (Fin 3) K) * z₂ = z₂ * y := by rw [hz₂]; exact hcz y hy hx₂
  exact ((Commute.pow_right c1 _).mul_right (Commute.pow_right c2 _)).eq

theorem card_le_nine_of_comm (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  by_cases hc : 3 < Nat.card E
  · rcases frame_or_heis h3 hτ hτ1 E hcomm hexp hc with ⟨b, hb, hd, -⟩ |
      ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
    · exact card_le_nine_of_frame E hexp hb hd
    · exact card_le_nine_of_heis h3 E hcomm hy₁ hy₂ hζ1 hζ
  · omega

end Classification

end CFSG.RankThree.PartTwo.Sec4
