module

public import CFSG.Quasithin.Background.A318PL3Core
public import CFSG.Quasithin.Background.A318PHeis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {K : Type} [Field K]


@[expose] def heisASL (ω : K) (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K := ⟨heisA ω, det_heisA hω⟩

@[expose] def heisBSL : SpecialLinearGroup (Fin 3) K := ⟨heisB, det_heisB⟩

@[simp] theorem coe_heisASL {ω : K} (hω : ω ^ 3 = 1) :
    (heisASL ω hω : Matrix (Fin 3) (Fin 3) K) = heisA ω := rfl

@[simp] theorem coe_heisBSL : ((heisBSL : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisB := rfl

theorem heisASL_pow_three {ω : K} (hω : ω ^ 3 = 1) : heisASL ω hω ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h := Matrix.SpecialLinearGroup.coe_pow (heisASL ω hω) 3
  exact (congr_fun (congr_fun h i) j).trans (by rw [coe_heisASL, heisA_pow_three hω]; rfl)

theorem heisBSL_pow_three : (heisBSL : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h := Matrix.SpecialLinearGroup.coe_pow (heisBSL : SpecialLinearGroup (Fin 3) K) 3
  exact (congr_fun (congr_fun h i) j).trans (by rw [coe_heisBSL, heisB_pow_three]; rfl)

theorem heisASL_mul_heisBSL {ω : K} (hω : ω ^ 3 = 1) (hω0 : ω ≠ 0) :
    heisASL ω hω * heisBSL =
      scalarElement (Units.mk0 ω hω0) (by ext; simpa using hω) * (heisBSL * heisASL ω hω) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h1 := Matrix.SpecialLinearGroup.coe_mul (heisASL ω hω) (heisBSL : SpecialLinearGroup (Fin 3) K)
  have h2 := Matrix.SpecialLinearGroup.coe_mul (heisBSL : SpecialLinearGroup (Fin 3) K) (heisASL ω hω)
  have h3 := Matrix.SpecialLinearGroup.coe_mul
    (scalarElement (Units.mk0 ω hω0) (by ext; simpa using hω) : SpecialLinearGroup (Fin 3) K)
    (heisBSL * heisASL ω hω)
  refine (congr_fun (congr_fun h1 i) j).trans (Eq.trans ?_ (congr_fun (congr_fun h3 i) j).symm)
  rw [coe_scalarElement, h2, coe_heisASL, coe_heisBSL, heisA_mul_heisB hω,
    Matrix.smul_eq_diagonal_mul]
  rfl



theorem exists_nine_projectiveSL [Finite K] {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (σ : K ≃+* K) (hσ : σ ω = ω) :
    ∃ E : Subgroup (projectiveSL 3 K), Nat.card E = 9 ∧ (∀ a b : E, a * b = b * a) ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ ∀ y ∈ E, fieldAut 3 K σ y = y := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  set A : SpecialLinearGroup (Fin 3) K := heisASL ω hω with hA
  set B : SpecialLinearGroup (Fin 3) K := heisBSL with hB
  have hAB : A * B = scalarElement (Units.mk0 ω hω0) (by ext; simpa using hω) * (B * A) :=
    heisASL_mul_heisBSL hω hω0
  have hu : proj 3 K A ^ 3 = 1 := by rw [← map_pow, heisASL_pow_three hω, map_one]
  have hv : proj 3 K B ^ 3 = 1 := by rw [← map_pow, heisBSL_pow_three, map_one]
  have hcomm : proj 3 K A * proj 3 K B = proj 3 K B * proj 3 K A := by
    rw [← map_mul, ← map_mul, proj_eq_proj_iff, hAB]
    have hz : scalarElement (Units.mk0 ω hω0) (by ext; simpa using hω) ∈ scalars 3 K :=
      scalarElement_mem_scalars _ _
    have hz' := (scalars 3 K).inv_mem hz
    have hcen := Subgroup.mem_center_iff.1 ((scalars_eq_center 3 K) ▸ hz') (B * A)
    rw [_root_.mul_inv_rev, mul_assoc, ← hcen, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hz'
  have hind : ∀ i j : ℕ, proj 3 K A ^ i * proj 3 K B ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j h
    rw [← map_pow, ← map_pow, ← map_mul, proj_eq_one_iff] at h
    obtain ⟨c, -, hc⟩ := (mem_scalars).1 h
    refine heis_indep hω hω1 i j (c : K) ?_
    have h1 := Matrix.SpecialLinearGroup.coe_mul (A ^ i) (B ^ j)
    have h2 := Matrix.SpecialLinearGroup.coe_pow A i
    have h3 := Matrix.SpecialLinearGroup.coe_pow B j
    rw [h1, h2, h3] at hc
    exact hc
  obtain ⟨E, hE9, hEc, hE3, hEfix⟩ := exists_nine_of_commuting hu hv hcomm hind
  refine ⟨E, hE9, hEc, hE3, fun y hy => ?_⟩
  refine hEfix (fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K) ?_ ?_ y hy
  · change fieldAut 3 K σ (proj 3 K A) = proj 3 K A
    rw [fieldAut_proj]
    congr 1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_heisASL, RingHom.mapMatrix_apply]
    simp only [heisA]
    rw [Matrix.diagonal_map (by simp)]
    congr 1
    ext a
    fin_cases a <;> simp [hσ]
  · change fieldAut 3 K σ (proj 3 K B) = proj 3 K B
    rw [fieldAut_proj]
    congr 1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_heisBSL, RingHom.mapMatrix_apply]
    fin_cases i <;> fin_cases j <;> simp [heisB]


theorem exists_cube_root_of_unity [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h
  refine ⟨(u : K), ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    omega

theorem ringEquiv_fix_cube_root {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K} (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : σ ω = ω := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hω1
    · exact h
  have hσ3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
    have h := congrArg (fun τ : K ≃+* K => τ x) hσ
    simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] at h
    exact h
  have h1 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  have h2 : σ ω ≠ 1 := fun h => hω1 (σ.injective (by rw [h, map_one]))
  have hprod : (σ ω - 1) * (σ ω - ω) * (σ ω - ω ^ 2) = 0 := by
    linear_combination h1 - ((σ ω) ^ 2 - σ ω) * hsum + (σ ω - 1) * hω
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) h2
    · exact sub_eq_zero.1 h
  · have h3 : σ ω = ω ^ 2 := sub_eq_zero.1 h
    have h4 : σ (σ ω) = ω := by
      rw [h3, map_pow, h3]
      linear_combination ω * hω
    have h5 := hσ3 ω
    rw [h4, h3] at h5
    exfalso
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination h5
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hω0
    · exact sub_eq_zero.1 h

theorem exists_not_cube [Finite K] (h3 : 3 ∣ Nat.card K - 1) : ∃ a : Kˣ, ∀ c : Kˣ, c ^ 3 ≠ a := by
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root_of_unity h3
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun c : Kˣ => c ^ 3) := fun a => hcon a
  have hinj : Function.Injective (fun c : Kˣ => c ^ 3) := Finite.injective_iff_surjective.2 hsurj
  have h := @hinj (Units.mk0 ω hω0) 1 (by
    apply Units.ext
    simp [hω])
  exact hω1 (by simpa using congrArg Units.val h)

theorem exists_conjAut_not_inner [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ A : GL (Fin 3) K, conjAut 3 K A ∉ inner (projectiveSL 3 K) := by
  obtain ⟨a, ha⟩ := exists_not_cube h3
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (R := K) (n := Fin 3) a
  refine ⟨A, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  have h1 : conjAut 3 K (A⁻¹ * SpecialLinearGroup.toGL g) * fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, conjAut_toGL, hx, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h1
  have hg : GeneralLinearGroup.det (SpecialLinearGroup.toGL g) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    simp
  have hdet := congrArg GeneralLinearGroup.det hc
  rw [Matrix.GeneralLinearGroup.det_scalar, map_mul, map_inv, hA, hg, Fintype.card_fin,
    mul_one] at hdet
  exact ha c⁻¹ (by rw [inv_pow, hdet, inv_inv])

theorem relIndex_inner_linearAutGroup_eq_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    (inner (projectiveSL 3 K)).relIndex (linearAutGroup 3 K) = 3 := by
  have h := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := 3) (by norm_num)
  rw [Nat.gcd_eq_left h3] at h
  rcases (Nat.dvd_prime Nat.prime_three).1 h with h1 | h1
  · exfalso
    obtain ⟨A, hA⟩ := exists_conjAut_not_inner h3
    exact hA ((Subgroup.relIndex_eq_one.1 h1) (conjAut_mem_linearAutGroup A))
  · exact h1

theorem mem_semilinear_of_orderOf_three_pow [Finite K] {α : MulAut (projectiveSL 3 K)} {k : ℕ}
    (hα : orderOf α = 3 ^ k) : α ∈ semilinearAutGroup 3 K := by
  have hR := (automorphism_generation (K := K) (n := 3) le_rfl).1
  have hmem : α ∈ standardAutGroup 3 K := hR ▸ Subgroup.mem_top α
  have hδδ := (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hsq : α ^ 2 ∈ semilinearAutGroup 3 K := by
    rcases mem_or_mul_dualAut_mem hmem with h | h
    · exact pow_mem h 2
    · have h2 : α ^ 2 = (α * dualAut 3 K) * (dualAut 3 K * (α * dualAut 3 K) * dualAut 3 K) := by
        rw [show (α * dualAut 3 K) * (dualAut 3 K * (α * dualAut 3 K) * dualAut 3 K) =
          α * (dualAut 3 K * dualAut 3 K) * α * (dualAut 3 K * dualAut 3 K) by group, hδδ]
        simp [pow_two]
      rw [h2]
      exact mul_mem h (dualAut_mul_mul_dualAut_mem h)
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k + 1 = 2 * m := by
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    exact ⟨j + 1, by omega⟩
  have hpow : α ^ (3 ^ k) = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have : α = (α ^ 2) ^ m := by
    rw [← pow_mul, ← hm, pow_succ, hpow, one_mul]
  rw [this]
  exact pow_mem hsq m

@[expose] noncomputable def l3FrameLinear [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    L3Frame (projectiveSL 3 K) (K ≃+* K) where
  D := linearAutGroup 3 K
  fld := fieldAut 3 K
  inner_le := (standard_outer_quotients (n := 3) (K := K)).1
  fld_norm := fun c d hd => by
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.1 hd
    rw [(standard_automorphism_transport (K := K) (n := 3)).2.2.1]
    exact conjAut_mem_linearAutGroup _
  fld_inter := fun c hc => by
    obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.1 hc
    have : conjAut 3 K B⁻¹ * fieldAut 3 K c = 1 := by rw [map_inv, hB, inv_mul_cancel]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ this).1
  three_mem := fun α k hα => by
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinear_of_orderOf_three_pow hα)
    exact ⟨conjAut 3 K A, conjAut_mem_linearAutGroup A, σ, rfl⟩
  card_DI := relIndex_inner_linearAutGroup_eq_three h3
  lang := fun α hα _ hαD => by
    obtain ⟨σ, hσ, H, rfl⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (le_refl 3) α hα hαD
    exact ⟨conjAut 3 K H, conjAut_mem_linearAutGroup H, σ, hσ, rfl⟩
  nine := fun c hc => by
    obtain ⟨ω, hω, hω1⟩ := exists_cube_root_of_unity h3
    have hσ3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    obtain ⟨E, hE9, hEc, hE3, hEfix⟩ :=
      exists_nine_projectiveSL hω hω1 c (ringEquiv_fix_cube_root hσ3 hω hω1)
    exact ⟨E, hE9, ⟨⟨⟨fun a b => hEc a b⟩⟩, hE3⟩, hEfix⟩

end A318P

end CFSG.Quasithin
