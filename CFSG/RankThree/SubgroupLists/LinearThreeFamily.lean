module

public import CFSG.RankThree.SubgroupLists.CentralizerPerfect
public import CFSG.RankThree.SubgroupLists.RationalFiveExclusions
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups commutatorElement

section Model

variable {F : Type} [Field F]

@[expose] def leviMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem leviMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    leviMat (A * B) = leviMat A * leviMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem leviMat_one : leviMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat]

theorem det_leviMat (A : Matrix (Fin 2) (Fin 2) F) : (leviMat A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [leviMat]

@[expose] def levi3 : SL(2, F) →* SL(3, F) where
  toFun A := ⟨leviMat (A : Matrix (Fin 2) (Fin 2) F), by rw [det_leviMat, A.2]⟩
  map_one' := Subtype.ext (by
    change leviMat ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, leviMat_one])
  map_mul' A B := Subtype.ext (by
    change leviMat ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      leviMat (A : Matrix (Fin 2) (Fin 2) F) * leviMat (B : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, leviMat_mul])

theorem coe_levi3 (A : SL(2, F)) :
    ((levi3 A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = leviMat (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] def negDiagSL3 (F : Type) [Field F] : SL(3, F) :=
  ⟨diagonal ![-1, -1, 1], by simp [det_diagonal, Fin.prod_univ_three]⟩

theorem levi3_commute_negDiagSL3 (A : SL(2, F)) :
    levi3 A * negDiagSL3 F = negDiagSL3 F * levi3 A := by
  apply Subtype.ext
  change leviMat (A : Matrix (Fin 2) (Fin 2) F) * diagonal ![-1, -1, 1] =
    diagonal ![-1, -1, 1] * leviMat (A : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat, Matrix.mul_apply, diagonal]

theorem negDiagSL3_sq : negDiagSL3 F ^ 2 = 1 := by
  apply Subtype.ext
  rw [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change diagonal ![-1, -1, 1] * diagonal ![-1, -1, 1] = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal]

theorem negDiagSL3_not_mem_center (h2 : (2 : F) ≠ 0) :
    negDiagSL3 F ∉ Subgroup.center SL(3, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h0 := congrFun (congrFun hr 0) 0
  have h2' := congrFun (congrFun hr 2) 2
  simp [negDiagSL3, diagonal] at h0 h2'
  apply h2
  linear_combination h0 - h2'

theorem levi3_mem_center {A : SL(2, F)} (hA : levi3 A ∈ Subgroup.center SL(3, F)) : A = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, -, hr⟩ := hA
  have e := fun i j => congrFun (congrFun hr i) j
  have e22 := e 2 2
  simp [coe_levi3, leviMat] at e22
  subst e22
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := e (Fin.castSucc i) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simp [coe_levi3, leviMat] at this ⊢ <;> simp_all

end Model

section PSL3

variable {F : Type} [Field F]

@[expose] def leviPSL3 (F : Type) [Field F] : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F) :=
  ((QuotientGroup.mk' (Subgroup.center SL(3, F))).comp levi3).range

theorem leviPSL3_injective :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center SL(3, F))).comp
      (levi3 : SL(2, F) →* SL(3, F))) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply levi3_mem_center
  simpa [QuotientGroup.eq_one_iff] using hA

theorem card_leviPSL3 [Finite F] :
    Nat.card (leviPSL3 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [leviPSL3, ← Nat.card_congr (MonoidHom.ofInjective leviPSL3_injective).toEquiv,
    card_sl2_field]

theorem isPerfect_leviPSL3 [Finite F] (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (leviPSL3 F) := by
  have : Group.IsPerfect SL(2, F) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    classical
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
    exact ⟨s, hs⟩
  exact Group.IsPerfect.range _

@[expose] noncomputable def negDiagPSL3 (F : Type) [Field F] :
    ProjectiveSpecialLinearGroup (Fin 3) F :=
  QuotientGroup.mk' (Subgroup.center SL(3, F)) (negDiagSL3 F)

theorem negDiagPSL3_sq : negDiagPSL3 F ^ 2 = 1 := by
  rw [negDiagPSL3, ← map_pow, negDiagSL3_sq, map_one]

theorem negDiagPSL3_ne_one (h2 : (2 : F) ≠ 0) : negDiagPSL3 F ≠ 1 := by
  intro h
  apply negDiagSL3_not_mem_center h2
  simpa [negDiagPSL3, QuotientGroup.eq_one_iff] using h

theorem leviPSL3_commute (x : ProjectiveSpecialLinearGroup (Fin 3) F) (hx : x ∈ leviPSL3 F) :
    x * negDiagPSL3 F = negDiagPSL3 F * x := by
  obtain ⟨A, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, negDiagPSL3, ← map_mul,
    levi3_commute_negDiagSL3]

end PSL3

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have key : ∀ m n : ℕ, 1 ≤ m → m < n → m * (m ^ 2 - 1) < n * (n ^ 2 - 1) := by
    intro m n hm hmn
    have h1 : m ^ 2 - 1 ≤ n ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hmn.le 2) 1
    have h2 : 0 < n ^ 2 - 1 := by
      have : 2 ≤ n := by omega
      have : 4 ≤ n ^ 2 := by nlinarith
      omega
    calc m * (m ^ 2 - 1) ≤ m * (n ^ 2 - 1) := Nat.mul_le_mul_left m h1
      _ < n * (n ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hmn h2
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (key a b ha hab).ne
  · exact hab
  · exact absurd h.symm (key b a hb hab).ne

theorem eq_five_or_eq_of_card_sl2 {q p : ℕ} (hq : 1 ≤ q) (hp : 1 ≤ p)
    (h : q * (q ^ 2 - 1) = 120 ∨ q * (q ^ 2 - 1) = 40 ∨ q * (q ^ 2 - 1) = p * (p ^ 2 - 1)) :
    q = 5 ∨ q = p := by
  rcases h with h | h | h
  · left
    exact eq_of_mul_sq_sub_one_eq hq (by norm_num) (by rw [h]; norm_num)
  · exfalso
    rcases Nat.lt_or_ge q 4 with hq4 | hq4
    · interval_cases q <;> simp at h
    · have : 4 * (4 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq4
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 2) 1)
      omega
  · right
    exact eq_of_mul_sq_sub_one_eq hq hp h


section RationalFive

variable {F : Type} [Field F]

@[expose] def transvection13 (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def diag231 (h6 : (6 : F) = 1) : SL(3, F) :=
  ⟨diagonal ![2, 3, 1], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    linear_combination h6⟩

theorem transvection13_pow_five (h5 : (5 : F) = 0) : transvection13 F ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 5 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h5

theorem diag231_mul_transvection13 (h6 : (6 : F) = 1) :
    diag231 h6 * transvection13 F = transvection13 F ^ 2 * diag231 h6 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow]
  change diagonal ![2, 3, 1] * (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
    (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 2 * diagonal ![2, 3, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, diagonal]
  norm_num

theorem transvection13_not_mem_center : transvection13 F ∉ Subgroup.center SL(3, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 2
  simp [transvection13] at h

theorem exists_rational_five_psl3 [Finite F] (hF : Nat.card F = 5) :
    ∃ s g : ProjectiveSpecialLinearGroup (Fin 3) F, s ^ 5 = 1 ∧ s ≠ 1 ∧ g * s * g⁻¹ = s ^ 2 := by
  have h5 : (5 : F) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF] at h
    exact_mod_cast h
  have h6 : (6 : F) = 1 := by linear_combination h5
  set π := QuotientGroup.mk' (Subgroup.center SL(3, F))
  refine ⟨π (transvection13 F), π (diag231 h6), ?_, ?_, ?_⟩
  · rw [← map_pow, transvection13_pow_five h5, map_one]
  · intro h
    exact transvection13_not_mem_center (F := F) (by simpa [π, QuotientGroup.eq_one_iff] using h)
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, diag231_mul_transvection13 h6,
      mul_inv_cancel_right]

end RationalFive

section Recognition

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_toGL_iff {n : ℕ} {K : Type*} [Field K] (g : GL (Fin n) K) :
    g ∈ (SpecialLinearGroup.toGL : SL(n, K) →* GL (Fin n) K).range ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact A.2
  · intro h
    refine ⟨⟨(g : Matrix (Fin n) (Fin n) K), h⟩, ?_⟩
    apply Units.ext
    rfl

theorem commutatorElement_mul_mul_of_central {G : Type*} [Group G] {x₁ x₂ w₁ w₂ : G}
    (c1 : ∀ g : G, g * w₁ = w₁ * g) (c2 : ∀ g : G, g * w₂ = w₂ * g) :
    ⁅x₁ * w₁, x₂ * w₂⁆ = ⁅x₁, x₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x₁ * w₁ * (x₂ * w₂) * (x₁ * w₁)⁻¹ * (x₂ * w₂)⁻¹
      = x₁ * (w₁ * x₂) * w₂ * w₁⁻¹ * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * (x₂ * w₁) * w₂ * w₁⁻¹ * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by rw [c1 x₂]
    _ = x₁ * x₂ * (w₁ * w₂ * w₁⁻¹) * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * x₂ * (w₂ * w₁ * w₁⁻¹) * x₁⁻¹ * w₂⁻¹ * x₂⁻¹ := by rw [c1 w₂]
    _ = x₁ * x₂ * (w₂ * x₁⁻¹) * w₂⁻¹ * x₂⁻¹ := by group
    _ = x₁ * x₂ * (x₁⁻¹ * w₂) * w₂⁻¹ * x₂⁻¹ := by rw [c2 x₁⁻¹]
    _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by group

theorem card_center_sl3 {K : Type*} [Field K] [Finite K] :
    Nat.card (Subgroup.center SL(3, K)) = Nat.gcd (Nat.card K - 1) 3 := by
  have h : rootsOfUnity 3 K = (powMonoidHom 3 : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin, h, IsCyclic.card_powMonoidHom_ker, Nat.card_units]

theorem forall_mem_iff_det_of_psl3_card_eq {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {F : Type} [Field F] [Finite F]
    (hFp : Nat.card F = p) (e : (H ⧸ Subgroup.center H) ≃* ProjectiveSpecialLinearGroup (Fin 3) F) :
    ∀ g : GL (Fin 3) (ZMod p), g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
  classical
  set SLp := (SpecialLinearGroup.toGL : SL(3, ZMod p) →* GL (Fin 3) (ZMod p)).range with hSLp
  have hHle : H ≤ SLp := fun x hx => (mem_range_toGL_iff x).mpr (hdet x hx)
  set N := Nat.card SL(3, ZMod p) with hN
  have hNF : Nat.card SL(3, F) = N := by
    rw [hN, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFp,
      Nat.card_zmod]
  have hcardSLp : Nat.card SLp = N := by
    rw [hN]
    exact (Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv).symm
  have hNpos : 0 < N := Nat.card_pos
  set d := Nat.gcd (p - 1) 3 with hd
  have hdF : Nat.card (Subgroup.center SL(3, F)) = d := by rw [card_center_sl3, hFp]
  have hdp : Nat.card (Subgroup.center SL(3, ZMod p)) = d := by
    rw [card_center_sl3, Nat.card_zmod]
  set c := Nat.card (Subgroup.center H) with hc
  have hS : Nat.card (H ⧸ Subgroup.center H) * d = N := by
    rw [Nat.card_congr e.toEquiv, ← hdF, ← hNF]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  have hHcard : Nat.card H = Nat.card (H ⧸ Subgroup.center H) * c :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hHN : Nat.card H ≤ N := hcardSLp ▸ Subgroup.card_le_of_le hHle
  have hd3 : d = 1 ∨ d = 3 := (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right _ _)
  have hc3 : c = 1 ∨ c = 3 := (Nat.dvd_prime Nat.prime_three).mp hZ
  have hfull : Nat.card H = N → ∀ g : GL (Fin 3) (ZMod p),
      g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
    intro hHN' g
    have hEq : H = SLp := Subgroup.eq_of_le_of_card_ge hHle (by rw [hcardSLp, hHN'])
    rw [hEq, mem_range_toGL_iff]
  rcases hd3 with hd1 | hd3 <;> rcases hc3 with hc1 | hc3'
  · exact hfull (by rw [hHcard, hc1, mul_one, ← hS, hd1, mul_one])
  · exfalso
    have : Nat.card H = 3 * N := by rw [hHcard, hc3', ← hS, hd1, mul_one, mul_comm]
    omega
  ·
    exfalso
    have hH3 : Nat.card H * 3 = N := by
      rw [hHcard, hc1, mul_one, ← hS, hd3]
    set W := (Subgroup.center SL(3, ZMod p)).map
      (SpecialLinearGroup.toGL : SL(3, ZMod p) →* GL (Fin 3) (ZMod p)) with hW
    have hWcard : Nat.card W = 3 := by
      calc Nat.card W = Nat.card (Subgroup.center SL(3, ZMod p)) :=
            (Nat.card_congr ((Subgroup.center SL(3, ZMod p)).equivMapOfInjective _
              SpecialLinearGroup.toGL_injective).toEquiv).symm
        _ = 3 := by rw [hdp, hd3]
    have hWc : ∀ w ∈ W, ∀ g : GL (Fin 3) (ZMod p), g * w = w * g := by
      rintro _ ⟨z, hz, rfl⟩ g
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
      apply Units.ext
      simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, ← hr]
      exact (Matrix.scalar_commute r (fun _ => Commute.all _ _) _).symm
    have hWle : W ≤ SLp := by
      rintro _ ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
    have hHW : ∀ w ∈ W, w ∈ H → w = 1 := by
      intro w hw hwH
      have hz : (⟨w, hwH⟩ : H) ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro h
        exact Subtype.ext (hWc w hw h)
      have : Subgroup.center H = ⊥ := by
        rw [← Subgroup.card_eq_one, ← hc, hc1]
      rw [this, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    let μ : H × W → SLp := fun hw => ⟨hw.1 * hw.2, SLp.mul_mem (hHle hw.1.2) (hWle hw.2.2)⟩
    have hμ : Function.Injective μ := by
      rintro ⟨h₁, w₁⟩ ⟨h₂, w₂⟩ heq
      have heq' : (h₁ : GL (Fin 3) (ZMod p)) * w₁ = h₂ * w₂ := congrArg Subtype.val heq
      have hx : (h₂ : GL (Fin 3) (ZMod p))⁻¹ * h₁ = w₂ * (w₁ : GL (Fin 3) (ZMod p))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
      have h1 : (h₂ : GL (Fin 3) (ZMod p))⁻¹ * h₁ = 1 :=
        hHW _ (by rw [hx]; exact W.mul_mem w₂.2 (W.inv_mem w₁.2))
          (H.mul_mem (H.inv_mem h₂.2) h₁.2)
      have hh : h₁ = h₂ := Subtype.ext (by rw [inv_mul_eq_one] at h1; exact h1.symm)
      subst hh
      have hw : w₁ = w₂ := Subtype.ext (mul_left_cancel heq')
      rw [hw]
    have hμs : Function.Surjective μ := by
      have : Finite (H × W) := inferInstance
      have hcard : Nat.card (H × W) = Nat.card SLp := by
        rw [Nat.card_prod, hWcard, hH3, hcardSLp]
      exact (Function.Injective.bijective_of_nat_card_le hμ hcard.ge).2
    have hcommH : ⁅SLp, SLp⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨⟨h₁, w₁⟩, hμ1⟩ := hμs ⟨a, ha⟩
      obtain ⟨⟨h₂, w₂⟩, hμ2⟩ := hμs ⟨b, hb⟩
      have ha' : a = h₁ * w₁ := (congrArg Subtype.val hμ1).symm
      have hb' : b = h₂ * w₂ := (congrArg Subtype.val hμ2).symm
      have hcomm : ⁅a, b⁆ = ⁅(h₁ : GL (Fin 3) (ZMod p)), (h₂ : GL (Fin 3) (ZMod p))⁆ := by
        rw [ha', hb']
        exact commutatorElement_mul_mul_of_central (hWc w₁ w₁.2) (hWc w₂ w₂.2)
      rw [hcomm, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁.2 h₂.2) (H.inv_mem h₁.2)) (H.inv_mem h₂.2)
    have hperf : Group.IsPerfect SL(3, ZMod p) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have hSLperf : ⁅SLp, SLp⁆ = SLp := by
      rw [hSLp, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        hperf.commutator_eq_top]
    have hle : SLp ≤ H := hSLperf.ge.trans hcommH
    have := Subgroup.card_le_of_le hle
    omega
  · exact hfull (by rw [hHcard, hc3', ← hS, hd3])

theorem forall_mem_iff_det_of_psl3 (hp2 : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {F : Type} [Field F] [Finite F] (hF2 : (2 : F) ≠ 0)
    (hF4 : 4 ≤ Nat.card F) (e : (H ⧸ Subgroup.center H) ≃* ProjectiveSpecialLinearGroup (Fin 3) F) :
    Nat.card F = p ∧
      ∀ g : GL (Fin 3) (ZMod p), g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  set t := e.symm (negDiagPSL3 F) with ht
  set L := (leviPSL3 F).map e.symm.toMonoidHom with hLdef
  have : Group.IsPerfect (leviPSL3 F) := isPerfect_leviPSL3 hF4
  have hLp : Group.IsPerfect L := Group.IsPerfect.map _
  have hLcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← card_leviPSL3]
    exact (Nat.card_congr ((leviPSL3 F).equivMapOfInjective _ e.symm.injective).toEquiv).symm
  have hL : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card L = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hLcard] at h1
    have : 4 * (4 ^ 2 - 1) ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul hF4
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF4 2) 1)
    omega
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, negDiagPSL3_sq, map_one]
  have ht1 : t ≠ 1 := fun h => negDiagPSL3_ne_one hF2 (e.symm.injective (by rw [← ht, h, map_one]))
  have hLt : ∀ x ∈ L, x * t = t * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ht, ← map_mul, leviPSL3_commute y hy]
  have hcard := card_perfect_of_le_centralizer hp2 hdet hZ ht2 ht1 L hL hLt
  rw [hLcard] at hcard
  have hq : Nat.card F = p := by
    rcases eq_five_or_eq_of_card_sl2 Nat.card_pos hp1 hcard with h5 | hp
    ·
      obtain ⟨s, g, hs5, hs1, hg⟩ := exists_rational_five_psl3 h5
      have h5p := five_eq_zero_of_rational_five hdet hZ3
        (s := e.symm s) (g := e.symm g) (by rw [← map_pow, hs5, map_one])
        (fun h => hs1 (e.symm.injective (by rw [h, map_one])))
        (by rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow])
      have hdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp (by exact_mod_cast h5p)
      rw [h5]
      exact ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd).symm
    · exact hp
  exact ⟨hq, forall_mem_iff_det_of_psl3_card_eq hdet hZ hq e⟩

end Recognition

end CFSG.RankThree.SubgroupLists
