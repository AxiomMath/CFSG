module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.Kit
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

local notation "PSL37" => Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)

@[expose] def dT7 : Fin 3 → ZMod 7 := ![1, 2, 4]

@[expose] def tMat7 : Matrix (Fin 3) (Fin 3) (ZMod 7) := Matrix.diagonal dT7

@[expose] def fMat7 : Matrix (Fin 3) (Fin 3) (ZMod 7) := !![6, 6, 6; 6, 5, 3; 6, 3, 5]

@[expose] def pMat7 : Matrix (Fin 3) (Fin 3) (ZMod 7) := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def dMat7 : Matrix (Fin 3) (Fin 3) (ZMod 7) := Matrix.diagonal ![1, 6, 6]

theorem det_tMat7 : tMat7.det = 1 := by
  rw [tMat7, Matrix.det_diagonal, Fin.prod_univ_three]; decide
theorem det_fMat7 : fMat7.det = 1 := by
  rw [Matrix.det_fin_three]; decide
theorem det_pMat7 : pMat7.det = 1 := by
  rw [Matrix.det_fin_three]; decide

theorem det_diag7 (a b c : ZMod 7) (h : a * b * c = 1) :
    (Matrix.diagonal ![a, b, c]).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]; simpa using h

@[expose] def tSL7 : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨tMat7, det_tMat7⟩
@[expose] def fSL7 : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨fMat7, det_fMat7⟩
@[expose] def pSL7 : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨pMat7, det_pMat7⟩

theorem fSL7_mul_tSL7 : fSL7 * tSL7 = pSL7 * fSL7 := by
  apply Subtype.ext
  show fMat7 * tMat7 = pMat7 * fMat7
  decide +kernel

@[expose] def dSL7 : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨dMat7, det_diag7 1 6 6 (by decide)⟩

@[expose] def IsV7 (A : Matrix (Fin 3) (Fin 3) (ZMod 7)) : Prop :=
  ∃ a b : ZMod 7, (a = 1 ∨ a = 6) ∧ (b = 1 ∨ b = 6) ∧ A = Matrix.diagonal ![a, b, a * b]

theorem sign7_mul : ∀ a b : ZMod 7, (a = 1 ∨ a = 6) → (b = 1 ∨ b = 6) → (a * b = 1 ∨ a * b = 6) := by
  decide

theorem sign7_sq : ∀ a : ZMod 7, (a = 1 ∨ a = 6) → a * a = 1 := by decide

theorem isV7_det {A : Matrix (Fin 3) (Fin 3) (ZMod 7)} (h : IsV7 A) : A.det = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h1 := sign7_sq a ha
  have h2 := sign7_sq b hb
  linear_combination (b * b) * h1 + h2

theorem isV7_mul {A B : Matrix (Fin 3) (Fin 3) (ZMod 7)} (hA : IsV7 A) (hB : IsV7 B) :
    IsV7 (A * B) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hA
  obtain ⟨a', b', ha', hb', rfl⟩ := hB
  refine ⟨a * a', b * b', sign7_mul a a' ha ha', sign7_mul b b' hb hb', ?_⟩
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

theorem isV7_sq {A : Matrix (Fin 3) (Fin 3) (ZMod 7)} (hA : IsV7 A) : A * A = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hA
  have h1 := sign7_sq a ha
  have h2 := sign7_sq b hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp
  · exact h1
  · exact h2
  · linear_combination (b * b) * h1 + h2

theorem isV7_comm {A : Matrix (Fin 3) (Fin 3) (ZMod 7)} (hA : IsV7 A) : A * tMat7 = tMat7 * A := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hA
  rw [tMat7, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem isV7_scalar {A : Matrix (Fin 3) (Fin 3) (ZMod 7)} (hA : IsV7 A) (c : ZMod 7)
    (h : A = Matrix.diagonal (fun _ => c)) : A = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hA
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  have h2 := congrFun (congrFun h 2) 2
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hba : b = a := h1.trans h0.symm
  subst hba
  have h3 := sign7_sq b hb
  have hb1 : b = 1 := by rw [h0, ← h2, h3]
  subst hb1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isV7_dMat7 : IsV7 dMat7 := ⟨1, 6, Or.inl rfl, Or.inr rfl, by rw [dMat7]; decide⟩

@[expose] def vSub7 : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 7)) where
  carrier := {g | IsV7 (g : Matrix (Fin 3) (Fin 3) (ZMod 7))}
  one_mem' := ⟨1, 1, Or.inl rfl, Or.inl rfl, by
    rw [Matrix.SpecialLinearGroup.coe_one]; decide⟩
  mul_mem' := fun {a b} ha hb => by
    show IsV7 ((a * b : SpecialLinearGroup (Fin 3) (ZMod 7)) : Matrix (Fin 3) (Fin 3) (ZMod 7))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact isV7_mul ha hb
  inv_mem' := fun {g} hg => by
    have h1 : g * g = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact isV7_sq hg)
    show IsV7 ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 7)) : Matrix (Fin 3) (Fin 3) (ZMod 7))
    rw [inv_eq_of_mul_eq_one_right h1]
    exact hg

theorem vSub7_comm {g : SpecialLinearGroup (Fin 3) (ZMod 7)} (hg : g ∈ vSub7) :
    g * tSL7 = tSL7 * g :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]; exact isV7_comm hg)

theorem vSub7_sq {g : SpecialLinearGroup (Fin 3) (ZMod 7)} (hg : g ∈ vSub7) : g ^ 2 = 1 :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]; exact isV7_sq hg)

theorem dSL7_mem : dSL7 ∈ vSub7 := isV7_dMat7

theorem card_vSub7 : Nat.card vSub7 = 4 := by
  let S := {t : ZMod 7 × ZMod 7 // (t.1 = 1 ∨ t.1 = 6) ∧ (t.2 = 1 ∨ t.2 = 6)}
  have hS : Nat.card S = 4 := by
    rw [Nat.card_eq_fintype_card]; decide
  let f : S → vSub7 := fun t => ⟨⟨Matrix.diagonal ![t.1.1, t.1.2, t.1.1 * t.1.2],
    isV7_det ⟨t.1.1, t.1.2, t.2.1, t.2.2, rfl⟩⟩, ⟨t.1.1, t.1.2, t.2.1, t.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro t u htu
      have h := congrArg (fun g : vSub7 =>
        ((g : SpecialLinearGroup (Fin 3) (ZMod 7)) : Matrix (Fin 3) (Fin 3) (ZMod 7))) htu
      have h0 := congrFun (congrFun h 0) 0
      have h1 := congrFun (congrFun h 1) 1
      simp [f] at h0 h1
      exact Subtype.ext (Prod.ext h0 h1)
    · rintro ⟨g, a, b, ha, hb, hg⟩
      exact ⟨⟨(a, b), ha, hb⟩, Subtype.ext (Subtype.ext hg.symm)⟩
  rw [← hS, Nat.card_congr (Equiv.ofBijective f hf)]

@[expose] def vBar7 : Subgroup (PSL37) :=
  vSub7.map (QuotientGroup.mk' _)

theorem scalar_mem_SL {c : ZMod 7} (hc : c ^ 3 = 1) :
    (Matrix.scalar (Fin 3) c).det = 1 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hc]

theorem mul_scalar7 (M : Matrix (Fin 3) (Fin 3) (ZMod 7)) (c : ZMod 7) :
    M * Matrix.scalar (Fin 3) c = c • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem mk_comm_iff (g h : SpecialLinearGroup (Fin 3) (ZMod 7)) :
    ((g : PSL37) * h = h * g) ↔
      ∃ c : ZMod 7, c ^ 3 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 7)) * h = c • ((h : Matrix (Fin 3) (Fin 3) (ZMod 7)) * g) := by
  constructor
  · intro H
    have H' : (h * g)⁻¹ * (g * h) ∈ Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7)) := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact H.symm
    obtain ⟨c, hc, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp H'
    rw [Fintype.card_fin] at hc
    refine ⟨c, hc, ?_⟩
    have h1 : g * h = (h * g) * ((h * g)⁻¹ * (g * h)) := by group
    rw [← Matrix.SpecialLinearGroup.coe_mul, h1, Matrix.SpecialLinearGroup.coe_mul (h * g), ← hcz, mul_scalar7,
      Matrix.SpecialLinearGroup.coe_mul]
  · rintro ⟨c, hc, hgh⟩
    let z : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨Matrix.scalar (Fin 3) c, scalar_mem_SL hc⟩
    have hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7)) :=
      Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by rw [Fintype.card_fin]; exact hc, rfl⟩
    have h1 : g * h = (h * g) * z := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hgh]
      exact (mul_scalar7 _ c).symm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h1]
    have : (h * g * z)⁻¹ * (h * g) = z⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hz

theorem mk_sq_iff (g : SpecialLinearGroup (Fin 3) (ZMod 7)) :
    ((g : PSL37) ^ 2 = 1) ↔
      ∃ μ : ZMod 7, μ ^ 3 = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 7)) * g = μ • (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff,
    Fintype.card_fin]
  constructor
  · rintro ⟨μ, hμ, hμg⟩
    refine ⟨μ, hμ, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two] at hμg
    rw [← hμg, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rintro ⟨μ, hμ, hμg⟩
    refine ⟨μ, hμ, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hμg, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem cube_roots_seven : ∀ c : ZMod 7, c ^ 3 = 1 → c = 1 ∨ c = 2 ∨ c = 4 := by decide +kernel

theorem diag_cases : ∀ a b c μ : ZMod 7, a * a = μ → b * b = μ → c * c = μ → μ ^ 3 = 1 →
    a * b * c = 1 → ∃ ν : ZMod 7, ν ^ 3 = 1 ∧
      ((a = ν ∧ b = ν ∧ c = ν) ∨ (a = ν ∧ b = 6 * ν ∧ c = 6 * ν) ∨
        (a = 6 * ν ∧ b = ν ∧ c = 6 * ν) ∨ (a = 6 * ν ∧ b = 6 * ν ∧ c = ν)) := by
  decide +kernel

theorem shape_of_comm_t (g : Matrix (Fin 3) (Fin 3) (ZMod 7)) (c : ZMod 7) (hc : c ^ 3 = 1)
    (hgt : g * tMat7 = c • (tMat7 * g)) (μ : ZMod 7) (hμ : μ ^ 3 = 1)
    (hg2 : g * g = μ • (1 : Matrix (Fin 3) (Fin 3) (ZMod 7))) (hdet : g.det = 1) :
    ∃ ν : ZMod 7, ν ^ 3 = 1 ∧ ∃ v, IsV7 v ∧ g = ν • v := by
  have hent : ∀ i j, g i j * dT7 j = c * (dT7 i * g i j) := fun i j => by
    have := congrFun (congrFun hgt i) j
    rw [Matrix.smul_apply, tMat7, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul] at this
    exact this
  have hz : ∀ i j, g i j = 0 ∨ dT7 j = c * dT7 i := fun i j => by
    have h1 : g i j * (dT7 j - c * dT7 i) = 0 := by linear_combination hent i j
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have h00 : (g * g) 0 0 = μ := by rw [hg2]; simp
  have h11 : (g * g) 1 1 = μ := by rw [hg2]; simp
  have h22 : (g * g) 2 2 = μ := by rw [hg2]; simp
  have hμ0 : μ ≠ 0 := by rintro rfl; norm_num at hμ
  rcases cube_roots_seven c hc with rfl | rfl | rfl
  ·
    have z01 : g 0 1 = 0 := (hz 0 1).resolve_right (by decide)
    have z02 : g 0 2 = 0 := (hz 0 2).resolve_right (by decide)
    have z10 : g 1 0 = 0 := (hz 1 0).resolve_right (by decide)
    have z12 : g 1 2 = 0 := (hz 1 2).resolve_right (by decide)
    have z20 : g 2 0 = 0 := (hz 2 0).resolve_right (by decide)
    have z21 : g 2 1 = 0 := (hz 2 1).resolve_right (by decide)
    have hg : g = Matrix.diagonal ![g 0 0, g 1 1, g 2 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [z01, z02, z10, z12, z20, z21]
    have ha : g 0 0 * g 0 0 = μ := by
      rw [← h00, Matrix.mul_apply, Fin.sum_univ_three, z01, z02]; ring
    have hb : g 1 1 * g 1 1 = μ := by
      rw [← h11, Matrix.mul_apply, Fin.sum_univ_three, z10, z12]; ring
    have hc' : g 2 2 * g 2 2 = μ := by
      rw [← h22, Matrix.mul_apply, Fin.sum_univ_three, z20, z21]; ring
    have hd : g 0 0 * g 1 1 * g 2 2 = 1 := by
      rw [hg, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
      simpa using hdet
    obtain ⟨ν, hν, hcase⟩ := diag_cases _ _ _ _ ha hb hc' hμ hd
    refine ⟨ν, hν, ?_⟩
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · refine ⟨Matrix.diagonal ![1, 1, 1], ⟨1, 1, Or.inl rfl, Or.inl rfl, by decide⟩, ?_⟩
      rw [hg, e1, e2, e3]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · refine ⟨Matrix.diagonal ![1, 6, 6], ⟨1, 6, Or.inl rfl, Or.inr rfl, by decide⟩, ?_⟩
      rw [hg, e1, e2, e3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]
    · refine ⟨Matrix.diagonal ![6, 1, 6], ⟨6, 1, Or.inr rfl, Or.inl rfl, by decide⟩, ?_⟩
      rw [hg, e1, e2, e3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]
    · refine ⟨Matrix.diagonal ![6, 6, 1], ⟨6, 6, Or.inr rfl, Or.inr rfl, by decide⟩, ?_⟩
      rw [hg, e1, e2, e3]
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]
  ·
    exfalso
    have z00 : g 0 0 = 0 := (hz 0 0).resolve_right (by decide)
    have z10 : g 1 0 = 0 := (hz 1 0).resolve_right (by decide)
    have z02 : g 0 2 = 0 := (hz 0 2).resolve_right (by decide)
    apply hμ0
    rw [← h00, Matrix.mul_apply, Fin.sum_univ_three, z00, z10, z02]; ring
  ·
    exfalso
    have z00 : g 0 0 = 0 := (hz 0 0).resolve_right (by decide)
    have z01 : g 0 1 = 0 := (hz 0 1).resolve_right (by decide)
    have z20 : g 2 0 = 0 := (hz 2 0).resolve_right (by decide)
    apply hμ0
    rw [← h00, Matrix.mul_apply, Fin.sum_univ_three, z00, z01, z20]; ring

theorem mem_vBar7_iff (x : PSL37) :
    x ∈ vBar7 ↔ x * (tSL7 : PSL37) =
      (tSL7 : PSL37) * x ∧ x ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  constructor
  · rintro ⟨v, hv, hvg⟩
    rw [← hvg]
    change (v : PSL37) * tSL7 = tSL7 * v ∧
      (v : PSL37) ^ 2 = 1
    refine ⟨by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, vSub7_comm hv], ?_⟩
    rw [← QuotientGroup.mk_pow, vSub7_sq hv, QuotientGroup.mk_one]
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc, hgt⟩ := (mk_comm_iff g tSL7).mp h1
    obtain ⟨μ, hμ, hg2⟩ := (mk_sq_iff g).mp h2
    obtain ⟨ν, hν, v, hv, hgv⟩ := shape_of_comm_t (g : Matrix (Fin 3) (Fin 3) (ZMod 7)) c hc hgt μ hμ
      hg2 g.2
    set w : SpecialLinearGroup (Fin 3) (ZMod 7) := ⟨v, isV7_det hv⟩ with hw
    have hwS : w ∈ vSub7 := hv
    refine ⟨w, hwS, ?_⟩
    change (w : PSL37) = g
    rw [QuotientGroup.eq]
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨ν, by rw [Fintype.card_fin]; exact hν, ?_⟩
    have hvi : v * v = 1 := isV7_sq hv
    have hwinv : ((w⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 7)) : Matrix (Fin 3) (Fin 3) (ZMod 7)) =
        v := by
      have h' : w⁻¹ = w := by
        rw [inv_eq_iff_mul_eq_one]
        exact Subtype.ext hvi
      rw [h']
    rw [Matrix.SpecialLinearGroup.coe_mul, hwinv, hgv, Matrix.mul_smul, hvi, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

theorem card_vBar7 : Nat.card vBar7 = 4 := by
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center
      (SpecialLinearGroup (Fin 3) (ZMod 7)))).comp vSub7.subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hvc : (v : SpecialLinearGroup (Fin 3) (ZMod 7)) ∈ Subgroup.center _ :=
      (QuotientGroup.eq_one_iff _).mp hv
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hvc
    apply Subtype.ext
    apply Subtype.ext
    exact isV7_scalar v.2 c (by rw [← hc, Matrix.scalar_apply])
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [range_comp_subtype] at h1
  rw [vBar7, ← h1]
  show Nat.card vSub7 = 4
  exact card_vSub7

theorem isPGroup_closure_pair {H₀ : Type*} [Group H₀] {a b : H₀} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) : IsPGroup 3 (Subgroup.closure ({a, b} : Set H₀)) := by
  set K := Subgroup.closure ({a, b} : Set H₀)
  have hKc : K ≤ Subgroup.centralizer ({a, b} : Set H₀) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro y (rfl | rfl)
      · rfl
      · exact hab.symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro y (rfl | rfl)
      · exact hab
      · rfl
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have : K ≤ Subgroup.centralizer ({x} : Set H₀) := by
      rw [Subgroup.closure_le]
      rintro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hKc hx) z hz)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  have h3 : ∀ x ∈ K, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hcomm x hx y hy) 3), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro x
  exact ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩

theorem conj_mem_map_iff {H₀ : Type*} [Group H₀] (g c : H₀) (V : Subgroup H₀)
    (hV : ∀ σ : H₀, σ ∈ V ↔ σ * c = c * σ ∧ σ ^ 2 = 1) (h : H₀) :
    h ∈ V.map (MulAut.conj g).toMonoidHom ↔ h * (g * c * g⁻¹) = (g * c * g⁻¹) * h ∧ h ^ 2 = 1 := by
  rw [Subgroup.mem_map_equiv, hV]
  have : (MulAut.conj g).symm h = g⁻¹ * h * g := by
    rw [MulAut.conj_symm_apply]
  rw [this, conj_comm_iff, conj_sq_iff]

set_option maxRecDepth 100000 in
theorem tSL7_cube' : tSL7 * (tSL7 * tSL7) = 1 := by decide +kernel
theorem tSL7_cube : tSL7 ^ 3 = 1 := by rw [pow_three]; exact tSL7_cube'
set_option maxRecDepth 100000 in
theorem pSL7_cube' : pSL7 * (pSL7 * pSL7) = 1 := by decide +kernel
theorem pSL7_cube : pSL7 ^ 3 = 1 := by rw [pow_three]; exact pSL7_cube'
theorem tSL7_pSL7 : (tSL7 : Matrix (Fin 3) (Fin 3) (ZMod 7)) * pSL7 =
    (4 : ZMod 7) • ((pSL7 : Matrix (Fin 3) (Fin 3) (ZMod 7)) * tSL7) := by decide +kernel
theorem dMat7_pMat7 : ∀ c : ZMod 7, ¬ (dMat7 * pMat7 = c • (pMat7 * dMat7)) := by decide +kernel

theorem twoInvCent_psl_three_seven :
    TwoInvCent (PSL37) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpb : (pSL7 : PSL37) = (fSL7 : PSL37) * (tSL7 : PSL37) * (fSL7 : PSL37)⁻¹ := by
    have h1 : (fSL7 : PSL37) * tSL7 = (pSL7 : PSL37) * fSL7 := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, fSL7_mul_tSL7]
    calc (pSL7 : PSL37) = (pSL7 : PSL37) * fSL7 * (fSL7 : PSL37)⁻¹ := by group
      _ = (fSL7 : PSL37) * (tSL7 : PSL37) * (fSL7 : PSL37)⁻¹ := by rw [← h1]
  have htp : (tSL7 : PSL37) * (pSL7 : PSL37) = (pSL7 : PSL37) * (tSL7 : PSL37) :=
    (mk_comm_iff tSL7 pSL7).mpr ⟨4, by decide, tSL7_pSL7⟩
  have ht3 : (tSL7 : PSL37) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, tSL7_cube, QuotientGroup.mk_one]
  have hp3 : (pSL7 : PSL37) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, pSL7_cube, QuotientGroup.mk_one]
  obtain ⟨T₀, hT₀⟩ := (isPGroup_closure_pair ht3 hp3 htp).exists_le_sylow
  intro T
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq PSL37 T₀ T
  have hT : (T : Subgroup PSL37) = (T₀ : Subgroup PSL37).map (MulAut.conj h).toMonoidHom := by
    rw [← hh, Sylow.coe_subgroup_smul]
    rfl
  have hmem : ∀ x ∈ (T₀ : Subgroup PSL37), h * x * h⁻¹ ∈ (T : Subgroup PSL37) := fun x hx => by
    rw [hT]; exact ⟨x, hx, rfl⟩
  have htT : (tSL7 : PSL37) ∈ (T₀ : Subgroup PSL37) := hT₀ (Subgroup.subset_closure (Or.inl rfl))
  have hpT : (pSL7 : PSL37) ∈ (T₀ : Subgroup PSL37) := hT₀ (Subgroup.subset_closure (Or.inr rfl))
  have hV : ∀ σ : PSL37, σ ∈ vBar7 ↔ σ * (tSL7 : PSL37) = (tSL7 : PSL37) * σ ∧ σ ^ 2 = 1 := mem_vBar7_iff
  refine ⟨h * (tSL7 : PSL37) * h⁻¹, hmem _ htT, h * (pSL7 : PSL37) * h⁻¹, hmem _ hpT,
    vBar7.map (MulAut.conj h).toMonoidHom, vBar7.map (MulAut.conj (h * (fSL7 : PSL37))).toMonoidHom,
    conj_mem_map_iff h (tSL7 : PSL37) vBar7 hV, ?_, ?_, ?_, ?_⟩
  · intro σ
    rw [conj_mem_map_iff (h * (fSL7 : PSL37)) (tSL7 : PSL37) vBar7 hV σ]
    have : h * (fSL7 : PSL37) * (tSL7 : PSL37) * (h * (fSL7 : PSL37))⁻¹ = h * (pSL7 : PSL37) * h⁻¹ := by rw [hpb]; group
    rw [this]
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, card_vBar7]
  · rw [Subgroup.card_map_of_injective (MulAut.conj (h * (fSL7 : PSL37))).injective, card_vBar7]
  · intro h12
    have h2 : vBar7 = vBar7.map (MulAut.conj (fSL7 : PSL37)).toMonoidHom := by
      have := congrArg (Subgroup.map (MulAut.conj h⁻¹).toMonoidHom) h12
      rw [Subgroup.map_map, Subgroup.map_map] at this
      have e1 : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
          MonoidHom.id PSL37 := by
        ext x; simp [MulAut.conj_apply]
      have e2 : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj (h * (fSL7 : PSL37))).toMonoidHom =
          (MulAut.conj (fSL7 : PSL37)).toMonoidHom := by
        ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [e1, e2, Subgroup.map_id] at this
      exact this
    have hd : (dSL7 : PSL37) ∈ vBar7 := ⟨dSL7, dSL7_mem, rfl⟩
    rw [h2] at hd
    obtain ⟨hd1, -⟩ := (conj_mem_map_iff (fSL7 : PSL37) (tSL7 : PSL37) vBar7 hV (dSL7 : PSL37)).mp hd
    rw [← hpb] at hd1
    obtain ⟨c, -, hc⟩ := (mk_comm_iff dSL7 pSL7).mp hd1
    exact dMat7_pMat7 c hc

theorem card_center_SL37 :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7))) = 3 := by
  let f : {r : ZMod 7 // r ^ 3 = 1} → Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7)) :=
    fun r => ⟨⟨Matrix.scalar (Fin 3) r.1, scalar_mem_SL r.2⟩,
      Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r.1, by rw [Fintype.card_fin]; exact r.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro r s hrs
      have h := congrArg (fun z : Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 7)) =>
        ((z : SpecialLinearGroup (Fin 3) (ZMod 7)) : Matrix (Fin 3) (Fin 3) (ZMod 7)) 0 0) hrs
      simp only [f, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
      exact Subtype.ext h
    · rintro ⟨z, hz⟩
      obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
      rw [Fintype.card_fin] at hr
      exact ⟨⟨r, hr⟩, Subtype.ext (Subtype.ext hrz)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  decide

theorem twoInvCent_sl_three_seven : TwoInvCent (SpecialLinearGroup (Fin 3) (ZMod 7)) :=
  twoInvCent_of_quotient le_rfl card_center_SL37 twoInvCent_psl_three_seven

section Row

set_option linter.unusedSectionVars false

theorem olRow_two_SL_seven [Fact (Nat.Prime 7)] :
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 7 1))) :=
  (olRow_of_twoInvCent _ twoInvCent_psl_three_seven).of_mulEquiv
    Sec4.Census.Karpilovsky.Coordinator.L37.pslEquivProjSL.symm

theorem olRow_two_statedSL_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    OLRow (fun T _ => Nonempty (T ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  have : Fintype K := Fintype.ofFinite K
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card])
  let e : CFSG.Assembly.LowTwoRank.StatedSL 3 K ≃* SpecialLinearGroup (Fin 3) (ZMod 7) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
      (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 3) φ)
  exact (olRow_of_twoInvCent _ twoInvCent_sl_three_seven).of_mulEquiv e

end Row

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
