module

public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace L43

abbrev F₃ : Type := GaloisField 3 1

noncomputable abbrev ψ : ZMod 3 →+* F₃ := algebraMap (ZMod 3) F₃

noncomputable def toProjSL : SpecialLinearGroup (Fin 4) (ZMod 3) →* projSL 4 F₃ :=
  MonoidHom.codRestrict
    (ProjGenLinGroup.mk.comp (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map ψ)))
    (projSL 4 F₃) fun x => ⟨SpecialLinearGroup.toGL (SpecialLinearGroup.map ψ x),
      MonoidHom.mem_ker.mpr (Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact (SpecialLinearGroup.map ψ x).2)), rfl⟩

theorem exists_unit_of_toProjSL_eq {x y : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (h : toProjSL x = toProjSL y) :
    ∃ u : F₃ˣ, ∀ i j, ψ ((x : Matrix (Fin 4) (Fin 4) (ZMod 3)) i j) * u =
      ψ ((y : Matrix (Fin 4) (Fin 4) (ZMod 3)) i j) := by
  have h1 : ProjGenLinGroup.mk (SpecialLinearGroup.toGL (SpecialLinearGroup.map ψ x)) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (SpecialLinearGroup.map ψ y)) :=
    congrArg Subtype.val h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
  refine ⟨u, fun i j => ?_⟩
  have h2 := congrArg (fun g : GL (Fin 4) F₃ => (g : Matrix (Fin 4) (Fin 4) F₃) i j) hu
  simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Finset.sum_ite_eq'] using h2

@[expose] def uM (b : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![1, 0, b 0, b 1; 0, 1, b 2, b 3; 0, 0, 1, 0; 0, 0, 0, 1]

theorem uM_mul (b c : Fin 4 → ZMod 3) : uM b * uM c = uM (b + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uM_zero : uM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_uM (b : Fin 4 → ZMod 3) : (uM b).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, uM]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [uM]

@[expose] def uHom : Multiplicative (Fin 4 → ZMod 3) →* SpecialLinearGroup (Fin 4) (ZMod 3) where
  toFun b := ⟨uM (Multiplicative.toAdd b), det_uM _⟩
  map_one' := Subtype.ext uM_zero
  map_mul' _ _ := Subtype.ext (uM_mul _ _).symm

theorem coe_uHom (b : Multiplicative (Fin 4 → ZMod 3)) :
    ((uHom b : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      uM (Multiplicative.toAdd b) := rfl

theorem toProjSL_uHom_injective : Function.Injective (toProjSL.comp uHom) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro b hb
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one toProjSL] at hb
  obtain ⟨u, hu⟩ := exists_unit_of_toProjSL_eq hb
  have hu1 : (u : F₃) = 1 := by
    have := hu 0 0
    simpa [coe_uHom, uM] using this
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · have := hu 0 2
    simpa [coe_uHom, uM, hu1] using this
  · have := hu 0 3
    simpa [coe_uHom, uM, hu1] using this
  · have := hu 1 2
    simpa [coe_uHom, uM, hu1] using this
  · have := hu 1 3
    simpa [coe_uHom, uM, hu1] using this

@[expose] def eAdd : ZMod 3 × ZMod 3 →+ (Fin 4 → ZMod 3) where
  toFun v := ![v.1, 0, 0, v.2]
  map_zero' := by
    funext k
    fin_cases k <;> rfl
  map_add' v w := by
    funext k
    fin_cases k <;> simp

@[expose] def eHom : Multiplicative (ZMod 3 × ZMod 3) →* SpecialLinearGroup (Fin 4) (ZMod 3) :=
  uHom.comp (AddMonoidHom.toMultiplicative eAdd)

theorem eAdd_injective : Function.Injective eAdd := by
  intro v w h
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  simp [eAdd] at h0 h3
  exact Prod.ext h0 h3

@[expose] def qEightL : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  [!![0, 0, 1, 0; 0, 1, 0, 0; 2, 0, 0, 0; 0, 0, 0, 1],
   !![0, 0, 2, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1],
   !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
   !![1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 2, 0; 0, 0, 0, 1],
   !![1, 0, 2, 0; 0, 1, 0, 0; 2, 0, 2, 0; 0, 0, 0, 1],
   !![2, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1],
   !![2, 0, 1, 0; 0, 1, 0, 0; 1, 0, 1, 0; 0, 0, 0, 1],
   !![2, 0, 2, 0; 0, 1, 0, 0; 2, 0, 1, 0; 0, 0, 0, 1]]

@[expose] def zThree : List (ZMod 3) := [0, 1, 2]

theorem mem_zThree (z : ZMod 3) : z ∈ zThree := by
  revert z
  decide

theorem qEightL_checks :
    (qEightL.all fun a => qEightL.all fun b => qEightL.contains (a * b)) = true ∧
      (qEightL.all fun a => qEightL.contains (a * a * a) && a * a * a * a == 1) = true ∧
      qEightL.contains 1 = true ∧
      (zThree.all fun x => zThree.all fun y => qEightL.all fun a =>
        qEightL.contains (uM ![x, 0, 0, y] * a * uM ![-x, 0, 0, -y])) = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem qEightL_mul {a b : Matrix (Fin 4) (Fin 4) (ZMod 3)} (ha : a ∈ qEightL)
    (hb : b ∈ qEightL) : a * b ∈ qEightL := by
  have h := List.all_eq_true.mp qEightL_checks.1 a ha
  have h' := List.all_eq_true.mp h b hb
  simpa using h'

theorem qEightL_pow {a : Matrix (Fin 4) (Fin 4) (ZMod 3)} (ha : a ∈ qEightL) :
    a * a * a ∈ qEightL ∧ a * a * a * a = 1 := by
  have h := List.all_eq_true.mp qEightL_checks.2.1 a ha
  simpa using h

theorem one_mem_qEightL : (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ qEightL := by
  simpa using qEightL_checks.2.2.1

theorem uM_conj_mem (v : ZMod 3 × ZMod 3) {a : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (ha : a ∈ qEightL) : uM (eAdd v) * a * uM (eAdd (-v)) ∈ qEightL := by
  obtain ⟨x, y⟩ := v
  have h := List.all_eq_true.mp qEightL_checks.2.2.2 x (mem_zThree x)
  have h' := List.all_eq_true.mp h y (mem_zThree y)
  have h'' := List.all_eq_true.mp h' a ha
  have e1 : eAdd (x, y) = ![x, 0, 0, y] := rfl
  have e2 : eAdd (-(x, y)) = ![-x, 0, 0, -y] := by
    funext k
    fin_cases k <;> simp [eAdd]
  rw [e1, e2]
  simpa using h''

@[expose] def qEight : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 3)) where
  carrier := {x | (x : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ qEightL}
  mul_mem' {x y} hx hy := by
    change ((x * y : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈
      qEightL
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact qEightL_mul hx hy
  one_mem' := one_mem_qEightL
  inv_mem' {x} hx := by
    have hx4 : x * (x * x * x) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact (qEightL_pow hx).2
    change ((x⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈
      qEightL
    rw [inv_eq_of_mul_eq_one_right hx4, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    exact (qEightL_pow hx).1

theorem isPGroup_qEight : IsPGroup 2 qEight := by
  intro x
  refine ⟨2, ?_⟩
  have hy : ((x : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈
      qEightL := x.2
  have h4 : (x : SpecialLinearGroup (Fin 4) (ZMod 3)) ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_succ, pow_succ,
      pow_succ, pow_one]
    exact (qEightL_pow hy).2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 2 = 4 by norm_num]
  exact h4

theorem eHom_range_le_normalizer : eHom.range ≤ Subgroup.normalizer (qEight : Set _) := by
  rintro _ ⟨v, rfl⟩
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  change ((eHom v * a * (eHom v)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 3)) :
    Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ qEightL
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact uM_conj_mem (Multiplicative.toAdd v) ha

@[expose] def tM : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 0, 1, 0; 0, 1, 0, 0; 2, 0, 0, 0; 0, 0, 0, 1]

theorem tM_facts : tM.det = 1 ∧ tM ∈ qEightL ∧ (uM ![1, 0, 0, 0] * tM) 0 0 = 2 ∧
    (tM * uM ![1, 0, 0, 0]) 0 0 = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem pow_three_multiplicative {ι : Type*} (x : Multiplicative (ι → ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext k
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rw [h3, zero_mul]

theorem isElemAbelian_range_multiplicative {ι : Type*} {Y : Type*} [Group Y]
    (f : Multiplicative (ι → ZMod 3) →* Y) : CFSG.Assembly.IsElemAbelian 3 f.range := by
  rw [MonoidHom.range_eq_map]
  refine isElemAbelian_map f ⟨inferInstance, fun x _ => pow_three_multiplicative x⟩

theorem eAdd_toMultiplicative_injective :
    Function.Injective (AddMonoidHom.toMultiplicative eAdd) :=
  fun _ _ h => Multiplicative.toAdd.injective (eAdd_injective (congrArg Multiplicative.toAdd h))

theorem backSimple_L43 (X : Type) [Group X] (e : X ≃* projSL 4 (GaloisField 3 1)) :
    ∃ P E₀ T₀ : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 4 ∧
      E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
      E₀ ≤ Subgroup.normalizer (T₀ : Set X) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set X) := by
  set ρ : SpecialLinearGroup (Fin 4) (ZMod 3) →* X := e.symm.toMonoidHom.comp toProjSL
  have hinjU : Function.Injective (ρ.comp uHom) := e.symm.injective.comp toProjSL_uHom_injective
  have hinjE : Function.Injective (ρ.comp eHom) := hinjU.comp eAdd_toMultiplicative_injective
  have hE : (ρ.comp eHom).range = eHom.range.map ρ := MonoidHom.range_comp _ _
  refine ⟨(ρ.comp uHom).range, (ρ.comp eHom).range, qEight.map ρ,
    isElemAbelian_range_multiplicative _, ?_, ?_, ?_, isPGroup_qEight.map ρ, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinjU).toEquiv]
    simp [Nat.card_eq_fintype_card]
  · rintro _ ⟨v, rfl⟩
    exact ⟨AddMonoidHom.toMultiplicative eAdd v, rfl⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv]
    simp [Nat.card_eq_fintype_card]
  · rw [hE]
    exact (Subgroup.map_mono eHom_range_le_normalizer).trans (Subgroup.le_normalizer_map _)
  · intro h
    obtain ⟨hdet, htmem, h1, h2⟩ := tM_facts
    set t : SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨tM, hdet⟩
    have htq : t ∈ qEight := htmem
    set e₂ := eHom (Multiplicative.ofAdd (1, 0))
    have hcomm := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_map_of_mem ρ htq)) (ρ e₂)
      (by rw [hE]; exact Subgroup.mem_map_of_mem ρ ⟨_, rfl⟩)
    rw [← map_mul, ← map_mul] at hcomm
    have hcomm' : toProjSL (e₂ * t) = toProjSL (t * e₂) := e.symm.injective hcomm
    obtain ⟨u, hu⟩ := exists_unit_of_toProjSL_eq hcomm'
    have h00 := hu 0 0
    have he₂ : ((e₂ : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        uM ![1, 0, 0, 0] := by
      change uM (eAdd (1, 0)) = _
      congr 1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, he₂] at h00
    change ψ ((uM ![1, 0, 0, 0] * tM) 0 0) * u = ψ ((tM * uM ![1, 0, 0, 0]) 0 0) at h00
    rw [h1, h2, map_zero] at h00
    have h2' : ψ 2 = 0 := by
      have := mul_eq_zero.mp h00
      rcases this with h | h
      · exact h
      · exact absurd h u.ne_zero
    have : (2 : ZMod 3) = 0 := ψ.injective (by rw [h2', map_zero])
    exact absurd this (by decide)

end L43

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts

end CFSG.RankThree.PartTwo.Sec4
