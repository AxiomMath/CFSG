module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4UniqueAbstract
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN3MovedContradiction
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CTensorAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.Quasithin.G11 CFSG.ASVolI.ChH

set_option autoImplicit false

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

section Helpers

variable {d : ℕ} {K : Type} [Field K]

private noncomputable def w1369_tv (i j : Fin d) (hij : i ≠ j) (c : K) : ↥(StatedSL d K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero),
    Subgroup.subset_closure (by
      show (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c) _ :
        Matrix.GeneralLinearGroup (Fin d) K).val.det = 1
      simp [Matrix.det_transvection_of_ne i j hij])⟩

private theorem w1369_tv_val (i j : Fin d) (hij : i ≠ j) (c : K) :
    (((w1369_tv i j hij c : ↥(StatedSL d K)) : Matrix.GeneralLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = Matrix.transvection i j c := rfl

private theorem w1369_addHom_eq_smul_of_commute_tensor (hd : 2 ≤ d)
    (g : Matrix (Fin d) (Fin d) K →+ Matrix (Fin d) (Fin d) K)
    (hg : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)) (X : Matrix (Fin d) (Fin d) K),
      g (((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ) =
        ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * g X *
          (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ) :
    ∃ c : K, ∀ X, g X = c • X := by
  have hleft : ∀ (b : ↥(StatedSL d K)) (X : Matrix (Fin d) (Fin d) K),
      g (((b : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X) =
        ((b : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * g X := by
    intro b X
    simpa using hg (b, 1) X
  let P : AddSubgroup (Matrix (Fin d) (Fin d) K) :=
    { carrier := {A | ∀ Y, g (A * Y) = A * g Y}
      zero_mem' := by intro Y; simp
      add_mem' := by
        intro A B hA hB Y
        rw [add_mul, map_add, hA Y, hB Y, add_mul]
      neg_mem' := by
        intro A hA Y
        rw [neg_mul, map_neg, hA Y, neg_mul] }
  have hone : (1 : Matrix (Fin d) (Fin d) K) ∈ P := by intro Y; simp
  have hmul : ∀ {A B : Matrix (Fin d) (Fin d) K}, A ∈ P → B ∈ P → A * B ∈ P := by
    intro A B hA hB Y
    rw [mul_assoc, hA (B * Y), hB Y, mul_assoc]
  have hSL : ∀ b : ↥(StatedSL d K),
      ((b : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈ P :=
    fun b Y => hleft b Y
  have hoff : ∀ (i j : Fin d), i ≠ j → ∀ c : K, Matrix.single i j c ∈ P := by
    intro i j hij c
    have hb := hSL (w1369_tv i j hij c)
    have hsub := P.sub_mem hb hone
    have he : (((w1369_tv i j hij c : ↥(StatedSL d K)) : Matrix.GeneralLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) - 1 = Matrix.single i j c := by
      rw [w1369_tv_val]
      simp [Matrix.transvection]
    rwa [he] at hsub
  have hsingle : ∀ (i j : Fin d) (c : K), Matrix.single i j c ∈ P := by
    intro i j c
    by_cases hij : i = j
    · subst hij
      haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
      obtain ⟨k, hk⟩ : ∃ k : Fin d, k ≠ i := exists_ne i
      have he : Matrix.single i i c = Matrix.single i k c * Matrix.single k i (1 : K) := by
        rw [Matrix.single_mul_single_same, mul_one]
      rw [he]
      exact hmul (hoff i k (Ne.symm hk) c) (hoff k i hk 1)
    · exact hoff i j hij c
  have hX : ∀ X : Matrix (Fin d) (Fin d) K, X ∈ P := by
    intro X
    rw [Matrix.matrix_eq_sum_single X]
    exact P.sum_mem fun i _ => P.sum_mem fun j _ => hsingle i j (X i j)
  have hFC : ∀ X, g X = X * g 1 := by
    intro X
    have h := hX X 1
    rwa [Matrix.mul_one] at h
  have hr : ∀ (i j : Fin d), i ≠ j →
      Matrix.single i j (1 : K) * g 1 = g 1 * Matrix.single i j 1 := by
    intro i j hij
    have h := hg (1, w1369_tv j i hij.symm 1) 1
    have he : (((w1369_tv j i hij.symm 1 : ↥(StatedSL d K)) :
        Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ =
        1 + Matrix.single i j 1 := by
      rw [w1369_tv_val]
      simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h
    rw [he] at h
    simp only [Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one] at h
    rw [hFC (1 + Matrix.single i j 1)] at h
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h
    exact add_left_cancel h
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := g 1)
    (fun i j hij => hr i j hij)
  have hc' : g 1 = c • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  exact ⟨c, fun X => by rw [hFC X, hc', Matrix.mul_smul, Matrix.mul_one]⟩

private theorem w1369_invariant_addSubgroup_eq_bot_or_top (hd : 2 ≤ d)
    (N : AddSubgroup (Matrix (Fin d) (Fin d) K))
    (hN : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)), ∀ X ∈ N,
      ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · right
    let P : AddSubgroup (Matrix (Fin d) (Fin d) K) :=
      { carrier := {A | ∀ X ∈ N, A * X ∈ N}
        zero_mem' := by intro X _; simp
        add_mem' := by
          intro A B hA hB X hX
          rw [add_mul]
          exact N.add_mem (hA X hX) (hB X hX)
        neg_mem' := by
          intro A hA X hX
          rw [neg_mul]
          exact N.neg_mem (hA X hX) }
    have hmulP : ∀ {A B : Matrix (Fin d) (Fin d) K}, A ∈ P → B ∈ P → A * B ∈ P := by
      intro A B hA hB X hX
      rw [mul_assoc]
      exact hA (B * X) (hB X hX)
    have honeP : (1 : Matrix (Fin d) (Fin d) K) ∈ P := by intro X hX; simpa using hX
    have hSLP : ∀ b : ↥(StatedSL d K),
        ((b : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈ P := by
      intro b X hX
      have h := hN (b, 1) X hX
      simpa using h
    have hoffP : ∀ (i j : Fin d), i ≠ j → ∀ c : K, Matrix.single i j c ∈ P := by
      intro i j hij c
      have hb := hSLP (w1369_tv i j hij c)
      have hsub := P.sub_mem hb honeP
      have he : (((w1369_tv i j hij c : ↥(StatedSL d K)) : Matrix.GeneralLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) - 1 = Matrix.single i j c := by
        rw [w1369_tv_val]
        simp [Matrix.transvection]
      rwa [he] at hsub
    have hsingleP : ∀ (i j : Fin d) (c : K), Matrix.single i j c ∈ P := by
      intro i j c
      by_cases hij : i = j
      · subst hij
        haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
        obtain ⟨k, hk⟩ : ∃ k : Fin d, k ≠ i := exists_ne i
        have he : Matrix.single i i c = Matrix.single i k c * Matrix.single k i (1 : K) := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [he]
        exact hmulP (hoffP i k (Ne.symm hk) c) (hoffP k i hk 1)
      · exact hoffP i j hij c
    have hPtop : ∀ A : Matrix (Fin d) (Fin d) K, A ∈ P := by
      intro A
      rw [Matrix.matrix_eq_sum_single A]
      exact P.sum_mem fun i _ => P.sum_mem fun j _ => hsingleP i j (A i j)
    let Q : AddSubgroup (Matrix (Fin d) (Fin d) K) :=
      { carrier := {B | ∀ X ∈ N, X * B ∈ N}
        zero_mem' := by intro X _; simp
        add_mem' := by
          intro A B hA hB X hX
          rw [mul_add]
          exact N.add_mem (hA X hX) (hB X hX)
        neg_mem' := by
          intro A hA X hX
          rw [mul_neg]
          exact N.neg_mem (hA X hX) }
    have hmulQ : ∀ {A B : Matrix (Fin d) (Fin d) K}, A ∈ Q → B ∈ Q → A * B ∈ Q := by
      intro A B hA hB X hX
      rw [← mul_assoc]
      exact hB (X * A) (hA X hX)
    have honeQ : (1 : Matrix (Fin d) (Fin d) K) ∈ Q := by intro X hX; simpa using hX
    have hSLQ : ∀ b : ↥(StatedSL d K),
        (((b : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ ∈ Q := by
      intro b X hX
      have h := hN (1, b) X hX
      simpa using h
    have hoffQ : ∀ (i j : Fin d), i ≠ j → ∀ c : K, Matrix.single i j c ∈ Q := by
      intro i j hij c
      have hb := hSLQ (w1369_tv j i hij.symm c)
      have hsub := Q.sub_mem hb honeQ
      have he : (((w1369_tv j i hij.symm c : ↥(StatedSL d K)) :
          Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ - 1 =
          Matrix.single i j c := by
        rw [w1369_tv_val]
        simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]
      rwa [he] at hsub
    have hsingleQ : ∀ (i j : Fin d) (c : K), Matrix.single i j c ∈ Q := by
      intro i j c
      by_cases hij : i = j
      · subst hij
        haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
        obtain ⟨k, hk⟩ : ∃ k : Fin d, k ≠ i := exists_ne i
        have he : Matrix.single i i c = Matrix.single i k c * Matrix.single k i (1 : K) := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [he]
        exact hmulQ (hoffQ i k (Ne.symm hk) c) (hoffQ k i hk 1)
      · exact hoffQ i j hij c
    have hQtop : ∀ B : Matrix (Fin d) (Fin d) K, B ∈ Q := by
      intro B
      rw [Matrix.matrix_eq_sum_single B]
      exact Q.sum_mem fun i _ => Q.sum_mem fun j _ => hsingleQ i j (B i j)
    obtain ⟨X₀, hX₀N, hX₀ne⟩ : ∃ X₀ ∈ N, X₀ ≠ 0 := by
      by_contra h
      apply hbot
      rw [eq_bot_iff]
      intro X hX
      by_contra hX0
      exact h ⟨X, hX, hX0⟩
    obtain ⟨p, q, hpq⟩ : ∃ p q, X₀ p q ≠ 0 := by
      by_contra h
      push Not at h
      exact hX₀ne (by ext i j; exact h i j)
    have hEpq : Matrix.single p q (1 : K) ∈ N := by
      have h1 : Matrix.single p p (1 : K) ∈ P := hPtop _
      have h2 : Matrix.single q q (1 : K) ∈ Q := hQtop _
      have h3 : Matrix.single p p (1 : K) * X₀ * Matrix.single q q (1 : K) ∈ N :=
        h2 (Matrix.single p p (1 : K) * X₀) (h1 X₀ hX₀N)
      have he : Matrix.single p p (1 : K) * X₀ * Matrix.single q q (1 : K) =
          X₀ p q • Matrix.single p q (1 : K) := by
        rw [Matrix.single_mul_mul_single, Matrix.smul_single]
        simp
      rw [he] at h3
      have h4 : ((X₀ p q)⁻¹ • (1 : Matrix (Fin d) (Fin d) K)) ∈ P := hPtop _
      have h5 := h4 _ h3
      have he2 : (X₀ p q)⁻¹ • (1 : Matrix (Fin d) (Fin d) K) *
          (X₀ p q • Matrix.single p q (1 : K)) = Matrix.single p q (1 : K) := by
        rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hpq, one_smul]
      rwa [he2] at h5
    rw [eq_top_iff]
    intro A _
    rw [Matrix.matrix_eq_sum_single A]
    refine N.sum_mem fun i _ => N.sum_mem fun j _ => ?_
    have h1 : Matrix.single i p (1 : K) ∈ P := hPtop _
    have h2 : Matrix.single q j (1 : K) ∈ Q := hQtop _
    have h3 : Matrix.single i p (1 : K) * Matrix.single p q (1 : K) *
        Matrix.single q j (1 : K) ∈ N :=
      h2 (Matrix.single i p (1 : K) * Matrix.single p q (1 : K)) (h1 _ hEpq)
    have he : Matrix.single i p (1 : K) * Matrix.single p q (1 : K) *
        Matrix.single q j (1 : K) = Matrix.single i j (1 : K) := by
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one, one_mul]
    rw [he] at h3
    have h4 : (A i j • (1 : Matrix (Fin d) (Fin d) K)) ∈ P := hPtop _
    have h5 := h4 _ h3
    have he2 : A i j • (1 : Matrix (Fin d) (Fin d) K) * Matrix.single i j (1 : K) =
        Matrix.single i j (A i j) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_single, smul_eq_mul, mul_one]
    rwa [he2] at h5

end Helpers

theorem natTensor_isIrrOn {Y : Subgroup (MulAut W)} {U : Subgroup W} {d a : ℕ}
    (hd : 2 ≤ d) (h : NatTensor Y U ⊥ d a) : IsIrrOn Y U ⊥ ∧ fixV Y ⊓ U = ⊥ := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hRealizes⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨π, hVia⟩ := hRealizes
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.tensorNat d K) rfl rfl hVia
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : ↥U ≃* Multiplicative (Matrix (Fin d) (Fin d) K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  have hβe' : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)) (u : ↥U)
      (hu : ((π p : ↥Y) : MulAut W) (u : W) ∈ U),
      e ⟨((π p : ↥Y) : MulAut W) (u : W), hu⟩ = tensorAct d K p (e u) := by
    intro p u hu
    have h := hβe p u hu
    change β ⟨((π p : ↥Y) : MulAut W) (u : W), hu⟩ =
      (FFModel.tensorNat d K).act p (β u)
    exact h
  have hUinv : ∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U := hVia.2.2.2.1
  have hUbot : U ≠ ⊥ := by
    intro hU
    haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
    have hne : (Multiplicative.ofAdd (1 : Matrix (Fin d) (Fin d) K)) ≠ 1 := by
      intro hh
      exact one_ne_zero (Multiplicative.ofAdd.injective hh)
    let u : ↥U := e.symm (Multiplicative.ofAdd (1 : Matrix (Fin d) (Fin d) K))
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (hU ▸ u.2))
    have h1 : e u = 1 := by rw [hu, map_one]
    rw [MulEquiv.apply_symm_apply] at h1
    exact hne h1
  have hStabU : StableUnder Y U := fun y hy => hUinv ⟨y, hy⟩
  refine ⟨⟨bot_lt_iff_ne_bot.mpr hUbot, hStabU, ?_, ?_⟩, ?_⟩
  · intro y hy u hu
    rw [Subgroup.mem_bot.mp hu, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · intro J hJ _ hJU
    let N : AddSubgroup (Matrix (Fin d) (Fin d) K) :=
      { carrier := {X | ∃ u : ↥U, (u : W) ∈ J ∧ e u = Multiplicative.ofAdd X}
        zero_mem' := ⟨1, J.one_mem, by rw [map_one, ofAdd_zero]⟩
        add_mem' := by
          rintro X Y ⟨u, hu, huX⟩ ⟨v, hv, hvY⟩
          refine ⟨u * v, J.mul_mem hu hv, ?_⟩
          rw [map_mul, huX, hvY, ofAdd_add]
        neg_mem' := by
          rintro X ⟨u, hu, huX⟩
          refine ⟨u⁻¹, J.inv_mem hu, ?_⟩
          rw [map_inv, huX, ofAdd_neg] }
    have hN : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)), ∀ X ∈ N,
        ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X *
          (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ ∈ N := by
      rintro p X ⟨u, hu, huX⟩
      have hmem : ((π p : ↥Y) : MulAut W) (u : W) ∈ U := hUinv (π p) (u : W) u.2
      refine ⟨⟨((π p : ↥Y) : MulAut W) (u : W), hmem⟩,
        hJ (π p) (π p).2 (u : W) hu, ?_⟩
      rw [hβe' p u hmem, huX]
      rfl
    rcases w1369_invariant_addSubgroup_eq_bot_or_top hd N hN with hNbot | hNtop
    · left
      rw [eq_bot_iff]
      intro u hu
      have hmem : Multiplicative.toAdd (e ⟨u, hJU hu⟩) ∈ N :=
        ⟨⟨u, hJU hu⟩, hu, (ofAdd_toAdd (e ⟨u, hJU hu⟩)).symm⟩
      rw [hNbot] at hmem
      have h1 : Multiplicative.toAdd (e ⟨u, hJU hu⟩) = 0 := AddSubgroup.mem_bot.mp hmem
      have h2 : e ⟨u, hJU hu⟩ = 1 := by
        rw [← ofAdd_toAdd (e ⟨u, hJU hu⟩), h1, ofAdd_zero]
      exact Subgroup.mem_bot.mp ((hβk ⟨u, hJU hu⟩).mp h2)
    · right
      refine le_antisymm hJU ?_
      intro u hu
      have hmem : Multiplicative.toAdd (e ⟨u, hu⟩) ∈ N := by
        rw [hNtop]
        exact AddSubgroup.mem_top _
      obtain ⟨v, hv, hvu⟩ := hmem
      have hvu' : e v = e ⟨u, hu⟩ := by rw [hvu, ofAdd_toAdd]
      have hker : v⁻¹ * ⟨u, hu⟩ = 1 := by
        apply e.injective
        rw [map_mul, map_inv, hvu', inv_mul_cancel, map_one]
      have hwu : (v : W) = (u : W) := by
        have h := congrArg (fun w : ↥U => (w : W)) hker
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h
        rwa [inv_mul_eq_one] at h
      have huv : u = (v : W) := hwu.symm
      rw [huv]
      exact hv
  · rw [eq_bot_iff]
    rintro w ⟨hwfix, hwU⟩
    have hfixβ : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)),
        ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          Multiplicative.toAdd (e ⟨w, hwU⟩) *
          (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ =
        Multiplicative.toAdd (e ⟨w, hwU⟩) := by
      intro p
      have hmem : ((π p : ↥Y) : MulAut W) w ∈ U := hUinv (π p) w hwU
      have h2 : (⟨((π p : ↥Y) : MulAut W) w, hmem⟩ : ↥U) = ⟨w, hwU⟩ :=
        Subtype.ext ((mem_fixV.mp hwfix) (π p) (π p).2)
      have h1 : e ⟨w, hwU⟩ = tensorAct d K p (e ⟨w, hwU⟩) := by
        have h := hβe p ⟨w, hwU⟩ hmem
        rw [h2] at h
        change β ⟨w, hwU⟩ = (FFModel.tensorNat d K).act p (β ⟨w, hwU⟩)
        exact h
      have h3 := congrArg Multiplicative.toAdd h1
      rw [show Multiplicative.toAdd (tensorAct d K p (e ⟨w, hwU⟩)) =
          ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            Multiplicative.toAdd (e ⟨w, hwU⟩) *
            (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ
          from rfl] at h3
      exact h3.symm
    have hX0 : ∀ (i j : Fin d), i ≠ j → ∀ c : K,
        Matrix.single i j c * Multiplicative.toAdd (e ⟨w, hwU⟩) = 0 := by
      intro i j hij c
      have h := hfixβ (w1369_tv i j hij c, 1)
      rw [w1369_tv_val] at h
      simp only [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.transpose_one,
        Matrix.mul_one, Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one,
        Matrix.SpecialLinearGroup.coe_one, add_zero] at h
      have h' : Multiplicative.toAdd (e ⟨w, hwU⟩) +
          Matrix.single i j c * Multiplicative.toAdd (e ⟨w, hwU⟩) =
          Multiplicative.toAdd (e ⟨w, hwU⟩) + 0 := by
        rw [add_zero]
        exact h
      exact add_left_cancel h'
    have hXzero : Multiplicative.toAdd (e ⟨w, hwU⟩) = 0 := by
      ext aa bb
      haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
      obtain ⟨i, hi⟩ : ∃ i : Fin d, i ≠ aa := exists_ne aa
      have h := congrFun (congrFun (hX0 i aa hi 1) i) bb
      rwa [Matrix.single_mul_apply_same, one_mul] at h
    have hβw : e ⟨w, hwU⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨w, hwU⟩), hXzero, ofAdd_zero]
    exact Subgroup.mem_bot.mp ((hβk ⟨w, hwU⟩).mp hβw)

theorem natTensor_order3_even {Y : Subgroup (MulAut W)} {U : Subgroup W} {d a : ℕ} (hd : 2 ≤ d)
    (h : NatTensor Y U ⊥ d a) {x : MulAut W} (hx3 : x ^ 3 = 1)
    (hxU : StableUnder (Subgroup.zpowers x) U) (hcomm : ∀ y ∈ Y, x * y = y * x)
    (hfix : fixV (Subgroup.zpowers x) ⊓ U = ⊥) : Even a := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hRealizes⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨π, hVia⟩ := hRealizes
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.tensorNat d K) rfl rfl hVia
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : ↥U ≃* Multiplicative (Matrix (Fin d) (Fin d) K) :=
    MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  have hβe' : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)) (u : ↥U)
      (hu : ((π p : ↥Y) : MulAut W) (u : W) ∈ U),
      e ⟨((π p : ↥Y) : MulAut W) (u : W), hu⟩ = tensorAct d K p (e u) := by
    intro p u hu
    have h := hβe p u hu
    change β ⟨((π p : ↥Y) : MulAut W) (u : W), hu⟩ =
      (FFModel.tensorNat d K).act p (β u)
    exact h
  have hUinv : ∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U := hVia.2.2.2.1
  have hxU' : ∀ u ∈ U, x u ∈ U := hxU x (Subgroup.mem_zpowers x)
  have hxUinv : ∀ u ∈ U, x⁻¹ u ∈ U := inv_mem_of_forall_mem x hxU'
  let xU : MulAut ↥U :=
    { toFun := fun u => ⟨x (u : W), hxU' (u : W) u.2⟩
      invFun := fun u => ⟨x⁻¹ (u : W), hxUinv (u : W) u.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp [map_mul]) }
  let T : Matrix (Fin d) (Fin d) K →+ Matrix (Fin d) (Fin d) K :=
    { toFun := fun X => Multiplicative.toAdd (e (xU (e.symm (Multiplicative.ofAdd X))))
      map_zero' := by simp
      map_add' := fun X Y => by simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hT : ∀ (p : ↥(StatedSL d K) × ↥(StatedSL d K)) (X : Matrix (Fin d) (Fin d) K),
      T (((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ) =
        ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * T X *
          (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ := by
    intro p X
    have hmem : ∀ u : ↥U, ((π p : ↥Y) : MulAut W) (u : W) ∈ U :=
      fun u => hUinv (π p) (u : W) u.2
    let πU : ↥U → ↥U := fun u => ⟨((π p : ↥Y) : MulAut W) (u : W), hmem u⟩
    have hπUx : ∀ u : ↥U, xU (πU u) = πU (xU u) := by
      intro u
      apply Subtype.ext
      exact congrArg (fun f : MulAut W => f (u : W)) (hcomm (π p) (π p).2)
    have hπUe : ∀ u : ↥U, e (πU u) = tensorAct d K p (e u) := by
      intro u
      exact hβe' p u (hmem u)
    have hkey : e.symm (Multiplicative.ofAdd (((p.1 : Matrix.GeneralLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ)) =
        πU (e.symm (Multiplicative.ofAdd X)) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, hπUe, MulEquiv.apply_symm_apply]
      rfl
    change Multiplicative.toAdd (e (xU (e.symm (Multiplicative.ofAdd
      (((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ))))) =
      ((p.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        Multiplicative.toAdd (e (xU (e.symm (Multiplicative.ofAdd X)))) *
        (((p.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ
    rw [hkey, hπUx, hπUe]
    rfl
  obtain ⟨c, hc⟩ := w1369_addHom_eq_smul_of_commute_tensor hd T hT
  have hx3' : ∀ w : W, x (x (x w)) = w := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) hx3
    simpa [pow_succ, pow_two, MulAut.mul_apply] using h
  have hxU3 : ∀ u : ↥U, xU (xU (xU u)) = u := by
    intro u
    apply Subtype.ext
    change x (x (x (u : W))) = (u : W)
    exact hx3' (u : W)
  have hT_apply : ∀ (X : Matrix (Fin d) (Fin d) K) (u : ↥U),
      e u = Multiplicative.ofAdd X → T X = Multiplicative.toAdd (e (xU u)) := by
    intro X u hu
    change Multiplicative.toAdd (e (xU (e.symm (Multiplicative.ofAdd X)))) =
      Multiplicative.toAdd (e (xU u))
    rw [← hu, MulEquiv.symm_apply_apply]
  have hT3 : ∀ X : Matrix (Fin d) (Fin d) K, T (T (T X)) = X := by
    intro X
    obtain ⟨u, hu⟩ : ∃ u : ↥U, e u = Multiplicative.ofAdd X :=
      ⟨e.symm (Multiplicative.ofAdd X), e.apply_symm_apply _⟩
    have h1 : T X = Multiplicative.toAdd (e (xU u)) := hT_apply X u hu
    have h2 : e (xU u) = Multiplicative.ofAdd (T X) := by rw [h1, ofAdd_toAdd]
    have h3 : T (T X) = Multiplicative.toAdd (e (xU (xU u))) := hT_apply (T X) (xU u) h2
    have h4 : e (xU (xU u)) = Multiplicative.ofAdd (T (T X)) := by rw [h3, ofAdd_toAdd]
    have h5 : T (T (T X)) = Multiplicative.toAdd (e (xU (xU (xU u)))) :=
      hT_apply (T (T X)) (xU (xU u)) h4
    rw [h5, hxU3 u, hu, toAdd_ofAdd]
  have hc3 : c ^ 3 = 1 := by
    have h1 : T (T (T (1 : Matrix (Fin d) (Fin d) K))) = 1 := hT3 1
    rw [hc (T (T 1)), hc (T 1), hc 1] at h1
    have h2 : c ^ 3 • (1 : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [show c ^ 3 = c * c * c by ring, mul_smul, mul_smul]
      exact h1
    have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3
  have hUbot : U ≠ ⊥ := by
    intro hU
    haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
    have hne : (Multiplicative.ofAdd (1 : Matrix (Fin d) (Fin d) K)) ≠ 1 := by
      intro hh
      exact one_ne_zero (Multiplicative.ofAdd.injective hh)
    let u : ↥U := e.symm (Multiplicative.ofAdd (1 : Matrix (Fin d) (Fin d) K))
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (hU ▸ u.2))
    have h1 : e u = 1 := by rw [hu, map_one]
    rw [MulEquiv.apply_symm_apply] at h1
    exact hne h1
  have hc1 : c ≠ 1 := by
    intro hc1'
    have hxfix : ∀ u : ↥U, xU u = u := by
      intro u
      have h := hc (Multiplicative.toAdd (e u))
      have h1 : T (Multiplicative.toAdd (e u)) = Multiplicative.toAdd (e (xU u)) := by
        change Multiplicative.toAdd (e (xU (e.symm (Multiplicative.ofAdd
          (Multiplicative.toAdd (e u)))))) = Multiplicative.toAdd (e (xU u))
        rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      rw [hc1', one_smul, h1] at h
      exact e.injective (Multiplicative.toAdd.injective h)
    have hle : U ≤ fixV (Subgroup.zpowers x) := by
      intro u hu
      rw [mem_fixV_zpowers_iff]
      have h := congrArg (fun v : ↥U => (v : W)) (hxfix ⟨u, hu⟩)
      exact h
    have hle' : U ≤ (⊥ : Subgroup W) := by rw [← hfix]; exact le_inf hle le_rfl
    exact hUbot (le_bot_iff.mp hle')
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc3
    norm_num at hc3
  let cu : Kˣ := Units.mk0 c hc0
  have hcu3 : cu ^ 3 = 1 := by
    ext
    simpa [cu] using hc3
  have hcu1 : cu ≠ 1 := by
    intro hh
    exact hc1 (Units.ext_iff.mp hh)
  have hord : orderOf cu = 3 := orderOf_eq_prime hcu3 hcu1
  have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard cu
  have hcard : Nat.card Kˣ = 2 ^ a - 1 := by
    rw [Nat.card_units, hKcard]
  have hdvd' : 3 ∣ 2 ^ a - 1 := by rwa [hcard] at hdvd
  have hmod : 2 ^ a ≡ 1 [MOD 3] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).2 hdvd').symm
  rcases Nat.even_or_odd a with ha | ha
  · exact ha
  · exfalso
    obtain ⟨k, rfl⟩ := ha
    have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod]
      norm_num [h4]
    have h5 : 2 ^ (2 * k + 1) % 3 = 1 % 3 := hmod
    rw [h2] at h5
    omega

theorem tensor22_commute_scalar {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup (GLV V)) (φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄))
    (ψ : V ≃ₗ[ZMod 2] M₄)
    (hψ : ∀ (h : ↥H) (v : V), ψ ((h : GLV V) v) =
      (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
        ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ)
    (g : GLV V) (hcomm : ∀ h : ↥H, g * (h : GLV V) = (h : GLV V) * g) :
    ∃ c : F₄, ∀ v : V, ψ (g v) = c • ψ v := by
  let T : M₄ →+ M₄ :=
    { toFun := fun X => ψ (g (ψ.symm X))
      map_zero' := by simp
      map_add' := fun X Y => by simp [map_add] }
  have hT : ∀ (p : ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄)) (X : M₄),
      T (((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ) =
        ((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * T X *
          (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ := by
    intro p X
    obtain ⟨h, hh⟩ := φ.surjective p
    have hact : ψ ((h : GLV V) (ψ.symm X)) =
        ((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * X *
          (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ := by
      rw [hψ h (ψ.symm X), hh, LinearEquiv.apply_symm_apply]
    have hkey : ψ.symm (((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * X *
        (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ) =
        (h : GLV V) (ψ.symm X) := by
      apply ψ.injective
      rw [hact, LinearEquiv.apply_symm_apply]
    change ψ (g (ψ.symm (((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * X *
      (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ))) =
      ((p.1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ (g (ψ.symm X)) *
        (((p.2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ
    have hcomp : g ((h : GLV V) (ψ.symm X)) = (h : GLV V) (g (ψ.symm X)) := by
      change (g * (h : GLV V)) (ψ.symm X) = ((h : GLV V) * g) (ψ.symm X)
      rw [hcomm h]
    rw [hkey, hcomp, hψ h (g (ψ.symm X)), hh]
  obtain ⟨c, hc⟩ := w1369_addHom_eq_smul_of_commute_tensor (d := 2) (K := F₄)
    (by norm_num) T hT
  refine ⟨c, fun v => ?_⟩
  have h := hc (ψ v)
  change ψ (g (ψ.symm (ψ v))) = c • ψ v at h
  rwa [LinearEquiv.symm_apply_apply] at h

theorem Std139.conc134_of_moved (h134 : W4Lem13_4) (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) {K : Subgroup (MulAut W)} {d : MulAut W}
    (hK : IsComponentOf K G) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) : Conc4_134 G K d := by
  have hdG : d ∈ G := S.DG hd
  have hd2 : orderOf d = 2 := orderOf_eq_prime (S.elem.2 d hd) hd1
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers d)) ≤ 3 := by
    rw [(Std139.commSub_axis hw2 S hd hd1).1]
    norm_num
  refine h134 W hw2 G S.isK ?_ d hdG hd2 hrk K hK hKd
  intro P hPG hPN hP2
  have hle : P ≤ pCoreOf 2 G := by
    have h1 : P.subgroupOf G ≤ CFSG.pCore 2 ↥G :=
      le_sSup ⟨hPN, hP2.comap_subtype⟩
    have h2 : (P.subgroupOf G).map G.subtype ≤ pCoreOf 2 G := Subgroup.map_mono h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hPG] at h2
  rw [S.o2] at hle
  exact le_bot_iff.mp hle

theorem Std139.selection (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d) :
    IsL2 ↥K 2 ∧ NatTensor (swapPair K d) (commSub ⊤ (swapPair K d)) ⊥ 2 2 := by
  let z : MulAut W := Classical.choose (Std139.exists_gen hw2 S)
  have hzspec := Classical.choose_spec (Std139.exists_gen hw2 S)
  have hzX : X = Subgroup.zpowers z := hzspec.1
  have hz3 : z ^ 3 = 1 := hzspec.2.1
  have hzne : z ≠ 1 := hzspec.2.2.1
  have hfixX : fixV X = ⊥ := hzspec.2.2.2.1
  have hzmem : z ∈ X := hzX ▸ Subgroup.mem_zpowers z
  have hKd' : IsComponentOf (K.map (MulAut.conj d).toMonoidHom) G :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (S.DG hd)
  have hLle : swapPair K d ≤ Subgroup.centralizer ({z} : Set (MulAut W)) := by
    rw [swapPair]
    refine sup_le ?_ ?_
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (Std139.component_commutes_X S hK k hk z hzmem).symm
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (Std139.component_commutes_X S hKd' k hk z hzmem).symm
  have hcommL : ∀ v ∈ swapPair K d, z * v = v * z := fun v hv =>
    Subgroup.mem_centralizer_iff.mp (hLle hv) z (Set.mem_singleton z)
  have hcommY : ∀ v ∈ swapPair K d, ∀ b ∈ Subgroup.zpowers z, v * b = b * v := by
    intro v hv b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute v z from (hcommL v hv).symm) i).eq
  have hxU : StableUnder (Subgroup.zpowers z) (commSub ⊤ (swapPair K d)) :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := swapPair K d)
      (B := Subgroup.zpowers z) (M := ⊤) hcommY (fun _ _ _ _ => Subgroup.mem_top _)
  have hfixU : fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (swapPair K d) = ⊥ := by
    rw [show fixV (Subgroup.zpowers z) = fixV X from by rw [hzX], hfixX]
    exact bot_inf_eq _
  rcases h134 with ⟨hcases, _⟩ | ⟨_, hIrr, _, hBNat⟩
  · rcases hcases with ⟨_, hNat⟩ | ⟨hL2, hNat⟩ | ⟨_, hNat⟩
    · exfalso
      have hEven : Even 1 := natTensor_order3_even (d := 3) (a := 1) (by norm_num)
        hNat hz3 hxU hcommL hfixU
      norm_num at hEven
    · exact ⟨hL2, hNat⟩
    · exfalso
      have hEven : Even 3 := natTensor_order3_even (d := 2) (a := 3) (by norm_num)
        hNat hz3 hxU hcommL hfixU
      norm_num at hEven
  · exfalso
    exact w1369_no_L3_of_order3 hw2 S hK hIrr hBNat hzX hz3 hfixX

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
