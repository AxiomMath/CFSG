module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTriplePair

public section

namespace CFSG.StandardType.S2MathFi1451

theorem isFiniteType_of_diagonal_similar {B : Type*} [Fintype B] [DecidableEq B]
    {A C : Matrix B B ℤ} (hC : TauCeti.IsFiniteType C) (D : B → ℚ) (hD : ∀ k, 0 < D k)
    (h2 : ∀ k, A k k = 2) (hsim : ∀ k l, k ≠ l → (A k l : ℚ) = D k * C k l / D l) :
    TauCeti.IsFiniteType A := by
  obtain ⟨d, hd, hpd⟩ := hC.exists_symmetrizer
  have hle : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    have hc : (C i j : ℚ) ≤ 0 := by exact_mod_cast hC.apply_le_zero_of_ne hij
    have : (A i j : ℚ) ≤ 0 := by
      rw [hsim i j hij]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hD i).le hc)
        (hD j).le
    exact_mod_cast this
  refine TauCeti.isFiniteType_of h2 hle (d := fun i => d i / D i ^ 2)
    (fun i => div_pos (hd i) (pow_pos (hD i) 2)) ?_
  set E : Matrix B B ℚ := Matrix.diagonal fun i => (D i)⁻¹ with hEdef
  have hE : (Matrix.of fun i j => d i / D i ^ 2 * (A i j : ℚ)) =
      E.conjTranspose * (Matrix.of fun i j => d i * (C i j : ℚ)) * E := by
    ext i j
    rw [hEdef, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, star_trivial]
    have hDi := (hD i).ne'
    have hDj := (hD j).ne'
    rcases eq_or_ne i j with rfl | hij
    · rw [h2 i, hC.apply_self i]
      push_cast
      field_simp
    · rw [hsim i j hij]
      field_simp
  rw [hE]
  refine hpd.conjTranspose_mul_mul_same ?_
  intro u v huv
  funext i
  have := congrFun huv i
  rw [hEdef, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at this
  exact mul_left_cancel₀ (inv_ne_zero (hD i).ne') this

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType.S2MathFi1451

theorem isConj_simple_of_odd {ι : Type*} {M : CoxeterMatrix ι} {j l : ι} (h : Odd (M j l)) :
    IsConj (M.simple j) (M.simple l) := by
  obtain ⟨k, hk⟩ := h
  have hs : ∀ i, M.simple i = M.toCoxeterSystem.simple i := fun i => by
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  rw [hs, hs]
  set cs := M.toCoxeterSystem
  set x := cs.simple j * cs.simple l with hx
  have hpow : x ^ (2 * k + 1) = 1 := hk ▸ cs.simple_mul_simple_pow j l
  have hconj : cs.simple j * x * cs.simple j = x⁻¹ := by
    rw [hx, mul_inv_rev, cs.inv_simple, cs.inv_simple, ← mul_assoc,
      cs.simple_mul_simple_self, one_mul]
  have hconjk : cs.simple j * x ^ k * cs.simple j = x⁻¹ ^ k := by
    have := map_pow (MulAut.conj (cs.simple j)) x k
    simpa [MulAut.conj_apply, cs.inv_simple, hconj] using this
  have h1 : x ^ k * cs.simple j = cs.simple j * x⁻¹ ^ k := by
    rw [← hconjk, ← mul_assoc, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
  have h2 : x ^ (2 * k) = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hpow])
  refine isConj_iff.2 ⟨x ^ k, ?_⟩
  rw [h1, mul_assoc, inv_pow, ← mul_inv_rev, ← pow_add, ← two_mul, h2, inv_inv, hx,
    cs.simple_mul_simple_cancel_left]

theorem exists_conj_of_closure_eq_top {ι κ : Type*} {M : CoxeterMatrix ι} (t : κ → M.Group)
    (ht : ∀ k, ∃ (w : M.Group) (i : ι), t k = w * M.simple i * w⁻¹)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (i : ι) :
    ∃ (u : M.Group) (k : κ), M.simple i = u * t k * u⁻¹ := by
  classical
  by_contra H
  push Not at H
  let f : ι → ℤˣ := fun j => if IsConj (M.simple i) (M.simple j) then -1 else 1
  have hf : M.IsLiftable f := by
    intro j l
    by_cases hjl : f j = f l
    · rw [hjl, Int.units_mul_self, one_pow]
    · obtain ⟨m, hm⟩ : Even (M j l) := by
        rcases Nat.even_or_odd (M j l) with h | h
        · exact h
        · refine absurd ?_ hjl
          have hc := isConj_simple_of_odd h
          have : IsConj (M.simple i) (M.simple j) = IsConj (M.simple i) (M.simple l) :=
            propext ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩
          simp only [f, this]
      rw [hm, ← two_mul, pow_mul, Int.units_sq, one_pow]
  let χ := M.toCoxeterSystem.lift ⟨f, hf⟩
  have hχ : ∀ j, χ (M.simple j) = f j := fun j => by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  have hker : ∀ k, χ (t k) = 1 := by
    intro k
    obtain ⟨w, j, hw⟩ := ht k
    rw [hw, map_mul, map_mul, map_inv, mul_comm (χ w), mul_inv_cancel_right, hχ]
    simp only [f]
    rw [if_neg]
    rintro hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc.symm
    refine H (c * w⁻¹) k ?_
    rw [← hc, hw]
    group
  have hle : Subgroup.closure (Set.range t) ≤ χ.ker :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hker k)
  rw [hgen] at hle
  have := hle (Subgroup.mem_top (M.simple i))
  rw [MonoidHom.mem_ker, hχ] at this
  simp only [f, if_pos (IsConj.refl _)] at this
  exact absurd this (by decide)

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType.S2MathFi1451

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg.OfCartan

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem weylAction_eq_or_eq_neg_of_conj_eq {w u : (coxeterMatrix hA).Group} {i j : I}
    (h : w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹ =
      u * (coxeterMatrix hA).toCoxeterSystem.simple j * u⁻¹) :
    weylAction hA w (Pi.single i 1) = weylAction hA u (Pi.single j 1) ∨
      weylAction hA w (Pi.single i 1) = -weylAction hA u (Pi.single j 1) := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  set g := u⁻¹ * w with hg
  have hgs : g * cs.simple i = cs.simple j * g := by
    have : u⁻¹ * (w * cs.simple i * w⁻¹) * w = u⁻¹ * (u * cs.simple j * u⁻¹) * w := by rw [h]
    rw [hg]
    simpa [mul_assoc] using this
  set γ := weylAction hA g (Pi.single i 1) with hγ
  have hneg : reflection A j γ = -γ := by
    rw [← weylAction_simple, hγ, ← weylAction_mul_apply, ← hgs, weylAction_mul_apply,
      weylAction_simple_single, map_neg]
  have h2 : (2 : ℤ) • γ = coroot A j γ • weylAction hA 1 (Pi.single j 1) := by
    rw [map_one, Module.End.one_apply]
    rw [reflection_apply_coroot] at hneg
    have := congrArg (fun v => γ - v) hneg
    simp only [sub_sub_cancel, sub_neg_eq_add] at this
    rw [two_smul, ← this]
  rcases eq_or_eq_neg_of_smul_eq_smul hA 1 g j i two_ne_zero h2.symm with h3 | h3
  · left
    rw [map_one, Module.End.one_apply] at h3
    rw [show w = u * g by rw [hg, mul_inv_cancel_left], weylAction_mul_apply, h3]
  · right
    rw [map_one, Module.End.one_apply] at h3
    rw [show w = u * g by rw [hg, mul_inv_cancel_left], weylAction_mul_apply, h3, map_neg]

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType.S2MathFi1451

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg.OfCartan CFSG.StandardType
open CFSG.StandardType.CoxTriple

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

@[expose] noncomputable def rootCoroot (w : (coxeterMatrix hA).Group) (i : I) : (I → ℤ) →ₗ[ℤ] ℤ :=
  (coroot A i).comp (weylAction hA w⁻¹)

theorem rootCoroot_apply (w : (coxeterMatrix hA).Group) (i : I) (v : I → ℤ) :
    rootCoroot hA w i v = coroot A i (weylAction hA w⁻¹ v) := rfl

theorem rootCoroot_self (w : (coxeterMatrix hA).Group) (i : I) :
    rootCoroot hA w i (weylAction hA w (Pi.single i 1)) = 2 := by
  rw [rootCoroot_apply, weylAction_inv_apply_apply, coroot_single, hA.apply_self]

private theorem l05nCJ_coxPairing_eq_coroot
    (g : (coxeterMatrix hA).Group) (i : I) (v : I → ℤ) :
    ((coroot A i (weylAction hA g⁻¹ v) : ℤ) : ℚ) = coxPairing hA v (coxRoot hA g i) := by
  have hρ : coxRoot hA g i = weylAction hA g (Pi.single i 1) := rfl
  have hBne : form hA (toRat (coxRoot hA g i)) (toRat (coxRoot hA g i)) ≠ 0 :=
    (form_pos hA (toRat_weylAction_single_ne_zero hA g i)).ne'
  have hself : ((coroot A i (weylAction hA g⁻¹ v) : ℤ) : ℚ) *
      form hA (toRat (coxRoot hA g i)) (toRat (coxRoot hA g i)) =
      2 * form hA (toRat v) (toRat (coxRoot hA g i)) := by
    have h := coroot_mul_form_self hA g i v
    rw [hρ]
    rwa [form_comm hA (toRat (weylAction hA g (Pi.single i 1))) (toRat v)] at h
  rw [coxPairing, eq_div_iff hBne]
  exact hself

theorem orderOf_conj_mul_conj {w u : (coxeterMatrix hA).Group} {i j : I}
    (hne : w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹ ≠
      u * (coxeterMatrix hA).toCoxeterSystem.simple j * u⁻¹) :
    coroot A i (weylAction hA w⁻¹ (weylAction hA u (Pi.single j 1))) *
        coroot A j (weylAction hA u⁻¹ (weylAction hA w (Pi.single i 1))) ∈
        ({0, 1, 2, 3} : Set ℤ) ∧
      (coroot A i (weylAction hA w⁻¹ (weylAction hA u (Pi.single j 1))) = 0 ↔
        coroot A j (weylAction hA u⁻¹ (weylAction hA w (Pi.single i 1))) = 0) ∧
      orderOf (w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹ *
          (u * (coxeterMatrix hA).toCoxeterSystem.simple j * u⁻¹)) =
        TauCeti.coxeterOrder (coroot A i (weylAction hA w⁻¹ (weylAction hA u (Pi.single j 1))) *
          coroot A j (weylAction hA u⁻¹ (weylAction hA w (Pi.single i 1)))) := by
  set β := weylAction hA w (Pi.single i 1) with hβ
  set γ := weylAction hA u (Pi.single j 1) with hγ
  set a := coroot A i (weylAction hA w⁻¹ γ) with ha
  set b := coroot A j (weylAction hA u⁻¹ β) with hb
  set X := form hA (toRat β) (toRat γ) with hX
  have hB1 : (a : ℚ) * form hA (toRat β) (toRat β) = 2 * X := coroot_mul_form_self hA w i γ
  have hB2 : (b : ℚ) * form hA (toRat γ) (toRat γ) = 2 * X := by
    have := coroot_mul_form_self hA u j β
    rw [form_comm hA _ (toRat β)] at this
    exact this
  have hβ0 := toRat_weylAction_single_ne_zero hA w i
  have hγ0 := toRat_weylAction_single_ne_zero hA u j
  have hPβ := form_pos hA hβ0
  have hPγ := form_pos hA hγ0
  have hsign : (a ≤ 0 ∧ b ≤ 0) ∨ (0 ≤ a ∧ 0 ≤ b) := by
    rcases le_total X 0 with hX0 | hX0
    · left
      constructor
      · have : (a : ℚ) ≤ 0 := by nlinarith
        exact_mod_cast this
      · have : (b : ℚ) ≤ 0 := by nlinarith
        exact_mod_cast this
    · right
      constructor
      · have : (0 : ℚ) ≤ a := by nlinarith
        exact_mod_cast this
      · have : (0 : ℚ) ≤ b := by nlinarith
        exact_mod_cast this
  have hab : a = 0 ↔ b = 0 := by
    constructor
    · intro h0
      rw [h0] at hB1
      have hX0 : X = 0 := by push_cast at hB1; linarith
      rw [hX0] at hB2
      have : (b : ℚ) = 0 := by
        rcases mul_eq_zero.mp (show (b : ℚ) * form hA (toRat γ) (toRat γ) = 0 by linarith) with
          h | h
        · exact h
        · exact absurd h hPγ.ne'
      exact_mod_cast this
    · intro h0
      rw [h0] at hB2
      have hX0 : X = 0 := by push_cast at hB2; linarith
      rw [hX0] at hB1
      have : (a : ℚ) = 0 := by
        rcases mul_eq_zero.mp (show (a : ℚ) * form hA (toRat β) (toRat β) = 0 by linarith) with
          h | h
        · exact h
        · exact absurd h hPβ.ne'
      exact_mod_cast this
  have hprop : ∀ t : ℚ, toRat β ≠ t • toRat γ := by
    intro t ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hβ0 (by rw [ht, zero_smul])
    exact hne (ggWeyl_conj_simple_eq_of_root_smul hA w u i j ht0 ht)
  have h4 : a * b < 4 := mul_lt_four hA hβ0 hγ0 hprop hB1 (by rw [hB2])
  have hnn : 0 ≤ a * b := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_nonneg_of_nonpos_of_nonpos h1 h2
    · exact mul_nonneg h1 h2
  have hmem : a * b ∈ ({0, 1, 2, 3} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    generalize a * b = c at *
    omega
  have haP : (a : ℚ) = coxPairing hA γ β := l05nCJ_coxPairing_eq_coroot hA w i γ
  have hbP : (b : ℚ) = coxPairing hA β γ := l05nCJ_coxPairing_eq_coroot hA u j β
  have hpair : coxPairing hA γ β * coxPairing hA β γ = (a * b : ℚ) := by
    rw [← haP, ← hbP]
  have hnp : ¬ ∃ q : ℚ, toRat (coxRoot hA u j) = q • toRat (coxRoot hA w i) := by
    rintro ⟨q, hq⟩
    have hcs : (coxeterMatrix hA).toCoxeterSystem.simple = (coxeterMatrix hA).simple :=
      CoxeterMatrix.toCoxeterSystem_simple (coxeterMatrix hA)
    rw [hcs] at hne
    have hc' : w * (coxeterMatrix hA).simple i * w⁻¹ =
        u * (coxeterMatrix hA).simple j * u⁻¹ :=
      (coxRefl_eq_of_proportional hA w u i j q hq).symm
    exact hne hc'
  refine ⟨hmem, hab, ?_⟩
  have hcs : (coxeterMatrix hA).toCoxeterSystem.simple = (coxeterMatrix hA).simple :=
    CoxeterMatrix.toCoxeterSystem_simple (coxeterMatrix hA)
  rw [hcs]
  change orderOf (coxRefl hA w i * coxRefl hA u j) = TauCeti.coxeterOrder (a * b)
  have hmem' : a * b = 0 ∨ a * b = 1 ∨ a * b = 2 ∨ a * b = 3 := by
    simpa using hmem
  rcases hmem' with h0 | h1 | h2 | h3
  · have hp : coxPairing hA γ β * coxPairing hA β γ = (0 : ℚ) := by
      rw [hpair, ← Int.cast_mul, h0]
      norm_num
    rw [h0, TauCeti.coxeterOrder_zero]
    exact (orderOf_coxRefl_mul hA w u i j hnp).1 hp
  · have hp : coxPairing hA γ β * coxPairing hA β γ = (1 : ℚ) := by
      rw [hpair, ← Int.cast_mul, h1]
      norm_num
    rw [h1, TauCeti.coxeterOrder_one]
    exact (orderOf_coxRefl_mul hA w u i j hnp).2.1 hp
  · have hp : coxPairing hA γ β * coxPairing hA β γ = (2 : ℚ) := by
      rw [hpair, ← Int.cast_mul, h2]
      norm_num
    rw [h2, TauCeti.coxeterOrder_two]
    exact (orderOf_coxRefl_mul hA w u i j hnp).2.2.1 hp
  · have hp : coxPairing hA γ β * coxPairing hA β γ = (3 : ℚ) := by
      rw [hpair, ← Int.cast_mul, h3]
      norm_num
    rw [h3, TauCeti.coxeterOrder_three]
    exact (orderOf_coxRefl_mul hA w u i j hnp).2.2.2 hp

end CFSG.StandardType.S2MathFi1451
