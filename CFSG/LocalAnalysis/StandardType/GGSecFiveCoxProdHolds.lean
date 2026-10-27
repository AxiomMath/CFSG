module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProd
import CFSG.LocalAnalysis.StandardType.GGWeylCartan
import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.OfCartan

private theorem p10_conj_simple_sq {ι : Type} (M : CoxeterMatrix ι) (w : M.Group) (i : ι) :
    (w * M.simple i * w⁻¹) ^ 2 = 1 := by
  rw [conj_pow, show M.simple i ^ 2 = 1 from M.toCoxeterSystem.simple_sq i, mul_one,
    mul_inv_cancel]

private theorem p10_symmetrizer_mul_entry {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (i j : I) :
    symmetrizer hA i * (A i j : ℚ) = symmetrizer hA j * (A j i : ℚ) := by
  have h1 : form hA (Pi.single i 1) (Pi.single j 1) = symmetrizer hA i * (A i j : ℚ) := by
    rw [form_single_left]
    congr 1
    simp [Pi.single_apply]
  have h2 : form hA (Pi.single j 1) (Pi.single i 1) = symmetrizer hA j * (A j i : ℚ) := by
    rw [form_single_left]
    congr 1
    simp [Pi.single_apply]
  have hc := form_comm hA (Pi.single i 1) (Pi.single j 1)
  rw [h1, h2] at hc
  exact hc

private theorem p10_symmetrizer_eq_of_entry_one {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) {i j : I}
    (hij : A i j = -1) (hji : A j i = -1) :
    symmetrizer hA i = symmetrizer hA j := by
  have h := p10_symmetrizer_mul_entry hA i j
  rw [hij, hji] at h
  ring_nf at h
  linarith

private theorem p10_symmetrizer_double_of_entry {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) {i j : I}
    (hij : A i j = -2) (hji : A j i = -1) :
    symmetrizer hA j = 2 * symmetrizer hA i := by
  have h := p10_symmetrizer_mul_entry hA i j
  rw [hij, hji] at h
  ring_nf at h
  linarith

private theorem p10_label_le_three_reindex {κ : Type*} (N : CoxeterMatrix κ)
    (h : ∀ i j : κ, i ≠ j → N.M i j ≤ 3) {ι : Type*} (e : κ ≃ ι) :
    ∀ i j : ι, i ≠ j → (N.reindex e).M i j ≤ 3 := by
  intro i j hij
  rw [CoxeterMatrix.reindex_apply]
  exact h (e.symm i) (e.symm j) (fun hh => hij (e.symm.injective hh))

private theorem p10_le_three_A (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

private theorem p10_le_three_D (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ggCoxeterMatrixD n).M i j ≤ 3 := by
  rw [ggCoxeterMatrixD_apply]
  split_ifs <;> omega

private theorem p10_le_three_E6 (i j : Fin 6) (hij : i ≠ j) :
    (CoxeterMatrix.E₆).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem p10_le_three_E7 (i j : Fin 7) (hij : i ≠ j) :
    (CoxeterMatrix.E₇).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem p10_le_three_E8 (i j : Fin 8) (hij : i ≠ j) :
    (CoxeterMatrix.E₈).M i j ≤ 3 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem p10_pow_sub_mem_span {V : Type*} [AddCommGroup V] [Module ℤ V]
    (F : Module.End ℤ V) (S : Submodule ℤ V)
    (hmaps : ∀ s ∈ S, F s ∈ S) (hsub : ∀ v : V, F v - v ∈ S) (k : ℕ) (v : V) :
    (F ^ k) v - v ∈ S := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (F ^ (k + 1)) v - v = F ((F ^ k) v - v) + (F v - v) := by
      rw [pow_succ']
      simp only [Module.End.mul_apply, map_sub]
      abel
    rw [h]
    exact S.add_mem (hmaps _ ih) (hsub v)

private theorem p10_weylAction_pow_eq_one_of_fixes_span {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ρ σ : I → ℤ) (k : ℕ)
    (hsub : ∀ v : I → ℤ,
      weylAction hC t v - v ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hfixρ : weylAction hC (t ^ k) ρ = ρ)
    (hfixσ : weylAction hC (t ^ k) σ = σ) :
    weylAction hC (t ^ k) = 1 := by
  classical
  set S : Submodule ℤ (I → ℤ) := Submodule.span ℤ ({ρ, σ} : Set (I → ℤ))
  have hmaps : ∀ s ∈ S, weylAction hC t s ∈ S := by
    intro s hs
    have h : weylAction hC t s = s + (weylAction hC t s - s) := by abel
    rw [h]
    exact S.add_mem hs (hsub s)
  have hfix : ∀ s ∈ S, weylAction hC (t ^ k) s = s := by
    intro s hs
    refine Submodule.span_induction (p := fun x _ => weylAction hC (t ^ k) x = x)
      ?_ ?_ ?_ ?_ hs
    · intro x hx
      rcases hx with rfl | rfl
      · exact hfixρ
      · exact hfixσ
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add, ihx, ihy]
    · intro c x hx ih
      rw [map_smul, ih]
  have hmem : ∀ v : I → ℤ, weylAction hC (t ^ k) v - v ∈ S := by
    intro v
    have h := p10_pow_sub_mem_span (weylAction hC t) S hmaps hsub k v
    simpa only [map_pow] using h
  have hinvfix : ∀ s ∈ S, weylAction hC ((t⁻¹) ^ k) s = s := by
    intro s hs
    have h1 : weylAction hC ((t⁻¹) ^ k) (weylAction hC (t ^ k) s) = s := by
      rw [← weylAction_mul_apply, inv_pow, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hfix s hs] at h1
    exact h1
  have hTk_inv_smul : ∀ x : I → ℤ,
      weylAction hC (t ^ k) (weylAction hC ((t⁻¹) ^ k) x) = x := by
    intro x
    rw [← weylAction_mul_apply, inv_pow, mul_inv_cancel, map_one, Module.End.one_apply]
  have horth : ∀ v : I → ℤ, ∀ s ∈ S,
      form hC (toRat (weylAction hC (t ^ k) v - v)) (toRat s) = 0 := by
    intro v s hs
    have h2 : form hC (toRat (weylAction hC (t ^ k) v)) (toRat s) =
        form hC (toRat v) (toRat (weylAction hC ((t⁻¹) ^ k) s)) := by
      have h3 := form_weylAction hC (t ^ k) v (weylAction hC ((t⁻¹) ^ k) s)
      rwa [hTk_inv_smul s] at h3
    have hsplit : form hC (toRat (weylAction hC (t ^ k) v - v)) (toRat s) =
        form hC (toRat (weylAction hC (t ^ k) v)) (toRat s) - form hC (toRat v) (toRat s) := by
      rw [map_sub, map_sub, LinearMap.sub_apply]
    rw [hsplit, h2, hinvfix s hs, sub_self]
  have hfinal : ∀ v : I → ℤ, weylAction hC (t ^ k) v = v := by
    intro v
    have hy : weylAction hC (t ^ k) v - v ∈ S := hmem v
    by_contra hv
    have hne : toRat (weylAction hC (t ^ k) v - v) ≠ 0 := fun h =>
      (sub_ne_zero.mpr hv) (toRat_injective (by simpa using h))
    have hpos := form_pos hC hne
    have hzero := horth v _ hy
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℚ)) hpos
  apply LinearMap.ext
  intro v
  exact hfinal v

private theorem p10_generic {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hno3 : ∀ (w w' : (coxeterMatrix hC).Group) (i j : I),
      coroot C i (weylAction hC w⁻¹ (weylAction hC w' (Pi.single j 1))) *
      coroot C j (weylAction hC w'⁻¹ (weylAction hC w (Pi.single i 1))) ≠ 3)
    (w w' : (coxeterMatrix hC).Group) (i j : I) :
    orderOf ((w * (coxeterMatrix hC).simple i * w⁻¹) *
      (w' * (coxeterMatrix hC).simple j * w'⁻¹)) ≤ 4 := by
  classical
  let u := w * (coxeterMatrix hC).simple i * w⁻¹
  let v := w' * (coxeterMatrix hC).simple j * w'⁻¹
  let t := u * v
  let ρ := weylAction hC w (Pi.single i 1)
  let σ := weylAction hC w' (Pi.single j 1)
  let a : ℤ := coroot C i (weylAction hC w⁻¹ σ)
  let b : ℤ := coroot C j (weylAction hC w'⁻¹ ρ)
  let Sρ := weylAction hC u
  let Sσ := weylAction hC v
  let Tm : Module.End ℤ (I → ℤ) := Sρ * Sσ
  let n1 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C i).comp (weylAction hC w⁻¹)
  let n2 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C j).comp (weylAction hC w'⁻¹)
  have ht : weylAction hC t = Tm := by
    show weylAction hC (u * v) = Sρ * Sσ
    rw [map_mul]
  have hn1ρ : n1 ρ = 2 := by
    show coroot C i (weylAction hC w⁻¹ ρ) = 2
    have h : weylAction hC w⁻¹ ρ = Pi.single i 1 := by
      show weylAction hC w⁻¹ (weylAction hC w (Pi.single i 1)) = Pi.single i 1
      rw [weylAction_inv_apply_apply]
    rw [h, coroot_single, hC.apply_self]
  have hn2σ : n2 σ = 2 := by
    show coroot C j (weylAction hC w'⁻¹ σ) = 2
    have h : weylAction hC w'⁻¹ σ = Pi.single j 1 := by
      show weylAction hC w'⁻¹ (weylAction hC w' (Pi.single j 1)) = Pi.single j 1
      rw [weylAction_inv_apply_apply]
    rw [h, coroot_single, hC.apply_self]
  have hn1σ : n1 σ = a := rfl
  have hn2ρ : n2 ρ = b := rfl
  have hSρ : ∀ x : I → ℤ, Sρ x = x - n1 x • ρ := by
    intro x
    change weylAction hC (w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹) x = _
    rw [weylAction_conj_simple hC w i x]
    rfl
  have hSσ : ∀ x : I → ℤ, Sσ x = x - n2 x • σ := by
    intro x
    change weylAction hC (w' * (coxeterMatrix hC).toCoxeterSystem.simple j * w'⁻¹) x = _
    rw [weylAction_conj_simple hC w' j x]
    rfl
  have hTmρ : Tm ρ = (a * b - 1) • ρ - b • σ := by
    show (Sρ * Sσ) ρ = _
    rw [Module.End.mul_apply, hSσ, hSρ]
    simp only [map_sub, map_smul, hn1ρ, hn1σ, hn2ρ, smul_eq_mul]
    module
  have hTmσ : Tm σ = a • ρ - σ := by
    show (Sρ * Sσ) σ = _
    rw [Module.End.mul_apply, hSσ, hSρ]
    simp only [map_sub, map_smul, hn2σ, hn1ρ, hn1σ, hn2ρ, smul_eq_mul]
    module
  have hspan_mem : ∀ x : I → ℤ,
      weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)) := by
    intro x
    rw [ht]
    have e1 : Sσ x - x = -(n2 x) • σ := by rw [hSσ]; module
    have e2 : Sρ (Sσ x) - Sσ x = -(n1 (Sσ x)) • ρ := by rw [hSρ]; module
    have e3 : Tm x - x = (Sρ (Sσ x) - Sσ x) + (Sσ x - x) := by
      show (Sρ * Sσ) x - x = _
      rw [Module.End.mul_apply]
      abel
    rw [e3, e2, e1]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  by_cases hprop : ∃ c : ℚ, toRat ρ = c • toRat σ
  · obtain ⟨c, hc⟩ := hprop
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact (toRat_weylAction_single_ne_zero hC w i) hc
    have huv : u = v := ggWeyl_conj_simple_eq_of_root_smul hC w w' i j hc0 hc
    have ht1 : t = 1 := by
      show u * v = 1
      rw [← huv, ← sq]
      exact p10_conj_simple_sq (coxeterMatrix hC) w i
    change orderOf t ≤ 4
    rw [ht1]
    simp
  · push Not at hprop
    have hx : toRat ρ ≠ 0 := toRat_weylAction_single_ne_zero hC w i
    have hy : toRat σ ≠ 0 := toRat_weylAction_single_ne_zero hC w' j
    have ha : (a : ℚ) * form hC (toRat ρ) (toRat ρ) = 2 * form hC (toRat ρ) (toRat σ) :=
      coroot_mul_form_self hC w i σ
    have hb : (b : ℚ) * form hC (toRat σ) (toRat σ) = 2 * form hC (toRat ρ) (toRat σ) := by
      have h := coroot_mul_form_self hC w' j ρ
      rwa [form_comm hC (toRat σ) (toRat ρ)] at h
    have hlt : a * b < 4 := mul_lt_four hC hx hy hprop ha hb
    have hBρρ : 0 < form hC (toRat ρ) (toRat ρ) := form_pos hC hx
    have hBσσ : 0 < form hC (toRat σ) (toRat σ) := form_pos hC hy
    have hge : 0 ≤ a * b := by
      have hfac : (a : ℚ) * form hC (toRat ρ) (toRat ρ) *
            ((b : ℚ) * form hC (toRat σ) (toRat σ)) =
          ((a : ℚ) * b) *
            (form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ)) := by ring
      have hmul : ((a : ℚ) * b) *
            (form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ)) =
          4 * form hC (toRat ρ) (toRat σ) ^ 2 := by
        rw [← hfac, ha, hb]
        ring
      have hpos : 0 < form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ) :=
        mul_pos hBρρ hBσσ
      have : 0 ≤ (a : ℚ) * b := by
        nlinarith [hmul, hpos, sq_nonneg (form hC (toRat ρ) (toRat σ))]
      exact_mod_cast this
    have hno3' : a * b ≠ 3 := hno3 w w' i j
    have hab : a * b = 0 ∨ a * b = 1 ∨ a * b = 2 := by omega
    have hT2ρ : Tm (Tm ρ) = ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ := by
      rw [hTmρ]
      simp only [map_sub, map_smul]
      rw [hTmρ, hTmσ]
      module
    have hT2σ : Tm (Tm σ) = (a * (a * b - 2)) • ρ + (1 - a * b) • σ := by
      rw [hTmσ]
      simp only [map_sub, map_smul]
      rw [hTmρ, hTmσ]
      module
    rcases hab with h0 | h1 | h2
    ·
      have hab0 : a = 0 ∧ b = 0 := by
        rcases mul_eq_zero.mp h0 with ha0 | hb0
        · have hBρσ : form hC (toRat ρ) (toRat σ) = 0 := by
            have h := ha
            rw [ha0] at h
            push_cast at h
            linarith
          refine ⟨ha0, ?_⟩
          have h := hb
          rw [hBρσ] at h
          push_cast at h
          have : (b : ℚ) = 0 := by nlinarith
          exact_mod_cast this
        · refine ⟨?_, hb0⟩
          have hBρσ : form hC (toRat ρ) (toRat σ) = 0 := by
            have h := hb
            rw [hb0] at h
            push_cast at h
            linarith
          have h := ha
          rw [hBρσ] at h
          push_cast at h
          have : (a : ℚ) = 0 := by nlinarith
          exact_mod_cast this
      have hT2ρ' : Tm (Tm ρ) = ρ := by rw [hT2ρ, hab0.1, hab0.2]; module
      have hT2σ' : Tm (Tm σ) = σ := by rw [hT2σ, hab0.1, hab0.2]; module
      have hfixρ : weylAction hC (t ^ 2) ρ = ρ := by
        rw [map_pow, ht, sq, Module.End.mul_apply]
        exact hT2ρ'
      have hfixσ : weylAction hC (t ^ 2) σ = σ := by
        rw [map_pow, ht, sq, Module.End.mul_apply]
        exact hT2σ'
      have h1 : weylAction hC (t ^ 2) = 1 :=
        p10_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 2 hspan_mem hfixρ hfixσ
      have hpow : (weylAction hC t) ^ 2 = 1 := by simpa only [map_pow] using h1
      have hdvd : orderOf (weylAction hC t) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hle : orderOf (weylAction hC t) ≤ 4 :=
        le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      rwa [orderOf_injective (weylAction hC) (weylAction_injective hC) t] at hle
    ·
      have hT2ρ' : Tm (Tm ρ) = -ρ + b • σ := by rw [hT2ρ, h1]; module
      have hT2σ' : Tm (Tm σ) = -a • ρ := by rw [hT2σ, h1]; module
      have h1b : b * a = 1 := by rw [mul_comm]; exact h1
      have hT3ρ : Tm (Tm (Tm ρ)) = ρ := by
        rw [hT2ρ', map_add, map_neg, map_smul, hTmρ, hTmσ]
        simp only [h1, h1b, smul_sub, smul_smul, one_smul, zero_smul, neg_smul, neg_neg,
          sub_self, sub_zero, add_zero, zero_add, neg_sub]
        simp
      have hT3σ : Tm (Tm (Tm σ)) = σ := by
        rw [hT2σ', map_smul, hTmρ]
        simp only [h1, smul_sub, smul_smul, one_smul, zero_smul, neg_smul, neg_neg, mul_one,
          one_mul, mul_neg, neg_mul, sub_self, sub_zero, add_zero, zero_add, neg_sub]
        simp
      have hfixρ : weylAction hC (t ^ 3) ρ = ρ := by
        rw [map_pow, ht]
        show (Tm ^ 3) ρ = ρ
        rw [show Tm ^ 3 = Tm * Tm * Tm by rw [pow_succ, pow_two], Module.End.mul_apply,
          Module.End.mul_apply]
        exact hT3ρ
      have hfixσ : weylAction hC (t ^ 3) σ = σ := by
        rw [map_pow, ht]
        show (Tm ^ 3) σ = σ
        rw [show Tm ^ 3 = Tm * Tm * Tm by rw [pow_succ, pow_two], Module.End.mul_apply,
          Module.End.mul_apply]
        exact hT3σ
      have h1 : weylAction hC (t ^ 3) = 1 :=
        p10_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 3 hspan_mem hfixρ hfixσ
      have hpow : (weylAction hC t) ^ 3 = 1 := by simpa only [map_pow] using h1
      have hdvd : orderOf (weylAction hC t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hle : orderOf (weylAction hC t) ≤ 4 :=
        le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      rwa [orderOf_injective (weylAction hC) (weylAction_injective hC) t] at hle
    ·
      have hT2ρ' : Tm (Tm ρ) = -ρ := by rw [hT2ρ, h2]; module
      have hT2σ' : Tm (Tm σ) = -σ := by rw [hT2σ, h2]; module
      have hfixρ : weylAction hC (t ^ 4) ρ = ρ := by
        rw [map_pow, ht]
        show (Tm ^ 4) ρ = ρ
        rw [show Tm ^ 4 = Tm ^ 2 * Tm ^ 2 by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
          Module.End.mul_apply]
        rw [show (Tm ^ 2) ρ = -ρ from hT2ρ']
        rw [map_neg, show (Tm ^ 2) ρ = -ρ from hT2ρ', neg_neg]
      have hfixσ : weylAction hC (t ^ 4) σ = σ := by
        rw [map_pow, ht]
        show (Tm ^ 4) σ = σ
        rw [show Tm ^ 4 = Tm ^ 2 * Tm ^ 2 by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
          Module.End.mul_apply]
        rw [show (Tm ^ 2) σ = -σ from hT2σ']
        rw [map_neg, show (Tm ^ 2) σ = -σ from hT2σ', neg_neg]
      have h1 : weylAction hC (t ^ 4) = 1 :=
        p10_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 4 hspan_mem hfixρ hfixσ
      have hpow : (weylAction hC t) ^ 4 = 1 := by simpa only [map_pow] using h1
      have hdvd : orderOf (weylAction hC t) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hpow
      have hle : orderOf (weylAction hC t) ≤ 4 :=
        le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      rwa [orderOf_injective (weylAction hC) (weylAction_injective hC) t] at hle

private theorem p10_no_three_of_symmetrizer_ne_three {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hsym : ∀ i j : I, symmetrizer hC i ≠ 3 * symmetrizer hC j) :
    ∀ (w w' : (coxeterMatrix hC).Group) (i j : I),
      coroot C i (weylAction hC w⁻¹ (weylAction hC w' (Pi.single j 1))) *
      coroot C j (weylAction hC w'⁻¹ (weylAction hC w (Pi.single i 1))) ≠ 3 := by
  intro w w' i j h
  let ρ := weylAction hC w (Pi.single i 1)
  let σ := weylAction hC w' (Pi.single j 1)
  generalize hA_def : coroot C i (weylAction hC w⁻¹ σ) = a at h
  generalize hB_def : coroot C j (weylAction hC w'⁻¹ ρ) = b at h
  have hBρρ : 0 < form hC (toRat ρ) (toRat ρ) :=
    form_pos hC (toRat_weylAction_single_ne_zero hC w i)
  have hBσσ : 0 < form hC (toRat σ) (toRat σ) :=
    form_pos hC (toRat_weylAction_single_ne_zero hC w' j)
  have ha : (a : ℚ) * form hC (toRat ρ) (toRat ρ) = 2 * form hC (toRat ρ) (toRat σ) := by
    rw [← hA_def]
    exact coroot_mul_form_self hC w i σ
  have hb : (b : ℚ) * form hC (toRat σ) (toRat σ) = 2 * form hC (toRat ρ) (toRat σ) := by
    have hb' := coroot_mul_form_self hC w' j ρ
    rw [form_comm hC (toRat σ) (toRat ρ)] at hb'
    rw [← hB_def]
    exact hb'
  have hratio : (a : ℚ) * symmetrizer hC i = (b : ℚ) * symmetrizer hC j := by
    have h1 := form_weylAction_single_self hC w i
    have h2 := form_weylAction_single_self hC w' j
    have : (a : ℚ) * (2 * symmetrizer hC i) = (b : ℚ) * (2 * symmetrizer hC j) := by
      rw [← h1, ← h2, ha, hb]
    linarith
  have hab3 : a * b = 3 := h
  have hcases : (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ (a = 3 ∧ b = 1) ∨
      (a = -3 ∧ b = -1) := by
    have hb_ne : b ≠ 0 := by intro hb0; rw [hb0] at hab3; norm_num at hab3
    have habs : |a| * |b| = 3 := by rw [← abs_mul, hab3]; norm_num
    have hb1 : (1 : ℤ) ≤ |b| := by have := abs_pos.mpr hb_ne; omega
    have ha3 : |a| ≤ 3 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hbd := abs_le.mp ha3
    have hbdl : -3 ≤ a := hbd.1
    have hbdu : a ≤ 3 := hbd.2
    interval_cases a <;> omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h' : symmetrizer hC i = 3 * symmetrizer hC j := by
      have := hratio; norm_num at this; linarith
    exact hsym i j h'
  · have h' : symmetrizer hC i = 3 * symmetrizer hC j := by
      have := hratio; norm_num at this; linarith
    exact hsym i j h'
  · have h' : symmetrizer hC j = 3 * symmetrizer hC i := by
      have := hratio; norm_num at this; linarith
    exact hsym j i h'
  · have h' : symmetrizer hC j = 3 * symmetrizer hC i := by
      have := hratio; norm_num at this; linarith
    exact hsym j i h'

private theorem p10_symmetrizer_B_ne_three (n : ℕ) (hn : 2 ≤ n)
    (hFT : TauCeti.IsFiniteType (CartanMatrix.B n)) (i j : Fin n) :
    symmetrizer hFT i ≠ 3 * symmetrizer hFT j := by
  have hn0 : 0 < n := by omega
  let d0 : ℚ := symmetrizer hFT ⟨0, hn0⟩
  have hd0 : 0 < d0 := symmetrizer_pos hFT ⟨0, hn0⟩
  have hsym : ∀ m (hm : m < n), symmetrizer hFT ⟨m, hm⟩ = d0 ∨
      (m = n - 1 ∧ symmetrizer hFT ⟨m, hm⟩ = 2 * d0) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · left
        have he : (⟨0, hm⟩ : Fin n) = ⟨0, hn0⟩ := Fin.ext rfl
        rw [he]
      · have hm'lt : m - 1 < n := by omega
        have hlt' : m - 1 < m := by omega
        have ih' := ih (m - 1) hlt' hm'lt
        have hprev : symmetrizer hFT ⟨m - 1, hm'lt⟩ = d0 := by
          rcases ih' with h | ⟨h, _⟩
          · exact h
          · omega
        by_cases hlast : m = n - 1
        · right
          refine ⟨hlast, ?_⟩
          have hA1 : CartanMatrix.B n ⟨m - 1, hm'lt⟩ ⟨m, hm⟩ = -2 := by
            have hne : (⟨m - 1, hm'lt⟩ : Fin n) ≠ ⟨m, hm⟩ := by
              intro h
              have := congrArg Fin.val h
              simp at this
              omega
            have hsucc : (⟨m - 1, hm'lt⟩ : Fin n).val + 1 = (⟨m, hm⟩ : Fin n).val := by
              simp
              omega
            simp only [CartanMatrix.B, Matrix.of_apply]
            rw [if_neg hne, if_pos hsucc, if_pos hlast]
          have hA2 : CartanMatrix.B n ⟨m, hm⟩ ⟨m - 1, hm'lt⟩ = -1 := by
            have hne : (⟨m, hm⟩ : Fin n) ≠ ⟨m - 1, hm'lt⟩ := by
              intro h
              have := congrArg Fin.val h
              simp at this
              omega
            have hnot : ¬ (⟨m, hm⟩ : Fin n).val + 1 = (⟨m - 1, hm'lt⟩ : Fin n).val := by
              simp
              omega
            have hsucc : (⟨m - 1, hm'lt⟩ : Fin n).val + 1 = (⟨m, hm⟩ : Fin n).val := by
              simp
              omega
            simp only [CartanMatrix.B, Matrix.of_apply]
            rw [if_neg hne, if_neg hnot, if_pos hsucc]
          have hd := p10_symmetrizer_double_of_entry hFT hA1 hA2
          rw [hd, hprev]
        · left
          have hA1 : CartanMatrix.B n ⟨m - 1, hm'lt⟩ ⟨m, hm⟩ = -1 := by
            have hne : (⟨m - 1, hm'lt⟩ : Fin n) ≠ ⟨m, hm⟩ := by
              intro h
              have := congrArg Fin.val h
              simp at this
              omega
            have hsucc : (⟨m - 1, hm'lt⟩ : Fin n).val + 1 = (⟨m, hm⟩ : Fin n).val := by
              simp
              omega
            simp only [CartanMatrix.B, Matrix.of_apply]
            rw [if_neg hne, if_pos hsucc, if_neg hlast]
          have hA2 : CartanMatrix.B n ⟨m, hm⟩ ⟨m - 1, hm'lt⟩ = -1 := by
            have hne : (⟨m, hm⟩ : Fin n) ≠ ⟨m - 1, hm'lt⟩ := by
              intro h
              have := congrArg Fin.val h
              simp at this
              omega
            have hnot : ¬ (⟨m, hm⟩ : Fin n).val + 1 = (⟨m - 1, hm'lt⟩ : Fin n).val := by
              simp
              omega
            have hsucc : (⟨m - 1, hm'lt⟩ : Fin n).val + 1 = (⟨m, hm⟩ : Fin n).val := by
              simp
              omega
            simp only [CartanMatrix.B, Matrix.of_apply]
            rw [if_neg hne, if_neg hnot, if_pos hsucc]
          have he := p10_symmetrizer_eq_of_entry_one hFT hA1 hA2
          rw [← he, hprev]
  have hi_cases : symmetrizer hFT i = d0 ∨ symmetrizer hFT i = 2 * d0 := by
    rcases hsym i.val i.isLt with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hj_cases : symmetrizer hFT j = d0 ∨ symmetrizer hFT j = 2 * d0 := by
    rcases hsym j.val j.isLt with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hi_cases with hi | hi <;> rcases hj_cases with hj | hj <;>
    (intro h3; rw [hi, hj] at h3; nlinarith [hd0])

private theorem p10_symmetrizer_F4_ne_three (hFF : TauCeti.IsFiniteType CartanMatrix.F₄)
    (i j : Fin 4) : symmetrizer hFF i ≠ 3 * symmetrizer hFF j := by
  have h01 : symmetrizer hFF 0 = symmetrizer hFF 1 :=
    p10_symmetrizer_eq_of_entry_one hFF (by decide) (by decide)
  have h12 : symmetrizer hFF 2 = 2 * symmetrizer hFF 1 :=
    p10_symmetrizer_double_of_entry hFF (i := 1) (j := 2) (by decide) (by decide)
  have h23 : symmetrizer hFF 2 = symmetrizer hFF 3 :=
    p10_symmetrizer_eq_of_entry_one hFF (by decide) (by decide)
  have h3 : symmetrizer hFF 3 = 2 * symmetrizer hFF 1 := by rw [← h23]; exact h12
  have hpos : 0 < symmetrizer hFF 1 := symmetrizer_pos hFF 1
  have hcases : ∀ k : Fin 4, symmetrizer hFF k = symmetrizer hFF 1 ∨
      symmetrizer hFF k = 2 * symmetrizer hFF 1 := by
    intro k
    fin_cases k
    · exact Or.inl h01
    · exact Or.inl rfl
    · exact Or.inr h12
    · exact Or.inr h3
  intro h
  rcases hcases i with hi | hi <;> rcases hcases j with hj | hj <;>
    (rw [hi, hj] at h; linarith [hpos])

private theorem p10_no_three_B (n : ℕ) (hn : 2 ≤ n)
    (hFT : TauCeti.IsFiniteType (CartanMatrix.B n)) :
    ∀ (w w' : (coxeterMatrix hFT).Group) (i j : Fin n),
      coroot (CartanMatrix.B n) i (weylAction hFT w⁻¹ (weylAction hFT w' (Pi.single j 1))) *
      coroot (CartanMatrix.B n) j (weylAction hFT w'⁻¹ (weylAction hFT w (Pi.single i 1))) ≠ 3 :=
  p10_no_three_of_symmetrizer_ne_three hFT (p10_symmetrizer_B_ne_three n hn hFT)

private theorem p10_no_three_F4 (hFF : TauCeti.IsFiniteType CartanMatrix.F₄) :
    ∀ (w w' : (coxeterMatrix hFF).Group) (i j : Fin 4),
      coroot CartanMatrix.F₄ i (weylAction hFF w⁻¹ (weylAction hFF w' (Pi.single j 1))) *
      coroot CartanMatrix.F₄ j (weylAction hFF w'⁻¹ (weylAction hFF w (Pi.single i 1))) ≠ 3 :=
  p10_no_three_of_symmetrizer_ne_three hFF (p10_symmetrizer_F4_ne_three hFF)

private theorem p10_generic_of_eq {I : Type} [Fintype I] [DecidableEq I]
    {M : CoxeterMatrix I} {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hco : coxeterMatrix hC = M)
    (hno3 : ∀ (w w' : (coxeterMatrix hC).Group) (i j : I),
      coroot C i (weylAction hC w⁻¹ (weylAction hC w' (Pi.single j 1))) *
      coroot C j (weylAction hC w'⁻¹ (weylAction hC w (Pi.single i 1))) ≠ 3)
    (i j : I) (g h : M.Group) :
    orderOf (g * M.simple i * g⁻¹ * (h * M.simple j * h⁻¹)) ≤ 4 := by
  cases hco
  exact p10_generic hC hno3 g h i j

private theorem p10_simplyLaced {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (i j : ι) (g h : M.Group) :
    orderOf (g * M.simple i * g⁻¹ * (h * M.simple j * h⁻¹)) ≤ 4 := by
  obtain ⟨C, hC, -, rfl⟩ := ggWeylCartan hM hle3
  have hconn := ggSimplyLacedConnected_of_weyl hM hle3
  by_cases hc : Commute (g * (coxeterMatrix hC).simple i * g⁻¹)
      (h * (coxeterMatrix hC).simple j * h⁻¹)
  · have hx2 : (g * (coxeterMatrix hC).simple i * g⁻¹) ^ 2 = 1 :=
      p10_conj_simple_sq (coxeterMatrix hC) g i
    have hy2 : (h * (coxeterMatrix hC).simple j * h⁻¹) ^ 2 = 1 :=
      p10_conj_simple_sq (coxeterMatrix hC) h j
    have hp2 : ((g * (coxeterMatrix hC).simple i * g⁻¹) *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ^ 2 = 1 := by
      rw [hc.mul_pow, hx2, hy2, mul_one]
    have hdvd : orderOf ((g * (coxeterMatrix hC).simple i * g⁻¹) *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hp2
    exact le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  · have h3 := ggWeyl_refl_order3 hC hconn g h i j hc
    have hdvd : orderOf ((g * (coxeterMatrix hC).simple i * g⁻¹) *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h3
    exact le_trans (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

private theorem p10_B (n : ℕ) (hn : 2 ≤ n) :
    ∀ (i j : Fin n) (g h : (CoxeterMatrix.B n).Group),
      orderOf (g * (CoxeterMatrix.B n).simple i * g⁻¹ *
        (h * (CoxeterMatrix.B n).simple j * h⁻¹)) ≤ 4 := by
  intro i j g h
  have hFT : TauCeti.IsFiniteType (CartanMatrix.B n) := TauCeti.isFiniteType_cartanMatrix_B n
  have hco : coxeterMatrix hFT = CoxeterMatrix.B n :=
    coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_B n)
  exact p10_generic_of_eq hFT hco (p10_no_three_B n hn hFT) i j g h

private theorem p10_F4 :
    ∀ (i j : Fin 4) (g h : (CoxeterMatrix.F₄).Group),
      orderOf (g * (CoxeterMatrix.F₄).simple i * g⁻¹ *
        (h * (CoxeterMatrix.F₄).simple j * h⁻¹)) ≤ 4 := by
  intro i j g h
  have hFF : TauCeti.IsFiniteType CartanMatrix.F₄ := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
    rwa [TauCeti.DynkinType.cartanMatrix_F4] at h
  have hco : coxeterMatrix hFF = CoxeterMatrix.F₄ :=
    coxeterMatrix_eq_of_ggIntCartan hFF ggIntCartan_F₄
  exact p10_generic_of_eq hFF hco (p10_no_three_F4 hFF) i j g h

private theorem p10_B_reindex (n : ℕ) (hn : 2 ≤ n) {ι : Type} (e : Fin n ≃ ι)
    (i j : ι) (g h : ((CoxeterMatrix.B n).reindex e).Group) :
    orderOf (g * ((CoxeterMatrix.B n).reindex e).simple i * g⁻¹ *
      (h * ((CoxeterMatrix.B n).reindex e).simple j * h⁻¹)) ≤ 4 := by
  have hbase := p10_B n hn (e.symm i) (e.symm j)
    (((CoxeterMatrix.B n).reindexGroupEquiv e) g) (((CoxeterMatrix.B n).reindexGroupEquiv e) h)
  have hmap : ((CoxeterMatrix.B n).reindexGroupEquiv e)
      (g * ((CoxeterMatrix.B n).reindex e).simple i * g⁻¹ *
        (h * ((CoxeterMatrix.B n).reindex e).simple j * h⁻¹)) =
      ((CoxeterMatrix.B n).reindexGroupEquiv e) g * (CoxeterMatrix.B n).simple (e.symm i) *
          (((CoxeterMatrix.B n).reindexGroupEquiv e) g)⁻¹ *
        (((CoxeterMatrix.B n).reindexGroupEquiv e) h *
          (CoxeterMatrix.B n).simple (e.symm j) *
          (((CoxeterMatrix.B n).reindexGroupEquiv e) h)⁻¹) := by
    simp only [map_mul, map_inv, CoxeterMatrix.reindexGroupEquiv_apply_simple]
  rw [← hmap] at hbase
  rwa [MulEquiv.orderOf_eq] at hbase

private theorem p10_F4_reindex {ι : Type} (e : Fin 4 ≃ ι)
    (i j : ι) (g h : ((CoxeterMatrix.F₄).reindex e).Group) :
    orderOf (g * ((CoxeterMatrix.F₄).reindex e).simple i * g⁻¹ *
      (h * ((CoxeterMatrix.F₄).reindex e).simple j * h⁻¹)) ≤ 4 := by
  have hbase := p10_F4 (e.symm i) (e.symm j)
    ((CoxeterMatrix.F₄).reindexGroupEquiv e g) ((CoxeterMatrix.F₄).reindexGroupEquiv e h)
  have hmap : (CoxeterMatrix.F₄).reindexGroupEquiv e
      (g * ((CoxeterMatrix.F₄).reindex e).simple i * g⁻¹ *
        (h * ((CoxeterMatrix.F₄).reindex e).simple j * h⁻¹)) =
      (CoxeterMatrix.F₄).reindexGroupEquiv e g * (CoxeterMatrix.F₄).simple (e.symm i) *
          ((CoxeterMatrix.F₄).reindexGroupEquiv e g)⁻¹ *
        ((CoxeterMatrix.F₄).reindexGroupEquiv e h *
          (CoxeterMatrix.F₄).simple (e.symm j) *
          ((CoxeterMatrix.F₄).reindexGroupEquiv e h)⁻¹) := by
    simp only [map_mul, map_inv, CoxeterMatrix.reindexGroupEquiv_apply_simple]
  rw [← hmap] at hbase
  rwa [MulEquiv.orderOf_eq] at hbase

theorem ggSecFiveCoxProdInput_holds : GGSecFiveCoxProdInput := by
  intro ι M hM hnotG2 i j g h
  haveI : Finite ι := ggIsWeylMatrix_finite hM
  haveI : Fintype ι := Fintype.ofFinite ι
  classical
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ |
    ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2Eq⟩
  · have hM' : GGIsWeylMatrix ((CoxeterMatrix.A n).reindex e) :=
      Or.inl ⟨n, e, hn, Or.inl rfl⟩
    subst M
    exact p10_simplyLaced hM'
      (p10_label_le_three_reindex (CoxeterMatrix.A n) (p10_le_three_A n) e) i j g h
  · subst M
    exact p10_B_reindex n hn2 e i j g h
  · have hM' : GGIsWeylMatrix ((ggCoxeterMatrixD n).reindex e) :=
      Or.inl ⟨n, e, by omega, Or.inr (Or.inr ⟨hn4, rfl⟩)⟩
    subst M
    exact p10_simplyLaced hM'
      (p10_label_le_three_reindex (ggCoxeterMatrixD n) (p10_le_three_D n) e) i j g h
  · have hM' : GGIsWeylMatrix (CoxeterMatrix.E₆.reindex e) := Or.inr (Or.inl ⟨e, rfl⟩)
    subst M
    exact p10_simplyLaced hM'
      (p10_label_le_three_reindex CoxeterMatrix.E₆ p10_le_three_E6 e) i j g h
  · have hM' : GGIsWeylMatrix (CoxeterMatrix.E₇.reindex e) :=
      Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))
    subst M
    exact p10_simplyLaced hM'
      (p10_label_le_three_reindex CoxeterMatrix.E₇ p10_le_three_E7 e) i j g h
  · have hM' : GGIsWeylMatrix (CoxeterMatrix.E₈.reindex e) :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))
    subst M
    exact p10_simplyLaced hM'
      (p10_label_le_three_reindex CoxeterMatrix.E₈ p10_le_three_E8 e) i j g h
  · subst M
    exact p10_F4_reindex e i j g h
  · exact absurd ⟨e, hG2Eq⟩ hnotG2

end CFSG.StandardType

end
