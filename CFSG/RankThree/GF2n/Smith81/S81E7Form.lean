module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


theorem exists_opp (a : Fin e7Data.d) : ∃ b : Fin e7Data.d, e7Data.wt b = -e7Data.wt a := by
  revert a
  decide +kernel

open _root_.Classical in
@[expose] def opp (a : Fin e7Data.d) : Fin e7Data.d :=
  if h : ∃ b : Fin e7Data.d, e7Data.wt b = -e7Data.wt a then h.choose else a

theorem wt_opp (a : Fin e7Data.d) : e7Data.wt (opp a) = -e7Data.wt a := by
  have h := exists_opp a
  unfold opp
  rw [dif_pos h]
  exact h.choose_spec

theorem opp_eq {a b : Fin e7Data.d} (h : e7Data.wt b = -e7Data.wt a) : opp a = b :=
  wt_injective ((wt_opp a).trans h.symm)

theorem opp_opp (a : Fin e7Data.d) : opp (opp a) = a :=
  opp_eq (by rw [wt_opp, neg_neg])

theorem opp_ne_self (a : Fin e7Data.d) : opp a ≠ a := by
  have hfin : ∀ b : Fin e7Data.d, e7Data.wt b ≠ -e7Data.wt b := by
    decide +kernel
  intro h
  have h1 := wt_opp a
  rw [h] at h1
  exact hfin a h1

theorem pr_opp (a : Fin e7Data.d) (γ : Fin (Tag.rank .E7) → ℤ) : pr (opp a) γ = - pr a γ := by
  unfold pr
  rw [wt_opp, neg_dotProduct]

theorem opp_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) : opp (shift γ a) = shift (-γ) (opp a) := by
  have h' : pr (opp a) (-γ) = -1 := by
    rw [pr_opp, pr_neg, neg_neg, h]
  apply opp_eq
  rw [wt_shift (isRoot_neg hγ) h', wt_shift hγ h, wt_opp, MinData.toWeight_neg]
  abel

variable {K : Type} [Field K]

@[expose] def beta (x y : V K) : K := ∑ a : Fin e7Data.d, x a * y (opp a)

theorem beta_comm (x y : V K) : beta x y = beta y x := by
  unfold beta
  refine Fintype.sum_equiv (Function.Involutive.toPerm opp opp_opp) _ _ fun a => ?_
  show x a * y (opp a) = y (opp a) * x (opp (opp a))
  rw [opp_opp]
  exact mul_comm _ _

theorem beta_add_left (x x' y : V K) : beta (x + x') y = beta x y + beta x' y := by
  unfold beta
  simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem beta_add_right (x y y' : V K) : beta x (y + y') = beta x y + beta x y' := by
  unfold beta
  simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem beta_smul_left (c : K) (x y : V K) : beta (c • x) y = c * beta x y := by
  unfold beta
  simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem beta_smul_right (c : K) (x y : V K) : beta x (c • y) = c * beta x y := by
  unfold beta
  simp only [Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem beta_self [CharP K 2] (x : V K) : beta x x = 0 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  unfold beta
  refine Finset.sum_involution (fun a _ => opp a) ?_ ?_ ?_ ?_
  · intro a _
    show x a * x (opp a) + x (opp a) * x (opp (opp a)) = 0
    rw [opp_opp, mul_comm (x (opp a)) (x a)]
    linear_combination (x a * x (opp a)) * h2
  · intro a _ _
    exact opp_ne_self a
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    exact opp_opp a

theorem beta_xu [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) (x y : V K) :
    beta ((e7Data_valid.xu K γ c : Module.End K (V K)) x)
      ((e7Data_valid.xu K γ c : Module.End K (V K)) y) = beta x y := by
  have hx : ∀ b, ((e7Data_valid.xu K γ c : Module.End K (V K)) x) b
      = x b + c * (if pr b γ = 1 then x (shift (-γ) b) else 0) :=
    fun b => xu_apply_coord hγ c x b
  have hy : ∀ b, ((e7Data_valid.xu K γ c : Module.End K (V K)) y) b
      = y b + c * (if pr b γ = 1 then y (shift (-γ) b) else 0) :=
    fun b => xu_apply_coord hγ c y b
  have key : ∑ a : Fin e7Data.d, (if pr a γ = 1 then x (shift (-γ) a) else 0) * y (opp a)
      = ∑ a : Fin e7Data.d, x a * (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0) := by
    have h1 : ∀ a : Fin e7Data.d, (if pr a γ = 1 then x (shift (-γ) a) else 0) * y (opp a)
        = if pr a γ = 1 then x (shift (-γ) a) * y (opp a) else 0 := fun a => by
      by_cases h : pr a γ = 1 <;> simp [h]
    have h2 : ∀ a : Fin e7Data.d,
        x a * (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0)
        = if pr (opp a) γ = 1 then x a * y (shift (-γ) (opp a)) else 0 := fun a => by
      by_cases h : pr (opp a) γ = 1 <;> simp [h]
    simp only [h1, h2]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun a => shift (-γ) a) (fun a => shift γ a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simp [pr_opp, pr_shift_neg hγ ha]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have h' : pr a γ = -1 := by
        have := pr_opp a γ
        omega
      exact pr_shift_self hγ h'
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact shift_shift_neg hγ ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have h' : pr a γ = -1 := by
        have := pr_opp a γ
        omega
      exact shift_neg_shift hγ h'
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have h1' : opp (shift (-γ) a) = shift γ (opp a) := by
        have h2' := opp_shift (isRoot_neg hγ) (show pr a (-γ) = -1 by rw [pr_neg, ha])
        rwa [neg_neg] at h2'
      have h3' : pr (opp a) γ = -1 := by rw [pr_opp, ha]
      show x (shift (-γ) a) * y (opp a) = x (shift (-γ) a) * y (shift (-γ) (opp (shift (-γ) a)))
      rw [h1', shift_neg_shift hγ h3']
  have sq : ∑ a : Fin e7Data.d, (if pr a γ = 1 then x (shift (-γ) a) else 0)
      * (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases h : pr a γ = 1
    · have h' : pr (opp a) γ = -1 := by rw [pr_opp, h]
      simp [h, h']
    · simp [h]
  have pw : ∀ a : Fin e7Data.d,
      (x a + c * (if pr a γ = 1 then x (shift (-γ) a) else 0)) *
        (y (opp a) + c * (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0))
      = x a * y (opp a) + (c * ((if pr a γ = 1 then x (shift (-γ) a) else 0) * y (opp a))
          + c * (x a * (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0))
          + c * c * ((if pr a γ = 1 then x (shift (-γ) a) else 0) *
            (if pr (opp a) γ = 1 then y (shift (-γ) (opp a)) else 0))) :=
    fun a => by ring
  unfold beta
  simp only [hx, hy]
  rw [Finset.sum_congr rfl (fun a _ => pw a), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, key, sq,
    mul_zero, add_zero, CharTwo.add_self_eq_zero, add_zero]

theorem E_isometry [CharP K 2] {g : (Module.End K (V K))ˣ} (hg : g ∈ EGrp K) (x y : V K) :
    beta ((g : Module.End K (V K)) x) ((g : Module.End K (V K)) y) = beta x y := by
  have hg' : g ∈ Subgroup.closure {h : (Module.End K (V K))ˣ |
      ∃ γ, IsRoot .E7 γ ∧ ∃ c : K, h = e7Data_valid.xu K γ c} := hg
  clear hg
  revert x y
  induction hg' using Subgroup.closure_induction with
  | mem h hh =>
    obtain ⟨γ, hγ, c, rfl⟩ := hh
    intro x y
    exact beta_xu hγ c x y
  | one =>
    intro x y
    simp only [Units.val_one, Module.End.one_apply]
  | mul h₁ h₂ _ _ ih₁ ih₂ =>
    intro x y
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [ih₁, ih₂]
  | inv h _ ih =>
    intro x y
    have hinv : ∀ z : V K,
        (h : Module.End K (V K)) (((h⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) z) = z := by
      intro z
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have h1 := ih (((h⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) x)
      (((h⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) y)
    rw [hinv, hinv] at h1
    exact h1.symm

theorem beta_single (a b : Fin e7Data.d) :
    beta (Finsupp.single a (1 : K)) (Finsupp.single b 1) = if opp a = b then 1 else 0 := by
  unfold beta
  rw [Finset.sum_eq_single a]
  · by_cases h : opp a = b
    · subst h
      simp
    · have h' : b ≠ opp a := fun e => h e.symm
      simp [Finsupp.single_apply, h, h']
  · intro c _ hc
    simp [Finsupp.single_apply, hc, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem beta_nondeg_V0 {v : V K} (hv : ∀ b, b ∉ idx0 → v b = 0)
    (h : ∀ w : V K, (∀ b, b ∉ idx0 → w b = 0) → beta v w = 0) : v = 0 := by
  ext b
  rw [Finsupp.zero_apply]
  by_cases hb : b ∈ idx0
  · have hob : opp b ∈ idx0 := by
      rw [mem_idx0, pr_opp, mem_idx0.1 hb, neg_zero]
    have hw : ∀ c, c ∉ idx0 → (Finsupp.single (opp b) (1 : K)) c = 0 := by
      intro c hc
      have hne : opp b ≠ c := by
        rintro rfl
        exact hc hob
      rw [Finsupp.single_apply, if_neg hne]
    have hvw := h (Finsupp.single (opp b) (1 : K)) hw
    unfold beta at hvw
    rw [Finset.sum_eq_single b] at hvw
    · simpa using hvw
    · intro a _ ha
      have hne : opp b ≠ opp a := by
        intro e
        apply ha
        have h2 := congrArg opp e
        rw [opp_opp, opp_opp] at h2
        exact h2.symm
      rw [Finsupp.single_apply, if_neg hne, mul_zero]
    · intro hb'
      exact absurd (Finset.mem_univ b) hb'
  · exact hv b hb

theorem beta_V0_orth {x y : V K} (hx : ∀ b, b ∉ idx0 → x b = 0) (hy : ∀ b, b ∈ idx0 → y b = 0) :
    beta x y = 0 := by
  unfold beta
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ idx0
  · have hoa : opp a ∈ idx0 := by
      rw [mem_idx0, pr_opp, mem_idx0.1 ha, neg_zero]
    rw [hy (opp a) hoa, mul_zero]
  · rw [hx a ha, zero_mul]

end CFSG.RankThree.GF2n.Smith81.E7Model
