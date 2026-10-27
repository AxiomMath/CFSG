module

public import CFSG.Timmesfeld.ARS.ExclNSFrame

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}

structure InvForm (A : Matrix (Fin r) (Fin r) ℤ) where
  Q : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) →ₗ[ℤ] ℤ
  symm : ∀ x y, Q x y = Q y x
  refl : ∀ k x y, Q (reflection A k x) (reflection A k y) = Q x y
  coroot_iff : ∀ k x, Q x (Pi.single k 1) = 0 ↔ coroot A k x = 0

namespace InvForm

variable (F : InvForm A) (hA : TauCeti.IsFiniteType A)

theorem weylAction (w : (coxeterMatrix hA).Group) (x y : Fin r → ℤ) :
    F.Q (CFSG.LieType.RootSystem.weylAction hA w x)
      (CFSG.LieType.RootSystem.weylAction hA w y) = F.Q x y := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, F.refl, ih]

theorem exists_eq_of_mem_roots {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) :
    ∃ i, F.Q γ γ = F.Q (Pi.single i 1) (Pi.single i 1) := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · exact ⟨i, F.weylAction hA w _ _⟩
  · exact absurd hi (Set.notMem_empty i)

theorem apply_eq_sum (x v : Fin r → ℤ) : F.Q x v = ∑ k, v k * F.Q x (Pi.single k 1) := by
  conv_lhs => rw [← sum_smul_single v]
  simp only [map_sum, map_zsmul, smul_eq_mul]

theorem reflection_ne {w : (coxeterMatrix hA).Group} {i : Fin r} {x : Fin r → ℤ}
    (h : F.Q x (CFSG.LieType.RootSystem.weylAction hA w (Pi.single i 1)) ≠ 0) :
    CFSG.LieType.RootSystem.weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i)
        (CFSG.LieType.RootSystem.weylAction hA w⁻¹ x) ≠
      CFSG.LieType.RootSystem.weylAction hA w⁻¹ x := by
  intro he
  rw [weylAction_simple, reflection_apply_coroot] at he
  have hc : coroot A i (CFSG.LieType.RootSystem.weylAction hA w⁻¹ x) = 0 := by
    have h1 : coroot A i (CFSG.LieType.RootSystem.weylAction hA w⁻¹ x) •
        (Pi.single i 1 : Fin r → ℤ) = 0 := by
      have := congrArg (fun v => CFSG.LieType.RootSystem.weylAction hA w⁻¹ x - v) he
      simpa using this
    have h2 := congrFun h1 i
    simpa using h2
  apply h
  have h3 := (F.coroot_iff i _).2 hc
  rw [← F.weylAction hA w, weylAction_apply_inv_apply] at h3
  exact h3

theorem forall_notMem_openCone {β β' : Fin r → ℤ} (hN : F.Q β' β' = F.Q β β)
    (hN0 : 0 ≤ F.Q β β) (hc : F.Q β' β < 0)
    (hM : ∀ i, F.Q (Pi.single i 1) (Pi.single i 1) ≤ 2 * F.Q β β) :
    ∀ ε ∈ roots hA ∅, ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • β' + b • (-β) := by
  rintro ε hε ⟨a, b, ha, hb, rfl⟩
  obtain ⟨i, hi⟩ := F.exists_eq_of_mem_roots hA hε
  have hle := hM i
  rw [← hi] at hle
  have hv : a • β' + b • (-β) = (a : ℤ) • β' - (b : ℤ) • β := by
    rw [smul_neg, ← sub_eq_add_neg, natCast_zsmul, natCast_zsmul]
  have e : F.Q (a • β' + b • (-β)) (a • β' + b • (-β)) =
      (a : ℤ) ^ 2 * F.Q β' β' + (b : ℤ) ^ 2 * F.Q β β - 2 * a * b * F.Q β' β := by
    rw [hv]
    simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      F.symm β β']
    ring
  rw [e, hN] at hle
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have h1 : F.Q β β ≤ (a : ℤ) ^ 2 * F.Q β β := le_mul_of_one_le_left hN0 (by nlinarith)
  have h2 : F.Q β β ≤ (b : ℤ) ^ 2 * F.Q β β := le_mul_of_one_le_left hN0 (by nlinarith)
  have h3 : -F.Q β' β ≤ -(a * b * F.Q β' β) := by
    have hab : (1 : ℤ) ≤ a * b := by nlinarith
    nlinarith
  nlinarith

theorem mem_closure_of_weylAction_eq {l : Fin r → ℤ} (hdom : ∀ k, 0 ≤ F.Q l (Pi.single k 1))
    (w : (coxeterMatrix hA).Group) (hw : CFSG.LieType.RootSystem.weylAction hA w l = l) :
    w ∈ Subgroup.closure
      ((coxeterMatrix hA).toCoxeterSystem.simple '' {k | F.Q l (Pi.single k 1) = 0}) := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  induction hlen : cs.length w using Nat.strong_induction_on generalizing w with
  | _ N ih =>
    by_cases h1 : w = 1
    · rw [h1]
      exact one_mem _
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one h1
    have hneg := nonpos_of_isRightDescent hA hi
    have hzero : F.Q l (Pi.single i 1) = 0 := by
      refine le_antisymm ?_ (hdom i)
      have e := F.weylAction hA w l (Pi.single i 1)
      rw [hw] at e
      rw [← e, F.apply_eq_sum]
      exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg (hneg k) (hdom k)
    have hfix : CFSG.LieType.RootSystem.weylAction hA (cs.simple i) l = l := by
      rw [weylAction_simple, reflection_apply_coroot, (F.coroot_iff i l).1 hzero, zero_smul,
        sub_zero]
    have hmem := ih (cs.length (w * cs.simple i)) (hlen ▸ hi) (w * cs.simple i)
      (by rw [weylAction_mul_apply, hfix, hw]) rfl
    have e : w = w * cs.simple i * cs.simple i := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    rw [e]
    exact mul_mem hmem (Subgroup.subset_closure ⟨i, hzero, rfl⟩)

end InvForm

@[expose] def symForm (q : Fin r → ℤ) (A : Matrix (Fin r) (Fin r) ℤ) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) →ₗ[ℤ] ℤ :=
  Matrix.toLinearMap₂' ℤ (Matrix.of fun i j => q i * A i j)

theorem symForm_apply (q : Fin r → ℤ) (x y : Fin r → ℤ) :
    symForm q A x y = x ⬝ᵥ Matrix.mulVec (Matrix.of fun i j => q i * A i j) y :=
  Matrix.toLinearMap₂'_apply' _ _ _

section Symmetrizer

variable {q : Fin r → ℤ} (hsymm : ∀ i j, q i * A i j = q j * A j i)
include hsymm

theorem symForm_single (x : Fin r → ℤ) (k : Fin r) :
    symForm q A x (Pi.single k 1) = q k * coroot A k x := by
  rw [symForm_apply, coroot_apply, Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsymm i k]
  ring

theorem symForm_comm (x y : Fin r → ℤ) : symForm q A x y = symForm q A y x := by
  rw [symForm_apply, symForm_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm i j]
  ring

theorem symForm_reflection (hA : TauCeti.IsFiniteType A) (k : Fin r) (x y : Fin r → ℤ) :
    symForm q A (reflection A k x) (reflection A k y) = symForm q A x y := by
  rw [reflection_apply_coroot, reflection_apply_coroot]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    symForm_single hsymm]
  rw [symForm_comm hsymm (Pi.single k 1) y, symForm_single hsymm, coroot_single, hA.apply_self k]
  ring

end Symmetrizer

@[expose] def InvForm.ofSymmetrizer (hA : TauCeti.IsFiniteType A) (q : Fin r → ℤ)
    (hq : ∀ k, 0 < q k) (hsymm : ∀ i j, q i * A i j = q j * A j i) : InvForm A where
  Q := symForm q A
  symm := symForm_comm hsymm
  refl := symForm_reflection hsymm hA
  coroot_iff k x := by
    rw [symForm_single hsymm]
    exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (hq k).ne', fun h => by rw [h, mul_zero]⟩

theorem symForm_single_single (hA : TauCeti.IsFiniteType A) {q : Fin r → ℤ}
    (hsymm : ∀ i j, q i * A i j = q j * A j i) (k : Fin r) :
    symForm q A (Pi.single k 1) (Pi.single k 1) = 2 * q k := by
  rw [symForm_single hsymm, coroot_single, hA.apply_self k]
  ring

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A₁ A₀ : Subgroup G}
  {F : NSLFrameData (LeviBar R A₁ A₀) (quotClass (levi R A₁ A₀) (leviSet R A₁ A₀))}

theorem InvForm.memberRoots_norm (Q : InvForm F.D.cartan) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ memberRoots F) :
    Q.Q β β = Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
  obtain ⟨w, rfl⟩ := hβ
  exact Q.weylAction F.D.isFiniteType w _ _

theorem LowMember.form_nonneg (hS : Sec13 R A₁ A₀) {B : Subgroup G} (hB : LowMember F B)
    (Q : InvForm F.D.cartan)
    (hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
      2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1))
    {β β' : Fin F.D.rank → ℤ} (hβ : β ∈ lowSet F B) (hβ' : β' ∈ lowSet F B) :
    0 ≤ Q.Q β' β := by
  by_contra hneg'
  have hneg : Q.Q β' β < 0 := not_le.1 hneg'
  have hNβ := Q.memberRoots_norm hβ.1
  have hNβ' := Q.memberRoots_norm hβ'.1
  have hne : β ≠ β' := by
    rintro rfl
    have h1 := hM F.i₀
    rw [← hNβ] at h1
    linarith
  obtain ⟨w, hw⟩ := hβ.1
  have hβR := memberRoots_subset F hβ.1
  have hβ'R := memberRoots_subset F hβ'.1
  have hind : LinIndepPair β' (-β) := linIndepPair_neg_right (linIndepPair_of_ht_neg F.hdiv hβ'R
    (LowMember.ht_lt_zero hS hB hβ') hβR (LowMember.ht_lt_zero hS hB hβ) (Ne.symm hne))
  obtain ⟨ε, hε, a, b, ha, hb, he⟩ := LowMember.exists_mem_openCone hS hB hβ hβ' w hw.symm hind
    (Q.reflection_ne F.D.isFiniteType (by rw [← hw]; exact hneg.ne))
  have hε' : ε ∈ roots F.D.isFiniteType ∅ := by
    have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
    rwa [F.hdiv] at this
  have hN0 : 0 ≤ Q.Q β β := by
    have h1 := hM F.i₀
    rw [← hNβ] at h1
    linarith
  refine Q.forall_notMem_openCone F.D.isFiniteType (hNβ'.trans hNβ.symm) hN0 hneg
    (fun i => (hM i).trans_eq (by rw [hNβ])) ε hε' ⟨a, b, ha, hb, he⟩

end CFSG.Timmesfeld.ARS.ExclNS
