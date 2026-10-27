module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowNF
public import CFSG.LocalAnalysis.StandardType.FS81.E7RowDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

@[expose] def Gen.mat : Gen → Matrix (Fin 8) (Fin 8) (ZMod 3)
  | .sw i j => spMat (Equiv.swap i j) (fun _ => 1)
  | .ng i j => spMat 1 (sgnOn {i, j})
  | .t1 => spMat 1 (sgnOn {1})

theorem Gen.mat_mulVec (g : Gen) (v : Coords 8) : g.mat *ᵥ v = g.act v := by
  funext k
  cases g with
  | sw i j => simp [Gen.mat, spMat_mulVec, Gen.act, Equiv.symm_swap]
  | ng i j =>
    simp only [Gen.mat, spMat_mulVec, Equiv.Perm.one_symm, Equiv.Perm.one_apply, sgnOn,
      Finset.mem_insert, Finset.mem_singleton, Gen.act]
    split_ifs <;> ring
  | t1 =>
    simp only [Gen.mat, spMat_mulVec, Equiv.Perm.one_symm, Equiv.Perm.one_apply, sgnOn,
      Finset.mem_singleton, Gen.act]
    split_ifs <;> ring

theorem Gen.mat_mem {g : Gen} (hg : g.Valid) : g.mat ∈ hSeven := by
  cases g with
  | sw i j =>
    obtain ⟨hi, hj⟩ := hg
    have h0i : (0 : Fin 8) ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by decide)
    have h0j : (0 : Fin 8) ≠ j := fun h => by rw [← h] at hj; exact absurd hj (by decide)
    have h1i : (1 : Fin 8) ≠ i := fun h => by rw [← h] at hi; exact absurd hi (by decide)
    have h1j : (1 : Fin 8) ≠ j := fun h => by rw [← h] at hj; exact absurd hj (by decide)
    exact hSix_subset_hSeven (perm_mem_hSix (Equiv.swap_apply_of_ne_of_ne h0i h0j)
      (Equiv.swap_apply_of_ne_of_ne h1i h1j))
  | ng i j =>
    obtain ⟨hi, hj, hij⟩ := hg
    have h0 : (0 : Fin 8) ∉ ({i, j} : Finset (Fin 8)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => by rw [← h] at hi; exact absurd hi (by decide),
        fun h => by rw [← h] at hj; exact absurd hj (by decide)⟩
    have h1 : (1 : Fin 8) ∉ ({i, j} : Finset (Fin 8)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => by rw [← h] at hi; exact absurd hi (by decide),
        fun h => by rw [← h] at hj; exact absurd hj (by decide)⟩
    exact hSix_subset_hSeven (sgnOn_mem_hSix h0 h1 (by rw [Finset.card_pair hij]; decide))
  | t1 => exact t1_mem_hSeven

theorem hSeven_mulVec_e0 {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven) :
    A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨σ, s, -, ⟨h0, hs0, -, -⟩, rfl⟩ := hA
  funext i
  rw [spMat_mulVec]
  by_cases hi : i = 0
  · subst hi
    have : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, h0]
    simp [this, hs0]
  · have : σ.symm i ≠ 0 := fun e => hi (by rw [← h0, ← e, Equiv.apply_symm_apply])
    simp [this, hi]

theorem hSeven_mulVec_e1 {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven) :
    A *ᵥ Pi.single 1 1 = A 1 1 • Pi.single 1 1 := by
  obtain ⟨σ, s, -, ⟨-, -, h1, -⟩, rfl⟩ := hA
  funext i
  rw [spMat_mulVec, Pi.smul_apply, smul_eq_mul, spMat_apply]
  by_cases hi : i = 1
  · subst hi
    have : σ.symm 1 = 1 := by rw [Equiv.symm_apply_eq, h1]
    simp [this, h1]
  · have : σ.symm i ≠ 1 := fun e => hi (by rw [← h1, ← e, Equiv.apply_symm_apply])
    simp [this, hi]

theorem hSeven_mulVec_zero {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven) {v : Coords 8}
    (hv : v 0 = 0) : (A *ᵥ v) 0 = 0 := by
  obtain ⟨σ, s, -, ⟨h0, -, -, -⟩, rfl⟩ := hA
  rw [spMat_mulVec]
  have : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, h0]
  simp [this, hv]

theorem hSeven_commute_t1 {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven) :
    A * Gen.t1.mat = Gen.t1.mat * A := by
  obtain ⟨σ, s, -, ⟨-, -, h1, -⟩, rfl⟩ := hA
  simp only [Gen.mat, spMat_mul, mul_one, one_mul, Equiv.Perm.one_apply]
  congr 1
  funext j
  have : σ j = 1 ↔ j = 1 := by
    constructor
    · intro h
      exact σ.injective (h.trans h1.symm)
    · rintro rfl
      exact h1
  simp only [sgnOn, Finset.mem_singleton, this]
  ring

theorem zmod3_neg_eq (a : ZMod 3) : -a = a + a := by
  revert a
  decide

theorem t1_act_eq (v : Coords 8) : Gen.t1.act v = v + v 1 • Pi.single 1 1 := by
  funext k
  by_cases hk : k = 1
  · subst hk
    simp only [Gen.act, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
    exact zmod3_neg_eq _
  · simp [Gen.act, hk]

theorem eq_smul_e1_of_t1 {w : Coords 8} (hw : Gen.t1.act w = -w) : w = w 1 • Pi.single 1 1 := by
  funext k
  by_cases hk : k = 1
  · subst hk
    simp
  · have h := congrFun hw k
    simp only [Gen.act, if_neg hk, Pi.neg_apply] at h
    have : w k = 0 := by
      have h' : -w k = w k := h.symm
      exact eq_zero_of_neg_eq_self h'
    simp [hk, this]

structure CoreHyp (X : Subgroup (GL (Fin 8) (ZMod 3))) : Prop where
  hH : ∀ A ∈ hSeven, ∃ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A
  hstab : ∀ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
    (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven
  hcard : Nat.card ↥(X ⊓ fixE0 7) = 2903040
  hA : ∀ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
    ∀ v : Coords 8, v 0 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

theorem CoreHyp.exists_fix (h : CoreHyp X) {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ hSeven) :
    ∃ x ∈ X ⊓ fixE0 7, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A := by
  obtain ⟨x, hx, rfl⟩ := h.hH A hA
  exact ⟨x, ⟨hx, mem_fixE0.mpr (hSeven_mulVec_e0 hA)⟩, rfl⟩

@[expose] def orb1 (X : Subgroup (GL (Fin 8) (ZMod 3))) : Set (Coords 8) :=
  {v | ∃ x ∈ X ⊓ fixE0 7, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = v}

theorem e1_mem_orb1 : (Pi.single 1 1 : Coords 8) ∈ orb1 X :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, Matrix.one_mulVec]⟩

theorem orb1_zero (h : CoreHyp X) {v : Coords 8} (hv : v ∈ orb1 X) : v 0 = 0 := by
  obtain ⟨x, ⟨hxX, hxF⟩, rfl⟩ := hv
  exact h.hA x hxX (mem_fixE0.mp hxF) _ (by simp)

theorem orb1_gen (h : CoreHyp X) {g : Gen} (hg : g.Valid) {v : Coords 8} (hv : v ∈ orb1 X) :
    g.act v ∈ orb1 X := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, hyA⟩ := h.exists_fix (Gen.mat_mem hg)
  refine ⟨y * x, Subgroup.mul_mem _ hy hx, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hyA, Gen.mat_mulVec]

theorem supp_of_spMat_rankOne {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} {r : Coords 8}
    (hr : r ≠ 0) (hneg : spMat σ s *ᵥ r = -r)
    (hrank : ∀ w : Coords 8, ∃ c : ZMod 3, spMat σ s *ᵥ w - w = c • r) :
    ∃ j k : Fin 8, ∀ i, i ≠ j → i ≠ k → r i = 0 := by
  by_cases hall : ∀ j : Fin 8, spMat σ s *ᵥ Pi.single j 1 = Pi.single j 1
  · exfalso
    have hA : spMat σ s = 1 := by
      ext i j
      have := congrFun (hall j) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
      rw [this, Matrix.one_apply, Pi.single_apply]
    rw [hA, Matrix.one_mulVec] at hneg
    exact hr (eq_zero_of_neg_eq_self hneg.symm)
  · simp only [not_forall] at hall
    obtain ⟨j, hj⟩ := hall
    obtain ⟨c, hc⟩ := hrank (Pi.single j 1)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, sub_eq_zero] at hc
      exact hj hc
    refine ⟨j, σ j, fun i hij hik => ?_⟩
    have hi := congrFun hc i
    rw [spMat_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    have h1 : σ.symm i ≠ j := fun e => hik (by rw [← e, Equiv.apply_symm_apply])
    simp only [Pi.single_apply, h1, hij, if_false, mul_zero, sub_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hc0

local notation:max "↑ₘ" g:max => ((g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3))

theorem mulVec_inv_mulVec (x : GL (Fin 8) (ZMod 3)) (v : Coords 8) : ↑ₘ(x⁻¹) *ᵥ (↑ₘ(x) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (x : GL (Fin 8) (ZMod 3)) (v : Coords 8) : ↑ₘ(x) *ᵥ (↑ₘ(x⁻¹) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_gmul (x y : GL (Fin 8) (ZMod 3)) (v : Coords 8) : ↑ₘ(x * y) *ᵥ v = ↑ₘ(x) *ᵥ (↑ₘ(y) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem t1_act_e1 : Gen.t1.act (Pi.single 1 1 : Coords 8) = -Pi.single 1 1 := by
  funext k
  by_cases hk : k = 1
  · subst hk
    simp [Gen.act]
  · simp [Gen.act, hk]

theorem supp_two_of_mem_orb1 (h : CoreHyp X) {v : Coords 8} (hv : v ∈ orb1 X) (hv1 : v 1 = 0) :
    ∃ j k : Fin 8, ∀ i, i ≠ j → i ≠ k → v i = 0 := by
  obtain ⟨x, hx, hxv⟩ := hv
  obtain ⟨y, hy, hyt⟩ := h.exists_fix (Gen.mat_mem (g := .t1) trivial)
  have hxinv : ↑ₘ(x⁻¹) *ᵥ v = Pi.single 1 1 := by
    rw [← hxv, mulVec_inv_mulVec]
  have ht1v : ↑ₘ(y) *ᵥ v = v := by
    rw [hyt, Gen.mat_mulVec, t1_act_eq, hv1, zero_smul, add_zero]
  have hc : x⁻¹ * y * x ∈ X ⊓ fixE0 7 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) hx
  have hce1 : ↑ₘ(x⁻¹ * y * x) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
    rw [mulVec_gmul, mulVec_gmul, hxv, ht1v, hxinv]
  have hcH : ↑ₘ(x⁻¹ * y * x) ∈ hSeven :=
    h.hstab _ hc.1 (mem_fixE0.mp hc.2) ⟨1, by rw [hce1, one_smul]⟩
  have hcomm : x⁻¹ * y * x * y = y * (x⁻¹ * y * x) := by
    refine Units.ext ?_
    rw [Units.val_mul (x⁻¹ * y * x) y, Units.val_mul y (x⁻¹ * y * x), hyt]
    exact hSeven_commute_t1 hcH
  have hρX : x * y * x⁻¹ ∈ X ⊓ fixE0 7 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)
  have hρy : y * (x * y * x⁻¹) = x * y * x⁻¹ * y := by
    calc y * (x * y * x⁻¹) = x * ((x⁻¹ * y * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * y * x)) * x⁻¹ := by rw [hcomm]
      _ = x * y * x⁻¹ * y := by group
  have hρe1 : ↑ₘ(x * y * x⁻¹) *ᵥ Pi.single 1 1 =
      (↑ₘ(x * y * x⁻¹) *ᵥ Pi.single 1 1) 1 • Pi.single 1 1 := by
    apply eq_smul_e1_of_t1
    have e2 := congrArg (fun g : GL (Fin 8) (ZMod 3) => ↑ₘ(g) *ᵥ Pi.single 1 1) hρy
    simp only [mulVec_gmul y, mulVec_gmul (x * y * x⁻¹) y] at e2
    rw [hyt, Gen.mat_mulVec, Gen.mat_mulVec, t1_act_e1, Matrix.mulVec_neg] at e2
    exact e2
  have hρH : ↑ₘ(x * y * x⁻¹) ∈ hSeven := h.hstab _ hρX.1 (mem_fixE0.mp hρX.2) ⟨_, hρe1⟩
  obtain ⟨σ, s, -, -, hρs⟩ := hρH
  have hv0 : v ≠ 0 := by
    intro e
    have h1 := congrFun hxinv 1
    rw [e, Matrix.mulVec_zero] at h1
    simp at h1
  apply supp_of_spMat_rankOne hv0
  · rw [← hρs, mulVec_gmul, mulVec_gmul, hxinv, hyt, Gen.mat_mulVec, t1_act_e1,
      Matrix.mulVec_neg, hxv]
  · intro w
    refine ⟨(↑ₘ(x⁻¹) *ᵥ w) 1, ?_⟩
    rw [← hρs, mulVec_gmul, mulVec_gmul, hyt, Gen.mat_mulVec, t1_act_eq, Matrix.mulVec_add,
      Matrix.mulVec_smul, mulVec_mulVec_inv, hxv]
    abel

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
