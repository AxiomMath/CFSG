module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace A7Mod

abbrev V7 : Type := ↥(permCore 7)

theorem permAct_mem (σ : Equiv.Perm (Fin 7)) {x : Fin 7 → ZMod 2} (hx : x ∈ permCore 7) :
    permAct σ x ∈ permCore 7 := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

theorem permAct_mul (σ τ : Equiv.Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    permAct (σ * τ) x = permAct σ (permAct τ x) := by
  funext i
  simp [permAct, mul_inv_rev, Equiv.Perm.mul_apply]

theorem permAct_one (x : Fin 7 → ZMod 2) : permAct 1 x = x := by
  funext i
  simp [permAct]

@[expose] def pActLin (σ : Equiv.Perm (Fin 7)) : V7 ≃ₗ[ZMod 2] V7 where
  toFun x := ⟨permAct σ x, permAct_mem σ x.2⟩
  invFun x := ⟨permAct σ⁻¹ x, permAct_mem σ⁻¹ x.2⟩
  map_add' x y := Subtype.ext (funext fun i => rfl)
  map_smul' c x := Subtype.ext (funext fun i => rfl)
  left_inv x := Subtype.ext (by
    show permAct σ⁻¹ (permAct σ x) = x
    rw [← permAct_mul, inv_mul_cancel, permAct_one])
  right_inv x := Subtype.ext (by
    show permAct σ (permAct σ⁻¹ x) = x
    rw [← permAct_mul, mul_inv_cancel, permAct_one])

@[expose] def pAct : Equiv.Perm (Fin 7) →* (V7 ≃ₗ[ZMod 2] V7) where
  toFun := pActLin
  map_one' := LinearEquiv.ext fun x => Subtype.ext (permAct_one x.1)
  map_mul' σ τ := LinearEquiv.ext fun x => Subtype.ext (permAct_mul σ τ x)

theorem pAct_apply (σ : Equiv.Perm (Fin 7)) (x : V7) (i : Fin 7) :
    (pAct σ x : Fin 7 → ZMod 2) i = (x : Fin 7 → ZMod 2) (σ⁻¹ i) := rfl

@[expose] def f (p : Fin 7) : V7 :=
  ⟨fun i => if i = p then 0 else 1, by
    show ∑ i, (if i = p then (0 : ZMod 2) else 1) = 0
    revert p
    decide⟩

theorem f_apply (p i : Fin 7) : (f p : Fin 7 → ZMod 2) i = if i = p then 0 else 1 := rfl

theorem pAct_f (σ : Equiv.Perm (Fin 7)) (p : Fin 7) : pAct σ (f p) = f (σ p) := by
  apply Subtype.ext
  funext i
  rw [pAct_apply, f_apply, f_apply]
  have : σ⁻¹ i = p ↔ i = σ p := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  by_cases h : i = σ p
  · rw [ite_eq_left (this.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (this.1 h')), ite_eq_right h]

theorem f_injective : Function.Injective f := by
  intro p q h
  have h1 := congrFun (congrArg Subtype.val h) p
  rw [f_apply, f_apply, ite_eq_left rfl] at h1
  by_contra hpq
  rw [ite_eq_right hpq] at h1
  exact absurd h1 (by decide)

theorem eq_sum_smul_f (x : V7) : x = ∑ i, (x : Fin 7 → ZMod 2) i • f i := by
  apply Subtype.ext
  funext j
  have hx : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := x.2
  have key : ∀ i, (x : Fin 7 → ZMod 2) i * (if j = i then 0 else 1) =
      (x : Fin 7 → ZMod 2) i + (if j = i then (x : Fin 7 → ZMod 2) i else 0) := by
    intro i
    generalize (x : Fin 7 → ZMod 2) i = a
    split_ifs
    · revert a
      decide
    · rw [mul_one, add_zero]
  have h2 : (↑(∑ i, (x : Fin 7 → ZMod 2) i • f i) : Fin 7 → ZMod 2) j =
      ∑ i, (x : Fin 7 → ZMod 2) i * (if j = i then 0 else 1) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, f_apply, smul_eq_mul]
  rw [h2, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq,
    ite_eq_left (Finset.mem_univ j), hx, zero_add]

theorem pAct_injective : Function.Injective pAct := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  ext p
  have h := pAct_f σ p
  rw [hσ] at h
  change f p = f (σ p) at h
  rw [← f_injective h]
  rfl

@[expose] def B0 : LinearMap.BilinForm (ZMod 2) V7 :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, (x : Fin 7 → ZMod 2) i * (y : Fin 7 → ZMod 2) i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_assoc, Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_left_comm, Finset.mul_sum])

theorem B0_apply (x y : V7) :
    B0 x y = ∑ i, (x : Fin 7 → ZMod 2) i * (y : Fin 7 → ZMod 2) i := rfl

theorem B0_pAct (σ : Equiv.Perm (Fin 7)) (x y : V7) : B0 (pAct σ x) (pAct σ y) = B0 x y := by
  rw [B0_apply, B0_apply]
  simp only [pAct_apply]
  exact Equiv.sum_comp σ⁻¹ (fun i => (x : Fin 7 → ZMod 2) i * (y : Fin 7 → ZMod 2) i)

theorem B0_f (i j : Fin 7) : B0 (f i) (f j) = if i = j then 0 else 1 := by
  rw [B0_apply]
  simp only [f_apply]
  revert i j
  decide

theorem exists_alt_two (i j : Fin 7) (hij : i ≠ j) :
    ∃ σ ∈ alternatingGroup (Fin 7), σ 0 = i ∧ σ 1 = j := by
  have h5 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) 5 := by
    have := alternatingGroup.isMultiplyPretransitive (Fin 7)
    simpa using this
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by simp)
  obtain ⟨g, hg0, hg1⟩ :=
    MulAction.is_two_pretransitive_iff.1 h2 (by decide : (0 : Fin 7) ≠ 1) hij
  exact ⟨g, g.2, hg0, hg1⟩

theorem bilin_ext_f {B B' : LinearMap.BilinForm (ZMod 2) V7}
    (h : ∀ i j, B (f i) (f j) = B' (f i) (f j)) : B = B' := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [eq_sum_smul_f x, eq_sum_smul_f y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h]

theorem eq_B0 (B : LinearMap.BilinForm (ZMod 2) V7) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x y, B (pAct σ x) (pAct σ y) = B x y) :
    B = B0 := by
  have hpair : ∀ i j, i ≠ j → B (f i) (f j) = B (f 0) (f 1) := by
    intro i j hij
    obtain ⟨σ, hσ, h0, h1⟩ := exists_alt_two i j hij
    rw [← h0, ← h1, ← pAct_f, ← pAct_f, hinv σ hσ]
  have hc : B (f 0) (f 1) = 1 := by
    by_contra hc0
    have hc0' : B (f 0) (f 1) = 0 := (by decide : ∀ c : ZMod 2, c ≠ 1 → c = 0) _ hc0
    have hB0 : B = 0 := bilin_ext_f fun i j => by
      by_cases hij : i = j
      · rw [hij, halt]
        rfl
      · rw [hpair i j hij, hc0']
        rfl
    have h0 := hnd (f 0) fun y => by
      rw [hB0]
      rfl
    have h1 := congrFun (congrArg Subtype.val h0) 1
    rw [f_apply, ite_eq_right (by decide)] at h1
    simp at h1
  refine bilin_ext_f fun i j => ?_
  rw [B0_f]
  by_cases hij : i = j
  · rw [ite_eq_left hij, hij, halt]
  · rw [ite_eq_right hij, hpair i j hij, hc]

end A7Mod

end CFSG.Quasithin.H13
