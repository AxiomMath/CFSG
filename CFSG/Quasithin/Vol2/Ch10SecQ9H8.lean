module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H7
public import CFSG.Quasithin.Vol2.Ch10SecQ9H6

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

theorem smul_eq_mulVec' (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    g • v = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v := rfl

theorem ext_mulVec {g h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hgh : ∀ x, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) : g = h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (hgh (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem mulVec_inv_of_mulVec {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    {x y : Fin n → ZMod 2} (h : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = y) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y =
      x := by
  rw [← h, mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem mulVec_ne_zero (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) {x : Fin n → ZMod 2}
    (hx : x ≠ 0) : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  rw [← mulVec_inv_of_mulVec h, mulVec_zero]

abbrev stabV (v : Fin n → ZMod 2) : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  MulAction.stabilizer _ v

theorem mem_stabV {v : Fin n → ZMod 2} {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} :
    g ∈ stabV v ↔ (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v :=
  MulAction.mem_stabilizer_iff

theorem card_ne_zero_vec_four :
    Nat.card {w : Fin 4 → ZMod 2 // w ≠ 0} = 15 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_stabV_four {v : Fin 4 → ZMod 2} (hv : v ≠ 0) : Nat.card (stabV v) = 1344 := by
  have ho : MulAction.orbit (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) v = {w | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      exact mulVec_ne_zero g hv
    · intro hw
      obtain ⟨g, hg⟩ := exists_mulVec_eq hv hw
      exact ⟨g, hg⟩
  have hi : (stabV v).index = 15 := by
    rw [MulAction.index_stabilizer, ho]
    exact card_ne_zero_vec_four
  have h := (stabV v).card_mul_index
  rw [hi, card_SL_four_two] at h
  omega

theorem trv_mul_trv (u u' w : Fin n → ZMod 2) (h : u ⬝ᵥ w = 0) (h' : u' ⬝ᵥ w = 0) :
    trv u w h * trv u' w h' = trv (u + u') w (by rw [add_dotProduct, h, h', add_zero]) := by
  apply ext_mulVec
  intro x
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, trv_mulVec, trv_mulVec, trv_mulVec,
    dotProduct_add, dotProduct_smul, h, smul_eq_mul, mul_zero, add_zero, add_dotProduct,
    add_smul, add_assoc, add_comm ((u ⬝ᵥ x) • w)]

theorem trv_zero (w : Fin n → ZMod 2) : trv 0 w (zero_dotProduct w) = 1 := by
  apply ext_mulVec
  intro x
  rw [trv_mulVec, zero_dotProduct, zero_smul, add_zero, Matrix.SpecialLinearGroup.coe_one,
    one_mulVec]

theorem trv_mem_stabV (u w : Fin n → ZMod 2) (h : u ⬝ᵥ w = 0) : trv u w h ∈ stabV w := by
  rw [mem_stabV, trv_mulVec, h, zero_smul, add_zero]

theorem conj_trv (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (u w : Fin n → ZMod 2)
    (h : u ⬝ᵥ w = 0) {w' : Fin n → ZMod 2} (hw : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w') :
    g * trv u w h * g⁻¹ = trv (u ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))) w'
      (by rw [← dotProduct_mulVec, mulVec_inv_of_mulVec hw, h]) := by
  apply ext_mulVec
  intro x
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, trv_mulVec, trv_mulVec, mulVec_add, mulVec_smul, hw, dotProduct_mulVec,
    mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

@[expose] def elV (w : Fin n → ZMod 2) : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) where
  carrier := {g | ∃ u, ∃ h : u ⬝ᵥ w = 0, g = trv u w h}
  one_mem' := ⟨0, zero_dotProduct w, (trv_zero w).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u, h, rfl⟩ ⟨u', h', rfl⟩
    exact ⟨_, _, trv_mul_trv u u' w h h'⟩
  inv_mem' := by
    rintro _ ⟨u, h, rfl⟩
    refine ⟨u, h, ?_⟩
    rw [inv_eq_iff_mul_eq_one, trv_mul_trv]
    convert trv_zero w
    exact add_self_vec u

theorem elV_le_stabV (w : Fin n → ZMod 2) : elV w ≤ stabV w := by
  rintro _ ⟨u, h, rfl⟩
  exact trv_mem_stabV u w h

theorem stabV_le_normalizer (w : Fin n → ZMod 2) :
    stabV w ≤ Subgroup.normalizer (elV w : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨u, h, rfl⟩
    exact ⟨_, _, conj_trv g u w h (mem_stabV.mp hg)⟩
  · rintro ⟨u, h, hx⟩
    have hg' : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w := mulVec_inv_of_mulVec (mem_stabV.mp hg)
    have hmem : g⁻¹ * trv u w h * g⁻¹⁻¹ ∈ elV w := ⟨_, _, conj_trv g⁻¹ u w h hg'⟩
    rw [inv_inv] at hmem
    have hx' : x = g⁻¹ * trv u w h * g := by
      rw [← hx]
      group
    rw [hx']
    exact hmem

theorem trv_injective {w : Fin n → ZMod 2} (hw : w ≠ 0) {u u' : Fin n → ZMod 2}
    (h : u ⬝ᵥ w = 0) (h' : u' ⬝ᵥ w = 0) (he : trv u w h = trv u' w h') : u = u' := by
  have hx : ∀ x, u ⬝ᵥ x = u' ⬝ᵥ x := fun x => by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) =>
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) he
    simp only [trv_mulVec, add_right_inj] at this
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      exact hw (funext fun i => by
        by_contra hi
        exact hc ⟨i, hi⟩)
    have := congrFun this i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  funext j
  have := hx (Pi.single j 1)
  rwa [dotProduct_single, dotProduct_single, mul_one, mul_one] at this

theorem card_perp_four : ∀ w : Fin 4 → ZMod 2, w ≠ 0 →
    (Finset.univ.filter fun u : Fin 4 → ZMod 2 => u ⬝ᵥ w = 0).card = 8 := by
  decide

theorem card_elV_four {w : Fin 4 → ZMod 2} (hw : w ≠ 0) : Nat.card (elV w) = 8 := by
  have hbij : Function.Bijective (fun u : {u : Fin 4 → ZMod 2 // u ⬝ᵥ w = 0} =>
      (⟨trv u.1 w u.2, u.1, u.2, rfl⟩ : ↥(elV w))) := by
    refine ⟨fun u u' h => Subtype.ext (trv_injective hw u.2 u'.2 (congrArg Subtype.val h)),
      fun g => ?_⟩
    obtain ⟨u, h, hg⟩ := g.2
    exact ⟨⟨u, h⟩, Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card,
    Fintype.card_subtype, card_perp_four w hw]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
