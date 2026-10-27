module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H10

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

theorem card_sup_mul_card_inf_of_normal' {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf' {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem transpose_transpose_SL (A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A) = A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_transpose]

theorem transpose_mul_SL (A B : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose (A * B) =
      Matrix.SpecialLinearGroup.transpose B * Matrix.SpecialLinearGroup.transpose A := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_mul]

theorem transpose_inv_SL (A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose A⁻¹ = (Matrix.SpecialLinearGroup.transpose A)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← transpose_mul_SL, mul_inv_cancel]
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.one_apply, eq_comm]

@[expose] def tInv (n : ℕ) : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) where
  toFun A := Matrix.SpecialLinearGroup.transpose A⁻¹
  invFun A := Matrix.SpecialLinearGroup.transpose A⁻¹
  left_inv A := by
    show Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A⁻¹)⁻¹ = A
    rw [← transpose_inv_SL, inv_inv, transpose_transpose_SL]
  right_inv A := by
    show Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A⁻¹)⁻¹ = A
    rw [← transpose_inv_SL, inv_inv, transpose_transpose_SL]
  map_mul' A B := by
    show Matrix.SpecialLinearGroup.transpose (A * B)⁻¹ =
      Matrix.SpecialLinearGroup.transpose A⁻¹ * Matrix.SpecialLinearGroup.transpose B⁻¹
    rw [_root_.mul_inv_rev, transpose_mul_SL]

theorem tInv_apply (A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    tInv n A = Matrix.SpecialLinearGroup.transpose A⁻¹ := rfl

theorem tInv_mem_stabV {u : Fin n → ZMod 2} {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : u ᵥ* (g : Matrix (Fin n) (Fin n) (ZMod 2)) = u) : tInv n g ∈ stabV u := by
  rw [mem_stabV, tInv_apply, Matrix.SpecialLinearGroup.coe_transpose, mulVec_transpose]
  calc u ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
      = (u ᵥ* (g : Matrix (Fin n) (Fin n) (ZMod 2))) ᵥ*
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) := by
        rw [hg]
    _ = u := by
        rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, vecMul_one]

theorem neg_vec (x : Fin n → ZMod 2) : -x = x := by
  funext i
  show -(x i) = x i
  generalize x i = c
  revert c
  decide

@[expose] def perpSet (u : Fin 4 → ZMod 2) : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {x | u ⬝ᵥ x = 0}
  add_mem' := fun {a b} ha hb => by
    show u ⬝ᵥ (a + b) = 0
    rw [dotProduct_add, show u ⬝ᵥ a = 0 from ha, show u ⬝ᵥ b = 0 from hb, add_zero]
  zero_mem' := dotProduct_zero u
  neg_mem' := fun {a} ha => by
    show u ⬝ᵥ (-a) = 0
    rw [neg_vec]
    exact ha

theorem mem_perpSet {u x : Fin 4 → ZMod 2} : x ∈ perpSet u ↔ u ⬝ᵥ x = 0 := Iff.rfl

theorem card_perpSet {u : Fin 4 → ZMod 2} (hu : u ≠ 0) : Nat.card (perpSet u) = 8 := by
  have h1 : Nat.card (perpSet u) = Nat.card {x : Fin 4 → ZMod 2 // x ⬝ᵥ u = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [mem_perpSet, dotProduct_comm])
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, card_perp_four u hu]

theorem vecMul_eq_of_comm_trv {k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    {u w : Fin n → ZMod 2} (hw : w ≠ 0) (h : u ⬝ᵥ w = 0)
    (hkw : (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w) (hc : k * trv u w h = trv u w h * k) :
    u ᵥ* (k : Matrix (Fin n) (Fin n) (ZMod 2)) = u := by
  have hconj := conj_trv k u w h hkw
  have hkr : k * trv u w h * k⁻¹ = trv u w h := by rw [hc, mul_inv_cancel_right]
  rw [hkr] at hconj
  have hu' := trv_injective hw _ _ hconj
  have hkk : ((k⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) * (k : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc u ᵥ* (k : Matrix (Fin n) (Fin n) (ZMod 2))
      = (u ᵥ* ((k⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))) ᵥ* (k : Matrix (Fin n) (Fin n) (ZMod 2)) := by
        rw [← hu']
    _ = u := by rw [vecMul_vecMul, hkk, vecMul_one]

theorem eq_one_of_comm_elV {k : SL4} (hk : orderOf k = 7) {v : Fin 4 → ZMod 2} (hv : v ≠ 0)
    (hkv : k • v = v) {r : SL4} (hr : r ∈ elV v) (hc : k * r = r * k) : r = 1 := by
  obtain ⟨u, h, rfl⟩ := hr
  by_cases hu : u = 0
  · subst hu
    exact trv_zero v
  exfalso
  have hu'' := vecMul_eq_of_comm_trv hv h hkv hc
  refine false_of_card_eight hk (card_perpSet hu) (fun x => ?_) hv h hkv
  rw [mem_perpSet, mem_perpSet, smul_eq_mulVec', dotProduct_mulVec, hu'']

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
