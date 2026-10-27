module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.B513N

open Matrix CFSG.Assembly.LowTwoRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {n : ℕ} [NeZero n]

@[expose] def e0 (n : ℕ) [NeZero n] : Fin n → ZMod 2 := Pi.single 0 1

@[expose] def tcMat (φ : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  1 + vecMulVec (e0 n) φ

theorem dot_e0 (φ : Fin n → ZMod 2) : φ ⬝ᵥ e0 n = φ 0 := by
  simp [e0, dotProduct_single]

theorem tcMat_mul {φ ψ : Fin n → ZMod 2} (hφ : φ 0 = 0) :
    tcMat φ * tcMat ψ = tcMat (φ + ψ) := by
  unfold tcMat
  rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, dot_e0, hφ, zero_smul,
    vecMulVec_zero, add_zero, add_assoc, ← vecMulVec_add, add_comm ψ φ]

theorem tcMat_mul_self {φ : Fin n → ZMod 2} (hφ : φ 0 = 0) : tcMat φ * tcMat φ = 1 := by
  rw [tcMat_mul hφ]
  have : φ + φ = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (φ i)
  rw [this]
  simp [tcMat]

theorem det_tcMat {φ : Fin n → ZMod 2} (hφ : φ 0 = 0) : (tcMat φ).det = 1 := by
  unfold tcMat
  rw [vecMulVec_eq (Fin 1), det_one_add_replicateCol_mul_replicateRow, dot_e0, hφ, add_zero]

theorem tcMat_mulVec (φ x : Fin n → ZMod 2) : tcMat φ *ᵥ x = x + (φ ⬝ᵥ x) • e0 n := by
  unfold tcMat
  rw [add_mulVec, one_mulVec]
  congr 1
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j, e0 n i * φ j * x j) = e0 n i * ∑ j, φ j * x j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _]
  ring

theorem tcMat_transpose_mulVec (φ x : Fin n → ZMod 2) :
    (tcMat φ)ᵀ *ᵥ x = x + (x 0) • φ := by
  unfold tcMat
  rw [transpose_add, transpose_one, add_mulVec, one_mulVec, transpose_vecMulVec]
  congr 1
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ j, e0 n j * x j = x 0 := by
    rw [show (∑ j, e0 n j * x j) = e0 n ⬝ᵥ x from rfl, dotProduct_comm, dot_e0]
  rw [show (∑ j, φ i * e0 n j * x j) = φ i * ∑ j, e0 n j * x j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _, this, mul_comm]

@[expose] def tcGL (φ : Fin n → ZMod 2) (hφ : φ 0 = 0) :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  ⟨tcMat φ, tcMat φ, tcMat_mul_self hφ, tcMat_mul_self hφ⟩

theorem tcGL_mem (φ : Fin n → ZMod 2) (hφ : φ 0 = 0) : tcGL φ hφ ∈ StatedSL n (ZMod 2) :=
  Subgroup.subset_closure (det_tcMat hφ)

@[expose] def tcSub (n : ℕ) [NeZero n] : Subgroup ↥(StatedSL n (ZMod 2)) where
  carrier := {g | ∃ φ : Fin n → ZMod 2, φ 0 = 0 ∧
    ((g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = tcMat φ}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    refine ⟨φ + ψ, by simp [hφ, hψ], ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, ha, hb, tcMat_mul hφ]
  one_mem' := ⟨0, rfl, by simp [tcMat]⟩
  inv_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    have hsq : a * a = 1 := Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Units.val_mul, ha, tcMat_mul_self hφ]
      rfl))
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
    exact ⟨φ, hφ, by rw [hinv]; exact ha⟩

theorem tcSub_mul_self {g : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n) : g * g = 1 := by
  obtain ⟨φ, hφ, ha⟩ := hg
  exact Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, ha, tcMat_mul_self hφ]
    rfl))

theorem tcSub_comm {g h : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n) (hh : h ∈ tcSub n) :
    g * h = h * g := by
  obtain ⟨φ, hφ, ha⟩ := hg
  obtain ⟨ψ, hψ, hb⟩ := hh
  exact Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, ha, hb, Subgroup.coe_mul, Units.val_mul, ha, hb,
      tcMat_mul hφ, tcMat_mul hψ, add_comm]))

theorem card_tcSub_ge (m : ℕ) : 2 ^ m ≤ Nat.card (tcSub (m + 1)) := by
  classical
  let f : (Fin m → ZMod 2) → ↥(tcSub (m + 1)) := fun ψ =>
    ⟨⟨tcGL (Fin.cons 0 ψ) rfl, tcGL_mem _ rfl⟩, ⟨Fin.cons 0 ψ, rfl, rfl⟩⟩
  have hf : Function.Injective f := by
    intro ψ ψ' h
    have h1 : tcMat (Fin.cons 0 ψ : Fin (m + 1) → ZMod 2) = tcMat (Fin.cons 0 ψ') :=
      congrArg (fun g : ↥(tcSub (m + 1)) =>
        (((g : ↥(StatedSL (m + 1) (ZMod 2))) : Matrix.GeneralLinearGroup (Fin (m + 1)) (ZMod 2)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) h
    funext i
    have h2 := congrFun (congrFun h1 0) i.succ
    simpa [tcMat, e0, vecMulVec_apply, Matrix.one_apply, Fin.succ_ne_zero] using h2
  calc 2 ^ m = Nat.card (Fin m → ZMod 2) := by
        rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    _ ≤ Nat.card (tcSub (m + 1)) := Nat.card_le_card_of_injective f hf

theorem natAct_tc {g : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n)
    (x : Multiplicative (Fin n → ZMod 2)) :
    natAct (StatedSL n (ZMod 2)) g x * x⁻¹ ∈
      Subgroup.zpowers (Multiplicative.ofAdd (e0 n)) := by
  obtain ⟨φ, hφ, ha⟩ := hg
  have h1 : natAct (StatedSL n (ZMod 2)) g x * x⁻¹ =
      Multiplicative.ofAdd ((φ ⬝ᵥ Multiplicative.toAdd x) • e0 n) := by
    apply Multiplicative.toAdd.injective
    simp only [natAct, toAdd_mul, toAdd_inv, toAdd_ofAdd, ha, tcMat_mulVec]
    abel
  rw [h1]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (φ ⬝ᵥ Multiplicative.toAdd x) with h | h
  · rw [h, zero_smul, ofAdd_zero]
    exact Subgroup.one_mem _
  · rw [h, one_smul]
    exact Subgroup.mem_zpowers _

theorem natAct_tc_e0 {g : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n) :
    natAct (StatedSL n (ZMod 2)) g (Multiplicative.ofAdd (e0 n)) = Multiplicative.ofAdd (e0 n) := by
  obtain ⟨φ, hφ, ha⟩ := hg
  apply Multiplicative.toAdd.injective
  simp only [natAct, toAdd_ofAdd, ha, tcMat_mulVec, dot_e0, hφ, zero_smul, add_zero]

@[expose] def e0Perp (n : ℕ) [NeZero n] : Subgroup (Multiplicative (Fin n → ZMod 2)) where
  carrier := {y | Multiplicative.toAdd y 0 = 0}
  mul_mem' := fun {a b} ha hb => by
    show Multiplicative.toAdd (a * b) 0 = 0
    rw [toAdd_mul, Pi.add_apply, ha, hb, add_zero]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    have ha' : Multiplicative.toAdd a 0 = 0 := ha
    show Multiplicative.toAdd a⁻¹ 0 = 0
    simp [ha']

theorem dualNatAct_tc {g : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n)
    (x : Multiplicative (Fin n → ZMod 2)) :
    dualNatAct (StatedSL n (ZMod 2)) g x * x⁻¹ ∈ e0Perp n := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (tcSub_mul_self hg)
  obtain ⟨φ, hφ, ha⟩ := hg
  show Multiplicative.toAdd (dualNatAct (StatedSL n (ZMod 2)) g x * x⁻¹) 0 = 0
  simp only [dualNatAct, hinv, toAdd_mul, toAdd_inv, toAdd_ofAdd, ha, tcMat_transpose_mulVec]
  simp [hφ]
  exact CharTwo.add_self_eq_zero _

theorem dualNatAct_tc_perp {g : ↥(StatedSL n (ZMod 2))} (hg : g ∈ tcSub n)
    {x : Multiplicative (Fin n → ZMod 2)} (hx : x ∈ e0Perp n) :
    dualNatAct (StatedSL n (ZMod 2)) g x = x := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (tcSub_mul_self hg)
  obtain ⟨φ, hφ, ha⟩ := hg
  apply Multiplicative.toAdd.injective
  have hx0 : Multiplicative.toAdd x 0 = 0 := hx
  simp only [dualNatAct, hinv, toAdd_ofAdd, ha, tcMat_transpose_mulVec, hx0, zero_smul, add_zero]

end CFSG.Quasithin.B513N
