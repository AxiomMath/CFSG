module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_coboundary {L : Subgroup G} (hL : IsShort2 L) {a l : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf a))
    (hLa : a * l * a⁻¹ * l⁻¹ ∈ blockU L) :
    ∃ x ∈ blockU L, a * l * a⁻¹ * l⁻¹ = x * (a * x * a⁻¹)⁻¹ := by
  classical
  have hV : IsElemAbelian 2 (blockU L) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hL)
  have haU : a ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU ha
  set f : ℕ → G := fun k => a ^ k * l * (a ^ k)⁻¹ * l⁻¹ with hf
  have hrec : ∀ k, f (k + 1) = a * f k * a⁻¹ * f 1 := by
    intro k
    simp only [hf]
    group
  have hf1 : f 1 = a * l * a⁻¹ * l⁻¹ := by simp [hf]
  have hfU : ∀ k, f k ∈ blockU L := by
    intro k
    induction k with
    | zero =>
      have : f 0 = 1 := by simp [hf]
      rw [this]
      exact one_mem _
    | succ k ih =>
      rw [hrec]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp haU _).mp ih) (hf1 ▸ hLa)
  let α : MulAut (IntMod (blockU L) hV) := convI hV ⟨a, haU⟩
  let g : ℕ → IntMod (blockU L) hV := fun k => IntMod.mk hV ⟨f k, hfU k⟩
  have hgrec : ∀ k, g (k + 1) = α (g k) * g 1 := by
    intro k
    refine IntMod.val_injective ?_
    rw [IntMod.val_mul, convI_apply_val]
    exact hrec k
  have hg0 : g 0 = 1 := by
    refine IntMod.val_injective ?_
    show f 0 = 1
    simp [hf]
  set n := orderOf a with hn
  have hgn : g n = 1 := by
    refine IntMod.val_injective ?_
    show f n = 1
    simp [hf, hn, pow_orderOf_eq_one]
  let x : IntMod (blockU L) hV := ∏ k ∈ Finset.range n, g k
  have hαg : ∀ k, α (g k) = g (k + 1) * (g 1)⁻¹ := fun k => by
    rw [hgrec k]
    group
  have h1 : α x = (∏ k ∈ Finset.range n, g (k + 1)) * ((g 1)⁻¹) ^ n := by
    simp only [x, map_prod, hαg]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2 : ∏ k ∈ Finset.range n, g (k + 1) = x := by
    have e1 := Finset.prod_range_succ g n
    have e2 := Finset.prod_range_succ' g n
    rw [hgn, mul_one] at e1
    rw [hg0, mul_one] at e2
    exact e2.symm.trans e1
  have h3 : ((g 1)⁻¹) ^ n = (g 1)⁻¹ := by
    obtain ⟨m, hm⟩ := hodd
    have hsq : ((g 1)⁻¹) ^ 2 = 1 := by
      rw [inv_pow, IntMod.sq_eq_one, inv_one]
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hαx : α x = x * (g 1)⁻¹ := by rw [h1, h2, h3]
  have hg1 : g 1 = x * (α x)⁻¹ := by
    rw [hαx, mul_inv_rev, inv_inv, mul_comm (g 1) x⁻¹, mul_inv_cancel_left]
  refine ⟨x.val, x.val_mem, ?_⟩
  have := congrArg IntMod.val hg1
  rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val] at this
  rw [← hf1]
  exact this

omit [Finite G] in
theorem centralizes_of_odd_order {L : Subgroup G} (hL : IsShort2 L) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf a))
    (hLa : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ blockU L)
    (hUa : ∀ u ∈ blockU L, a * u * a⁻¹ * u⁻¹ ∈ blockZ L) :
    ∀ l ∈ L, a * l = l * a := by
  have hZ : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ blockZ L := by
    intro l hl
    obtain ⟨x, hx, hxe⟩ := exists_coboundary hL ha hodd (hLa l hl)
    rw [hxe]
    have := inv_mem (hUa x hx)
    have e : (a * x * a⁻¹ * x⁻¹)⁻¹ = x * (a * x * a⁻¹)⁻¹ := by group
    rw [e] at this
    exact this
  have hZ2 : IsPGroup 2 (blockZ L) := (C1.isPGroup_blockU hL).to_le inf_le_left
  have hker := C1.commutator_mem_of_noTwoQuotient (L := L) (M := blockZ L) (N := ⊥) hL.1 hZ2
    (fun m _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; rw [hn]; group)
    (fun l hl w hw => by
      rw [Subgroup.mem_bot]
      have := Subgroup.mem_centralizer_iff.mp hw.2 l hl
      rw [this]
      group)
    (y := a) hZ
  intro l hl
  have h := hker l hl
  rw [Subgroup.mem_bot] at h
  calc a * l = (a * l * a⁻¹ * l⁻¹) * (l * a) := by group
    _ = l * a := by rw [h, one_mul]

end CFSG.Quasithin.C1Pack
