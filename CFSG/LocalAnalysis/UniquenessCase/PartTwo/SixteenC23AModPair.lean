module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open

variable {V : Type} [CommGroup V]

structure C23AModPair (Mb L₁ L₂ : Subgroup (MulAut V)) (E₁ E₂ Z₁ Z₂ : Subgroup V) : Prop where
  exp2 : ∀ v : V, v ^ 2 = 1
  blk₁ : C23ABlock L₁ E₁ Z₁
  blk₂ : C23ABlock L₂ E₂ Z₂
  sup : E₁ ⊔ E₂ = ⊤
  inf₁ : E₁ ⊓ E₂ ≤ Z₁
  inf₂ : E₁ ⊓ E₂ ≤ Z₂
  ne₁ : Z₁ ≠ ⊥
  ne₂ : Z₂ ≠ ⊥
  perm : ∀ m ∈ Mb,
    (m ∈ Subgroup.normalizer (L₁ : Set (MulAut V)) ∧
      m ∈ Subgroup.normalizer (L₂ : Set (MulAut V)) ∧
      (∀ e ∈ E₁, m e ∈ E₁) ∧ (∀ e ∈ E₂, m e ∈ E₂)) ∨
    ((∀ e ∈ E₁, m e ∈ E₂) ∧ (∀ e ∈ E₂, m e ∈ E₁))

theorem C23AModPair.symm {Mb L₁ L₂ : Subgroup (MulAut V)} {E₁ E₂ Z₁ Z₂ : Subgroup V}
    (h : C23AModPair Mb L₁ L₂ E₁ E₂ Z₁ Z₂) : C23AModPair Mb L₂ L₁ E₂ E₁ Z₂ Z₁ where
  exp2 := h.exp2
  blk₁ := h.blk₂
  blk₂ := h.blk₁
  sup := by rw [sup_comm]; exact h.sup
  inf₁ := by rw [inf_comm]; exact h.inf₂
  inf₂ := by rw [inf_comm]; exact h.inf₁
  ne₁ := h.ne₂
  ne₂ := h.ne₁
  perm := fun m hm =>
    (h.perm m hm).elim (fun ⟨a, b, c, d⟩ => Or.inl ⟨b, a, d, c⟩) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)

theorem c23a_block_card_eq {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) : Nat.card ↥E = 2 ^ 3 * Nat.card ↥Z := by
  obtain ⟨D⟩ := h.nat
  have hZE : Z ≤ E := h.fix ▸ inf_le_left
  have h1 := Subgroup.card_ker_mul_card_range D.θ
  have hker : D.θ.ker = Z.subgroupOf E := by
    ext u
    rw [MonoidHom.mem_ker, D.θ_ker]
    rfl
  have hrange : Nat.card D.θ.range = 2 ^ 3 := by
    rw [MonoidHom.range_eq_top.2 D.θ_surj, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hZ : Nat.card ↥(Z.subgroupOf E) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  rw [hker, hZ, hrange] at h1
  rw [← h1, mul_comm]

theorem c23a_block_rk_eq [Finite V] {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) : rk ↥E = 3 + rk ↥Z := by
  unfold rk
  rw [c23a_block_card_eq h, padicValNat.mul (by norm_num) Nat.card_pos.ne',
    padicValNat.prime_pow]

theorem c23a_eq_one_of_fix {L : Subgroup (MulAut V)} {E Z : Subgroup V} (h : C23ABlock L E Z)
    {l : MulAut V} (hl : l ∈ L) (hfix : ∀ e ∈ E, l e = e) : l = 1 := by
  by_contra hl1
  refine c23a_not_commSub_le h hl hl1 ?_
  have hbot : commSub E (Subgroup.zpowers l) = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro w hw x hx
    have hle : Subgroup.zpowers l ≤ MulAction.stabilizer (MulAut V) w :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 (hfix w hw))
    exact MulAction.mem_stabilizer_iff.1 (hle hx)
  rw [hbot]
  exact bot_le

theorem c23a_rk_lt_of_lt [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {H K : Subgroup V} (h : H < K) :
    rk ↥H < rk ↥K := by
  by_contra hge
  exact h.ne (eq_of_le_of_rk_le hV h.le (not_lt.1 hge))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
