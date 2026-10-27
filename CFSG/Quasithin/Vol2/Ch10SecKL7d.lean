module

public import CFSG.Quasithin.Vol2.Ch10SecKL7c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W}

@[expose] noncomputable def conj (c : Coord L U) (τ : MulAut W) :
    Coord (L.map (MulAut.conj τ).toMonoidHom) (U.map (τ : W →* W)) where
  π := c.π.trans (MulEquiv.subgroupMap (MulAut.conj τ) L)
  Ψ := c.Ψ.trans (MulEquiv.subgroupMap τ U)
  equivar γ v := by
    show (MulAut.conj τ ((c.π γ : ↥L) : MulAut W)) (τ (c.Ψ v : W)) = τ (c.Ψ (actN 4 γ v) : W)
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
      c.equivar]

end Coord

structure Hyp (Mb L₁ L₂ : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (τ : MulAut W) : Prop where
  exp2 : ∀ w : W, w ^ 2 = 1
  sup : W₁ ⊔ W₂ = ⊤
  le₁ : L₁ ≤ Mb
  le₂ : L₂ ≤ Mb
  norm : Mb ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W))
  comm : L₂ ≤ Subgroup.centralizer (L₁ : Set (MulAut W))
  fix₁ : ∀ x ∈ L₁, ∀ w ∈ W₂, x w = w
  fix₂ : ∀ x ∈ L₂, ∀ w ∈ W₁, x w = w
  coord : Nonempty (Coord L₁ W₁)
  memτ : τ ∈ Mb
  mapL : L₁.map (MulAut.conj τ).toMonoidHom = L₂
  mapW : W₁.map (τ : W →* W) = W₂

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}

theorem swap (h : Hyp Mb L₁ L₂ W₁ W₂ τ) : Hyp Mb L₂ L₁ W₂ W₁ τ⁻¹ where
  exp2 := h.exp2
  sup := by rw [sup_comm]; exact h.sup
  le₁ := h.le₂
  le₂ := h.le₁
  norm := by rw [sup_comm]; exact h.norm
  comm := Subgroup.le_centralizer_iff.1 h.comm
  fix₁ := h.fix₂
  fix₂ := h.fix₁
  coord := by
    obtain ⟨c⟩ := h.coord
    rw [← h.mapL, ← h.mapW]
    exact ⟨c.conj τ⟩
  memτ := inv_mem h.memτ
  mapL := by
    rw [← h.mapL, Subgroup.map_map]
    convert Subgroup.map_id L₁
    ext x w
    simp [MulAut.conj_apply]
  mapW := by
    rw [← h.mapW, Subgroup.map_map]
    convert Subgroup.map_id W₁
    ext w
    simp

variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem eq_one_of_fix {x : MulAut W} (hx₁ : ∀ w ∈ W₁, x w = w) (hx₂ : ∀ w ∈ W₂, x w = w) :
    x = 1 := by
  ext w
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (h.sup ▸ Subgroup.mem_top w)
  rw [map_mul, hx₁ a ha, hx₂ b hb, MulAut.one_apply]

theorem inf_L : L₁ ⊓ L₂ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  exact h.eq_one_of_fix (h.fix₂ x hx.2) (h.fix₁ x hx.1)

theorem mem_W₂_iff {w : W} : w ∈ W₂ ↔ ∀ x ∈ L₁, x w = w := by
  refine ⟨fun hw x hx => h.fix₁ x hx w hw, fun hw => ?_⟩
  obtain ⟨c⟩ := h.coord
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (h.sup ▸ Subgroup.mem_top w)
  have ha1 : a = 1 := c.fix_eq_one ha fun x hx => by
    have := hw x hx
    rw [map_mul, h.fix₁ x hx b hb, mul_left_inj] at this
    exact this
  rw [ha1, one_mul]
  exact hb

theorem mem_W₁_iff {w : W} : w ∈ W₁ ↔ ∀ x ∈ L₂, x w = w :=
  h.swap.mem_W₂_iff

theorem inf_W : W₁ ⊓ W₂ = ⊥ := by
  obtain ⟨c⟩ := h.coord
  refine eq_bot_iff.2 fun w hw => ?_
  exact c.fix_eq_one hw.1 fun x hx => h.fix₁ x hx w hw.2

theorem bijective_prodMul : Function.Bijective (W₁.subtype.coprod W₂.subtype) := by
  refine ⟨?_, fun w => ?_⟩
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : W) * b = 1 := hab
    have ha : (a : W) ∈ W₁ ⊓ W₂ := ⟨a.2, by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact W₂.inv_mem b.2⟩
    rw [h.inf_W, Subgroup.mem_bot] at ha
    have hb : (b : W) = 1 := by rw [ha, one_mul] at hab'; exact hab'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (h.sup ▸ Subgroup.mem_top w)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem card_W₁ : Nat.card W₁ = 2 ^ 12 := by
  obtain ⟨c⟩ := h.coord
  exact c.card_U

theorem card_W₂ : Nat.card W₂ = 2 ^ 12 :=
  h.swap.card_W₁

theorem card_W : Nat.card W = 2 ^ 24 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ h.bijective_prodMul), Nat.card_prod, h.card_W₁,
    h.card_W₂]
  norm_num

theorem rk_W : rk W = 24 := by
  rw [rk, h.card_W, padicValNat.prime_pow]

theorem finite_W : Finite W :=
  Nat.finite_of_card_ne_zero (by rw [h.card_W]; norm_num)

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
