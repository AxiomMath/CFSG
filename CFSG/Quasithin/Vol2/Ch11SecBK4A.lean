module

public import CFSG.Quasithin.Vol2.KGNatReal

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin

namespace BK4

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : D.Gam →* ↥H} {f : W → M}

theorem fix_of_comm (hf : KGNat.IsCoord LM H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    {γ : D.Gam} {S : Set D.Gam} (hS : ∀ δ ∈ S, γ * δ = δ * γ)
    (hspan : ∀ x : M, LM.lin γ x = x →
      x ∈ AddSubgroup.closure {y | ∃ δ ∈ S, ∃ x' : M, LM.lin γ x' = x' ∧ y = LM.lin δ x' - x'})
    {w : W} (hw : LM.lin γ (f w) = f w) : ((π γ : ↥H) : MulAut W) w = w := by
  set g : MulAut W := ((π γ : ↥H) : MulAut W) with hg
  have hgZ : ∀ z ∈ Z, g z = z := hZ g (π γ).2
  suffices key : ∀ x ∈ AddSubgroup.closure {y | ∃ δ ∈ S, ∃ x' : M, LM.lin γ x' = x' ∧
      y = LM.lin δ x' - x'}, ∀ w' : W, f w' = x → g w' = w' from key _ (hspan _ hw) w rfl
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨δ, hδ, x', hx', rfl⟩ := hy
    intro w' hw'
    obtain ⟨u, rfl⟩ := hf.surj x'
    set d : MulAut W := ((π δ : ↥H) : MulAut W) with hd
    have hgd : g * d = d * g := by
      rw [hg, hd, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hS δ hδ]
    have hc : g u * u⁻¹ ∈ Z := (hf.eq_iff _ _).mp (by rw [hg, hf.act, hx'])
    have hz : w' * (d u * u⁻¹)⁻¹ ∈ Z :=
      (hf.eq_iff _ _).mp (by rw [hw', hf.map_mul_inv, hd, hf.act])
    have e1 : g (d u) = d (g u) := by
      have := congrArg (fun φ : MulAut W => φ u) hgd
      simpa only [MulAut.mul_apply] using this
    have e2 : d (g u) = d u * (g u * u⁻¹) := by
      conv_lhs => rw [show g u = u * (g u * u⁻¹) by rw [mul_inv_cancel_comm_assoc]]
      rw [map_mul, hZ d (π δ).2 _ hc]
    have hw'eq : w' = (w' * (d u * u⁻¹)⁻¹) * (d u * u⁻¹) := (inv_mul_cancel_right _ _).symm
    rw [hw'eq, map_mul, hgZ _ hz, map_mul, map_inv, e1, e2]
    congr 1
    rw [mul_assoc, mul_comm (g u) u⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  | zero =>
    intro w' hw'
    exact hgZ w' ((hf.ker w').mp hw')
  | add x y _ _ ihx ihy =>
    intro w' hw'
    obtain ⟨w₁, hw₁⟩ := hf.surj x
    have hw₂ : f (w₁⁻¹ * w') = y := by
      rw [hf.map_mul, hf.map_inv, hw₁, hw']
      abel
    have e : w' = w₁ * (w₁⁻¹ * w') := (mul_inv_cancel_left _ _).symm
    rw [e, map_mul, ihx w₁ hw₁, ihy _ hw₂]
  | neg x _ ih =>
    intro w' hw'
    have h1 := ih w'⁻¹ (by rw [hf.map_inv, hw', neg_neg])
    rw [map_inv] at h1
    exact inv_injective h1

@[expose] def preFix (hf : KGNat.IsCoord LM H Z π f) (T : M →+ M) : Subgroup W where
  carrier := {w | T (f w) = f w}
  mul_mem' := fun {a b} ha hb => by
    show T (f (a * b)) = f (a * b)
    rw [hf.map_mul, map_add, show T (f a) = f a from ha, show T (f b) = f b from hb]
  one_mem' := by
    show T (f 1) = f 1
    rw [hf.map_one, map_zero]
  inv_mem' := fun {a} ha => by
    show T (f a⁻¹) = f a⁻¹
    rw [hf.map_inv, map_neg, show T (f a) = f a from ha]

theorem mem_preFix (hf : KGNat.IsCoord LM H Z π f) {T : M →+ M} {w : W} :
    w ∈ preFix hf T ↔ T (f w) = f w := Iff.rfl

theorem card_preFix (hf : KGNat.IsCoord LM H Z π f) (T : M →+ M) :
    Nat.card (preFix hf T) = Nat.card Z * Nat.card {x : M // T x = x} := by
  have hZP : Z ≤ preFix hf T := fun z hz => by
    show T (f z) = f z
    rw [(hf.ker z).mpr hz, map_zero]
  have h1 := hf.card_img (U := preFix hf T)
  have h2 : Nat.card (hf.img (preFix hf T)) = Nat.card {x : M // T x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hx
      obtain ⟨w, rfl⟩ := hf.surj x
      exact ⟨w, hx, rfl⟩
  have h3 := Subgroup.card_mul_index (Z.subgroupOf (preFix hf T))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv] at h3
  rw [← h3, ← h2, h1]
  rfl

theorem card_eq_mul (hf : KGNat.IsCoord LM H Z π f) : Nat.card W = Nat.card Z * Nat.card M := by
  have h1 := card_preFix hf (AddMonoidHom.id M)
  have h2 : preFix hf (AddMonoidHom.id M) = ⊤ := by
    ext w
    simp only [mem_preFix, AddMonoidHom.id_apply, Subgroup.mem_top]
  rw [h2, Subgroup.card_top] at h1
  rw [h1]
  congr 1
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => (rfl : AddMonoidHom.id M x = x))

theorem card_le_index_mul [Finite W] (hf : KGNat.IsCoord LM H Z π f) {T : M →+ M}
    {C : Subgroup W} (hC : ∀ w ∈ C, T (f w) = f w) :
    Nat.card M ≤ C.index * Nat.card {x : M // T x = x} := by
  have hCP : C ≤ preFix hf T := hC
  have h1 := Subgroup.card_le_of_le hCP
  rw [card_preFix] at h1
  have h2 := Subgroup.card_mul_index C
  rw [card_eq_mul hf] at h2
  have hZ : 0 < Nat.card Z := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hZ
  calc Nat.card Z * Nat.card M = Nat.card C * C.index := h2.symm
    _ ≤ Nat.card Z * Nat.card {x : M // T x = x} * C.index := Nat.mul_le_mul_right _ h1
    _ = Nat.card Z * (C.index * Nat.card {x : M // T x = x}) := by ring

theorem mem_of_index_mul_le [Finite W] (hf : KGNat.IsCoord LM H Z π f) {T : M →+ M}
    {C : Subgroup W} (hC : ∀ w ∈ C, T (f w) = f w)
    (hle : C.index * Nat.card {x : M // T x = x} ≤ Nat.card M) {w : W} (hw : T (f w) = f w) :
    w ∈ C := by
  have hCP : C ≤ preFix hf T := hC
  have h2 := Subgroup.card_mul_index C
  rw [card_eq_mul hf] at h2
  have hi : 0 < C.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h3 : Nat.card (preFix hf T) ≤ Nat.card C := by
    rw [card_preFix]
    refine Nat.le_of_mul_le_mul_right ?_ hi
    calc Nat.card Z * Nat.card {x : M // T x = x} * C.index
        = Nat.card Z * (C.index * Nat.card {x : M // T x = x}) := by ring
      _ ≤ Nat.card Z * Nat.card M := Nat.mul_le_mul_left _ hle
      _ = Nat.card C * C.index := h2.symm
  rw [Subgroup.eq_of_le_of_card_ge hCP h3]
  exact hw

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
