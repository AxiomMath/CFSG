module

public import CFSG.Quasithin.EmptyFaithful.S146zUD1
public import CFSG.Quasithin.EmptyFaithful.S146zUBOrd
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Dec

public section

namespace CFSG.Quasithin.S146zU.UD3

open CFSG.Quasithin

section Module

variable {W : Type} [CommGroup W]

theorem card_fixV_le_sixteen {Mp L L' : Subgroup (MulAut W)}
    {V : Subgroup W} (hV : V = ⊤) (e : Nonempty (↥L ≃* SBc16.L216))
    (hcase : ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n)
    (hMp : Mp = L ⊔ L') (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) {a b : MulAut W}
    (ha : a ∈ L) (hb : b ∈ L') (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤ 2 ^ 4 := by
  obtain ⟨n, hL, hΩ⟩ := hcase
  have hn : n = 4 := UB.eq_four_of_case_one hV e hL
  subst hn
  subst hV
  exact omega4_fixV_card_le (by norm_num) hL hΩ hMp hcomm ha hb ha1 hb1 ha2 hb2

theorem false_of_two_fixed [Finite W]
    {Mp L L' : Subgroup (MulAut W)} {V : Subgroup W} (hV : V = ⊤)
    (e : Nonempty (↥L ≃* SBc16.L216))
    (hcase : ∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n)
    (hMp : Mp = L ⊔ L') (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) {a b : MulAut W}
    (ha : a ∈ L) (hb : b ∈ L') (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    {X₁ X₂ : Subgroup W} (hinf : X₁ ⊓ X₂ = ⊥) (hc₁ : Nat.card ↥X₁ = 2 ^ 4)
    (hc₂ : Nat.card ↥X₂ = 2 ^ 4) (h₁a : ∀ w ∈ X₁, a w = w) (h₁b : ∀ w ∈ X₁, b w = w)
    (h₂a : ∀ w ∈ X₂, a w = w) (h₂b : ∀ w ∈ X₂, b w = w) : False := by
  have hfix : ∀ {X : Subgroup W}, (∀ w ∈ X, a w = w) → (∀ w ∈ X, b w = w) →
      X ≤ fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    intro X hXa hXb w hw g hg
    have h1 : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ MulAction.stabilizer (MulAut W) w :=
      sup_le ((Subgroup.zpowers_le).mpr (by simpa [MulAction.mem_stabilizer_iff] using hXa w hw))
        ((Subgroup.zpowers_le).mpr (by simpa [MulAction.mem_stabilizer_iff] using hXb w hw))
    simpa [MulAction.mem_stabilizer_iff] using h1 hg
  have hle : X₁ ⊔ X₂ ≤ fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    sup_le (hfix h₁a h₁b) (hfix h₂a h₂b)
  have hcard : Nat.card ↥(X₁ ⊔ X₂) = 2 ^ 4 * 2 ^ 4 := by
    rw [SBc15.card_sup_eq_mul_of_commute (fun x _ y _ => mul_comm x y) (disjoint_iff.mpr hinf),
      hc₁, hc₂]
  have h := (Subgroup.card_le_of_le hle).trans
    (card_fixV_le_sixteen hV e hcase hMp hcomm ha hb ha1 hb1 ha2 hb2)
  rw [hcard] at h
  norm_num at h

end Module

end CFSG.Quasithin.S146zU.UD3
