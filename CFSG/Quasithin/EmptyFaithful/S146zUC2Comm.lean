module

import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.EmptyFaithful.S146zUC2NT

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Natural

theorem eq_of_natAct_eq {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    {B : Subgroup ↥(StatedSL 2 K)} (hB : ∀ x ∈ B, x ^ 2 = 1) (hbot : B ≠ ⊥)
    (heq : Nat.card ↥B * Nat.card ↥(fixNat B) = Nat.card K ^ 2)
    {θ : Multiplicative (Fin 2 → K)} (hθ : θ ∉ fixNat B) {h h' : ↥(StatedSL 2 K)} (hh : h ∈ B)
    (hh' : h' ∈ B) (hθh : natAct (StatedSL 2 K) h θ = natAct (StatedSL 2 K) h' θ) : h = h' := by
  obtain ⟨-, hfix⟩ := card_eq_field_of_mul_card_fixNat hK hB hbot heq
  by_contra hne
  have hk1 : h'⁻¹ * h ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
  have hkB : h'⁻¹ * h ∈ B := B.mul_mem (B.inv_mem hh') hh
  have hkθ : natAct (StatedSL 2 K) (h'⁻¹ * h) θ = θ := by
    rw [SzN15.natAct_mul', hθh, SzN15.natAct_inv']
  have hle := card_natAct_fixed_le (h'⁻¹ * h) hk1
  let i : ↥(fixNat B) →
      {x : Multiplicative (Fin 2 → K) // natAct (StatedSL 2 K) (h'⁻¹ * h) x = x} :=
    fun y => ⟨y.1, y.2 _ hkB⟩
  have hinj : Function.Injective i := fun y z hyz =>
    Subtype.ext (congrArg (fun w : {x : Multiplicative (Fin 2 → K) //
      natAct (StatedSL 2 K) (h'⁻¹ * h) x = x} => (w : Multiplicative (Fin 2 → K))) hyz)
  have hbij : Function.Bijective i :=
    hinj.bijective_of_nat_card_le (by rw [hfix]; exact hle)
  obtain ⟨y, hy⟩ := hbij.2 ⟨θ, hkθ⟩
  apply hθ
  have : y.1 = θ := congrArg Subtype.val hy
  rw [← this]
  exact y.2

end Natural

section Headline

variable {V : Type} [CommGroup V] [Finite V]

theorem card_commV_ge_four {Γ L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (h : S153M.TwoNat L₁ L₂ τ) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₁ : Nat.card ↥L₁ = 4080) (hL₂ : Nat.card ↥L₂ = 4080)
    (hn : ∀ x ∈ Γ, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hcen : ∀ x ∈ Γ, (∀ l ∈ L₁ ⊔ L₂, x * l = l * x) → x = 1) {A : Subgroup (MulAut V)}
    (hAΓ : A ≤ Γ) (hA : A ≠ ⊥) : 4 ≤ Nat.card ↥(commV A) := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha1' : (a : MulAut V) ≠ 1 := fun h' => ha1 (Subtype.ext h')
  refine (nt_of_twoNat h hcomm hL₁ hL₂ hn hcen (hAΓ a.2) ha1').trans
    (Subgroup.card_le_of_le ?_)
  rw [commV_eq_commSub, commV_eq_commSub]
  exact commSub_mono le_rfl ((Subgroup.zpowers_le (g := (a : MulAut V)) (H := A)).2 a.2)

end Headline

end CFSG.Quasithin.S146zU.UC2
