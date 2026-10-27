module

public import CFSG.Quasithin.EmptyFaithful.S153E56B
public import CFSG.Quasithin.EmptyFaithful.S153E55C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace S153E56a

open CFSG.Quasithin.S153E CFSG.Quasithin.S153E55

section Orders

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem W_eq (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
    (c : Chain15354 cx N₁ N₂ g s) :
    Wgp153 T M V₁ Mc g = UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  apply le_antisymm
  · intro w hw
    refine ⟨hw.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp (c.h54.two_center hv).2 w hw.2)).symm
  · intro x hx
    refine ⟨hx.1, centralizer_le_P c.h54.one cx ⟨U_le_YU hx.1, hx.2⟩⟩

theorem card_P (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) : Nat.card ↥(Pgp153 T M V₁ Mc g) = 2 ^ (4 * s + 4) := by
  have hpd := pdecomp cx c
  have h₁ := card_eq_of_sumNat c.h54.four_nat₁ hpd.symm.V_le_P₂
  have h₂ := card_eq_of_sumNat c.h54.four_nat₂ hpd.V_le_P₂
  rw [card_P_of_pdecomp hpd h₁ h₂, cx.c.hyp.card_VZ, pow_add]
  ring

theorem card_W (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) : Nat.card ↥(Wgp153 T M V₁ Mc g) = 2 ^ (2 * s + 3) := by
  have hsq := card_W_sq c.h54.two_prod c.h54.five_norm
  have hinf : Nat.card ↥(Wgp153 T M V₁ Mc g ⊓ conjSubgroup (Wgp153 T M V₁ Mc g) g) = 4 := by
    have h4 := c.h54.three_klein.1
    rw [c.h54.three_eq] at h4
    exact h4
  have hP := card_P cx c
  have hsq' : Nat.card ↥(Wgp153 T M V₁ Mc g) * Nat.card ↥(Wgp153 T M V₁ Mc g) =
      2 ^ (2 * s + 3) * 2 ^ (2 * s + 3) := by
    have e : (2 : ℕ) ^ (2 * s + 3) * 2 ^ (2 * s + 3) = 2 ^ (4 * s + 4) * 4 := by
      rw [← pow_add]
      ring_nf
    rw [e, ← hP, ← hinf, mul_comm]
    exact hsq.symm
  exact Nat.mul_self_inj.mp hsq'

end Orders

end S153E56a

end CFSG.Quasithin
