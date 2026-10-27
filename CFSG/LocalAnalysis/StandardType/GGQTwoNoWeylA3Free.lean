module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQTwoNoWeylA3Free : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → Nat.card ↥Bs = p ^ 4 → Nat.card (ggAutomizer L Bs) ≠ 24

theorem ggQTwoNoWeylA3_of_free (h : GGQTwoNoWeylA3Free) : GGQTwoNoWeylA3 := by
  intro G _ _ p B Bs x L D J hS _ y K hnb M hcard4
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨hpprime, -, -, -, h4card⟩ := hcfg.tableB_facts
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod p) M.V := Module.Finite.of_finite
  have hcardV : Nat.card M.V = p ^ Module.finrank (ZMod p) M.V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M.V), Nat.card_zmod]
  have hcardM : Nat.card M.V = Nat.card ↥Bs := by
    calc Nat.card M.V = Nat.card (Additive ↥Bs) := (Nat.card_congr M.model.toEquiv).symm
      _ = Nat.card ↥Bs := Nat.card_congr Additive.toMul
  have hpowle : p ^ 4 ≤ p ^ Module.finrank (ZMod p) M.V := by
    calc p ^ 4 ≤ Nat.card ↥Bs := h4card
      _ = Nat.card M.V := hcardM.symm
      _ = p ^ Module.finrank (ZMod p) M.V := hcardV
  have hfin4 : 4 ≤ Module.finrank (ZMod p) M.V :=
    (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowle
  have hle := GGQTwoModel.finrank_le_card_add_one M
  have hcardΛ : Fintype.card {k // k ≠ M.a} = Fintype.card M.ι - 1 := Set.card_ne_eq M.a
  have hfin : Module.finrank (ZMod p) M.V = 4 := by omega
  have hBs : Nat.card ↥Bs = p ^ 4 := by rw [← hcardM, hcardV, hfin]
  exact h G p B Bs x L D J hS hBs

end CFSG.StandardType

end
