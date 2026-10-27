module

public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.EmptyFaithful.SzN15Vocab

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Open CFSG.Quasithin.SzN15

@[expose] def StmtH16_2_1M22 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (L : Subgroup (MulAut W)) (U Z : Subgroup W),
    MathieuCode22 L U Z → ∀ N : Subgroup (MulAut W), N ≤ L → Nat.card N = 5760 →
      Nat.card (fixMod (pCoreOf 2 N) U Z) = 2 * Nat.card Z

variable {W : Type} [CommGroup W]

theorem fixMod_le_fixMod_of_le {R S : Subgroup (MulAut W)} (h : R ≤ S) (U Z : Subgroup W) :
    fixMod S U Z ≤ fixMod R U Z :=
  fun _ hu => ⟨hu.1, fun r hr => hu.2 r (h hr)⟩

theorem card_fixMod_le_of_pCoreOf_le (h : StmtH16_2_1M22) [Finite W]
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hL : MathieuCode22 L U Z)
    {N : Subgroup (MulAut W)} (hNL : N ≤ L) (hN : Nat.card N = 5760)
    {R : Subgroup (MulAut W)} (hR : pCoreOf 2 N ≤ R) :
    Nat.card (fixMod R U Z) ≤ 2 * Nat.card Z :=
  (Subgroup.card_le_of_le (fixMod_le_fixMod_of_le hR U Z)).trans (h W L U Z hL N hNL hN).le

end CFSG.Quasithin.H.Mathieu
