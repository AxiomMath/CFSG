module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def AsB4_8Three : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (W C : Subgroup V),
      Nonempty (↥G ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) → C ≤ W →
      XMod.IsInv ↥G W → XMod.IsInv ↥G C →
      (∀ g ∈ G, (∀ w ∈ W, g w * w⁻¹ ∈ C) → g = 1) →
      Nat.card ↥W = 2 ^ 4 * Nat.card ↥C →
      (¬ ∃ A B : Subgroup V, C < A ∧ C < B ∧ XMod.IsInv ↥G A ∧ XMod.IsInv ↥G B ∧
        A ⊔ B = W ∧ A ⊓ B = C) →
      BinaryNaturalSL G (modComm G W ⊔ C) C 3 1 →
      ∀ a ∈ G, orderOf a = 2 → ∀ w ∈ W, a w * w⁻¹ ∈ C → w ∈ modComm G W ⊔ C

@[expose] def FactA312L32RankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B L : Subgroup X), A312Case B L →
    Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    CFSG.Open.pRank 3 L ≤ 1 →
    ∀ r : ℕ, r.Prime → r ∣ Nat.card L → r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 43

end CFSG.Quasithin.Vol2.Ch10.SecB
