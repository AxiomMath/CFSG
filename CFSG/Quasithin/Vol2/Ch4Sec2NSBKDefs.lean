module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

@[expose] def NSBModuleStructure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k → ∀ n : ℕ,
      ((n = 4 ∧ m = 3) ∨ (n = 5 ∧ m = 3) ∨ (n = 5 ∧ m = 4)) → IsPSL n 2 1 (ModO2 K) →
      ∃ (j : ℕ) (α : ↥K →* GL (Fin n) (ZMod 2))
        (β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)),
        j + 1 ≤ n ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥K ∧ Function.Bijective β ∧
        ∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
          Multiplicative.toAdd (β v) i =
            ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
              (Multiplicative.toAdd (β u) i)

end CFSG.Quasithin.H13.Ch4.NSB
