module

public import CFSG.Quasithin.H13.A5S1521d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactQuadRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → Rows1321Final G L A →
      ∀ v : MulAut V, Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ∀ c ∈ L, c * v = v * c → c ^ 3 = 1 → c ≠ 1 →
          ∀ q : V → ZMod 2, (∀ x ∈ G, ∀ w, q (x w) = q w) →
            (∀ a b w, q (a * b * w) - q (a * b) - q w =
              (q (a * w) - q a - q w) + (q (b * w) - q b - q w)) →
            (∀ a, a ≠ 1 → ∃ w, q (a * w) - q a - q w ≠ 0) →
            ∃ w, c w = w ∧ q w ≠ 0

end CFSG.Quasithin.H13.A5
