module

public import CFSG.Quasithin.Background.C116Two.NatAlt3
public import CFSG.Quasithin.Background.C116Two.NatAltOdd
public import CFSG.Quasithin.Background.C116Two.NatLin2
public import CFSG.Quasithin.Background.C116Two.NatTranslate
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem natCount_chiBlock {H L B : Subgroup G} (hL : IsChiBlock H L) (hB : IsElemAbelian 2 B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    (B ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex B *
        Nat.card {u : G // u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L} ≤
      Nat.card (blockU L) := by
  rcases hL.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
  · obtain ⟨F, _, _, D, hcard, hrange⟩ := modData_of_lin2 hlin
    have hN : NatCountMod (Multiplicative (Fin 2 → F)) D.ρ.range := by
      rw [hrange]
      exact natCountMod_lin2 hn hcard
    exact natCount_of_modData hL.1.1 D hB hBN hN
  · obtain ⟨D, hrange⟩ := modData_of_alt hm3 halt
    have hN : NatCountMod (Multiplicative (evenWeight m)) D.ρ.range := by
      rw [hrange]
      by_cases h3 : m = 3
      · subst h3
        exact natCountMod_alt3
      · obtain ⟨k, hk⟩ := hm
        exact natCountMod_altOdd ⟨k, hk⟩ (by omega)
    exact natCount_of_modData hL.1.1 D hB hBN hN

end CFSG.Quasithin.C116Two
