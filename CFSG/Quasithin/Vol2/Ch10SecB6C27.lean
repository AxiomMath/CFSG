module

public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.Quasithin.Vol2.Ch10SecV1N

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem false_of_c27 (hC27 : C27NoL2pJ1)
    (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    {X H K : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t)
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hS : IsSylowTwoOf (T1 T L) H) (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K) (hch : CharTwo K)
    (hq : CFSG.IsQuasisimple (ModO2 K))
    (htype : (∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 ↥(modO2Image H K) ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5)) ∨ (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 ↥(modO2Image H K)) ∨
      IsSporadic .J1 ↥(modO2Image H K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (fsuL0 T L ⊔ T) with hRdef
  have hC23 := hypC23Cat_of_inM hK h331 h37 h38 hyp hH hS
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_L0T_le_T1 hyp).trans (le_sup_right.trans hH.2)).trans hKn
  have hKM : ¬ K ≤ fsuM T L ⊓ H := fun h => not_le_fsuM hyp ht hX hKc hXK (h.trans inf_le_left)
  exact hC27 G H R (fsuM T L ⊓ H) K hC23 hKc hq hch hKM hRK _ (modO2_mulEquiv hKc) htype

end CFSG.Quasithin.Vol2.Ch10.SecB
