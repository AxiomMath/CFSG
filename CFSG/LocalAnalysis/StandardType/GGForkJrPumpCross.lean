module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpCrossLattice
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpCrossReal
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpFork
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggForkCross_of_jr_pump_core (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
        GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGScalarsOrWeyl' p B Bs x D J → ∀ [Fact p.Prime], 5 ≤ p →
        ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
        (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
        (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
        GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
        (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
        (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
        LinearIndependent (ZMod p) (ggOptFam ha h) →
        ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
        ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
        3 ≤ Fintype.card Λ → αa (h b) = 0 ∨ αa (h b) = 1 := by
  intro G _ _ p B Bs x L D J hcfg hop hInn hNT y K hnb hsc _ hp5 Λ _ _ M C V _ _ ι φ φa h α ha αa b c
    hM hC hF hlin hlina hind hAL hAK h3
  obtain ⟨v₂, hvb, hvc, hn⟩ := exists_fork_second_neighbour hM hC hF.ne hF.bL h3
  rcases ggForkCross_realize hL hP hJr hPump hcfg hop hInn hNT hnb hsc hp5 ι hF hlin hlina hind
      hAL hAK hvb hvc with h0 | ⟨X, hX, htX, hcX, hvX⟩
  · exact Or.inl h0
  · exact ggForkCross_lattice_step hp5 hcfg.2.1.2.1 hNT hX ι hF hlin hlina hind hvb hvc hn htX hcX
      hvX

theorem ggForkCrossGe5Main_of_jr_pump (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) : GGForkCrossGe5MainInput :=
  fun G _ _ p B Bs x L D J hcfg hop hInn hNT y K hnb _ hsc _ hp5 Λ _ _ M C V _ _ ι φ φa h α
      ha αa b c hM hC hF hlin hlina hind hAL hAK _ h3 =>
    ggForkCross_of_jr_pump_core hL hP hJr hPump G p B Bs x L D J hcfg hop hInn hNT y K hnb hsc
      hp5 Λ M C V ι φ φa h α ha αa b c hM hC hF hlin hlina hind hAL hAK h3

theorem ggForkCrossGe5Exc_of_jr_pump (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) : GGForkCrossGe5ExcInput :=
  fun G _ _ p B Bs x L D J hcfg hop hInn hNT y K hnb _ hsc _ hp5 Λ _ _ M C V _ _ ι φ φa h α
      ha αa b c hM hC hF hlin hlina hind hAL hAK hF1 =>
    ggForkCross_of_jr_pump_core hL hP hJr hPump G p B Bs x L D J hcfg hop hInn hNT y K hnb hsc
      hp5 Λ M C V ι φ φa h α ha αa b c hM hC hF hlin hlina hind hAL hAK
      (three_le_card_of_ggForkF1Fails hF1)

end CFSG.StandardType
