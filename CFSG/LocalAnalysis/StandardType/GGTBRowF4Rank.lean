module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4RankAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4Row_finrank_le_five
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hL : GGInnerDiagOnLabel GGTableBF4Label p Bs L)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) V ≤ 5 := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hall : ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab → GGTableBF4Label p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
          Nat.card X ≤ p ^ 4) :=
    fun lab hlab h => ggF4Row_labelAll_card h.1 hlab hp h.2
  obtain ⟨hLc, lab, hlab, hraw⟩ :=
    largeEvenMarking_and_labelAll_simple (X := L) (S := GGTableBF4Label p)
      hall (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, hs, hna, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hBsI : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' => (l' : G) = b⁻¹ * l * b) φ := hP.2.2
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  have hγ : Nat.card (ggGamma L hN).range ≤ p ^ 4 := by
    have hBp : ∀ b : ↥Bs, b ^ p = 1 :=
      fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
    have hBc : ∀ a b : ↥Bs, a * b = b * a :=
      fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
    have hAab : IsElemAbelian p (ggGamma L hN).range :=
      isElemAbelian_range hBc hBp (ggGamma L hN)
    set A := (ggGamma L hN).range with hA
    set X := TypeA.inducedSub (ggQuotHom θ) A with hX
    have hXab : IsElemAbelian p X :=
      TypeA.isElemAbelian_inducedSub (ggQuotHom_surjective θ) hAab
    have hXI : (X : Set (MulAut R)) ⊆ I := by
      rintro φ ⟨a, ha, hφa⟩
      obtain ⟨b, rfl⟩ := ha
      have hβI : ggBeta L θ hN b ∈ I := ggBeta_mem L θ hN hBsI b
      have hφβ : φ = ggBeta L θ hN b :=
        TypeA.induced_unique (ggQuotHom θ) (ggQuotHom_surjective θ) hφa
          (fun l => ggBeta_ggQuotHom L hN θ b l)
      rwa [hφβ]
    have hXcard : Nat.card X = Nat.card A :=
      TypeA.card_inducedSub (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hLc
        (fun a ha => by
          obtain ⟨b, rfl⟩ := ha
          exact ⟨ggBeta L θ hN b, fun l => ggBeta_ggQuotHom L hN θ b l⟩)
    calc Nat.card (ggGamma L hN).range = Nat.card A := by rw [hA]
      _ = Nat.card X := hXcard.symm
      _ ≤ p ^ 4 := hP' X hXI hXab
  have hBscard : Nat.card ↥Bs ≤ p ^ 5 :=
    calc Nat.card ↥Bs = Nat.card (ggGamma L hN).range * p := hmul.symm
      _ ≤ p ^ 4 * p := Nat.mul_le_mul_right p hγ
      _ = p ^ 5 := by ring
  haveI : Module.Finite (ZMod p) V := by
    haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
    exact Module.Finite.of_finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
      Nat.card_zmod]
  have hpow : p ^ Module.finrank (ZMod p) V ≤ p ^ 5 := by
    rw [← hcardV]
    exact hBscard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow

end CFSG.StandardType

end
