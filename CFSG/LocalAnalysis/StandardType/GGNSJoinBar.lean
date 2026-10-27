module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData
import CFSG.LocalAnalysis.StandardType.GGNSJoinBarAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin


@[expose] def NSBarInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) →
      ∀ [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
        (ι : Additive ↥Bs ≃+ V), ∃ (U : Submodule (ZMod p) V)
          (Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)) (ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar),
          GGSecFiveBarData p B Bs x L D J ι U Abar ρ

theorem nsBarInput_holds {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hBase : NSBaseFrameInputOf T)
    (hPumpNbr : NSPumpNbrInputOf T) (hFix : NSFixInputOf T) (hJA2 : NSJA2InputOf T) :
    NSBarInputOf T := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg0 hC _ V _ _ ι
  have hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0.1
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hp, hBs_ea, hxBs, hLx, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hWeylL : GGWeylReflectionGroup p (ggAutomizer L Bs) := by
    obtain ⟨ιL, _, ML, hADE, hW, -, -⟩ := hBase G p B Bs x L D J 𝒦 hcfg0
    exact ⟨ιL, ML, hADE.elim (fun h => h.isWeylMatrix) (fun h => h.isWeylMatrix), hW⟩
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hconf.1 hconf.2.2
  have hJL : J ≤ L := (eq_of_le_of_stdSub hconf.1 hconf.2.2 hpJ).1
  let A : Subgroup (MulAut ↥Bs) := ggAInf p B Bs x L D J
  let Ag : Subgroup (V ≃ₗ[ZMod p] V) := A.map (ggLin (p := p) ι)
  let I : Type := nsBar_Idx p B x D J
  let AX : I → Subgroup (V ≃ₗ[ZMod p] V) :=
    nsBar_AX (p := p) (B := B) (Bs := Bs) (x := x) (D := D) (J := J) ι (L := L)
  let AJ : Subgroup (V ≃ₗ[ZMod p] V) := (ggAutomizer J Bs).map (ggLin (p := p) ι)
  let U : Submodule (ZMod p) V := nsBar_U p B Bs x L D J ι
  have hI : Nonempty I := ⟨none⟩
  have hAg : Ag = ⨆ X : I, AX X := by
    dsimp only [Ag, A]
    rw [ggAInf, Subgroup.map_sup]
    simp only [Subgroup.map_iSup]
    dsimp only [AX, I]
    rw [iSup_option]
    simp only [nsBar_AX]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact le_sup_left
      · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
        exact (le_iSup (fun q : {q : G × Subgroup G // GGNbr p B x D J q.1 q.2} =>
          (ggAutomizer q.1.2 Bs).map (ggLin (p := p) ι)) ⟨(y, K), h⟩).trans le_sup_right
    · refine sup_le ?_ ?_
      · exact le_sup_left
      · refine iSup_le fun q => ?_
        exact (le_iSup (fun _ : GGNbr p B x D J q.1.1 q.1.2 =>
            (ggAutomizer q.1.2 Bs).map (ggLin (p := p) ι)) q.2).trans
          ((le_iSup (fun K : Subgroup G => ⨆ (_ : GGNbr p B x D J q.1.1 K),
            (ggAutomizer K Bs).map (ggLin (p := p) ι)) q.1.2).trans
          ((le_iSup (fun y : G => ⨆ K : Subgroup G, ⨆ (_ : GGNbr p B x D J y K),
            (ggAutomizer K Bs).map (ggLin (p := p) ι)) q.1.1).trans le_sup_right))
  have hX : ∀ X : I, GGLinConnGen (AX X) := by
    intro X
    cases X with
    | none =>
      exact ggLinConnGen_of_weyl (p := p) hp2 ι hNT (A := ggAutomizer L Bs)
        (ggAutomizer_mono Bs le_top) hWeylL
    | some q =>
      exact ggLinConnGen_of_weyl (p := p) hp2 ι hNT (A := ggAutomizer q.1.2 Bs)
        (ggAutomizer_mono Bs le_top)
        (hPumpNbr G p B Bs x L D J 𝒦 hcfg0 q.1.1 q.1.2 q.2).1
  have hJ : ∀ X : I, AJ ≤ AX X := by
    intro X
    cases X with
    | none =>
      exact Subgroup.map_mono (ggAutomizer_mono Bs hJL)
    | some q =>
      exact Subgroup.map_mono
        (ggAutomizer_mono Bs (le_of_ggNbr hL hconf.1 hconf.2.2 hpJ q.2))
  have hJr : ∃ r ∈ AJ, GGLinRefl r :=
    nsBar_hJr (p := p) (Bs := Bs) (J := J) ι hp2
      (hJA2 G p B Bs x L D J 𝒦 hcfg0)
  have hfix : ggLinFix (Ag : Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
    change ggLinFix ((nsBar_A p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
      Set (V ≃ₗ[ZMod p] V)) = ⊥
    exact nsBar_hfix ι hC
  have hnotr : ∀ g ∈ Ag, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg
    change g ∈ nsBar_A p B Bs x L D J ι at hg
    exact nsBar_hnotr ι hNT hg
  have hdim : 3 ≤ Module.finrank (ZMod p) U := by
    change 3 ≤ Module.finrank (ZMod p)
      (ggLinCom ((nsBar_A p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
        Set (V ≃ₗ[ZMod p] V)))
    exact nsBar_three_le_finrank hBase hcfg0 ι
  obtain ⟨Abar, ρ', hRG, hAI, hres, htriv, hrefl, hneg⟩ :=
    ggLin_bar_linear_data (p := p) hp2 (I := I) AX hX AJ hJ hJr Ag hAg hfix hnotr U rfl hdim
  let ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar :=
    (Subgroup.equivMapOfInjective (ggAInf p B Bs x L D J) (ggLin (p := p) ι)
      (ggLin_injective (p := p) ι)).trans ρ'
  refine ⟨U, Abar, ρ, hdim, hRG, hAI, ?_, ?_, ?_, ?_⟩
  · intro a u
    exact hres (Subgroup.equivMapOfInjective (ggAInf p B Bs x L D J) (ggLin (p := p) ι)
      (ggLin_injective (p := p) ι) a) u
  · intro a ha v
    exact htriv (ggLin (p := p) ι a) (Subgroup.mem_map_of_mem (ggLin (p := p) ι) ha) v
  · intro a
    have h1 : GGIsReflection p (a : MulAut ↥Bs) ↔ GGLinRefl (ggLin (p := p) ι a) :=
      ggIsReflection_iff_ggLinRefl (p := p) hp2 ι (a : MulAut ↥Bs)
    have h2 : GGLinRefl (ggLin (p := p) ι a) ↔
        ZS.IsRefl p ((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) :=
      hrefl ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem (ggLin (p := p) ι) a.2⟩
    exact h1.trans h2
  · exact hneg

end NSJoin

end CFSG.StandardType

end
