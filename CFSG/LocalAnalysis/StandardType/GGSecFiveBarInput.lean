module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleBarAbs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarPump
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarDim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveBarInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) →
      ∀ [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
        (ι : Additive ↥Bs ≃+ V), ∃ (U : Submodule (ZMod p) V)
          (Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)) (ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar),
          3 ≤ Module.finrank (ZMod p) U ∧ ZS.ReflGen p Abar ∧ ZS.AbsIrred p Abar ∧
          (∀ (a : ↥(ggAInf p B Bs x L D J)) (u : ↥U),
            (((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u : V) = ggLin (p := p) ι a u) ∧
          (∀ a ∈ ggAInf p B Bs x L D J, ∀ v : V, ggLin (p := p) ι a v - v ∈ U) ∧
          (∀ a : ↥(ggAInf p B Bs x L D J), GGIsReflection p (a : MulAut ↥Bs) ↔
            ZS.IsRefl p ((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U)) ∧
          ((LinearEquiv.neg (ZMod p) : ↥U ≃ₗ[ZMod p] ↥U) ∈ Abar → U = ⊤)

private abbrev BarIdx {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (D J : Subgroup G) : Type _ :=
  Option {q : G × Subgroup G // GGNbr p B x D J q.1 q.2}

private noncomputable def BarAX {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {L : Subgroup G} :
    BarIdx p B x D J → Subgroup (V ≃ₗ[ZMod p] V) :=
  fun X => match X with
    | none => (ggAutomizer L Bs).map (ggLin (p := p) ι)
    | some q => (ggAutomizer q.1.2 Bs).map (ggLin (p := p) ι)

private noncomputable def BarA {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  (ggAInf p B Bs x L D J).map (ggLin (p := p) ι)

private noncomputable def BarU {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : Submodule (ZMod p) V :=
  ggLinCom ((BarA p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))

private lemma bar_ggInducedSubgroup_mono {G : Type} [Group G] {H H' : Subgroup G} (Bs : Subgroup G)
    (h : H ≤ H') : ggInducedSubgroup H Bs ≤ ggInducedSubgroup H' Bs := by
  rintro φ ⟨g, hg, hgN, hφ⟩
  exact ⟨g, h hg, hgN, hφ⟩

private lemma bar_ggAInf_le_induced {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) :
    ggAInf p B Bs x L D J ≤ ggInducedSubgroup ⊤ Bs := by
  simp only [ggAInf]
  refine sup_le ?_ ?_
  · rw [ggAutomizer_eq]
    exact bar_ggInducedSubgroup_mono Bs le_top
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun _ => ?_
    rw [ggAutomizer_eq]
    exact bar_ggInducedSubgroup_mono Bs le_top

private lemma bar_hfix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    ggLinFix ((BarA p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
      Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
  rw [BarA]
  exact ggLinFix_map_eq_bot (p := p) ι (ggAInf p B Bs x L D J) hC

private lemma bar_hnotr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection p Bs)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ BarA p B Bs x L D J ι) :
    g ≠ 1 → ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
  intro _ h
  rw [BarA, Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  exact hNT φ (bar_ggAInf_le_induced p B Bs x L D J hφ)
    ((ggIsTransvection_iff_ggLin (p := p) ι φ).mpr h)

private lemma bar_hJr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2)
    (h : ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs, GGIsReflection p r ∧
      GGIsReflection p r' ∧ orderOf (r * r') = 3) :
    ∃ r ∈ (ggAutomizer J Bs).map (ggLin (p := p) ι), GGLinRefl r := by
  obtain ⟨r, hr, r', hr', hreflr, -, -⟩ := h
  exact ⟨ggLin (p := p) ι r, Subgroup.mem_map_of_mem _ hr,
    (ggIsReflection_iff_ggLinRefl (p := p) hp2 ι r).mp hreflr⟩

theorem ggSecFiveBarInput_holds
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hPump : GGSecFivePumpReadInput) (hFix : GGSecFiveFixInput) (hJA2 : GGSecFiveJA2Input) :
    GGSecFiveBarInput := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hC _ V _ _ ι
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hp, hBs_ea, hxBs, hLx, -⟩ := hconf.tableB_facts
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let A : Subgroup (MulAut ↥Bs) := ggAInf p B Bs x L D J
  let Ag : Subgroup (V ≃ₗ[ZMod p] V) := A.map (ggLin (p := p) ι)
  let I : Type := BarIdx p B x D J
  let AX : I → Subgroup (V ≃ₗ[ZMod p] V) :=
    BarAX (p := p) (B := B) (Bs := Bs) (x := x) (D := D) (J := J) ι (L := L)
  let AJ : Subgroup (V ≃ₗ[ZMod p] V) := (ggAutomizer J Bs).map (ggLin (p := p) ι)
  let U : Submodule (ZMod p) V := BarU p B Bs x L D J ι
  have hI : Nonempty I := ⟨none⟩
  have hAg : Ag = ⨆ X : I, AX X := by
    dsimp only [Ag, A]
    rw [ggAInf, Subgroup.map_sup]
    simp only [Subgroup.map_iSup]
    dsimp only [AX, I]
    rw [iSup_option]
    simp only [BarAX]
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
        (ggAutomizer_mono Bs le_top) (ggSecFive_bar_pump_L hP hPump hcfg hsplit).1
    | some q =>
      exact ggLinConnGen_of_weyl (p := p) hp2 ι hNT (A := ggAutomizer q.1.2 Bs)
        (ggAutomizer_mono Bs le_top) (ggSecFive_bar_pump_nbr hL hP hPump hcfg hsplit q.2).1
  have hJ : ∀ X : I, AJ ≤ AX X := by
    intro X
    cases X with
    | none =>
      exact Subgroup.map_mono (ggSecFive_bar_pump_L hP hPump hcfg hsplit).2
    | some q =>
      exact Subgroup.map_mono (ggSecFive_bar_pump_nbr hL hP hPump hcfg hsplit q.2).2
  have hJr : ∃ r ∈ AJ, GGLinRefl r :=
    bar_hJr (p := p) (Bs := Bs) (J := J) ι hp2
      (hJA2 G p B Bs x L D J 𝒦 hcfg hsplit)
  have hfix : ggLinFix (Ag : Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
    change ggLinFix ((BarA p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
      Set (V ≃ₗ[ZMod p] V)) = ⊥
    exact bar_hfix ι hC
  have hnotr : ∀ g ∈ Ag, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg
    change g ∈ BarA p B Bs x L D J ι at hg
    exact bar_hnotr ι hNT hg
  have hdim : 3 ≤ Module.finrank (ZMod p) U := by
    change 3 ≤ Module.finrank (ZMod p)
      (ggLinCom ((BarA p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
        Set (V ≃ₗ[ZMod p] V)))
    exact ggSecFive_bar_three_le_finrank (p := p) (B := B) (Bs := Bs) (x := x) (L := L)
      (D := D) (J := J) (𝒦 := 𝒦) hPump hFix hJA2 hcfg hsplit (V := V) ι
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

end CFSG.StandardType

end
