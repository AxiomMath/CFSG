module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourDefs
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSome

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGHalfAutWithin (Bs L K : Subgroup G) : Prop :=
  ∀ φ ∈ ggInduced ⊤ Bs, φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs

end Defs

@[expose] def GGTypeAHalfEndNodesAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeAHalfNbr p B Bs x L D J n y K →
    GGHalfAutWithin Bs L K →
    ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1)) ∧
      ∃ T₁ T₂ : G, T₁ ∈ ggG0 p B x L D J ∧ T₂ ∈ ggG0 p B x L D J ∧
        GGTypeATwoEndNodes φ₁ T₁ T₂ ∧
        ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
          K' ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
            L.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
              L.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom

theorem ggTypeAHalfEndNodesAutInput_of_halfEndNodes (h : GGTypeAHalfEndNodesInput) :
    GGTypeAHalfEndNodesAutInput := fun G _ _ p B Bs x L D J n y K hcfg hOp hInn hNoTr hN _ =>
  h G p B Bs x L D J n y K hcfg hOp hInn hNoTr hN

@[expose] def GGTypeAHalfJoinEndNodesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeAHalfNbr p B Bs x L D J n y K →
    GGHalfAutWithin Bs L K →
    ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1)) ∧
      ∃ T₁ T₂ : G, T₁ ∈ L ⊔ K ∧ T₂ ∈ L ⊔ K ∧ GGTypeATwoEndNodes φ₁ T₁ T₂ ∧
        K ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
          L.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
            L.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom

@[expose] def GGTypeAHalfJoinAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeAHalfNbr p B Bs x L D J n y K →
    GGHalfAutWithin Bs L K → ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → K' ≤ L ⊔ K

theorem GGHalfAutWithin.automizer_le {G : Type} [Group G] {Bs L K : Subgroup G}
    (h : GGHalfAutWithin Bs L K) (K' : Subgroup G) :
    ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  rw [ggAutomizer, Subgroup.closure_le]
  rintro φ ⟨g, -, hgN, hφ⟩
  exact h φ ⟨g, Subgroup.mem_top g, hgN, hφ⟩

theorem ggTypeAHalfEndNodesAutInput_of_join (h₁ : GGTypeAHalfJoinEndNodesInput)
    (h₂ : GGTypeAHalfJoinAutInput) : GGTypeAHalfEndNodesAutInput := by
  intro G _ _ p B Bs x L D J n y K hcfg hOp hInn hNoTr hN hAut
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁, hT₂, hT, hK⟩ :=
    h₁ G p B Bs x L D J n y K hcfg hOp hInn hNoTr hN hAut
  have hLK : L ⊔ K ≤ ggG0 p B x L D J :=
    sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr hN.2.2.2.2.1)
  refine ⟨φ₁, hφL, hker, T₁, T₂, hLK hT₁, hLK hT₂, hT, fun y' K' hK' => ?_⟩
  exact (h₂ G p B Bs x L D J n y K hcfg hOp hInn hNoTr hN hAut y' K' hK'
    (hAut.automizer_le K')).trans (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) hK)

theorem ggSecFiveTypeA_of_halfAut (hH : GGTypeAHalfEndNodesAutInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeAHalfNbr p B Bs x L D J n y K) (hAut : GGHalfAutWithin Bs L K) :
    GGSecFiveTypeA p B x L D J (n + 1 + 1) (n + 1) 1 := by
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁G, hT₂G, hT, hnbr⟩ :=
    hH G p B Bs x L D J n y K hcfg hOp hInn hNoTr h hAut
  exact ggSecFiveTypeA_of_twoEndNodes (by have := h.2.2.1; omega) le_rfl φ₁ hφL hker hT hT₁G hT₂G
    hnbr

section Data

@[expose] def GGTypeAHalfLargeAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (y : G) (K : Subgroup G), GGSecFiveRestHyp p B Bs x L D J →
    GGSecFiveWeylCase' p B Bs x D J →
    (¬ ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K) →
    GGTypeAHalfNbr p B Bs x L D J n y K → ¬ GGHalfAutWithin Bs L K → GGSecFiveData p B x L D J

theorem ggSecFiveDataInputRest_of_cases_halfAut (hNW : GGSecFiveNonWeylInput)
    (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoInput)
    (hH : GGTypeAHalfEndNodesAutInput) (hHL : GGTypeAHalfLargeAutInput)
    (hA : GGSecFiveWeylAInput) (hB : GGSecFiveWeylBInput) (hD : GGSecFiveWeylDInput)
    (hEx : GGSecFiveWeylEInput) (hF : GGSecFiveWeylF4Input) (hG : GGSecFiveWeylG2Input) :
    GGSecFiveDataInputRest := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW hnA
  have hR : GGSecFiveRestHyp p B Bs x L D J := ⟨hcfg, hOp, hInn, hNoTr, hW, hnA⟩
  show GGSecFiveData p B x L D J
  by_cases hWC : GGSecFiveWeylCase' p B Bs x D J
  swap
  · exact hNW G p B Bs x L D J hR hWC
  by_cases hTA : ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K
  · obtain ⟨n, f, y, K, hN⟩ := hTA
    have hf1 : 1 ≤ f := hN.1.1.2.1
    have hn : 3 ≤ n := hN.2.2.1
    by_cases hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K
    · exact Or.inl ⟨n + 1, n + 1, f, by omega, le_rfl, hf1,
        ggSecFiveTypeA_of_join hE hcfg hOp hInn hNoTr hN hjoin⟩
    · push Not at hjoin
      exact Or.inl ⟨n + 1 + 1, n + 1, f, by omega, by omega, hf1,
        ggSecFiveTypeA_of_corankTwo hE hC hcfg hOp hInn hNoTr hN (hR.dvd_of_typeANbr hN) hjoin⟩
  by_cases hHalf : ∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K
  · obtain ⟨n, y, K, hN⟩ := hHalf
    have hn : 5 ≤ n := hN.2.2.1
    by_cases hAut : GGHalfAutWithin Bs L K
    · exact Or.inl ⟨n + 1 + 1, n + 1, 1, by omega, by omega, le_rfl,
        ggSecFiveTypeA_of_halfAut hH hcfg hOp hInn hNoTr hN hAut⟩
    · exact hHL G p B Bs x L D J n y K hR hWC hTA hN hAut
  · by_cases hAll : GGSecFiveAllAJoin p B Bs x L D J
    ·
      obtain ⟨y, K, hnbr⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
      obtain ⟨n, hn, hT⟩ := hAll y K hnbr
      exact hA G p B Bs x L D J hR hWC ⟨n, hn, y, K, hnbr, hT⟩ hTA
    ·
      rcases hR.exists_nonA_weylAt hWC hAll with hBt | hDt | hE6 | hE7 | hE8 | hFt | hGt
      · exact hB G p B Bs x L D J hR hWC hBt hHalf
      · exact hD G p B Bs x L D J hR hWC hDt
      · exact hEx G p B Bs x L D J hR hWC (Or.inl hE6)
      · exact hEx G p B Bs x L D J hR hWC (Or.inr (Or.inl hE7))
      · exact hEx G p B Bs x L D J hR hWC (Or.inr (Or.inr hE8))
      · exact hF G p B Bs x L D J hR hWC hFt
      · exact hG G p B Bs x L D J hR hWC hGt

theorem ggSecFiveDataInputRest_of_rest4_halfAut (hNW : GGSecFiveNonWeylInput)
    (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoInput)
    (hH : GGTypeAHalfEndNodesAutInput) (hHL : GGTypeAHalfLargeAutInput) (hL : GGSpLiftInput)
    (hSE : GGSpJoinEndNodeInput) (hSJ : GGSpJoinInput) (h : GGSecFiveWeylRest4) :
    GGSecFiveDataInputRest :=
  ggSecFiveDataInputRest_of_cases_halfAut hNW hE hC hH hHL h.1
    (ggSecFiveWeylBInput_of_typeC hL hSE hSJ h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem ggSecFiveCompat_of_halfAut (hH : GGTypeAHalfEndNodesAutInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeAHalfNbr p B Bs x L D J n y K) (hAut : GGHalfAutWithin Bs L K) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁G, hT₂G, hT, hnbr⟩ :=
    hH G p B Bs x L D J n y K hcfg hOp hInn hNoTr h hAut
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_twoEndNodesAt
    (by have := h.2.2.1; omega) le_rfl φ₁ hφL hker hT (le_ggG0_left p B x L D J) hT₁G hT₂G
    (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr
  exact ⟨.PSL, n + 1 + 1 + 1, 1, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

@[expose] def GGSecFiveCompatHalfLargeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
        ∀ (m : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J m y K →
          ¬ GGHalfAutWithin Bs L K → GGSecFiveCompat p B x L D J

end Data

section Compat

theorem ggCompatNbrSomeInput_of_secFive_halfAut (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (hA : GGTypeAEndNodeInput) (hE : GGTypeAJoinEndNodeInput)
    (hC : GGTypeACorankTwoInput) (hH : GGTypeAHalfEndNodesAutInput)
    (hHL : GGSecFiveCompatHalfLargeInput) (hSpL : GGSpLiftInput) (hSpE : GGSpJoinEndNodeInput)
    (hSpJ : GGSpJoinInput) (hrest : GGSecFiveCompatRestInput) : GGCompatNbrSomeInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  by_cases hlevi : GGSecFiveLeviCase p B Bs x L D J
  · rcases hlevi with ⟨m, f', y, K, hN⟩ | ⟨m, y, K, hN⟩ | ⟨m, f', y, K, hN⟩
    · by_cases hsplit : ∃ n' f'' : ℕ, GGTypeASplitConfig p B Bs x L D J n' f''
      · obtain ⟨n', f'', hS⟩ := hsplit
        exact ggSecFiveCompat_of_endNodeInput hA hcfg hOp hInn hNoTr hS
      have hdiv : p ∣ m + 3 := by
        by_contra hp
        exact hsplit ⟨m, f', hN.splitConfig hp⟩
      by_cases hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K
      · exact ggSecFiveCompat_of_join hE hcfg hOp hInn hNoTr hN hjoin
      · push Not at hjoin
        exact ggSecFiveCompat_of_corankTwo hE hC hcfg hOp hInn hNoTr hN hdiv hjoin
    · by_cases hAut : GGHalfAutWithin Bs L K
      · exact ggSecFiveCompat_of_halfAut hH hcfg hOp hInn hNoTr hN hAut
      · exact hHL G p B Bs x L D J hcfg hOp hInn hNoTr hW t n f ψ hpres m y K hN hAut
    · exact ggSecFiveCompat_of_typeC hSpL hSpE hSpJ hcfg hOp hInn hNoTr hN
  · exact hrest G p B Bs x L D J hcfg hOp hInn hNoTr hW t n f ψ hpres hlevi

end Compat

end CFSG.StandardType
