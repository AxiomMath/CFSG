module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourTwins
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

@[expose] def GGTableBPosImage
    (p : ℕ) {G : Type} [Group G] (Bs : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (X : Subgroup G) : Prop :=
  ∃ ψ : (ggU t n f).K →* G, ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
    GGTableBPos p Bs X t n f ψ

@[expose] def GGF4QGeFourKGPosInput
    (row : GGF4QGeFourRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGF4QGeFourCfg p B Bs x L D J y K →
    GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGF4QGeFourRowHyp row f L K →
      match row with
      | .S1 => GGTableBPosImage p Bs .PSp 3 f L ∧ GGTableBPosImage p Bs .PSp 3 f K
      | .S2 => GGTableBPosImage p Bs .POmegaMinus 4 f L ∧
          (GGTableBPosImage p Bs .PSU 6 f K ∨ GGTableBPosImage p Bs .POmegaMinus 4 f K)

private theorem exists_weylAction_of_mem_roots' {U : Type*} [Group U] (D : UniversalRootDatum U)
    (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      γ = weylAction D.isFiniteType w (Pi.single i 1) := by
  change γ ∈ roots D.isFiniteType D.divisible at hγ
  rw [roots, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hγ
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact ⟨w, i, rfl⟩
  · rw [hdiv] at hi
    simp at hi

private theorem le_iSup_ggRankOneIn_of_tableBPos
    {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hcox : ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → r ∈ ggCoxRefl M e)
    {t : StatedLieTag} {n f : ℕ} (hgen : ggSub (ggU t n f).D (ggU t n f).D.roots = ⊤)
    (hdiv : (ggU t n f).D.divisible = ∅) {ψ : (ggU t n f).K →* G} (hrange : ψ.range = X)
    (hpos : GGTableBPos p Bs X t n f ψ) :
    X ≤ ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
      ggRankOneIn X Bs r := by
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  conv_lhs => rw [← hrange]
  rw [MonoidHom.range_eq_map, ← hgen, ggSub]
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, i, rfl⟩ := exists_weylAction_of_mem_roots' (ggU t n f).D hdiv hγ
  have hlevi := hεlevi w i
  simp only [ggRootLevi] at hlevi
  refine le_trans (Subgroup.map_mono (le_sup_left : (ggU t n f).D.rootGroup
    (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ≤
    (ggU t n f).D.rootGroup (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) ⊔
    (ggU t n f).D.rootGroup (-(weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))))) ?_
  rw [← hlevi]
  refine le_iSup₂ (f := fun r (_ : r ∈ {r : MulAut ↥Bs |
      r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}) => ggRankOneIn X Bs r) _ ⟨?_, ?_⟩
  · exact (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2
  · refine hcox _ (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2 ?_
    have hconj : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
          ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
          ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)⁻¹ := by
      simp [map_mul, map_inv]
    rw [hconj]
    exact (hεrefl i).conj ((ε w : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)

private theorem ggF4QGeFour_coxRefl_of_isReflection {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    (e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hX : X = L ∨ X = K) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → r ∈ ggCoxRefl CoxeterMatrix.F₄ e := by
  intro r hrX hr
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
  obtain ⟨hp, hp2, -⟩ := hβ
  have hrA : r ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hX with rfl | rfl
    · exact Subgroup.mem_sup_left hrX
    · exact Subgroup.mem_sup_right hrX
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    have h := Fintype.card_congr e'
    simp at h
  obtain ⟨i, g, hig⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hEl hNT _
    hAind (Fin 4) CoxeterMatrix.F₄ hpres.1 hG2 e hpres.2 ⟨r, hrA⟩ hr
  exact ⟨g, i, congrArg Subtype.val hig⟩

theorem ggF4QGeFourGenInput_of_kgPos
    (row : GGF4QGeFourRow) (hKG : GGF4QGeFourKGPosInput row) : GGF4QGeFourGenInput row := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow X hX
  have hcox := ggF4QGeFour_coxRefl_of_isReflection hcfg e hpres hX
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  refine le_antisymm ?_ (iSup₂_le fun r _ => ggRankOneIn_le X Bs r)
  obtain ⟨t, n, hgen, hdiv, ψ, -, hrange, hposX⟩ : ∃ (t : StatedLieTag) (n : ℕ),
      ggSub (ggU t n f).D (ggU t n f).D.roots = ⊤ ∧ (ggU t n f).D.divisible = ∅ ∧
        GGTableBPosImage p Bs t n f X := by
    cases row with
    | S1 =>
      have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, by omega, by omega, by simp⟩
      refine ⟨.PSp, 3, (ggTagFacts_PSp hadm (by decide)).2.2.1, rfl, ?_⟩
      rcases hX with rfl | rfl
      · exact hpos.1
      · exact hpos.2
    | S2 =>
      have hf1 : 1 ≤ f := by omega
      have hXpos : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨
          GGTableBPosImage p Bs .PSU 6 f X := by
        rcases hX with rfl | rfl
        · exact Or.inl hpos.1
        · exact Or.symm hpos.2
      rcases hXpos with hXpos | hXpos
      · have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, hf1, le_rfl⟩
        exact ⟨.POmegaMinus, 4, (ggTagFacts_POmegaMinus hadm (by decide)).2.2.1, rfl, hXpos⟩
      · have hadm : StatedLieAdmissible .PSU 6 2 f := ⟨Nat.prime_two, hf1, by omega, by simp⟩
        refine ⟨.PSU, 6, (ggTagFacts_PSU hadm (by decide)).2.2.1, ?_, hXpos⟩
        have hD : ggU .PSU 6 f =
            ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6,
              Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) 6⟩ := by
          simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
        rw [hD]
        show Unitary.divisible 6 = ∅
        rw [Unitary.divisible, if_pos (by decide)]
  exact le_iSup_ggRankOneIn_of_tableBPos e hcox hgen hdiv hrange hposX

end CFSG.StandardType

end
