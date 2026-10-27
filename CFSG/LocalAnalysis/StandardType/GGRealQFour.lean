module

public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95C
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.Assembly.OpenBridges
public import CFSG.Goldschmidt.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.ComponentClassification Subgroup

@[expose] def GGReflRealizedIn {G : Type} [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) :
    Prop :=
  ∀ t ∈ ggAutomizer X Bs, GGIsReflection p t →
    ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧
      GLAPComponent p (X ⊓ centralizer (ggFixG Bs t : Set G)) Jt

theorem mem_ggFixG_of_mem_ggAutomizer {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {z : G} (hzBs : z ∈ Bs)
    (hXz : X ≤ centralizer ({z} : Set G)) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs) :
    z ∈ ggFixG Bs t := by
  obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp ht
  have hc : g * z = z * g := mem_centralizer_singleton_iff.mp (hXz hgX)
  refine ⟨⟨z, hzBs⟩, Subtype.ext ((hg ⟨z, hzBs⟩).trans ?_), rfl⟩
  change g * z * g⁻¹ = z
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem ggRealized_of_reflRealizedIn {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} {z : G}
    (hzBs : z ∈ Bs) (hX : GLAPComponent p (centralizer ({z} : Set G)) X)
    (hR : GGReflRealizedIn p Bs X) {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer X Bs)
    (ht : GGIsReflection p t) : GGRealized p Bs t := by
  obtain ⟨Jt, hind, hJ⟩ := hR t htA ht
  have hXz := ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp hX).1
  have hzE := mem_ggFixG_of_mem_ggAutomizer hzBs hXz htA
  obtain ⟨hle, hpc⟩ := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp (CFSG.LocalAnalysis.GLTheoremA.S9.glaPComponent_centralizer hp hX hzE hJ)
  exact ⟨Jt, hind, hle, hpc⟩

theorem ggRealized_of_reflRealizedIn_L {G : Type} [Group G] [Finite G]
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hR : GGReflRealizedIn p Bs L)
    {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer L Bs) (ht : GGIsReflection p t) :
    GGRealized p Bs t := by
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  obtain ⟨hI, -, hDJ⟩ := hcfg
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  obtain ⟨-, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  exact ggRealized_of_reflRealizedIn hp hxBs
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ L).mp hLpc) hR htA ht

@[expose] def GGReflRealizedQFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs →
      ∀ X : Subgroup G, (X = L ∨ ∃ y, GGNbr p B x D J y X) →
        GGInnerDiagOnLabel GGLabQFour p Bs X → GGReflRealizedIn p Bs X

theorem ggRealInputQFour_of_reflRealized (hP : GGStdSubPrimeInput)
    (hR : GGReflRealizedQFourInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
        GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGInnerDiagOnLabel GGLabQFour p Bs L → GGInnerDiagOnLabel GGLabQFour p Bs K →
        GGReflGenerated p (ggAutomizer K Bs) → GGScalarsPmOne Bs → ∀ [Fact p.Prime]
        (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
        (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
        (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
        (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
        GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
        (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
        (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
        LinearIndependent (ZMod p) (ggOptFam ha h) →
        ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
        ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
        (∀ i, GGRealized p Bs (φ i)) ∧ GGRealized p Bs φa := by
  intro G _ _ p B Bs x L D J hcfg _ hInn hNT y K hnb hLq hKq _ _ hfact Λ _ _ M C V _ _ ι φ φa h α
    ha αa b c _ _ hF hφ hφa _ hAL hAK
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hpr : p.Prime := hfact.out
  have hRL := hR G p B Bs x L D J hcfg hInn hNT L (Or.inl rfl) hLq
  have hRK := hR G p B Bs x L D J hcfg hInn hNT K (Or.inr ⟨y, hnb⟩) hKq
  refine ⟨fun i => ?_, ?_⟩
  · have hmem : φ i ∈ ggAutomizer L Bs := by
      rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
    have hr : GGIsReflection p (φ i) :=
      ggIsReflection_of_eq_reflection hp2 ι (hF.self i) (ggLin_eq_reflection ι (hF.self i) (hφ i))
    exact ggRealized_of_reflRealizedIn_L hP hcfg hRL hmem hr
  · have hmem : φa ∈ ggAutomizer K Bs := by
      rw [hAK]; exact Subgroup.subset_closure (Or.inr rfl)
    have hr : GGIsReflection p φa :=
      ggIsReflection_of_eq_reflection hp2 ι hF.aa (ggLin_eq_reflection ι hF.aa hφa)
    have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
    have hKpc : LargeEvenPComponent p (centralizer ({y} : Set G)) K := hnb.1.2.2.2.2.1
    exact ggRealized_of_reflRealizedIn hpr hyBs
      ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ K).mp hKpc) hRK hmem hr

private theorem two_le_n_of_ggLabelIso_nbr {p : ℕ} {lab labJ labK : LargeEvenLabel}
    (hrow : GGTablePRow p labJ labK) (hiso : GGLabelIso lab labJ) (h2 : 2 ≤ lab.n) :
    2 ≤ labJ.n := by
  rcases hiso with rfl | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h2
  · omega
  all_goals first
    | (rw [h]; exact h2)
    | (rw [h]; dsimp only; omega)
    | (exfalso; rw [h] at hrow; simp [GGTablePRow] at hrow)

theorem ggNbr_qFour_of_five {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInput) (hA8 : GGForkNbrSevenExcl') {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs)
    (hq : GGInnerDiagOnLabel GGLabQFour p Bs L) (hp5 : 5 ≤ p) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hRG : GGReflGenerated p (ggAutomizer K Bs)) :
    GGInnerDiagOnLabel GGLabQFour p Bs K := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  by_cases hok : GGInnerDiagOnLabel GGLabNbrOk p Bs K
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨h, hP⟩ =>
      ⟨h.resolve_right (fun ⟨_, _, h3, _⟩ => by omega), hP⟩) hok
  · exfalso
    obtain ⟨labK, hKΛ, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y K hnb)
    obtain ⟨labL, labJ, -, hq4, -, hJΛ, hdvd, hhasJ⟩ :=
      ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
    have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
    obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
      hTP G p B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb labJ labK hJΛ hKΛ hhasJ hhasK
    have hj2 : 2 ≤ jlab.n :=
      two_le_n_of_ggLabelIso_nbr hrow (hRig labJ jlab _ hJΛ hjΛ hhasJ hhasJ1) hJ2
    have hnok : ¬ GGLabNbrOk p klab := fun hok' => hok (largeEvenMarking_mono
      (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok', hP⟩)
      (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hkΛ hhasK1))
    rcases ggTablePRow_fieldTwo hp hrow hkΛ hj2 hnok with ⟨h3, -⟩ | ⟨rfl, rfl⟩
    · omega
    · exact hA8 G B Bs x L D J hcfg hOp hInn hNT y K hnb hRG hhasK1

@[expose] def GGRealInputFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGInnerDiagOnLabel GGLabQFour p Bs L → 5 ≤ p →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsPmOne Bs → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (φa : MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (ha : V) (αa : Module.Dual (ZMod p) V) (b c : Λ),
      GGIsWeylMatrix M → GGIntCartan M C → GGForkPairing C b c h α ha αa →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      (∀ w, ggLin (p := p) ι φa w = w - αa w • ha) →
      LinearIndependent (ZMod p) (ggOptFam ha h) →
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
      ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}) →
      (∀ i, GGRealized p Bs (φ i)) ∧ GGRealized p Bs φa

theorem ggRealInputFive_of_reflRealized (hP : GGStdSubPrimeInput)
    (hR : GGReflRealizedQFourInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInput) (hA8 : GGForkNbrSevenExcl') : GGRealInputFive := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT y K hnb hLq hp5 hRG hsc hfact
  exact ggRealInputQFour_of_reflRealized hP hR G p B Bs x L D J hcfg hOp hInn hNT y K hnb hLq
    (ggNbr_qFour_of_five hRig hTCJ hTP hA8 hcfg hOp hInn hNT hLq hp5 hnb hRG) hRG hsc

end CFSG.StandardType
