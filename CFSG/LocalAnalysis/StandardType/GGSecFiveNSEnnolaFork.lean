module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusFork (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ a₀ ∈ ggTorusReflSet p A, ∃ a₁ ∈ ggTorusReflSet p A, ∃ a₂ ∈ ggTorusReflSet p A,
    ∃ a₃ ∈ ggTorusReflSet p A,
    orderOf (a₀ * a₁) = 3 ∧ orderOf (a₀ * a₂) = 3 ∧ orderOf (a₀ * a₃) = 3 ∧
    orderOf (a₁ * a₂) = 2 ∧ orderOf (a₁ * a₃) = 2 ∧ orderOf (a₂ * a₃) = 2

@[expose] def GGRowFork (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A

@[expose] def GGRowForkAt (S : ℕ → LargeEvenLabel → Prop) (r : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A

theorem ggX_fork_of_lift {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hQ : GGTorusFork p (ggGamma X hN).range)
    (hlift : ∀ a ∈ ggTorusReflSet p (ggGamma X hN).range,
      ∃ c ∈ ggAutomizer X Bs, GGIsReflection p c ∧ GGOverGamma hN c a) :
    ∃ c₀ ∈ ggAutomizer X Bs, ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs,
      ∃ c₃ ∈ ggAutomizer X Bs, GGIsReflection p c₀ ∧ GGIsReflection p c₁ ∧
        GGIsReflection p c₂ ∧ GGIsReflection p c₃ ∧
        3 ∣ orderOf (c₀ * c₁) ∧ 3 ∣ orderOf (c₀ * c₂) ∧ 3 ∣ orderOf (c₀ * c₃) ∧
        2 ∣ orderOf (c₁ * c₂) ∧ 2 ∣ orderOf (c₁ * c₃) ∧ 2 ∣ orderOf (c₂ * c₃) := by
  obtain ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, a₃, ha₃, h01, h02, h03, h12, h13, h23⟩ := hQ
  obtain ⟨c₀, hc₀, hr₀, hov₀⟩ := hlift a₀ ha₀
  obtain ⟨c₁, hc₁, hr₁, hov₁⟩ := hlift a₁ ha₁
  obtain ⟨c₂, hc₂, hr₂, hov₂⟩ := hlift a₂ ha₂
  obtain ⟨c₃, hc₃, hr₃, hov₃⟩ := hlift a₃ ha₃
  refine ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hr₀, hr₁, hr₂, hr₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h01 ▸ (hov₀.mul hov₁).orderOf_dvd
  · exact h02 ▸ (hov₀.mul hov₂).orderOf_dvd
  · exact h03 ▸ (hov₀.mul hov₃).orderOf_dvd
  · exact h12 ▸ (hov₁.mul hov₂).orderOf_dvd
  · exact h13 ▸ (hov₁.mul hov₃).orderOf_dvd
  · exact h23 ▸ (hov₂.mul hov₃).orderOf_dvd

theorem ggX_exists_fork (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hInn : GGInnerDiagOn Bs X) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A) :
    ∃ c₀ ∈ ggAutomizer X Bs, ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs,
      ∃ c₃ ∈ ggAutomizer X Bs, GGIsReflection p c₀ ∧ GGIsReflection p c₁ ∧
        GGIsReflection p c₂ ∧ GGIsReflection p c₃ ∧
        3 ∣ orderOf (c₀ * c₁) ∧ 3 ∣ orderOf (c₀ * c₂) ∧ 3 ∣ orderOf (c₀ * c₃) ∧
        2 ∣ orderOf (c₁ * c₂) ∧ 2 ∣ orderOf (c₁ * c₃) ∧ 2 ∣ orderOf (c₂ * c₃) := by
  obtain ⟨hN, hQ, hlift⟩ :=
    ggX_exists_overGamma_lift hRig hcfg hX hInn hlab hhas (fun _ _ A => GGTorusFork p A) hF
  exact ggX_fork_of_lift hN hQ hlift

theorem ggX_exists_overGamma_lift_of_card (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p r : ℕ} (hr3 : 3 ≤ r) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hInn : GGInnerDiagOn Bs X)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (Q : ∀ (L' : Type) [Group L'], Subgroup (MulAut L') → Prop)
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ r ≤ Nat.card (ggGamma X hN).range)
    (hF : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → Q L' A) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G), Q ↥X (ggGamma X hN).range ∧
      ∀ a ∈ ggTorusReflSet p (ggGamma X hN).range,
        ∃ c ∈ ggAutomizer X Bs, GGIsReflection p c ∧ GGOverGamma hN c a := by
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInn
  obtain ⟨R, _, θ, I, F, hBsI, hfr⟩ := exists_datum_of_label hRig hInn hlab hhas hF hN
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hTB := ggTorusTBGroup_of_card hcfg hr3 hInn.1 θ hN hBsI (hrk hN)
  refine ⟨hN, hfr X (ggQuotHom θ) (ggGamma X hN).range hTB, ?_⟩
  rintro _ ⟨n, hn, hW, rfl, hr'⟩
  obtain ⟨g, hgK, hg, hrefl, hov⟩ :=
    exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN hW hn hr'
  exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgK hg, hrefl, hov⟩

theorem ggX_exists_fork_of_card (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p r : ℕ} (hr3 : 3 ≤ r) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hInn : GGInnerDiagOn Bs X)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ r ≤ Nat.card (ggGamma X hN).range)
    (hF : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A) :
    ∃ c₀ ∈ ggAutomizer X Bs, ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs,
      ∃ c₃ ∈ ggAutomizer X Bs, GGIsReflection p c₀ ∧ GGIsReflection p c₁ ∧
        GGIsReflection p c₂ ∧ GGIsReflection p c₃ ∧
        3 ∣ orderOf (c₀ * c₁) ∧ 3 ∣ orderOf (c₀ * c₂) ∧ 3 ∣ orderOf (c₀ * c₃) ∧
        2 ∣ orderOf (c₁ * c₂) ∧ 2 ∣ orderOf (c₁ * c₃) ∧ 2 ∣ orderOf (c₂ * c₃) := by
  obtain ⟨hN, hQ, hlift⟩ := ggX_exists_overGamma_lift_of_card hRig hr3 hcfg hInn hlab hhas
    (fun _ _ A => GGTorusFork p A) hrk hF
  exact ggX_fork_of_lift hN hQ hlift

end CFSG.StandardType

end
