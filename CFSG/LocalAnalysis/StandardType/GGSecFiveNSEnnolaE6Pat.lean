module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusE6Pat (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ a₀ ∈ ggTorusReflSet p A, ∃ a₁ ∈ ggTorusReflSet p A, ∃ a₂ ∈ ggTorusReflSet p A,
    ∃ a₃ ∈ ggTorusReflSet p A, ∃ b₁ ∈ ggTorusReflSet p A, ∃ b₂ ∈ ggTorusReflSet p A,
    orderOf (a₀ * a₁) = 3 ∧ orderOf (a₀ * a₂) = 3 ∧ orderOf (a₀ * a₃) = 3 ∧
    orderOf (a₁ * a₂) = 2 ∧ orderOf (a₁ * a₃) = 2 ∧ orderOf (a₂ * a₃) = 2 ∧
    orderOf (b₁ * a₁) = 3 ∧ orderOf (b₁ * a₂) = 2 ∧ orderOf (b₁ * a₃) = 2 ∧
    orderOf (b₂ * a₂) = 3 ∧ orderOf (b₂ * a₃) = 2

@[expose] def GGRowE6Pat (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A

@[expose] def GGRowE6PatAt (S : ℕ → LargeEvenLabel → Prop) (r : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A

@[expose] def GGNoReflE6Pat {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ¬ ∃ c₀ ∈ ggAutomizer X Bs, ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs,
      ∃ c₃ ∈ ggAutomizer X Bs, ∃ d₁ ∈ ggAutomizer X Bs, ∃ d₂ ∈ ggAutomizer X Bs,
        GGIsReflection p c₀ ∧ GGIsReflection p c₁ ∧ GGIsReflection p c₂ ∧
        GGIsReflection p c₃ ∧ GGIsReflection p d₁ ∧ GGIsReflection p d₂ ∧
        3 ∣ orderOf (c₀ * c₁) ∧ 3 ∣ orderOf (c₀ * c₂) ∧ 3 ∣ orderOf (c₀ * c₃) ∧
        2 ∣ orderOf (c₁ * c₂) ∧ 2 ∣ orderOf (c₁ * c₃) ∧ 2 ∣ orderOf (c₂ * c₃) ∧
        3 ∣ orderOf (d₁ * c₁) ∧ 2 ∣ orderOf (d₁ * c₂) ∧ 2 ∣ orderOf (d₁ * c₃) ∧
        3 ∣ orderOf (d₂ * c₂) ∧ 2 ∣ orderOf (d₂ * c₃)

theorem ggX_e6Pat_of_lift {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hQ : GGTorusE6Pat p (ggGamma X hN).range)
    (hlift : ∀ a ∈ ggTorusReflSet p (ggGamma X hN).range,
      ∃ c ∈ ggAutomizer X Bs, GGIsReflection p c ∧ GGOverGamma hN c a) :
    ¬ GGNoReflE6Pat p Bs X := by
  obtain ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, a₃, ha₃, b₁, hb₁, b₂, hb₂,
    h01, h02, h03, h12, h13, h23, hb11, hb12, hb13, hb22, hb23⟩ := hQ
  obtain ⟨c₀, hc₀, hr₀, hov₀⟩ := hlift a₀ ha₀
  obtain ⟨c₁, hc₁, hr₁, hov₁⟩ := hlift a₁ ha₁
  obtain ⟨c₂, hc₂, hr₂, hov₂⟩ := hlift a₂ ha₂
  obtain ⟨c₃, hc₃, hr₃, hov₃⟩ := hlift a₃ ha₃
  obtain ⟨d₁, hd₁, hs₁, hovb₁⟩ := hlift b₁ hb₁
  obtain ⟨d₂, hd₂, hs₂, hovb₂⟩ := hlift b₂ hb₂
  refine not_not.2 ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, d₁, hd₁, d₂, hd₂,
    hr₀, hr₁, hr₂, hr₃, hs₁, hs₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h01 ▸ (hov₀.mul hov₁).orderOf_dvd
  · exact h02 ▸ (hov₀.mul hov₂).orderOf_dvd
  · exact h03 ▸ (hov₀.mul hov₃).orderOf_dvd
  · exact h12 ▸ (hov₁.mul hov₂).orderOf_dvd
  · exact h13 ▸ (hov₁.mul hov₃).orderOf_dvd
  · exact h23 ▸ (hov₂.mul hov₃).orderOf_dvd
  · exact hb11 ▸ (hovb₁.mul hov₁).orderOf_dvd
  · exact hb12 ▸ (hovb₁.mul hov₂).orderOf_dvd
  · exact hb13 ▸ (hovb₁.mul hov₃).orderOf_dvd
  · exact hb22 ▸ (hovb₂.mul hov₂).orderOf_dvd
  · exact hb23 ▸ (hovb₂.mul hov₃).orderOf_dvd

theorem ggX_exists_e6Pat (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hInn : GGInnerDiagOn Bs X) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A) :
    ¬ GGNoReflE6Pat p Bs X := by
  obtain ⟨hN, hQ, hlift⟩ :=
    ggX_exists_overGamma_lift hRig hcfg hX hInn hlab hhas (fun _ _ A => GGTorusE6Pat p A) hF
  exact ggX_e6Pat_of_lift hN hQ hlift

theorem ggX_exists_e6Pat_of_card (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p r : ℕ} (hr3 : 3 ≤ r) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hInn : GGInnerDiagOn Bs X)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ r ≤ Nat.card (ggGamma X hN).range)
    (hF : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusE6Pat p A) :
    ¬ GGNoReflE6Pat p Bs X := by
  obtain ⟨hN, hQ, hlift⟩ := ggX_exists_overGamma_lift_of_card hRig hr3 hcfg hInn hlab hhas
    (fun _ _ A => GGTorusE6Pat p A) hrk hF
  exact ggX_e6Pat_of_lift hN hQ hlift

theorem ggX_row_absurd_of_noReflE6Pat (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hF : GGRowE6Pat S) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hNP : GGNoReflE6Pat p Bs X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  exact ggX_exists_e6Pat hRig hcfg hX hInn hΛ hhas (hF p hp hodd lab hΛ hS) hNP

theorem ggX_row_absurd_of_noReflE6PatAt (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} {r : ℕ} (hr3 : 3 ≤ r) (hF : GGRowE6PatAt S r)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hNP : GGNoReflE6Pat p Bs X)
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ r ≤ Nat.card (ggGamma X hN).range)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  exact ggX_exists_e6Pat_of_card hRig hr3 hcfg.1.1 hInn hΛ hhas hrk (hF p hp hodd lab hΛ hS) hNP

end CFSG.StandardType

end
