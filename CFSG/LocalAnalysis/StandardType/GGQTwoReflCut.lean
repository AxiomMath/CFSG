module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2Ind {G : Type} [Group G] (Bs : Subgroup G) (g : G) (φ : MulAut ↥Bs) : Prop :=
  g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹

@[expose] def GGQ2MovesX {G : Type} [Group G] (Bs : Subgroup G) (x : G) (φ : MulAut ↥Bs) : Prop :=
  ∃ b : ↥Bs, (b : G) = x ∧ φ b ≠ b

@[expose] def GGQ2CentreNotIn {G : Type} [Group G] (Bs D : Subgroup G) (φ : MulAut ↥Bs) : Prop :=
  ∃ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∉ D

@[expose] def GGQ2EForm {G : Type} [Group G] (Bs J : Subgroup G) (φ : MulAut ↥Bs) : Prop :=
  (∀ b : ↥Bs, ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G)) ∧
    ∀ h ∈ J, h ∈ Subgroup.normalizer (Bs : Set G) → ∀ b c : ↥Bs,
      (c : G) = (b : G)⁻¹ * (h * b * h⁻¹) → φ c = c

@[expose] def GGQ2GammaX {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  ∀ g ∈ Subgroup.normalizer (Bs : Set G), g * x * g⁻¹ ∈ Subgroup.zpowers x →
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2P3 {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (x : G) : Prop :=
  ∀ g ∈ Subgroup.normalizer (Bs : Set G), ∃ r ∈ Subgroup.closure
      {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ},
    Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers (r * x * r⁻¹)

@[expose] def GGQ2ReflMoveX {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2LieRank (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .A | .twA | .B | .C | .D | .twD => lab.rank
  | .E6 | .twE6 => 6
  | .E7 => 7
  | .E8 => 8
  | .F4 | .twF4 | .twF4der | .triD4 => 4
  | .G2 | .G2der | .twB2 | .B2der => 2

@[expose] def GGQ2TBFull {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G) : Prop :=
  ∃ labL : LargeEvenLabel, GGLabQTwo p labL ∧
    LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) ∧
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ GGQ2LieRank labL

@[expose] def GGQ2CavOfTBFull : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQ2TBFull p Bs L → 4 ∣ Nat.card (ggAutomizer J Bs)

@[expose] def GGQ2TBHeart {G : Type} [Group G] (p : ℕ) (Bs L : Subgroup G) : Prop :=
  ∃ labL : LargeEvenLabel, GGLabQTwo p labL ∧
    LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) ∧
    ((labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6) ∧
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ (GGQ2LieRank labL - 1)

@[expose] def GGQ2CavOfTBHeart : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      GGQ2TBHeart p Bs L → ∀ M : GGQ2LDatum p Bs L x, M.HeartShape →
        4 ∣ Nat.card (ggAutomizer J Bs)

@[expose] def GGQ2ReflEInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      GGQ2CentreNotIn Bs D φ → GGQ2EForm Bs J φ →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2ReflKInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      GGQ2CentreNotIn Bs D φ → ¬ GGQ2EForm Bs J φ →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → (∀ c : ↥Bs, (c : G) = y → φ c = c) →
        (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) →
        (¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) →
          g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2ReflRestInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      (¬ GGQ2CentreNotIn Bs D φ ∨ (¬ GGQ2EForm Bs J φ ∧ ¬ ∃ (y : G) (K : Subgroup G),
        GGNbr p B x D J y K ∧ (∀ c : ↥Bs, (c : G) = y → φ c = c) ∧ (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) ∧
        ¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹)) →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggQ2ReflMoveX_of_split {G : Type} [Group G] [Finite G] (hE : GGQ2ReflEInput)
    (hK : GGQ2ReflKInput) (hRest : GGQ2ReflRestInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : ¬ GGQTwoI1 Bs D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs)) :
    GGQ2ReflMoveX p B Bs x L D J := by
  intro g φ hInd hR hM
  classical
  by_cases hC : GGQ2CentreNotIn Bs D φ
  · by_cases hEF : GGQ2EForm Bs J φ
    · exact hE hS hp hI1 hCav g φ hInd hR hM hC hEF
    · by_cases hW : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
          (∀ c : ↥Bs, (c : G) = y → φ c = c) ∧ (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) ∧
          ¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹
      · obtain ⟨y, K, hN, hy, hAK, hO⟩ := hW
        exact hK hS hp hI1 hCav g φ hInd hR hM hC hEF y K hN hy hAK hO
      · exact hRest hS hp hI1 hCav g φ hInd hR hM (Or.inr ⟨hEF, hW⟩)
  · exact hRest hS hp hI1 hCav g φ hInd hR hM (Or.inl hC)

theorem ggQ2_normalizer_le_of_refl {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hx : x ∈ Bs) (hΓ : GGQ2GammaX p B Bs x L D J)
    (hP3 : GGQ2P3 p Bs x) (hR : GGQ2ReflMoveX p B Bs x L D J) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  intro g hg
  obtain ⟨r, hr, hgr⟩ := hP3 g hg
  have hgen : {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ} ⊆
      (Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.normalizer (ggG0 p B x L D J : Set G) :
        Subgroup G) := by
    rintro h ⟨φ, hInd, hRf⟩
    refine ⟨hInd.1, ?_⟩
    by_cases hm : GGQ2MovesX Bs x φ
    · exact hR h φ hInd hRf hm
    · apply hΓ h hInd.1
      have hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
        by_contra hne
        exact hm ⟨⟨x, hx⟩, rfl, hne⟩
      have h2 := hInd.2 ⟨x, hx⟩
      rw [hfix] at h2
      rw [← h2]
      exact Subgroup.mem_zpowers x
  have hr' := (Subgroup.closure_le _).mpr hgen hr
  have hmem : g * x * g⁻¹ ∈ Subgroup.zpowers (r * x * r⁻¹) := hgr ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have key : (r⁻¹ * g) * x * (r⁻¹ * g)⁻¹ = x ^ k := by
    have e : (r⁻¹ * g) * x * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * x * g⁻¹) * r := by group
    rw [e, ← hk, conj_zpow]
    group
  have hrg : r⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hr'.1) hg
  have h1 := hΓ (r⁻¹ * g) hrg (key ▸ Subgroup.zpow_mem_zpowers x k)
  have : g = r * (r⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem _ hr'.2 h1

theorem ggQ2_x_mem_Bs {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) : x ∈ Bs := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, -⟩ := hcfg
  have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  exact hBstar.1 hSst.2.1

end CFSG.StandardType

end
