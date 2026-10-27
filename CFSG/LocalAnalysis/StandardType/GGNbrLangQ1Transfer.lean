module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferMark
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

private theorem l02qj14_ggInducedAut_mem {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ)
    (b : ↥Bs) : ggInducedAut θ (ggGamma L hN b) ∈ I := by
  obtain ⟨φ, hφI, hφ⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
  have hφ' : LargeEvenInduces θ (fun l l' : ↥L => l' = ggGamma L hN b l) φ := by
    intro l l' hl
    have h2 : (l' : G) = (((b : G)⁻¹))⁻¹ * (l : G) * ((b : G)⁻¹) := by
      rw [hl, ggGamma_coe]
      group
    exact hφ l l' h2
  have hEq : ggInducedAut θ (ggGamma L hN b) = φ := by
    ext r
    obtain ⟨z, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact (hφ' l (ggGamma L hN b l) rfl).symm
  rw [hEq]
  exact hφI

private theorem l02qj14_ggInducedInn_range {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {I : Set (MulAut R)}
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ) :
    GGInducedInn (ggGamma L hN).range θ I := by
  intro a ha
  obtain ⟨b, rfl⟩ := ha
  exact l02qj14_ggInducedAut_mem hN θ hact b

private theorem l02qj14_isElemAbelian_range {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hE : IsElemAbelian p Bs) {L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian p (ggGamma L hN).range := by
  haveI : IsMulCommutative ↥Bs := hE.1
  exact isElemAbelian_range
    (fun a b : ↥Bs => mul_comm' a b)
    (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2))
    (ggGamma L hN)

private theorem l02qj14_le_normalizer_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Bs ≤ Subgroup.normalizer (J : Set G) :=
  GGDichotomy.le_normalizer_stdSub
    (fun a ha b hb => by
      haveI : IsMulCommutative ↥Bs := hcfg.2.1.2.1.1
      have h := mul_comm' (⟨a, ha⟩ : ↥Bs) (⟨b, hb⟩ : ↥Bs)
      simpa using congrArg Subtype.val h)
    hcfg.2.1.1 hcfg.2.2.1 hN

theorem q1SelectedTransfer_of_toral
    {Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop}
    {S : ℕ → LargeEvenLabel → Prop} {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hT : Q1ToralActionTransfer Toral S Rel)
    (hTor : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J →
      GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
        S p lab → ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          (∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
          Toral R ((ggGamma L hN).range.map (ggInducedAut θ)))) :
    Q1SelectedTransfer S Rel := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hS : S p lab
  · obtain ⟨-, -, -, -, -, hβ, -, -⟩ := hcfg.1
    have hp : p.Prime := hβ.1
    have hp2 : p ≠ 2 := hβ.2.1
    have hP_S : LargeEvenMarking L (fun lab' R _ I F θ => P lab' R I F θ ∧ S p lab') :=
      ⟨hperf, lab, hlab, largeEvenRawDatum_mono (fun R _ I F hh => by
        obtain ⟨hs, hna, θ, hPθ⟩ := hh
        exact ⟨hs, hna, θ, hPθ, hS⟩) hraw⟩
    obtain ⟨hperf₂, lab₂, hlab₂, hraw₂⟩ :=
      hTor G p B Bs x L D J hcfg (fun lab' R _ I F θ => P lab' R I F θ ∧ S p lab') hP_S
    obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw₂
    obtain ⟨-, -, θ₀, hPS₀, -⟩ := hQ₀
    obtain ⟨-, hS₂⟩ := hPS₀
    refine ⟨hperf₂, lab₂, hlab₂, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_)
      ((hT p hp hp2 lab₂ hlab₂ hS₂) _ hraw₂)
    obtain ⟨hhQ, hP'⟩ := hh
    obtain ⟨hs, hna, hEx⟩ := hhQ
    obtain ⟨θ, hPSθ, hQtorθ⟩ := hEx
    obtain ⟨hPθ, hSθ⟩ := hPSθ
    refine ⟨hs, hna, θ, hPθ, ?_⟩
    intro _ hN hact
    obtain ⟨y, u, -, hyu, huord, hcomm, hJL, hJcomp⟩ := q1_fixed_component_data hcfg hN
    have hNJ := l02qj14_le_normalizer_J hcfg hN
    have hAb : IsElemAbelian p (ggGamma L hN).range :=
      l02qj14_isElemAbelian_range hcfg.2.1.2.1 hN
    have hInn : GGInducedInn (ggGamma L hN).range θ I :=
      l02qj14_ggInducedInn_range hN θ hact
    have hmemA : u ∈ (ggGamma L hN).range := ⟨y, hyu⟩
    have htor : Toral R ((ggGamma L hN).range.map (ggInducedAut θ)) := hQtorθ hSθ hN hact
    have hconc : Q1ComponentConclusion p lab₂ (ggGamma L hN).range (J.subgroupOf L) Rel :=
      hP' (↥L) hperf₂ θ (ggGamma L hN).range hAb hInn htor u hmemA huord
        (J.subgroupOf L) hJcomp
    exact q1_marking_of_component_conclusion hN hJL hNJ hconc
  · refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hPθ⟩ := hh
    exact ⟨hs, hna, θ, hPθ, fun hh' => absurd hh' hS⟩

end CFSG.StandardType
