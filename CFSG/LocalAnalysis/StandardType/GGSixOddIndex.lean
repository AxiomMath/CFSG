module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Elementary

variable {G : Type} [Group G]

theorem ggSix_inf_centralizer_le_normalizer (H : Subgroup G) (s : G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.centralizer {s} ≤
      Subgroup.normalizer ((H ⊓ Subgroup.centralizer {s} : Subgroup G) : Set G) := by
  intro m hm
  have hmH : m ∈ Subgroup.normalizer (H : Set G) := hm.1
  have hms : m * s = s * m := Subgroup.mem_centralizer_singleton_iff.mp hm.2
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.mp hmH z
  have h2 : z * s = s * z ↔ m * z * m⁻¹ * s = s * (m * z * m⁻¹) := by
    have hs' : m⁻¹ * s * m = s := by
      calc m⁻¹ * s * m = m⁻¹ * (s * m) := by group
        _ = s := by rw [← hms, inv_mul_cancel_left]
    have hs'' : m * s * m⁻¹ = s := by rw [hms, mul_inv_cancel_right]
    constructor
    · intro h
      calc m * z * m⁻¹ * s = m * z * (m⁻¹ * s * m) * m⁻¹ := by group
        _ = m * (z * s) * m⁻¹ := by rw [hs']; group
        _ = m * (s * z) * m⁻¹ := by rw [h]
        _ = m * s * m⁻¹ * (m * z * m⁻¹) := by group
        _ = s * (m * z * m⁻¹) := by rw [hs'']
    · intro h
      calc z * s = m⁻¹ * (m * z * m⁻¹ * (m * s * m⁻¹)) * m := by group
        _ = m⁻¹ * (m * z * m⁻¹ * s) * m := by rw [hs'']
        _ = m⁻¹ * (s * (m * z * m⁻¹)) * m := by rw [h]
        _ = m⁻¹ * s * m * z := by group
        _ = s * z := by rw [hs']
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem ggSix_isPGroup_zpowers_of_orderOf_eq_two {b : G} (hb : orderOf b = 2) :
    IsPGroup 2 (Subgroup.zpowers b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])

theorem ggSix_orderOf_conj (g r : G) : orderOf (g * r * g⁻¹) = orderOf r := by
  have ho := MulEquiv.orderOf_eq (MulAut.conj g) r
  rwa [MulAut.conj_apply] at ho

end Elementary

section Inputs

@[expose] def GGOuterInvolutionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank → ψ.range = G₀ →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → commutator ↥G₀ = ⊤ →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (G₀ : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
    ¬ (t = .F4 ∧ Odd f) →
    ∀ X : Subgroup G, G₀ ≤ X → X ≤ Subgroup.normalizer (G₀ : Set G) → Even (G₀.relIndex X) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      ∃ s ∈ X, s ∉ G₀ ∧ orderOf s = 2 ∧
        (∀ Q : Subgroup G, Q ≤ G₀ ⊓ Subgroup.centralizer {s} → IsPGroup 2 Q →
          G₀ ⊓ Subgroup.centralizer {s} ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥) ∧
        ∃ g ∈ G₀, s * (g * r * g⁻¹) = g * r * g⁻¹ * s ∧
          ∃ a ∈ G₀, a * s = s * a ∧ a * (g * r * g⁻¹) = g * r * g⁻¹ * a ∧ a ≠ 1 ∧
            Odd (orderOf a)

@[expose] def GGSixStepThreeCFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .F4 n f).K →* G), Odd f →
    GGSixCtxV2 p B Bs x L D J (ggU .F4 n f).D .F4 n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .F4 n f).D .F4 ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
          Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J))

theorem ggSix_relIndex_odd_of_outerInvolution (hKG : GGOuterInvolutionInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r)
    (hC : Subgroup.centralizer {r} ≤ ggM p B x L D J) (hF : ¬ (t = .F4 ∧ Odd f)) :
    Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨⟨-, -, -, hchar, -, hp, hS, -⟩, hcore⟩ := hctx
  obtain ⟨hBs, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf, hlie⟩, ⟨hBsN, hBsI⟩, -, -⟩ := hcore
  set G₀ := ggG0 p B x L D J with hG₀
  set M := ggM p B x L D J with hM
  have hcard : p ^ 4 ≤ Nat.card Bs := by
    obtain ⟨hpp, -, -, hrk⟩ := hp
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hrk
      _ = Nat.card B := hS.1.2.1.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  obtain ⟨s, hsM, -, hs2, hO2, g, hgG₀, hsr, a, haG₀, has, har, ha1, haodd⟩ :=
    hKG G t n f ψ G₀ hadm hrank hrange hker hperf hlie s1.1
      ⟨p, Bs, hp.1, hp.2.1, hBs.2.1, hcard, hBsN, hBsI⟩ hF M Subgroup.le_normalizer le_rfl hev
      r hch.rootInvolution
  have hrG₀ : r ∈ G₀ := hrange ▸ hch.mem_range
  have hgM : g ∈ M := Subgroup.le_normalizer hgG₀
  refine ggSix_false_of_charTwo (M := M) (Y := G₀ ⊓ Subgroup.centralizer {s})
    (b := g * r * g⁻¹) hchar hs2 inf_le_right hO2
    (ggSix_inf_centralizer_le_normalizer G₀ s) ⟨?_, ?_⟩ ?_ (centralizer_conj_le hC hgM)
    ⟨haG₀, Subgroup.mem_centralizer_singleton_iff.mpr has⟩ har haodd ha1
  · exact G₀.mul_mem (G₀.mul_mem hgG₀ hrG₀) (G₀.inv_mem hgG₀)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hsr.symm
  · exact ggSix_isPGroup_zpowers_of_orderOf_eq_two
      ((ggSix_orderOf_conj g r).trans hch.rootInvolution.1)

theorem ggSixStepThreeCInput_of_inputs (hKG : GGOuterInvolutionInput)
    (hF4 : GGSixStepThreeCFourInput) : GGSixStepThreeCInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC
  by_cases hF : t = .F4 ∧ Odd f
  · obtain ⟨rfl, hf⟩ := hF
    exact hF4 G p B Bs x L D J n f ψ hf hctx s1 s2 E r hch hC
  · exact ggSix_relIndex_odd_of_outerInvolution hKG hctx s1 hch hC hF

end Inputs

end CFSG.StandardType
