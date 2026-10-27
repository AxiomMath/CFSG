module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrXNotNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) →
      ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧
        k ∉ Subgroup.normalizer (Subgroup.zpowers x : Set G)

@[expose] def GGNbrLangInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I F θ =>
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧
                k * b₀ * k⁻¹ = e * b₀

@[expose] def GGNbrInnerXNotNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun _ _ _ I _ θ =>
          ggLAut K θ ⟨x, hxK⟩ ∈ I →
            ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧
              k ∉ Subgroup.normalizer (Subgroup.zpowers x : Set G)

section Proofs

variable {G : Type} [Group G] [Finite G]

theorem normalizer_and_not_normalizer_of_lang {p : ℕ} (hp : p.Prime) {Bs B₀ : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hB₀ : B₀ ≤ Bs) (hcard : Nat.card B₀ * p = Nat.card Bs)
    {b₀ k e : G} (hb₀ : b₀ ∈ Bs) (hb₀' : b₀ ∉ B₀) (hk : k ∈ Subgroup.centralizer (B₀ : Set G))
    (he : e ∈ B₀) (he1 : e ≠ 1) (hkb : k * b₀ * k⁻¹ = e * b₀) :
    k ∈ Subgroup.normalizer (Bs : Set G) ∧
      k ∉ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hkinv : k⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
    rw [inv_inv]
    exact NbrFieldLang.conj_mem_of_lang hp hBs hB₀ hcard hb₀ hb₀' hk he hkb hw
  refine ⟨by simpa using Subgroup.inv_mem _ hkinv, fun hkn => hb₀' ?_⟩
  have h1 : e * b₀ ∈ Subgroup.zpowers b₀ := by
    rw [← hkb]
    exact (Subgroup.mem_normalizer_iff.mp hkn b₀).mp (Subgroup.mem_zpowers b₀)
  have h2 : e ∈ Subgroup.zpowers b₀ := by
    have := (Subgroup.zpowers b₀).mul_mem h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers b₀))
    simpa using this
  have h3 := zpowers_eq_of_mem_of_ne_one (hBs.2 b₀ hb₀) h2 he1
  have h4 : b₀ ∈ Subgroup.zpowers e := h3 ▸ Subgroup.mem_zpowers b₀
  exact (Subgroup.zpowers_le.mpr he) h4

end Proofs

theorem ggXNotNormalInput_of_nbr (hnorm : GGBstarNbrNormalInput) (h : GGNbrXNotNormalInput) :
    GGXNotNormalInput := by
  intro G _ _ p B Bs x L D J hcfg hle
  obtain ⟨y, K, hK⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
  obtain ⟨k, -, hkN, hkx⟩ :=
    h G p B Bs x L D J hcfg y K hK (hnorm G p B Bs x L D J hcfg y K hK)
  exact hkx (hle hkN)

theorem ggNbrXNotNormal_of_lang (hgraph : GGNbrGraphInput) (hlang : GGNbrLangInput)
    (hinner : GGNbrInnerXNotNormalInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ Subgroup.normalizer (Bs : Set G),
      k ∉ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have h5 := (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K (isNeighborOf_of_ggNbr hcfg.2.2 hK)).2
  have hM1 := hgraph G p B Bs x L D J hcfg y K hK hN _ h5
  have hM2 := hlang G p B Bs x L D J hcfg y K hK hN _ hM1
  have hM3 := hinner G p B Bs x L D J hcfg y K hK hN (hN hxBs) _ hM2
  obtain ⟨-, lab, -, hraw⟩ := hM3
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hall⟩, hQlang⟩, hQinner⟩ := largeEvenRawDatum_exists hraw
  by_cases hxI : ggLAut K θ ⟨x, hN hxBs⟩ ∈ I
  · obtain ⟨k, -, hkN, hkx⟩ := hQinner hxI
    exact ⟨k, hkN, hkx⟩
  · obtain ⟨B₀, hB₀, hcard, hx₀, k, hk, e, he, he1, hkb⟩ := hQlang hall x hxBs hxI
    obtain ⟨hkN, hkx⟩ :=
      normalizer_and_not_normalizer_of_lang hp hBs hB₀ hcard hxBs hx₀ hk he he1 hkb
    exact ⟨k, hkN, hkx⟩

theorem ggXNotNormalInput_of_lang (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hlang : GGNbrLangInput) (hinner : GGNbrInnerXNotNormalInput) : GGXNotNormalInput := by
  intro G _ _ p B Bs x L D J hcfg hle
  obtain ⟨y, K, hK⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
  obtain ⟨k, hkN, hkx⟩ := ggNbrXNotNormal_of_lang hgraph hlang hinner hcfg hK
    (hnorm G p B Bs x L D J hcfg y K hK)
  exact hkx (hle hkN)

theorem ggNbrFieldTransvectionInput_of_lang (hlang : GGNbrLangInput) :
    GGNbrFieldTransvectionInput := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  refine largeEvenMarking_mono ?_ (hlang G p B Bs x L D J hcfg y K hK hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  refine ⟨hPθ, fun hall ⟨b, hb, hbI⟩ => ?_⟩
  obtain ⟨B₀, hB₀, hcard, hb₀, k, hk, e, he, he1, hkb⟩ := hQ hall b hb hbI
  exact NbrFieldLang.exists_transvection_of_lang hp hBs hB₀ hcard hb hb₀ hk he he1 hkb

end CFSG.StandardType

end
