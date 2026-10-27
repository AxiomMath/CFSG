module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggNbrLangS1CoreAux_mem_Bs_of_fixed {G : Type} [Group G] {p : ℕ} {Bs K : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {e : ↥K}
    (hefix : ∀ α ∈ (ggBsAut hN).range, α e = e) (hep : e ^ p = 1) : (e : G) ∈ Bs := by
  refine hSC _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) (congrArg Subtype.val hep)
  have h : ggBsAut hN ⟨b, hb⟩ e = e := hefix (ggBsAut hN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
  have h1 : (b : G) * (e : G) * (b : G)⁻¹ = (e : G) := congrArg Subtype.val h
  calc (b : G) * (e : G) = (b : G) * (e : G) * (b : G)⁻¹ * (b : G) := by group
    _ = (e : G) * (b : G) := by rw [h1]

private theorem ggNbrLangS1CoreAux_conj_of_fixed {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {b : ↥Bs} {k : ↥K}
    (h : ggBsAut hN b k = k) : (b : G) * (k : G) = (k : G) * (b : G) := by
  have h1 : (b : G) * (k : G) * (b : G)⁻¹ = (k : G) := congrArg Subtype.val h
  calc (b : G) * (k : G) = (b : G) * (k : G) * (b : G)⁻¹ * (b : G) := by group
    _ = (k : G) * (b : G) := by rw [h1]

private theorem ggNbrLangS1CoreAux_mem_B0_of_inner {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    {B₀ : Subgroup G} (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    {e : ↥K} (heBs : (e : G) ∈ Bs) : (e : G) ∈ B₀ := by
  refine (hmem _ heBs).2 ?_
  have h1 : ggLAut K θ ⟨(e : G), hN heBs⟩ =
      MulAut.conj (θ ((⟨(e : G), e.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)) :=
    ggLAut_of_mem_outdiag K θ e.2
  rw [h1]
  exact hinn _

theorem ggNbrLangCore_of_langElem {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) (b₀ : G) (hb₀ : b₀ ∈ Bs) {B₀ : Subgroup G}
    (hB₀ : B₀ ≤ Bs) (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hke : ∃ k e : ↥K, e ≠ 1 ∧ e ^ p = 1 ∧ (∀ α ∈ (ggBsAut hN).range, α e = e) ∧
      (∀ α ∈ (ggBsAut hN).range, kgInducedAut θ α ∈ I → α k = k) ∧
      k * (ggBsAut hN ⟨b₀, hb₀⟩ k)⁻¹ = e) :
    ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧ k * b₀ * k⁻¹ = e * b₀ := by
  obtain ⟨k, e, he1, hep, hefix, hkfix, hke⟩ := hke
  have heBs : (e : G) ∈ Bs := ggNbrLangS1CoreAux_mem_Bs_of_fixed hSC hN hefix hep
  have heB₀ : (e : G) ∈ B₀ := ggNbrLangS1CoreAux_mem_B0_of_inner hN θ hinn hmem heBs
  have hkC : (k : G) ∈ Subgroup.centralizer (B₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ggNbrLangS1CoreAux_conj_of_fixed hN
      (hkfix (ggBsAut hN ⟨b, hB₀ hb⟩) ⟨⟨b, hB₀ hb⟩, rfl⟩ ((hmem b (hB₀ hb)).1 hb))
  have haxis : (k : G) * b₀ * (k : G)⁻¹ = (e : G) * b₀ := by
    have h1 : (k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹ = (e : G) := congrArg Subtype.val hke
    calc (k : G) * b₀ * (k : G)⁻¹
        = (k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹ * b₀ := by group
      _ = (e : G) * b₀ := by rw [h1]
  exact ⟨(k : G), hkC, (e : G), heB₀, fun h => he1 (Subtype.ext h), haxis⟩

end CFSG.StandardType
