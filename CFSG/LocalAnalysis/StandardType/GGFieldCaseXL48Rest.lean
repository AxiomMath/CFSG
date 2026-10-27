module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48RestTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

namespace GGL48

variable {G : Type} [Group G]

theorem commutator_sup_le_sup {H₀ C₀ : Subgroup G}
    (hHC : H₀ ≤ Subgroup.normalizer (C₀ : Set G)) : ⁅H₀ ⊔ C₀, H₀ ⊔ C₀⁆ ≤ ⁅H₀, H₀⁆ ⊔ C₀ := by
  have hN : H₀ ⊔ C₀ ≤ Subgroup.normalizer (C₀ : Set G) := sup_le hHC Subgroup.le_normalizer
  have hdec : ∀ g ∈ H₀ ⊔ C₀, ∃ h ∈ H₀, ∃ c ∈ C₀, h * c = g := by
    intro g hg
    have hg' : g ∈ ((H₀ ⊔ C₀ : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ C₀ hHC] at hg'
    obtain ⟨h, hh, c, hc, hgc⟩ := hg'
    exact ⟨h, hh, c, hc, hgc⟩
  have hconj : ∀ n ∈ H₀ ⊔ C₀, ∀ c ∈ C₀, n * c * n⁻¹ ∈ C₀ := fun n hn c hc =>
    (Subgroup.mem_normalizer_iff.mp (hN hn) c).mp hc
  set S : Subgroup G := ⁅H₀, H₀⁆ ⊔ C₀ with hS
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨h₁, hh₁, c₁, hc₁, rfl⟩ := hdec a ha
  obtain ⟨h₂, hh₂, c₂, hc₂, rfl⟩ := hdec b hb
  have e : ⁅h₁ * c₁, h₂ * c₂⁆ =
      (h₁ * ⁅c₁, h₂ * c₂⁆ * h₁⁻¹) * ⁅h₁, h₂⁆ * (h₂ * ⁅h₁, c₂⁆ * h₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hm1 : ⁅c₁, h₂ * c₂⁆ ∈ C₀ := by
    rw [commutatorElement_def]
    have := C₀.mul_mem hc₁ (hconj _ hb _ (C₀.inv_mem hc₁))
    simpa [mul_assoc] using this
  have hm2 : ⁅h₁, c₂⁆ ∈ C₀ := by
    rw [commutatorElement_def]
    exact C₀.mul_mem (hconj _ (Subgroup.mem_sup_left hh₁) _ hc₂) (C₀.inv_mem hc₂)
  rw [e]
  exact S.mul_mem (S.mul_mem
    (Subgroup.mem_sup_right (hconj _ (Subgroup.mem_sup_left hh₁) _ hm1))
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hh₁ hh₂)))
    (Subgroup.mem_sup_right (hconj _ (Subgroup.mem_sup_left hh₂) _ hm2))

theorem not_mem_sup_of_not_mem_sup_inf {H₀ C₀ : Subgroup G}
    (hHC : H₀ ≤ Subgroup.normalizer (C₀ : Set G)) {x : G} (hx : x ∈ H₀)
    (hxn : x ∉ ⁅H₀, H₀⁆ ⊔ (H₀ ⊓ C₀)) : x ∉ ⁅H₀, H₀⁆ ⊔ C₀ := by
  intro hxS
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((Subgroup.commutator_le_self H₀).trans hHC)] at hxS
  obtain ⟨k, hk, c, hc, hkc⟩ := hxS
  dsimp only at hkc
  apply hxn
  have hkH : k ∈ H₀ := Subgroup.commutator_le_self H₀ hk
  have hcH : c ∈ H₀ := by
    have e : c = k⁻¹ * x := by rw [← hkc]; group
    rw [e]
    exact H₀.mul_mem (H₀.inv_mem hkH) hx
  rw [← hkc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hcH, hc⟩)

theorem not_mem_commutator_of_not_dvd_relIndex [Finite G] {p : ℕ} [Fact p.Prime]
    {N₀ H₀ C₀ : Subgroup G} (hH₀ : H₀ ≤ N₀) (hC₀ : C₀ ≤ N₀)
    (hN : N₀ ≤ Subgroup.normalizer (C₀ : Set G)) {x : G} (hx : x ∈ H₀) (hxp : x ^ p = 1)
    (hconj : ∀ n ∈ N₀, n * x * n⁻¹ * x⁻¹ ∈ C₀)
    (hind : ¬ p ∣ (H₀ ⊔ C₀).relIndex N₀) (hxn : x ∉ ⁅H₀, H₀⁆ ⊔ (H₀ ⊓ C₀)) :
    x ∉ ⁅N₀, N₀⁆ := by
  have hHC : H₀ ≤ Subgroup.normalizer (C₀ : Set G) := hH₀.trans hN
  have hKN : H₀ ⊔ C₀ ≤ N₀ := sup_le hH₀ hC₀
  have hxN : x ∈ N₀ := hH₀ hx
  have hx' : x ∉ ⁅H₀, H₀⁆ ⊔ C₀ := not_mem_sup_of_not_mem_sup_inf hHC hx hxn
  have hCK : C₀.subgroupOf N₀ ≤ (H₀ ⊔ C₀).subgroupOf N₀ := fun g hg => by
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact Subgroup.mem_sup_right hg
  have hxK : (⟨x, hxN⟩ : N₀) ∈ (H₀ ⊔ C₀).subgroupOf N₀ := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hx
  have hxp' : (⟨x, hxN⟩ : N₀) ^ p = 1 := Subtype.ext (by simp [hxp])
  have hconj' : ∀ n : N₀, n⁻¹ * ⟨x, hxN⟩ * n * (⟨x, hxN⟩ : N₀)⁻¹ ∈ C₀.subgroupOf N₀ := by
    intro n
    rw [Subgroup.mem_subgroupOf]
    have := hconj _ (N₀.inv_mem n.2)
    simpa using this
  have hxK' : (⟨x, hxN⟩ : N₀) ∉
      ⁅(H₀ ⊔ C₀).subgroupOf N₀, (H₀ ⊔ C₀).subgroupOf N₀⁆ ⊔ C₀.subgroupOf N₀ := by
    intro h
    apply hx'
    have hmap : x ∈ (⁅(H₀ ⊔ C₀).subgroupOf N₀, (H₀ ⊔ C₀).subgroupOf N₀⁆ ⊔
        C₀.subgroupOf N₀).map N₀.subtype := ⟨⟨x, hxN⟩, h, rfl⟩
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN,
      Subgroup.map_subgroupOf_eq_of_le hC₀] at hmap
    exact (sup_le (commutator_sup_le_sup hHC) le_sup_right) hmap
  have hmain := not_mem_commutator_of_not_dvd_index hCK hxK hxp' hconj' hind hxK'
  intro hxc
  apply hmain
  rw [← N₀.map_subtype_commutator] at hxc
  obtain ⟨k, hk, hkx⟩ := hxc
  have e : k = ⟨x, hxN⟩ := Subtype.ext hkx
  rw [← e]
  exact hk

end GGL48

section Config

variable {G : Type} [Group G] [Finite G]

theorem not_mem_commutator_of_not_dvd_relIndex' {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hind : ¬ p ∣ (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G))) :
    x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆ := by
  obtain ⟨hp, hxp, hxN, ⟨e, he⟩, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hxH : x ∈ ggL48H0 x U₁ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxN⟩
  have hNC : Subgroup.normalizer (U₁ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U₁ : Set G) : Set G) :=
    ggNormalizer_le_normalizer_centralizer U₁
  have hHN : ggL48H0 x U₁ ≤ Subgroup.normalizer (U₁ : Set G) := inf_le_right
  have hU₂n : ggL48H0 x U₁ ≤ Subgroup.normalizer (ggL48U2 x U₁ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, Subgroup.le_normalizer hg.1⟩
  have hxn := GGL48.not_mem_sup_inf_of_not_mem_sup hU₂n (hHN.trans hNC)
    (fun c hc k hck => ⟨hpel c hc.2 k hck, hc.1.1⟩) hxH hxp hcent
  exact GGL48.not_mem_commutator_of_not_dvd_relIndex hHN (Subgroup.centralizer_le_normalizer _)
    hNC hxH hxp (fun n hn => GGL48.conj_mul_inv_mem_centralizer he hn) hind hxn

end Config

end CFSG.StandardType

end
