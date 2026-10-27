module

public import CFSG.OddTranspositions.SevenAlphaTransitive
public import CFSG.OddTranspositions.SevenThreeOrderThree
public import CFSG.OddTranspositions.SevenTwo

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem order_three_conj_of_base (hC : HypothesisC D)
    (h3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3)
    {g₀ x y : G} (hxD : x ∈ D) (hxg : x ∈ cimg g₀ hC.alpha)
    (hyA : y ∈ AalphaStar D (cimg g₀ hC.alpha)) :
    orderOf (x * y) = 3 := by
  classical
  let hC' : HypothesisC D := hC.conj g₀
  have hα' : hC'.alpha = cimg g₀ hC.alpha := hC.conj_alpha g₀
  have hd' : hC'.d = g₀ * hC.d * g₀⁻¹ := hC.conj_d g₀
  have h3' : ∀ w ∈ AalphaStar D hC'.alpha, orderOf (hC'.d * w) = 3 := by
    intro w hw
    obtain ⟨β, hβA, hwβ⟩ := hw
    let w' : G := g₀⁻¹ * w * g₀
    have hα'' : cimg g₀⁻¹ (cimg g₀ hC.alpha) = hC.alpha := by
      change (fun x => g₀⁻¹ * x * (g₀⁻¹)⁻¹) ''
        ((fun x => g₀ * x * g₀⁻¹) '' hC.alpha) = hC.alpha
      rw [Set.image_image]
      have hfun : (fun z => g₀⁻¹ * (g₀ * z * g₀⁻¹) * (g₀⁻¹)⁻¹) = id := by
        funext z
        change g₀⁻¹ * (g₀ * z * g₀⁻¹) * (g₀⁻¹)⁻¹ = z
        group
      rw [hfun, Set.image_id]
    have hβ'A : cimg g₀⁻¹ β ∈ Aalpha D (cimg g₀⁻¹ hC'.alpha) :=
      Aalpha.conj hC.setup.normal hβA g₀⁻¹
    rw [hα'] at hβ'A
    rw [hα''] at hβ'A
    have hw'A : w' ∈ AalphaStar D hC.alpha := ⟨_, hβ'A, ⟨w, hwβ, by simp [w']⟩⟩
    have h := h3 w' hw'A
    have heq : hC'.d * w = g₀ * (hC.d * w') * g₀⁻¹ := by
      rw [hd']
      show g₀ * hC.d * g₀⁻¹ * w = g₀ * (hC.d * (g₀⁻¹ * w * g₀)) * g₀⁻¹
      group
    rw [heq, orderOf_conj_eq]
    exact h
  have hxα' : x ∈ hC'.alpha := by
    rw [hα']
    exact hxg
  have hyA' : y ∈ AalphaStar D hC'.alpha := by
    rw [hα']
    exact hyA
  obtain ⟨n, hnN, hn⟩ := normalizer_transitive_alpha hC' hC'.d_mem_alpha hxα'
  have hy'' : n⁻¹ * y * n ∈ AalphaStar D hC'.alpha := by
    obtain ⟨β, hβA, hyβ⟩ := hyA'
    have hβ'A : cimg n⁻¹ β ∈ Aalpha D hC'.alpha :=
      Aalpha.conj_normalizer hC'.setup.normal (Subgroup.inv_mem _ hnN) hβA
    exact ⟨cimg n⁻¹ β, hβ'A, ⟨y, hyβ, by simp [cimg]⟩⟩
  have h := h3' (n⁻¹ * y * n) hy''
  have e : x * y = n * (hC'.d * (n⁻¹ * y * n)) * n⁻¹ := by
    rw [← hn]
    group
  rw [e, orderOf_conj_eq]
  exact h

theorem sevenThree_of_faithful_of_base (hC : HypothesisC D)
    (h3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3)
    (hfaith : FaithfulOnBlocks hC.alpha)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    ∃ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) ≠ 3 := by
  have h3inv : ∀ x ∈ D, ∀ g : ConjAct G, x ∈ g • hC.alpha →
      ∀ y ∈ AalphaStar D (g • hC.alpha), orderOf (x * y) = 3 := by
    intro x hxD g hxg y hyA
    let g₀ : G := ConjAct.ofConjAct g
    have hg : ConjAct.toConjAct g₀ = g := ConjAct.toConjAct_ofConjAct g
    have hgα : g • hC.alpha = cimg g₀ hC.alpha := by
      rw [← hg, ← Set.image_smul]
      rfl
    have hxg' : x ∈ cimg g₀ hC.alpha := by rwa [← hgα]
    have hyA' : y ∈ AalphaStar D (cimg g₀ hC.alpha) := by rwa [← hgα]
    exact order_three_conj_of_base hC h3 hxD hxg' hyA'
  exact sevenThree_of_faithful hC h3inv hfaith hnot3

end CFSG.OddTranspositions

