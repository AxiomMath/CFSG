module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinO
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W]

theorem Setup.transitive {ρ : A6 →* MulAut W} (h : Setup ρ) {u v : W} (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ g : A6, ρ g u = v := by
  classical
  by_contra hne
  push Not at hne
  have hdisj : Disjoint (orb ρ u) (orb ρ v) := by
    rw [Set.disjoint_left]
    rintro w ⟨g, hg⟩ ⟨g', hg'⟩
    apply hne (g'⁻¹ * g)
    have hg1 : ρ g u = w := hg
    have hg2 : ρ g' v = w := hg'
    rw [map_mul, MulAut.mul_apply, hg1, map_inv, ← hg2]
    exact MulAut.inv_apply_self W (ρ g') v
  have h1 := h.orb_ncard_ge_ten hu
  have h2 := h.orb_ncard_ge_ten hv
  have hunion := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have : Fintype W := Fintype.ofFinite W
  have hsub : orb ρ u ∪ orb ρ v ⊆ ↑(Finset.univ.erase (1 : W)) := by
    intro w hw
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, true_and]
    rcases hw with hw | hw
    · exact Setup.orb_ne_one hu hw
    · exact Setup.orb_ne_one hv hw
  have h3 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)] at h3
  have hc : (Finset.univ : Finset W).card = 16 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card]
  omega


theorem Setup.orb_eq {ρ : A6 →* MulAut W} (h : Setup ρ) {u : W} (hu : u ≠ 1) :
    orb ρ u = {w | w ≠ 1} := by
  ext w
  constructor
  · intro hw
    exact Setup.orb_ne_one hu hw
  · intro hw
    obtain ⟨g, hg⟩ := h.transitive hu hw
    exact ⟨g, hg⟩

theorem Setup.centralizer_trivial {ρ : A6 →* MulAut W} (h : Setup ρ) (n : MulAut W)
    (hn : ∀ g : A6, n * ρ g = ρ g * n) : n = 1 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨u, hu⟩ : ∃ u : W, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card W = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
      exact ⟨1, fun w => hcon w⟩
    rw [h.card] at h1
    omega
  let _ : MulAction A6 W := MulAction.compHom W ρ
  let S : Subgroup A6 := MulAction.stabilizer A6 u
  have hS : ∀ g : A6, g ∈ S ↔ ρ g u = u := fun g => MulAction.mem_stabilizer_iff
  have hSidx : S.index = 15 := by
    have h1 := MulAction.index_stabilizer A6 u
    have h2 : MulAction.orbit A6 u = orb ρ u := rfl
    rw [h2, h.orb_eq hu] at h1
    rw [h1]
    have : {w : W | w ≠ 1} = ↑(Finset.univ.erase (1 : W)) := by
      ext w; simp
    rw [this, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)]
    have hc : (Finset.univ : Finset W).card = 16 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card]
    omega
  have hSN : Subgroup.normalizer (S : Set A6) = S := by
    have hle : S ≤ Subgroup.normalizer (S : Set A6) := Subgroup.le_normalizer
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [hSidx] at hdvd
    have hNidx : (Subgroup.normalizer (S : Set A6)).index = 15 := by
      have h15 : (Subgroup.normalizer (S : Set A6)).index ∣ 15 := hdvd
      have hle15 : (Subgroup.normalizer (S : Set A6)).index ≤ 15 := Nat.le_of_dvd (by norm_num) h15
      by_contra hne
      have hcases : (Subgroup.normalizer (S : Set A6)).index = 1 ∨
          (Subgroup.normalizer (S : Set A6)).index = 3 ∨ (Subgroup.normalizer (S : Set A6)).index = 5 := by
        interval_cases hi : (Subgroup.normalizer (S : Set A6)).index <;> simp_all
      rcases hcases with h1 | h1 | h1
      ·
        have hnormal : S.Normal := by
          have : Subgroup.normalizer (S : Set A6) = ⊤ := Subgroup.index_eq_one.mp h1
          exact ⟨fun x hx g => by
            have hg : g ∈ Subgroup.normalizer (S : Set A6) := by rw [this]; trivial
            exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hb | ht
        · rw [hb, Subgroup.index_bot, card_A6] at hSidx; omega
        · rw [ht, Subgroup.index_top] at hSidx; omega
      · exact no_index_small (Subgroup.normalizer (S : Set A6)) (by omega) (by omega)
      · exact no_index_small (Subgroup.normalizer (S : Set A6)) (by omega) (by omega)
    have hcardS := S.card_mul_index
    have hcardN := (Subgroup.normalizer (S : Set A6)).card_mul_index
    rw [hSidx, card_A6] at hcardS
    rw [hNidx, card_A6] at hcardN
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have hnu : n u ≠ 1 := by
    intro h1
    apply hu
    have : n u = n 1 := by rw [h1, map_one]
    exact n.injective this
  have hc : ∀ (x : A6) (w : W), n (ρ x w) = ρ x (n w) := fun x w => by
    have := congrArg (fun f : MulAut W => f w) (hn x)
    simpa using this
  obtain ⟨g, hg⟩ := h.transitive hu hnu
  have key : ∀ x : A6, ρ (g⁻¹ * x * g) u = u ↔ ρ x u = u := by
    intro x
    have e1 : ρ (g⁻¹ * x * g) u = ρ g⁻¹ (ρ x (n u)) := by
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hg]
    constructor
    · intro h1
      rw [e1] at h1
      have h2 : ρ x (n u) = n u := by
        have := congrArg (ρ g) h1
        rw [map_inv] at this
        rw [MulAut.apply_inv_self] at this
        rw [this, ← hg]
      rw [← hc] at h2
      exact n.injective h2
    · intro h1
      rw [e1, ← hc, h1, ← hg, map_inv]
      exact MulAut.inv_apply_self W (ρ g) u
  have hgN : g ∈ Subgroup.normalizer (S : Set A6) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := key (g * x * g⁻¹)
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
    show x ∈ S ↔ g * x * g⁻¹ ∈ S
    rw [hS, hS]
    exact h1
  rw [hSN] at hgN
  have hnu_fix : n u = u := by
    have : ρ g u = u := (hS g).mp hgN
    rw [← hg]
    exact this
  ext w
  by_cases hw : w = 1
  · rw [hw, map_one]; rfl
  · obtain ⟨g', hg'⟩ := h.transitive hu hw
    rw [← hg', hc, hnu_fix]
    rfl

end CFSG.Quasithin.A6Fin
