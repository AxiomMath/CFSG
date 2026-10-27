module

public import CFSG.RankThree.GF2n.Parrott.CaseIIG0
public import CFSG.CharacterTheory.SteinbergBYNormalOddCore
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem parrott_theoremA_two_of_index_two
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨ CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (h : Tim79a.ParrottHypA z) {G₀ : Subgroup G} (hG₀ : G₀.Normal) (hidx : G₀.index = 2)
    (hzG₀ : z ∈ G₀) (hJ : J z ≤ ⁅H z, H z⁆) (hHH : ⁅H z, H z⁆.relIndex (H z) = 2)
    (hHG₀ : H z ⊓ G₀ = ⁅H z, H z⁆) :
    centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤ ∨
      ∃ G₁ : Subgroup G, G₁.index = 2 ∧ (∀ c : G, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥G₁ ≃* X)) ∧
        G₁ ⊓ H z ≤ ⁅H z, H z⁆ := by
  by_cases hsup : centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤
  · exact Or.inl hsup
  refine Or.inr ?_
  have hHnle : ¬ H z ≤ G₀ := by
    intro hle
    rw [inf_eq_left.mpr hle] at hHG₀
    rw [← hHG₀, Subgroup.relIndex_self] at hHH
    exact absurd hHH (by norm_num)
  have hcoatom : IsCoatom G₀ :=
    Subgroup.isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_two)
  have hHA1 : Tim79a.ParrottHypA1 (⟨z, hzG₀⟩ : ↥G₀) :=
    parrottHypA1_of_inf_eq_commutator h hG₀ hzG₀ hJ hHG₀
  rcases hA1 ↥G₀ ⟨z, hzG₀⟩ hHA1 with hL | hLie
  ·
    exfalso
    have hOle : (pPrimeCore 2 ↥G₀).map G₀.subtype ≤ pPrimeCore 2 G :=
      (CFSG.CharacterTheory.SteinbergBY.normal_subgroup_odd_core_containment hG₀).2.1
    have hCle : (centralizer ({(⟨z, hzG₀⟩ : ↥G₀)} : Set ↥G₀)).map G₀.subtype ≤
        centralizer ({z} : Set G) := by
      have h1 := map_H_G₀ hzG₀
      rw [H_eq_centralizer] at h1
      exact h1.le.trans inf_le_left
    have hG₀le : G₀ ≤ centralizer ({z} : Set G) ⊔ pPrimeCore 2 G := by
      have h1 : G₀ ≤ (centralizer ({(⟨z, hzG₀⟩ : ↥G₀)} : Set ↥G₀)).map G₀.subtype ⊔
          (pPrimeCore 2 ↥G₀).map G₀.subtype := by
        rw [← Subgroup.map_sup, hL, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact h1.trans (sup_le_sup hCle hOle)
    have hsupTop : G₀ ⊔ H z = ⊤ :=
      hcoatom.2 _ (lt_of_le_of_ne le_sup_left
        (fun heq => hHnle (le_sup_right.trans_eq heq.symm)))
    apply hsup
    rw [eq_top_iff, ← hsupTop]
    exact sup_le hG₀le (le_sup_left : H z ≤ centralizer ({z} : Set G) ⊔ pPrimeCore 2 G)
  · refine ⟨G₀, hidx, ?_, ⟨↥G₀, inferInstance, hLie, ⟨MulEquiv.refl _⟩⟩, ?_⟩
    · intro c hc
      have hcH : c ∈ H z := by
        rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
        exact hc z hzG₀
      have hJG₀ : J z ≤ G₀ := hJ.trans (hHG₀ ▸ inf_le_right)
      have hcJ : c ∈ Subgroup.centralizer (J z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact (hc j (hJG₀ hj)).symm
      have hcZ : c ∈ Subgroup.zpowers z := by
        rw [← centerIn_J_eq_zpowers_A h, ← centralizer_J_eq_centerIn_A h]
        exact Subgroup.mem_inf.mpr ⟨hcH, hcJ⟩
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_A h)).mp hcZ with h1 | h1
      · exact h1
      ·
        exfalso
        have hG₀H : G₀ ≤ H z := by
          intro x hx
          rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
          have h2 := hc x hx
          rw [h1] at h2
          exact h2.symm
        have hHtop : H z = ⊤ :=
          hcoatom.2 _ (lt_of_le_of_ne hG₀H (fun heq => hHnle heq.symm.le))
        apply hsup
        rw [← H_eq_centralizer (z := z), hHtop, top_sup_eq]
    · rw [inf_comm]
      exact hHG₀.le

end CFSG.RankThree.GF2n.Parrott
