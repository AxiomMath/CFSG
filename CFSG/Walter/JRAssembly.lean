module

public import CFSG.Walter.Assembly
public import CFSG.Walter.J1.Defs
public import CFSG.Walter.ReeOrder.JTMain
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels

public section

namespace CFSG.Walter

open scoped MatrixGroups

@[expose] def Walter67Hyp : Prop := ∀ (G : Type) [Group G] [Finite G], IsTypeJR G →
  (∃ a b : G, a * b ≠ b * a) → ∀ t : G, orderOf t = 2 →
  ∃ (p f : ℕ) (_ : Fact p.Prime) (K : Subgroup G), Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
    K ≤ Subgroup.centralizer ({t} : Set G) ∧ t ∉ K ∧
    Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t ⊔ K ∧
    Nonempty (K ≃* PSL(2, GaloisField p f))

@[expose] def J1RecogHyp : Prop := ∀ (G : Type) [Group G] [Finite G], J1.JankoHyp G →
  Nonempty (G ≃* CFSG.Open.walterJ1)

@[expose] def JTThreeHyp : Prop := ∀ (G : Type) [Group G] [Finite G] (h : JT.JTHyp G),
  h.p ≠ 2 → h.p = 3

@[expose] def JRStrongHyp : Prop := ∀ (G : Type) [Group G] [Finite G], IsTypeJR G →
  (∃ a b : G, a * b ≠ b * a) → Nonempty (Ward.ReeTypeHyp G) ∨
    Nonempty (G ≃* CFSG.Open.walterJ1)

theorem index_ne_two_of_isSimpleGroup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) : H.index ≠ 2 := by
  intro h2
  have hN : H.Normal := Subgroup.normal_of_index_eq_two h2
  rcases hN.eq_bot_or_eq_top with hb | ht
  · subst hb
    rw [Subgroup.index_bot] at h2
    obtain ⟨a, b, hab⟩ := hnonab
    have hcomm : ∀ x y : G, x * y = y * x := by
      have hc : IsCyclic G := isCyclic_of_prime_card (p := 2) (by rw [h2])
      exact fun x y => hc.commGroup.mul_comm x y
    exact hab (hcomm a b)
  · subst ht
    rw [Subgroup.index_top] at h2
    omega

theorem jrStrongHyp_of
    (hW : Walter67Hyp) (hJ1 : J1RecogHyp) (hJT : JTThreeHyp) :
    JRStrongHyp := by
  intro G _ _ hJR hnonab
  have hS : IsSimpleGroup G := hJR.1
  obtain ⟨t, ht⟩ : ∃ t : G, orderOf t = 2 :=
    exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp (even_card_of_isSimpleGroup hnonab))
  obtain ⟨p, f, hp, K, hpodd, hf, h5, hKC, htK, hC, ⟨e⟩⟩ := hW G hJR hnonab t ht
  rcases (show 5 = p ^ f ∨ 5 < p ^ f by omega) with h5' | h5'
  ·
    have hp5 : p = 5 ∧ f = 1 := Nat.prime_five.pow_eq_iff.mp h5'.symm
    obtain ⟨rfl, rfl⟩ := hp5
    obtain ⟨eA⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model
      (GaloisField 5 1) (by simpa using GaloisField.card 5 1 one_ne_zero)).1
    exact Or.inr (hJ1 G ⟨hS, hJR.2.1, t, ht, K, hKC, htK, hC, e.trans eA⟩)
  ·
    let h : JT.JTHyp G := ⟨p, f, h5', hJR.2.1, index_ne_two_of_isSimpleGroup hnonab, t, ht, K,
      hKC, htK, hC, e⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    exact Or.inl (h.nonempty_reeTypeHyp_of_three (hJT G h hp2))

theorem exists_card_eq_ordRee
    {G : Type} [Group G] [Finite G] (h : Ward.ReeTypeHyp G) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card G = CFSG.Open.ordRee (3 ^ (2 * m + 1)) := by
  obtain ⟨⟨k, hk, hq⟩, hcard⟩ := Ward.ward_order h
  exact ⟨k, hk, by rw [hcard, hq, CFSG.Open.ordRee]⟩

theorem jrHyp_of_jrStrongHyp
    (h : JRStrongHyp) : JRHyp := by
  intro G _ _ hJR hnonab
  rcases h G hJR hnonab with hR | hJ
  · obtain ⟨hR⟩ := hR
    exact Or.inl (exists_card_eq_ordRee hR)
  · exact Or.inr hJ

end CFSG.Walter
