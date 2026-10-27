module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.Q1327C.BTransfer

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem reflection_data {F : Subgroup G} {t : MulAut ↥F} (ht : IsAutReflection 5 F t) :
    ∃ ℓ : ↥F, ℓ ≠ 1 ∧ t ℓ = ℓ⁻¹ ∧ ∀ e : ↥F, ∃ k : ℤ, t e * e⁻¹ = ℓ ^ k := by
  obtain ⟨hord, hcard⟩ := ht
  have ht2 : ∀ f : ↥F, t (t f) = f := fun f => by
    have h1 : t ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one t
    have h2 := congrArg (fun s : MulAut ↥F => s f) h1
    simpa [pow_two] using h2
  have hne : ∃ e₀ : ↥F, t e₀ * e₀⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : autMoved F t = ⊥ := by
      apply eq_bot_iff.2
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨e, rfl⟩
      exact hall e
    rw [hbot] at hcard
    simp at hcard
  obtain ⟨e₀, he₀⟩ := hne
  set ℓ : ↥F := t e₀ * e₀⁻¹ with hℓ
  have hℓmem : ℓ ∈ autMoved F t := Subgroup.subset_closure ⟨e₀, rfl⟩
  have hℓinv : t ℓ = ℓ⁻¹ := by
    rw [hℓ, map_mul, map_inv, ht2, mul_inv_rev, inv_inv]
  have hordℓ : orderOf ℓ = 5 := by
    have hd : orderOf ℓ ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard (autMoved F t) hℓmem
      rwa [hcard] at this
    rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) he₀
    · exact h1
  have hfin : Finite ↥(autMoved F t) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hz : Subgroup.zpowers ℓ = autMoved F t := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hℓmem)
    rw [hcard, Nat.card_zpowers, hordℓ]
  refine ⟨ℓ, he₀, hℓinv, fun e => ?_⟩
  have hemem : t e * e⁻¹ ∈ autMoved F t := Subgroup.subset_closure ⟨e, rfl⟩
  rw [← hz] at hemem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hemem
  exact ⟨k, hk.symm⟩

theorem mem_normalizer_bar {X F : Subgroup G} {w : G} (hwX : w ∈ X)
    (hwN : w ∈ Subgroup.normalizer (F : Set G)) :
    proj X ⟨w, hwX⟩ ∈ Subgroup.normalizer ((bar X F : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X)) := by
  have hwN' := Subgroup.mem_normalizer_iff.1 hwN
  rw [Subgroup.mem_normalizer_iff]
  intro y
  set w' : ↥X := ⟨w, hwX⟩ with hw'
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨w' * x * w'⁻¹, ?_, by simp⟩
    have hx' : (x : G) ∈ F := Subgroup.mem_subgroupOf.1 hx
    exact (hwN' _).1 hx'
  · rintro ⟨x', hx', hx'y⟩
    refine ⟨w'⁻¹ * x' * w', ?_, ?_⟩
    · have hx'' : (x' : G) ∈ F := Subgroup.mem_subgroupOf.1 hx'
      show w⁻¹ * (x' : G) * w ∈ F
      rw [hwN' (w⁻¹ * (x' : G) * w)]
      simpa [mul_assoc] using hx''
    · simp only [map_mul, map_inv, hx'y]
      group

end CFSG.RankThree.PartOne.Q1327C
