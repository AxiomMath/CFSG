module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lbl0
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Swp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def F2At (Γ : SimpleGraph V) (z : G) (α : V) : Prop :=
  ∀ (β : V) (l : List V) (h : V → G), ¬ Equiv3 G α β → l.Nodup → (∀ u, u ∈ l ↔ Γ.Adj β u) →
    (∀ u, Γ.Adj β u → h u • α = u) →
    (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
      (l.map fun u => h u * z * (h u)⁻¹).prod = 1

theorem conj_of_valence (F : FanTree Γ G) {α u : V} (hα : valence Γ α = 5)
    (hu : valence Γ u = 5) : ∃ g : G, g • α = u :=
  P62.exists_smul_of_valence_eq F (by rw [hu, hα])

theorem three_labels (F : FanTree Γ G) {z : G} {α β u₁ u₂ u₃ : V} (hz : z ∈ Cinv G α)
    (hα : valence Γ α = 5) (hβ : valence Γ β = 3) (hF2 : F2At Γ z α) (h₁ : Γ.Adj β u₁)
    (h₂ : Γ.Adj β u₂) (h₃ : Γ.Adj β u₃) (n12 : u₁ ≠ u₂) (n13 : u₁ ≠ u₃) (n23 : u₂ ≠ u₃) :
    Lb z α u₁ * Lb z α u₂ * Lb z α u₃ = 1 ∧ Lb z α u₁ * Lb z α u₂ = Lb z α u₂ * Lb z α u₁ ∧
      Lb z α u₁ * Lb z α u₃ = Lb z α u₃ * Lb z α u₁ ∧
      Lb z α u₂ * Lb z α u₃ = Lb z α u₃ * Lb z α u₂ := by
  have hset := P72.nbrSet_eq_three hβ h₁ h₂ h₃ n12 n13 n23
  have c₁ := conj_of_valence F hα (valence_adj_five F hβ h₁)
  have c₂ := conj_of_valence F hα (valence_adj_five F hβ h₂)
  have c₃ := conj_of_valence F hα (valence_adj_five F hβ h₃)
  have hnE : ¬ Equiv3 G α β := by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g α
    rw [hg, hα, hβ] at this
    omega
  have hex : ∀ u : V, ∃ g : G, Γ.Adj β u → g • α = u := fun u => by
    by_cases hu : Γ.Adj β u
    · have hu' : u = u₁ ∨ u = u₂ ∨ u = u₃ := by
        have : u ∈ Γ.neighborSet β := hu
        rw [hset] at this
        simpa using this
      rcases hu' with rfl | rfl | rfl
      · obtain ⟨g, hg⟩ := c₁
        exact ⟨g, fun _ => hg⟩
      · obtain ⟨g, hg⟩ := c₂
        exact ⟨g, fun _ => hg⟩
      · obtain ⟨g, hg⟩ := c₃
        exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun h => absurd h hu⟩
  choose h hh using hex
  have hl : [u₁, u₂, u₃].Nodup := by simp [n12, n13, n23]
  have hmem : ∀ u, u ∈ [u₁, u₂, u₃] ↔ Γ.Adj β u := fun u => by
    constructor
    · intro hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    · intro hu
      have : u ∈ Γ.neighborSet β := hu
      rw [hset] at this
      simpa using this
  obtain ⟨hcomm, hprod⟩ := hF2 β [u₁, u₂, u₃] h hnE hl hmem hh
  have e1 : h u₁ * z * (h u₁)⁻¹ = Lb z α u₁ := (Lb_eq hz (hh u₁ h₁)).symm
  have e2 : h u₂ * z * (h u₂)⁻¹ = Lb z α u₂ := (Lb_eq hz (hh u₂ h₂)).symm
  have e3 : h u₃ * z * (h u₃)⁻¹ = Lb z α u₃ := (Lb_eq hz (hh u₃ h₃)).symm
  simp only [List.map_cons, List.map_nil, e1, e2, e3, List.prod_cons, List.prod_nil,
    mul_one] at hprod
  simp only [List.map_cons, List.map_nil, e1, e2, e3] at hcomm
  simp [List.pairwise_cons] at hcomm
  exact ⟨by rw [← mul_assoc] at hprod; exact hprod, hcomm.1.1.eq, hcomm.1.2.eq, hcomm.2.eq⟩

theorem swap_fix (F : FanTree Γ G) {z : G} {α δ μ l l' : V} (hz : z ∈ Cinv G α)
    (hα : valence Γ α = 5) (hδ : ∃ g : G, g • α = δ) (hμ : valence Γ μ = 3)
    (hδμ : Γ.Adj μ δ) (hμl : Γ.Adj μ l) (hμl' : Γ.Adj μ l') (hδl : δ ≠ l) (hδl' : δ ≠ l')
    (hll' : l ≠ l') (hF2 : F2At Γ z α) {w : G} (hwδ : w • δ = δ) (hwμ : w • μ = μ)
    (hwc : w * Lb z α l = Lb z α l * w) : w • l = l := by
  have hset := P72.nbrSet_eq_three hμ hδμ hμl hμl' hδl hδl' hll'
  obtain ⟨hprod, hcδl, -, -⟩ := three_labels F hz hα hμ hF2 hδμ hμl hμl' hδl hδl' hll'
  have hl5 := valence_adj_five F hμ hμl
  have hl : ∃ g : G, g • α = l := conj_of_valence F hα hl5
  rcases P73.swap_or_fix F hset hll' hδl hδl' hwδ hwμ with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exfalso
    have hc := Lb_conj hz hl w
    rw [h1] at hc
    have hconj : w * Lb z α l * w⁻¹ = Lb z α l := by
      rw [hwc]
      group
    rw [hconj] at hc
    have hmul := Lb_mul_self hz hl
    have hδ1 : Lb z α δ = 1 := by
      calc Lb z α δ = Lb z α δ * (Lb z α l * Lb z α l) := by rw [hmul, mul_one]
        _ = Lb z α δ * Lb z α l * Lb z α l := by rw [mul_assoc]
        _ = 1 := by
          rw [← hc] at hprod
          exact hprod
    exact Lb_ne_one hz hδ hδ1

end P515

end CFSG.Quasithin.Fan86
