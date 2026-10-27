module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.O4PairCommSet
import CFSG.OddTranspositions.PartThree.Twelve.FiveChartBasic
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlanePerp
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace FiveChart

open CFSG.OddTranspositions.PartFour.TableE1Five CFSG.OddTranspositions.PartFour.FivePlane

private def comb {m : ℕ} (u : Fin 3 → Fin m → ZMod 5) (a : Fin 3 → ZMod 5) :
    Fin m → ZMod 5 :=
  a 0 • u 0 + a 1 • u 1 + a 2 • u 2

private theorem exists_orthonormal_triple {m : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin m → ZMod 5)}
    (hsym : ∀ x y, b x y = b y x) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (hm : 5 ≤ m) :
    ∃ u : Fin 3 → Fin m → ZMod 5, ∀ i j, b (u i) (u j) = if i = j then 1 else 0 := by
  obtain ⟨z₀, -, hz₀⟩ :=
    exists_aniso_perp (b := b) hsym hnd (k := 0) (by omega)
      (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  obtain ⟨u₀, -, hu₀⟩ :=
    exists_norm_eq_perp (b := b) hsym hnd (by omega) (v := z₀) hz₀
      (c := 1) (by decide)
  obtain ⟨u₁, hu₁₀, hu₁⟩ :=
    exists_norm_eq_perp (b := b) hsym hnd (by omega) (v := u₀)
      (by rw [hu₀]; decide) (c := 1) (by decide)
  have hu₁_ne_u₀ : u₁ ≠ u₀ := by
    intro h
    rw [h, hu₀] at hu₁₀
    exact absurd hu₁₀ (by decide)
  have hu₁_ne_neg_u₀ : u₁ ≠ -u₀ := by
    intro h
    rw [h, LinearMap.BilinForm.neg_left, hu₀] at hu₁₀
    exact absurd (neg_eq_zero.1 hu₁₀) (by decide)
  obtain ⟨u₂, hu₂, hu₂₀, hu₂₁⟩ :=
    exists_norm_one_perp_pair (b := b) hsym hnd hm
      (p := u₀) (q := u₁) hu₀ hu₁ hu₁_ne_u₀ hu₁_ne_neg_u₀
  have h00 : b u₀ u₀ = 1 := hu₀
  have h11 : b u₁ u₁ = 1 := hu₁
  have h22 : b u₂ u₂ = 1 := hu₂
  have h10 : b u₁ u₀ = 0 := hu₁₀
  have h20 : b u₂ u₀ = 0 := hu₂₀
  have h21 : b u₂ u₁ = 0 := hu₂₁
  have h01 : b u₀ u₁ = 0 := by rw [hsym]; exact hu₁₀
  have h02 : b u₀ u₂ = 0 := by rw [hsym]; exact hu₂₀
  have h12 : b u₁ u₂ = 0 := by rw [hsym]; exact hu₂₁
  refine ⟨![u₀, u₁, u₂], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h11, h22, h01, h10, h02, h20, h12, h21]

private theorem b_comb_comb {m : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin m → ZMod 5)}
    (u : Fin 3 → Fin m → ZMod 5)
    (hu : ∀ i j, b (u i) (u j) = if i = j then 1 else 0)
    (a a' : Fin 3 → ZMod 5) :
    b (comb u a) (comb u a') = a 0 * a' 0 + a 1 * a' 1 + a 2 * a' 2 := by
  have h00 : b (u 0) (u 0) = 1 := by simpa using hu 0 0
  have h11 : b (u 1) (u 1) = 1 := by simpa using hu 1 1
  have h22 : b (u 2) (u 2) = 1 := by simpa using hu 2 2
  have h01 : b (u 0) (u 1) = 0 := by simpa using hu 0 1
  have h10 : b (u 1) (u 0) = 0 := by simpa using hu 1 0
  have h02 : b (u 0) (u 2) = 0 := by simpa using hu 0 2
  have h20 : b (u 2) (u 0) = 0 := by simpa using hu 2 0
  have h12 : b (u 1) (u 2) = 0 := by simpa using hu 1 2
  have h21 : b (u 2) (u 1) = 0 := by simpa using hu 2 1
  simp only [comb, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    h00, h11, h22, h01, h10, h02, h20, h12, h21, mul_zero, mul_one, zero_add, add_zero]
  ring

private theorem b_comb_coord {m : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin m → ZMod 5)}
    (u : Fin 3 → Fin m → ZMod 5)
    (hu : ∀ i j, b (u i) (u j) = if i = j then 1 else 0)
    (k : Fin 3) (a : Fin 3 → ZMod 5) : b (comb u a) (u k) = a k := by
  have h := b_comb_comb u hu a (Pi.single k 1)
  fin_cases k <;> simpa [comb, Pi.single_apply] using h

private theorem coord_eq_or_neg_of_comb {m : ℕ}
    {b : LinearMap.BilinForm (ZMod 5) (Fin m → ZMod 5)}
    (u : Fin 3 → Fin m → ZMod 5)
    (hu : ∀ i j, b (u i) (u j) = if i = j then 1 else 0)
    {a a' : Fin 3 → ZMod 5}
    (h : comb u a' = comb u a ∨ comb u a' = -comb u a) :
    a' = a ∨ a' = -a := by
  have hcoord : (∀ k, a' k = a k) ∨ (∀ k, a' k = -a k) := by
    rcases h with h | h
    · left
      intro k
      have hk := congrArg (fun w => b w (u k)) h
      rwa [b_comb_coord u hu k a', b_comb_coord u hu k a] at hk
    · right
      intro k
      have hk := congrArg (fun w => b w (u k)) h
      rw [LinearMap.BilinForm.neg_left, b_comb_coord u hu k a',
        b_comb_coord u hu k a] at hk
      exact hk
  rcases hcoord with h | h
  · exact Or.inl (funext h)
  · exact Or.inr (funext (fun k => by simpa using h k))

variable {hC : HypothesisC D} {n : ℕ}

theorem fifteen_le_ncard_commSet (c : FiveChart hC n) (hn : 5 ≤ n) :
    15 ≤ (commSet D hC.d).ncard := by
  classical
  obtain ⟨u, hu⟩ := exists_orthonormal_triple c.hsym c.hnd hn
  let t : Fin 15 → Fin 3 → ZMod 5 :=
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 2], ![1, 1, 3], ![1, 4, 2], ![1, 4, 3],
      ![1, 2, 1], ![1, 2, 4], ![1, 3, 1], ![1, 3, 4], ![2, 1, 1], ![2, 1, 4], ![2, 4, 1],
      ![2, 4, 4]]
  have ht_norm : ∀ i : Fin 15,
      t i 0 * t i 0 + t i 1 * t i 1 + t i 2 * t i 2 = 1 := by
    decide
  have ht_sign : ∀ i j : Fin 15, (t j = t i ∨ t j = -t i) → i = j := by
    decide
  have hnorm_comb : ∀ i : Fin 15, c.b (comb u (t i)) (comb u (t i)) = 1 := by
    intro i
    rw [b_comb_comb u hu]
    exact ht_norm i
  choose z hz using fun i => c.exists_vec (comb u (t i)) (hnorm_comb i)
  have hz_mem : ∀ i, z i ∈ commSet D hC.d := fun i => (hz i).1
  have hz_vec : ∀ i, c.vec (z i) = comb u (t i) ∨ c.vec (z i) = -comb u (t i) :=
    fun i => (hz i).2
  have hz_inj : Function.Injective z := by
    intro i j hij
    have hvec : c.vec (z j) = c.vec (z i) := by rw [hij]
    have hzj : c.vec (z i) = comb u (t j) ∨ c.vec (z i) = -comb u (t j) := by
      rcases hz_vec j with h | h
      · exact Or.inl (by rw [← hvec, h])
      · exact Or.inr (by rw [← hvec, h])
    have hV : comb u (t j) = comb u (t i) ∨ comb u (t j) = -comb u (t i) :=
      eq_or_neg_of_eq_or_neg hzj (hz_vec i)
    exact ht_sign i j (coord_eq_or_neg_of_comb u hu hV)
  have hrange : (Set.range z).ncard = 15 := by
    rw [Set.ncard_range_of_injective hz_inj, Nat.card_fin]
  have hsub : Set.range z ⊆ commSet D hC.d := by
    rintro - ⟨i, rfl⟩
    exact hz_mem i
  have hle := Set.ncard_le_ncard hsub (Set.toFinite (commSet D hC.d))
  omega

theorem not_o4PairData (c : FiveChart hC n) (hn : 5 ≤ n) : ¬ QZ.O4PairData G D := by
  intro hO4
  have h15 := c.fifteen_le_ncard_commSet hn
  rw [QZ.ncard_commSet_of_o4PairData hO4 hC.hd] at h15
  omega

end FiveChart

end CFSG.OddTranspositions.PartThree
