module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBasic

public section

namespace CFSG.StandardType

namespace TwE6Per

variable {R : Type} [Group R]

theorem eq_mulSingle_four {p : ℕ} (f : Fin 4 → Multiplicative (ZMod p)) (h0 : f 0 = 1)
    (h1 : f 1 = 1) (h2 : f 2 = 1) : f = Pi.mulSingle 3 (f 3) := by
  funext j
  fin_cases j <;> simp [h0, h1, h2]

theorem eq_mulSingle_five {p : ℕ} (f : Fin 5 → Multiplicative (ZMod p)) (h0 : f 0 = 1)
    (h1 : f 1 = 1) (h2 : f 2 = 1) : f = Pi.mulSingle 3 (f 3) * Pi.mulSingle 4 (f 4) := by
  funext j
  fin_cases j <;> simp [h0, h1, h2]

theorem toAdd_eq_zero_of_pow {p : ℕ} [NeZero p] {x : R} (hx : orderOf x = p)
    {a : Multiplicative (ZMod p)} (h : x ^ (Multiplicative.toAdd a).val = 1) : a = 1 := by
  set v := (Multiplicative.toAdd a).val with hv
  have hd : p ∣ v := by
    have := orderOf_dvd_of_pow_eq_one h
    rwa [hx] at this
  have h0 : v = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact (ZMod.val_eq_zero _).1 h0

theorem centralizer_mem_of_commute {U : Subgroup R} {x : R} (hx : ∀ u ∈ U, Commute x u) :
    x ∈ Subgroup.centralizer (U : Set R) :=
  Subgroup.mem_centralizer_iff.2 fun u hu => (hx u hu).eq.symm

theorem ggTorusLift_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : Fin 4 → R)
    (hc : ∀ i j, Commute (b i) (b j)) (hb : ∀ i, b i ^ p = 1) (hne : ∀ i, b i ≠ 1)
    (w : Fin 4 → R) (hw : ∀ i, w i * b i * (w i)⁻¹ = (b i)⁻¹)
    (hw' : ∀ i j, i ≠ 3 → j ≠ i → w i * b j * (w i)⁻¹ = b j)
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hbU : ∀ i, ∀ u ∈ U, Commute (b i) u) :
    GGTorusLift p 4 R := by
  have : Fact p.Prime := ⟨hp⟩
  set τ := basisTorus b hb hc
  have hord : ∀ i, orderOf (b i) = p := fun i => orderOf_eq_prime (hb i) (hne i)
  have hτ : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hi : ∀ i : Fin 4, i ≠ 3 → f i = 1 := fun i hi3 =>
      eq_one_of_inverter hp hp2 b hb hc (hne i) (hw i) (fun j hj => hw' i j hi3 hj) hf
    have e := eq_mulSingle_four f (hi 0 (by decide)) (hi 1 (by decide)) (hi 2 (by decide))
    rw [e, basisTorus_mulSingle] at hf
    rw [e, toAdd_eq_zero_of_pow (hord 3) hf, Pi.mulSingle_one]
  have hsub : ∀ i, b i ∈ Subgroup.closure (Set.range b) :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  refine ggTorusLift_of_inverters hp hp2 τ hτ (Set.range b) ?_ ?_ ?_
    (fun _ ⟨f, hf⟩ => hf ▸ basisTorus_mem b hb hc hsub f)
    (fun i => ⟨w i, by rw [torusBasis_basisTorus]; exact hw i⟩) hU hU2 ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j
  · rintro _ ⟨i, rfl⟩
    exact hb i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi3 : i = 3
    · have hj3 : j ≠ 3 := fun h => hij' (hi3.trans h.symm)
      exact ⟨w j, Or.inr ⟨hw j, hw' j i hj3 hij'⟩⟩
    · exact ⟨w i, Or.inl ⟨hw i, hw' i j hi3 (Ne.symm hij')⟩⟩
  · intro f u hu
    have hC : τ f ∈ Subgroup.centralizer (U : Set R) :=
      basisTorus_mem b hb hc (fun i => centralizer_mem_of_commute (hbU i)) f
    rw [← Subgroup.mem_centralizer_iff.1 hC u hu, mul_inv_cancel_right]
    exact hu


theorem ggTorusLift_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (b : Fin 5 → R)
    (hc : ∀ i j, Commute (b i) (b j)) (hb : ∀ i, b i ^ p = 1) (hne : ∀ i, b i ≠ 1)
    (w : Fin 5 → R) (hw : ∀ i, w i * b i * (w i)⁻¹ = (b i)⁻¹)
    (hw' : ∀ i j, i.val < 3 → j ≠ i → w i * b j * (w i)⁻¹ = b j)
    (h34 : w 3 * b 4 * (w 3)⁻¹ = b 4 * b 3) (h43 : w 4 * b 3 * (w 4)⁻¹ = b 3 * b 4)
    {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hbU : ∀ i, ∀ u ∈ U, Commute (b i) u) :
    GGTorusLift p 5 R := by
  have : Fact p.Prime := ⟨hp⟩
  set τ := basisTorus b hb hc
  have hord : ∀ i, orderOf (b i) = p := fun i => orderOf_eq_prime (hb i) (hne i)
  have hτ : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hi : ∀ i : Fin 5, i.val < 3 → f i = 1 := fun i hi3 =>
      eq_one_of_inverter hp hp2 b hb hc (hne i) (hw i) (fun j hj => hw' i j hi3 hj) hf
    have e := eq_mulSingle_five f (hi 0 (by decide)) (hi 1 (by decide)) (hi 2 (by decide))
    rw [e, map_mul, basisTorus_mulSingle, basisTorus_mulSingle] at hf
    obtain ⟨d3, d4⟩ := dvd_of_pair hp hp2 hp3 (hc 3 4) (hord 3) (hord 4) (hw 3) h34 (hw 4) h43 hf
    have z3 : Multiplicative.toAdd (f 3) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt d3 (ZMod.val_lt _))
    have z4 : Multiplicative.toAdd (f 4) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt d4 (ZMod.val_lt _))
    have o3 : f 3 = 1 := z3
    have o4 : f 4 = 1 := z4
    rw [e, o3, o4, Pi.mulSingle_one, Pi.mulSingle_one, mul_one]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  set c : R := b 3 ^ (m + 1) * b 4 with hcdef
  set b' : Fin 5 → R := ![b 0, b 1, b 2, b 3, c] with hb'
  have hcc : ∀ i, Commute (b i) c := fun i => ((hc i 3).pow_right _).mul_right (hc i 4)
  have hc' : ∀ i j, Commute (b' i) (b' j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [b'] <;>
      first | exact hc _ _ | exact hcc _ | exact (hcc _).symm
  have hcp : c ^ p = 1 := by
    rw [hcdef, ((hc 3 4).pow_left _).mul_pow, ← pow_mul, mul_comm, pow_mul, hb 3, one_pow,
      hb 4, one_mul]
  have hb'p : ∀ i, b' i ^ p = 1 := by
    intro i
    fin_cases i <;> simp [b'] <;> first | exact hb _ | exact hcp
  have hw3c : w 3 * c * (w 3)⁻¹ = c := by
    have e1 : w 3 * c * (w 3)⁻¹ = (w 3 * b 3 * (w 3)⁻¹) ^ (m + 1) * (w 3 * b 4 * (w 3)⁻¹) := by
      rw [hcdef, conj_pow]
      group
    rw [e1, hw 3, h34, inv_pow, hcdef]
    have h33 : b 3 ^ (2 * m + 1) = 1 := hm ▸ hb 3
    have e2 : ((b 3 ^ (m + 1))⁻¹ * (b 4 * b 3)) = b 3 ^ (m + 1) * b 4 := by
      have hcomm : Commute (b 4) (b 3) := hc 4 3
      calc (b 3 ^ (m + 1))⁻¹ * (b 4 * b 3) = (b 3 ^ (m + 1))⁻¹ * (b 3 * b 4) := by
            rw [hcomm.eq]
        _ = (b 3 ^ (m + 1))⁻¹ * b 3 * b 4 := by group
        _ = b 3 ^ (m + 1) * b 4 := by
          congr 1
          rw [inv_mul_eq_iff_eq_mul, ← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring,
            pow_succ, h33, one_mul]
    exact e2
  have hwic : ∀ i : Fin 5, i.val < 3 → w i * c * (w i)⁻¹ = c := by
    intro i hi
    have h3 := hw' i 3 hi (by intro h; rw [← h] at hi; simp at hi)
    have h4 := hw' i 4 hi (by intro h; rw [← h] at hi; simp at hi)
    rw [hcdef, show w i * (b 3 ^ (m + 1) * b 4) * (w i)⁻¹ =
      (w i * b 3 * (w i)⁻¹) ^ (m + 1) * (w i * b 4 * (w i)⁻¹) by rw [conj_pow]; group, h3, h4]
  have hS : ∀ i, b' i ∈ Subgroup.closure (Set.range b') :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hsub : ∀ i, b i ∈ Subgroup.closure (Set.range b') := by
    intro i
    fin_cases i
    · exact hS 0
    · exact hS 1
    · exact hS 2
    · exact hS 3
    · have h4 : b 4 = (b 3 ^ (m + 1))⁻¹ * c := by rw [hcdef, inv_mul_cancel_left]
      show b 4 ∈ _
      rw [h4]
      exact mul_mem (inv_mem (Subgroup.pow_mem _ (hS 3) _)) (hS 4)
  refine ggTorusLift_of_inverters hp hp2 τ hτ (Set.range b') ?_ ?_ ?_
    (fun _ ⟨f, hf⟩ => hf ▸ basisTorus_mem b hb hc hsub f)
    (fun i => ⟨w i, by rw [torusBasis_basisTorus]; exact hw i⟩) hU hU2 ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc' i j
  · rintro _ ⟨i, rfl⟩
    exact hb'p i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    have key : ∀ i j : Fin 5, i ≠ j → i.val < 3 → ∃ g : R,
        g * b' i * g⁻¹ = (b' i)⁻¹ ∧ g * b' j * g⁻¹ = b' j := by
      intro i j hij hi
      refine ⟨w i, ?_, ?_⟩
      · fin_cases i <;> simp at hi <;> simp [b'] <;> exact hw _
      · fin_cases j
        · exact hw' i 0 hi (Ne.symm hij)
        · exact hw' i 1 hi (Ne.symm hij)
        · exact hw' i 2 hi (Ne.symm hij)
        · exact hw' i 3 hi (Ne.symm hij)
        · exact hwic i hi
    by_cases hi : i.val < 3
    · obtain ⟨g, h1, h2⟩ := key i j hij' hi
      exact ⟨g, Or.inl ⟨h1, h2⟩⟩
    by_cases hj : j.val < 3
    · obtain ⟨g, h1, h2⟩ := key j i (Ne.symm hij') hj
      exact ⟨g, Or.inr ⟨h1, h2⟩⟩
    have hb3 : w 3 * b' 3 * (w 3)⁻¹ = (b' 3)⁻¹ := hw 3
    have hb4 : w 3 * b' 4 * (w 3)⁻¹ = b' 4 := hw3c
    fin_cases i <;> fin_cases j <;> simp at hi hj hij' <;>
      first | exact ⟨w 3, Or.inl ⟨hb3, hb4⟩⟩ | exact ⟨w 3, Or.inr ⟨hb3, hb4⟩⟩
  · intro f u hu
    have hC : τ f ∈ Subgroup.centralizer (U : Set R) :=
      basisTorus_mem b hb hc (fun i => centralizer_mem_of_commute (hbU i)) f
    rw [← Subgroup.mem_centralizer_iff.1 hC u hu, mul_inv_cancel_right]
    exact hu

end TwE6Per

end CFSG.StandardType
