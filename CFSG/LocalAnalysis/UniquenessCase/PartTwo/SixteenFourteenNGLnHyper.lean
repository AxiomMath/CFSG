module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s1614_ln_hyperplane (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    {H : Subgroup (Multiplicative (Fin 4 → K))}
    (h2 : 2 * Nat.card ↥H = Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 4 → K)))) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧
      ∀ v : Fin 4 → K, Multiplicative.ofAdd v ∈ H ↔ dotProduct c v = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (Multiplicative (Fin 4 → K)) :=
    Fintype.ofEquiv (Fin 4 → K) Multiplicative.ofAdd
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
    have hy1 : y = 1 := (hy 1 one_ne_zero).symm
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by rw [hy x hx, hy1])
  haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
  haveI : Fintype ↥H := Subtype.fintype (fun x => x ∈ H)
  haveI : Finite ↥H := Finite.of_fintype ↥H
  have hcardH : Nat.card ↥H ≠ 0 := (Nat.card_pos (α := ↥H)).ne'
  have hmul : Nat.card ↥H * H.index = Nat.card ↥H * 2 := by
    calc Nat.card ↥H * H.index = Nat.card (Multiplicative (Fin 4 → K)) :=
          Subgroup.card_mul_index H
      _ = Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 4 → K))) := (Subgroup.card_top).symm
      _ = 2 * Nat.card ↥H := h2.symm
      _ = Nat.card ↥H * 2 := Nat.mul_comm _ _
  have hidx : H.index = 2 :=
    (Nat.mul_left_cancel_iff (Nat.card_pos (α := ↥H))).mp hmul
  obtain ⟨χ, hχ⟩ : ∃ χ : Multiplicative (Fin 4 → K) →* Multiplicative (ZMod 2),
      χ.ker = H := by
    refine ⟨{ toFun := fun g => if g ∈ H then 1 else Multiplicative.ofAdd 1
              map_one' := by simp
              map_mul' := fun a b => ?_ }, ?_⟩
    · simp only [Subgroup.mul_mem_iff_of_index_two hidx]
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb]
      decide
    · ext g
      simp only [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
      by_cases hg : g ∈ H <;> simp [hg]
  let e : Fin 4 → Multiplicative (Fin 4 → K) :=
    fun i => Multiplicative.ofAdd (Pi.single i (1 : K))
  let b : Fin 4 → ZMod 2 := fun i => (χ (e i)).toAdd
  let c : Fin 4 → K := fun i => if b i = 0 then 0 else 1
  let f : (Fin 4 → K) →+ ZMod 2 :=
    { toFun := fun v => (χ (Multiplicative.ofAdd v)).toAdd
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ofAdd_add, map_mul, toAdd_mul] }
  let ι : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime (p := 2) K Nat.prime_two hK'
  have hb : ∀ i, f (Pi.single i (1 : K)) = b i := fun i => rfl
  have hZ : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hc : ∀ i, c i = ι (b i) := by
    intro i
    rcases hZ (b i) with h | h
    · simp [c, h]
    · simp [c, h, zero_ne_one]
  have hfker : ∀ v : Fin 4 → K, f v = 0 ↔ Multiplicative.ofAdd v ∈ H := by
    intro v
    show (χ (Multiplicative.ofAdd v)).toAdd = 0 ↔ Multiplicative.ofAdd v ∈ H
    rw [toAdd_eq_zero, ← MonoidHom.mem_ker, hχ]
  have hiff : ∀ v : Fin 4 → K, Multiplicative.ofAdd v ∈ H ↔ dotProduct c v = 0 := by
    intro v
    let v' : Fin 4 → ZMod 2 := fun i => ι.symm (v i)
    have hv' : ∀ i, ι (v' i) = v i := fun i => ι.apply_symm_apply (v i)
    let w : Fin 4 → K := ∑ i, if v i = 1 then Pi.single i (1 : K) else 0
    have hdecomp : v = w := by
      change v = ∑ i, if v i = 1 then Pi.single i (1 : K) else 0
      conv_lhs => rw [pi_eq_sum_univ' v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases h01 (v i) with h | h <;> simp [h, zero_ne_one, one_ne_zero]
    have hf : f v = ∑ i, if v i = 1 then b i else 0 := by
      calc f v = f w := by rw [hdecomp]
        _ = ∑ i, f (if v i = 1 then Pi.single i (1 : K) else 0) := by
              simp only [w]
              rw [map_sum]
        _ = ∑ i, if v i = 1 then b i else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hi : v i = 1
              · rw [if_pos hi, if_pos hi]; exact hb i
              · rw [if_neg hi, if_neg hi, map_zero]
    have hsum_eq : (∑ i, b i * v' i) = ∑ i, if v i = 1 then b i else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases h01 (v i) with h | h
      · rw [h]
        have hvi : v' i = 0 := by simp [v', h]
        rw [hvi, mul_zero, if_neg zero_ne_one]
      · rw [h]
        have hvi : v' i = 1 := by simp [v', h]
        rw [hvi, mul_one, if_pos rfl]
    have hdot : dotProduct c v = ι (∑ i, b i * v' i) := by
      rw [dotProduct, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc i, hv' i]
    have hdotN : dotProduct c v = ι (f v) := by
      rw [hdot, hsum_eq, ← hf]
    rw [hdotN, show ι (f v) = 0 ↔ f v = 0 from by
      rw [← map_zero ι, ι.injective.eq_iff]]
    exact (hfker v).symm
  refine ⟨c, ?_, hiff⟩
  intro hc0
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = x :=
      ⟨Multiplicative.toAdd x, ofAdd_toAdd x⟩
    rw [hiff v, hc0]
    simp
  have h1 : H.index = 1 := by rw [htop, Subgroup.index_top]
  rw [h1] at hidx
  exact absurd hidx (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
