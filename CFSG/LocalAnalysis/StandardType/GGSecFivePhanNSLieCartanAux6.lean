module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux5
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux7

public section

namespace CFSG.StandardType

open Finset Module CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

lemma ggNSLiePI2_hoff (hp : p.Prime) (hp2 : p ≠ 2) (hel : IsElemAbelian p Bs) [Finite Bs]
    [IsMulCommutative ↥Bs] [Module (ZMod p) (Additive ↥Bs)]
    (ρ : Equiv.Perm (Fin N) →* MulAut ↥Bs) (hinj : Function.Injective ρ)
    (hnotr : ∀ g : Equiv.Perm (Fin N), ¬ GGIsTransvection p (ρ g))
    (hrefl : ∀ a b : Fin N, a ≠ b → GGIsReflection p (ρ (Equiv.swap a b)))
    (i j : Fin (N - 1)) (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) + 1 ≠ (j : ℕ))
    (hi1j : (i : ℕ) ≠ (j : ℕ) + 1)
    {x : Fin (N - 1) → Additive ↥Bs} {g : Fin (N - 1) → Module.Dual (ZMod p) (Additive ↥Bs)}
    (hx0 : ∀ k, x k ≠ 0) (hgx : ∀ k, g k (x k) = 2)
    (hnorm : ∀ k v, ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N k)) v =
      v - g k v • x k) :
    g i (x j) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hcomm_perm : ggNSLiePI2_simpleSwap N i * ggNSLiePI2_simpleSwap N j =
      ggNSLiePI2_simpleSwap N j * ggNSLiePI2_simpleSwap N i :=
    ggNSLiePI2_simpleSwap_comm N i j hij hij1 hi1j
  have hcomm : ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N i)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N j)) =
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N j)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N i)) := by
    simp only [← ggNSLiePI2_linearEquivOfMulAut_mul]
    congr 1
    simp only [← map_mul]
    exact congrArg ρ hcomm_perm
  by_contra hne
  have hline : x i ∈ Submodule.span (ZMod p) {x j} :=
    ggNSLiePI2_same_line h2 (hnorm i) (hnorm j) (hgx j) hne hcomm
  have htrans := ggNSLiePI2_transvection_of_same_line hp hp2 hel
    (ρ (ggNSLiePI2_simpleSwap N i)) (ρ (ggNSLiePI2_simpleSwap N j))
    (hrefl ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ (ggNSLiePI2_simpleSwap_ne_self N i))
    (hrefl ⟨j.1, by omega⟩ ⟨j.1 + 1, by omega⟩ (ggNSLiePI2_simpleSwap_ne_self N j))
    (hgx i) (hgx j) (hnorm i) (hnorm j) hline
  rcases htrans with h1 | h2'
  · have ht'2 : ρ (ggNSLiePI2_simpleSwap N j) * ρ (ggNSLiePI2_simpleSwap N j) = 1 := by
      have h := (hrefl ⟨j.1, by omega⟩ ⟨j.1 + 1, by omega⟩
        (ggNSLiePI2_simpleSwap_ne_self N j)).1
      rw [pow_two] at h
      exact h
    have heq : ρ (ggNSLiePI2_simpleSwap N i) = ρ (ggNSLiePI2_simpleSwap N j) := by
      calc ρ (ggNSLiePI2_simpleSwap N i)
          = ρ (ggNSLiePI2_simpleSwap N i) * 1 := (mul_one _).symm
        _ = ρ (ggNSLiePI2_simpleSwap N i) *
              (ρ (ggNSLiePI2_simpleSwap N j) * ρ (ggNSLiePI2_simpleSwap N j)) := by rw [ht'2]
        _ = (ρ (ggNSLiePI2_simpleSwap N i) * ρ (ggNSLiePI2_simpleSwap N j)) *
              ρ (ggNSLiePI2_simpleSwap N j) := by rw [mul_assoc]
        _ = 1 * ρ (ggNSLiePI2_simpleSwap N j) := by rw [h1]
        _ = ρ (ggNSLiePI2_simpleSwap N j) := one_mul _
    exact ggNSLiePI2_simpleSwap_ne N i j hij hij1 hi1j (hinj heq)
  · exact hnotr (ggNSLiePI2_simpleSwap N i * ggNSLiePI2_simpleSwap N j)
      (by simpa only [map_mul] using h2')

lemma ggNSLiePI2_hadj (hp : p.Prime) (hp2 : p ≠ 2) (hel : IsElemAbelian p Bs) [Finite Bs]
    [IsMulCommutative ↥Bs] [Module (ZMod p) (Additive ↥Bs)]
    (ρ : Equiv.Perm (Fin N) →* MulAut ↥Bs) (hinj : Function.Injective ρ)
    (hnotr : ∀ g : Equiv.Perm (Fin N), ¬ GGIsTransvection p (ρ g))
    (hrefl : ∀ a b : Fin N, a ≠ b → GGIsReflection p (ρ (Equiv.swap a b)))
    (i : Fin (N - 1)) (hi : (i : ℕ) + 1 < N - 1)
    {x : Fin (N - 1) → Additive ↥Bs} {g : Fin (N - 1) → Module.Dual (ZMod p) (Additive ↥Bs)}
    (hx0 : ∀ k, x k ≠ 0) (hgx : ∀ k, g k (x k) = 2)
    (hnorm : ∀ k v, ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N k)) v =
      v - g k v • x k) :
    g i (x ⟨i.1 + 1, hi⟩) * g ⟨i.1 + 1, hi⟩ (x i) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hbraid_perm := ggNSLiePI2_simpleSwap_braid N i hi
  have hbraid : ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N i)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N i)) =
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N i)) *
      ggNSLiePI2_linearEquivOfMulAut hp (ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩)) := by
    simp only [← ggNSLiePI2_linearEquivOfMulAut_mul]
    congr 1
    simp only [← map_mul]
    exact congrArg ρ hbraid_perm
  have hbraid' := ggNSLiePI2_braid (hnorm i) (hnorm ⟨i.1+1, hi⟩) (hgx i)
    (hgx ⟨i.1+1, hi⟩) hbraid
  by_contra hne
  have hfac : (1 - g i (x ⟨i.1+1, hi⟩) * g ⟨i.1+1, hi⟩ (x i)) ≠ 0 := by
    intro h0; exact hne (sub_eq_zero.mp h0).symm
  have hvec : g i (x ⟨i.1+1, hi⟩) • x i - 2 • x ⟨i.1+1, hi⟩ = 0 :=
    (smul_eq_zero.mp hbraid').resolve_left hfac
  by_cases hc : g i (x ⟨i.1+1, hi⟩) = 0
  · rw [hc, zero_smul, zero_sub] at hvec
    have hzero : x ⟨i.1+1, hi⟩ = 0 := by
      have hsm : (2 : ZMod p) • x ⟨i.1+1, hi⟩ = 0 := by
        have h' : (2 : ℕ) • x ⟨i.1+1, hi⟩ = 0 := neg_eq_zero.mp hvec
        rw [two_nsmul] at h'
        rw [two_smul]
        exact h'
      exact (smul_eq_zero.mp hsm).resolve_left h2
    exact hx0 _ hzero
  · have hline : x ⟨i.1+1, hi⟩ ∈ Submodule.span (ZMod p) {x i} := by
      rw [Submodule.mem_span_singleton]
      refine ⟨g i (x ⟨i.1+1, hi⟩) / 2, ?_⟩
      have hceq : g i (x ⟨i.1+1, hi⟩) • x i = 2 • x ⟨i.1+1, hi⟩ := by
        rw [sub_eq_zero] at hvec; exact hvec
      calc (g i (x ⟨i.1+1, hi⟩) / 2) • x i
          = ((2 : ZMod p)⁻¹ * g i (x ⟨i.1+1, hi⟩)) • x i := by rw [div_eq_inv_mul]
        _ = (2 : ZMod p)⁻¹ • (g i (x ⟨i.1+1, hi⟩) • x i) := by rw [mul_smul]
        _ = (2 : ZMod p)⁻¹ • ((2 : ℕ) • x ⟨i.1+1, hi⟩) := by rw [hceq]
        _ = x ⟨i.1+1, hi⟩ := by
          rw [two_nsmul, ← two_smul (ZMod p), smul_smul, inv_mul_cancel₀ h2, one_smul]
    have htrans := ggNSLiePI2_transvection_of_same_line hp hp2 hel
      (ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩)) (ρ (ggNSLiePI2_simpleSwap N i))
      (hrefl ⟨i.1 + 1, by omega⟩ ⟨i.1 + 2, by omega⟩ (ggNSLiePI2_simpleSwap_ne_self N ⟨i.1 + 1, hi⟩))
      (hrefl ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ (ggNSLiePI2_simpleSwap_ne_self N i))
      (hgx ⟨i.1+1, hi⟩) (hgx i) (hnorm ⟨i.1+1, hi⟩) (hnorm i) hline
    rcases htrans with h1 | h2'
    · have ht'2 : ρ (ggNSLiePI2_simpleSwap N i) * ρ (ggNSLiePI2_simpleSwap N i) = 1 := by
        have h := (hrefl ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩
          (ggNSLiePI2_simpleSwap_ne_self N i)).1
        rw [pow_two] at h
        exact h
      have heq : ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩) = ρ (ggNSLiePI2_simpleSwap N i) := by
        calc ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩)
            = ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩) * 1 := (mul_one _).symm
          _ = ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩) *
                (ρ (ggNSLiePI2_simpleSwap N i) * ρ (ggNSLiePI2_simpleSwap N i)) := by rw [ht'2]
          _ = (ρ (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩) * ρ (ggNSLiePI2_simpleSwap N i)) *
                ρ (ggNSLiePI2_simpleSwap N i) := by rw [mul_assoc]
          _ = 1 * ρ (ggNSLiePI2_simpleSwap N i) := by rw [h1]
          _ = ρ (ggNSLiePI2_simpleSwap N i) := one_mul _
      exact ggNSLiePI2_simpleSwap_ne_adj N i hi (hinj heq)
    · exact hnotr (ggNSLiePI2_simpleSwap N ⟨i.1+1, hi⟩ * ggNSLiePI2_simpleSwap N i)
        (by simpa only [map_mul] using h2')

end CFSG.StandardType

end
