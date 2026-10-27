module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSU

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (antidiag antidiag_mul_self)

namespace AutPSU

section Model

variable {K : Type} [Field K] {n : ℕ}

@[expose] def gramJ (n : ℕ) : GL (Fin n) K :=
  ⟨antidiag n, antidiag n, antidiag_mul_self n, antidiag_mul_self n⟩

theorem coe_gramJ : ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antidiag n :=
  rfl

theorem isPrimeFormGram_gramJ : IsPrimeFormGram (gramJ (K := K) n) :=
  RootDetectSU.isPrimeFormGram_of_eq_antidiag coe_gramJ

end Model

section Structure

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

abbrev XJ (h : UnitaryFieldData 2 f K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  gramSU h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

abbrev PJ (h : UnitaryFieldData 2 f K) (n : ℕ) : Type :=
  primeFormP h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

noncomputable abbrev inndiag : Subgroup (MulAut (PJ h n)) :=
  primeFormD h ((gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

noncomputable abbrev compl : Subgroup (MulAut (PJ h n)) :=
  (primeFormFieldHom h (isPrimeFormGram_gramJ (n := n))).range

omit [Field K] in
theorem not_three_of_four (hn : 4 ≤ n) : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega

theorem inndiag_normal (hn : 4 ≤ n) : (inndiag h (n := n)).Normal := by
  rw [inndiag, ← ker_primeFormFieldFactor h isPrimeFormGram_gramJ (by omega)
    (not_three_of_four hn)]
  infer_instance

theorem inn_le_inndiag :
    (MulAut.conj : PJ h n →* MulAut (PJ h n)).range ≤ inndiag h := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h _ s⟩

theorem odd_relIndex_inn_inndiag :
    Odd ((MulAut.conj : PJ h n →* MulAut (PJ h n)).range.relIndex (inndiag h)) := by
  have hdvd := card_primeFormD_quotient_dvd h (gramJ (K := K) n)
  have hodd : Odd (2 ^ f + 1) := by
    have : 1 ≤ f := h.one_le
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  exact Odd.of_dvd_nat hodd hdvd

theorem exists_mul_compl (hn : 4 ≤ n) (α : MulAut (PJ h n)) :
    ∃ i ∈ inndiag h, ∃ c ∈ compl h, α = i * c := by
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h isPrimeFormGram_gramJ (by omega)
    (not_three_of_four hn) α
  exact ⟨_, ⟨A, rfl⟩, _, ⟨φ, rfl⟩, primeFormPsi_apply h isPrimeFormGram_gramJ A φ⟩

theorem inndiag_inf_compl (hn : 4 ≤ n) : inndiag h ⊓ compl h (n := n) = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hcI, φ, rfl⟩
  have e := primeFormFieldFactor_apply h isPrimeFormGram_gramJ (by omega)
    (not_three_of_four hn) 1 φ
  rw [map_one, one_mul] at e
  have hk : primeFormFieldHom h isPrimeFormGram_gramJ φ ∈ (primeFormFieldFactor h
      isPrimeFormGram_gramJ (by omega) (not_three_of_four hn)).ker := by
    rw [ker_primeFormFieldFactor]
    exact hcI
  rw [MonoidHom.mem_ker, e] at hk
  rw [hk, map_one]
  exact Subgroup.one_mem _

end Structure

section Involution

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem isCyclic_ringEquiv : IsCyclic (K ≃+* K) := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let φ : (K ≃ₐ[ZMod 2] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine isCyclic_of_surjective φ fun e => ⟨AlgEquiv.ofRingEquiv (f := e) fun x => ?_, rfl⟩
  exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod
    ((e : K →+* K).comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))) x

include h in
theorem eq_sigma_of_mul_self_eq_one {φ : K ≃+* K} (hφ : φ * φ = 1) (hφ1 : φ ≠ 1) :
    φ = unitaryInvolution K 2 f := by
  classical
  have : IsCyclic (K ≃+* K) := isCyclic_ringEquiv
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) DFunLike.coe_injective
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  set σ := unitaryInvolution K 2 f
  have hσσ : σ * σ = 1 := RingEquiv.ext fun c => unitaryInvolution_involutive h.card_eq_sq c
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [RootDetectSU.bar_eq h]
    exact congrArg (fun e : K ≃+* K => e c) h1
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) (by norm_num)
  have hsub : ({1, σ, φ} : Finset (K ≃+* K)) ⊆
      Finset.univ.filter (fun a : K ≃+* K => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq, hσσ]
    · rw [sq, hφ]
  have hcard : ({1, σ, φ} : Finset (K ≃+* K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ1, Ne.symm hφ1⟩
  have := Finset.card_le_card hsub
  omega

theorem involution_compl (hn : 4 ≤ n) {c : MulAut (PJ h n)} (hc : c ∈ compl h)
    (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    c = primeFormFieldHom h isPrimeFormGram_gramJ (unitaryInvolution K 2 f) := by
  obtain ⟨φ, rfl⟩ := hc
  have hF : ∀ ψ : K ≃+* K, primeFormFieldFactor h isPrimeFormGram_gramJ (by omega)
      (not_three_of_four hn) (primeFormFieldHom h isPrimeFormGram_gramJ ψ) = ψ := fun ψ => by
    have e := primeFormFieldFactor_apply h (isPrimeFormGram_gramJ (n := n)) (by omega)
      (not_three_of_four hn) 1 ψ
    rwa [map_one, one_mul] at e
  have hφφ : φ * φ = 1 := by
    have e := congrArg (primeFormFieldFactor h isPrimeFormGram_gramJ (by omega)
      (not_three_of_four hn)) hc2
    rwa [map_pow, hF, map_one, sq] at e
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    exact hc1 (map_one _)
  rw [eq_sigma_of_mul_self_eq_one h hφφ hφ1]

end Involution

end AutPSU

end CFSG.StandardType
