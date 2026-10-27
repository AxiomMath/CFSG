module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem isCyclic_ringEquiv (K : Type) [Field K] [Finite K] : IsCyclic (K ≃+* K) := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  have hfin : Finite (ZMod (ringChar K)) := inferInstance
  let f : (K ≃ₐ[ZMod (ringChar K)] K) →* (K ≃+* K) :=
    { toFun := fun e => e.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    intro σ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), rfl⟩
    have := RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod (ringChar K)) K))
      (algebraMap (ZMod (ringChar K)) K)
    exact congrArg (fun φ => φ x) this
  exact isCyclic_of_surjective f hsurj

theorem ringEquiv_eq_of_sq_eq_one {K : Type} [Field K] [Finite K] (σ τ : K ≃+* K)
    (hσ : σ * σ = 1) (hτ : τ * τ = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  haveI := isCyclic_ringEquiv K
  haveI : Finite (K ≃+* K) := by
    haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
    exact Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
      (fun a b h => RingEquiv.ext (congrFun h))
  haveI := Fintype.ofFinite (K ≃+* K)
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) (by norm_num)
  have hsub : ({1, σ, τ} : Finset (K ≃+* K)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact hσ
    · rw [pow_two]; exact hτ
  have h3 : ({1, σ, τ} : Finset (K ≃+* K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp [Ne.symm hσ1, Ne.symm hτ1]
  have := Finset.card_le_card hsub
  omega

end CFSG.RankThree.GF2n.Stroth80
