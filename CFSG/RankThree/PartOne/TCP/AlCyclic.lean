module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.TCP

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_cyclic_of_multiplicity_le_one {x : Module.End K V}
    (hsq : Squarefree (minpoly K x))
    (hm : ∀ a : primaryFactors x, primaryMultiplicity x (a : K[X]) ≤ 1) :
    ∃ v : V, ∀ w : V, ∃ P : K[X], aeval x P v = w := by
  classical
  have hgen : ∀ a : primaryFactors x, ∃ va : primaryComponent x (a : K[X]),
      ∀ w : primaryComponent x (a : K[X]), ∃ P : K[X], aeval x P (va : V) = (w : V) := by
    intro a
    have hne : Nontrivial (primaryComponent x (a : K[X])) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq a.2)
    have h1 : Module.finrank (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])) = 1 := by
      have h0 : 0 < Module.finrank (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])) :=
        Module.finrank_pos
      have h1' : Module.finrank (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])) ≤ 1 :=
        hm a
      omega
    obtain ⟨v, hv⟩ := exists_ne (0 : primaryComponent x (a : K[X]))
    refine ⟨v, fun w => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h1 w
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective c
    exact ⟨P, by rw [← hc, coe_mk_smul_primaryComponent]⟩
  choose va hva using hgen
  refine ⟨∑ a : primaryFactors x, (va a : V), fun w => ?_⟩
  choose Pa hPa using fun a : primaryFactors x => hva a (primaryCoords x hsq w a)
  refine ⟨∑ a : primaryFactors x, Pa a * primaryIdempotent x (a : K[X]), ?_⟩
  have hεv : ∀ a : primaryFactors x, aeval x (primaryIdempotent x (a : K[X]))
      (∑ b : primaryFactors x, (va b : V)) = (va a : V) := by
    intro a
    change primaryProjection x (a : K[X]) (∑ b : primaryFactors x, (va b : V)) = _
    rw [map_sum, Finset.sum_eq_single a]
    · exact primaryProjection_of_mem hsq a.2 (va a).2
    · intro b _ hab
      exact primaryProjection_of_mem_ne hsq a.2 b.2 (fun h => hab (Subtype.ext h)) (va b).2
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hw := primarySum_primaryCoords hsq w
  rw [primarySum_apply] at hw
  conv_rhs => rw [← hw]
  rw [map_sum (aeval x), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, Module.End.mul_apply, hεv a, hPa a]

omit [FiniteDimensional K V] in
theorem commute_of_cyclic {x : Module.End K V} {v : V}
    (hv : ∀ w : V, ∃ P : K[X], aeval x P v = w) {g g' : Module.End K V} (hg : g * x = x * g)
    (hg' : g' * x = x * g') : g * g' = g' * g := by
  have hcomm : ∀ (h : Module.End K V), h * x = x * h → ∀ P : K[X],
      h * aeval x P = aeval x P * h := fun h hh P => by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
    | monomial n a =>
      rw [aeval_monomial]
      calc h * (algebraMap K (Module.End K V) a * x ^ n)
          = (h * algebraMap K (Module.End K V) a) * x ^ n := by rw [mul_assoc]
        _ = (algebraMap K (Module.End K V) a * h) * x ^ n := by
            rw [← Algebra.commutes (A := Module.End K V) a h]
        _ = algebraMap K (Module.End K V) a * (h * x ^ n) := by rw [mul_assoc]
        _ = algebraMap K (Module.End K V) a * (x ^ n * h) := by
            rw [((show Commute h x from hh).pow_right n).eq]
        _ = (algebraMap K (Module.End K V) a * x ^ n) * h := by rw [mul_assoc]
  have hap : ∀ (h : Module.End K V), h * x = x * h → ∀ (P : K[X]) (u : V),
      h (aeval x P u) = aeval x P (h u) := fun h hh P u => by
    have := congrArg (fun f : Module.End K V => f u) (hcomm h hh P)
    simpa [Module.End.mul_apply] using this
  have hpoly : ∀ (P Q : K[X]) (u : V), aeval x P (aeval x Q u) = aeval x Q (aeval x P u) :=
    fun P Q u => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  obtain ⟨t, ht⟩ := hv (g v)
  obtain ⟨t', ht'⟩ := hv (g' v)
  refine LinearMap.ext fun w => ?_
  obtain ⟨s, rfl⟩ := hv w
  rw [Module.End.mul_apply, Module.End.mul_apply]
  calc g (g' (aeval x s v)) = aeval x s (g (g' v)) := by rw [hap g' hg', hap g hg]
    _ = aeval x s (aeval x t' (aeval x t v)) := by
        rw [← ht', hap g hg t' v, ht]
    _ = aeval x s (aeval x t (aeval x t' v)) := by rw [hpoly t' t v]
    _ = aeval x s (g' (g v)) := by rw [← ht, hap g' hg' t v, ht']
    _ = g' (g (aeval x s v)) := by rw [hap g hg, hap g' hg']

end Generic

section Descent

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

variable {K : Type} [Field K] (k : Subfield K)

theorem spEnd_subfieldSpHom {r : ℕ} (g : StatedSp r k) (w : Fin r ⊕ Fin r → k) :
    spEnd (subfieldSpHom r k g) (fun i => (w i : K)) = fun i => ((spEnd g w i : k) : K) := by
  rw [spEnd_apply, spEnd_apply]
  funext i
  have h := RingHom.map_mulVec k.subtype
    ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) w i
  exact h.symm

theorem pow_spEnd_subfieldSpHom {r : ℕ} (g : StatedSp r k) (n : ℕ) (w : Fin r ⊕ Fin r → k) :
    (spEnd (subfieldSpHom r k g) ^ n) (fun i => (w i : K)) =
      fun i => (((spEnd g ^ n) w i : k) : K) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, spEnd_subfieldSpHom, ih, pow_succ, Module.End.mul_apply]

theorem aeval_spEnd_subfieldSpHom {r : ℕ} (g : StatedSp r k) (P : k[X])
    (w : Fin r ⊕ Fin r → k) :
    aeval (spEnd (subfieldSpHom r k g)) (P.map k.subtype) (fun i => (w i : K)) =
      fun i => ((aeval (spEnd g) P w i : k) : K) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, map_add, LinearMap.add_apply]
    funext i
    simp
  | monomial n c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, pow_spEnd_subfieldSpHom]
    funext i
    simp [Module.algebraMap_end_apply]

theorem cyclic_map_subfield {r : ℕ} (g : StatedSp r k) {v₀ : Fin r ⊕ Fin r → k}
    (hv₀ : ∀ w : Fin r ⊕ Fin r → k, ∃ P : k[X], aeval (spEnd g) P v₀ = w) :
    ∃ v : Fin r ⊕ Fin r → K, ∀ w : Fin r ⊕ Fin r → K,
      ∃ P : K[X], aeval (spEnd (subfieldSpHom r k g)) P v = w := by
  classical
  refine ⟨fun i => (v₀ i : K), fun w => ?_⟩
  choose P hP using fun i : Fin r ⊕ Fin r => hv₀ (Pi.single i 1)
  refine ⟨∑ i, C (w i) * (P i).map k.subtype, ?_⟩
  have hsingle : ∀ i : Fin r ⊕ Fin r, (fun j => ((Pi.single i (1 : k) : Fin r ⊕ Fin r → k) j : K))
      = (Pi.single i (1 : K) : Fin r ⊕ Fin r → K) := fun i => by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [map_sum, LinearMap.sum_apply]
  have : ∀ i : Fin r ⊕ Fin r, aeval (spEnd (subfieldSpHom r k g)) (C (w i) * (P i).map k.subtype)
      (fun j => (v₀ j : K)) = w i • (Pi.single i (1 : K) : Fin r ⊕ Fin r → K) := fun i => by
    rw [map_mul, Module.End.mul_apply, aeval_spEnd_subfieldSpHom, hP i, hsingle i, aeval_C,
      Module.algebraMap_end_apply]
  simp only [this]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

end Descent

end CFSG.RankThree.PartOne.TCP
