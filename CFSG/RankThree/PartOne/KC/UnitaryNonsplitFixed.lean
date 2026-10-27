module

public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitAction
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitOrbits

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {x : gramSU h (idGram K n)} (L : LiftData h n p x)

include L in
theorem LiftData.fixesIdempotents_of_card_orbits_lt [DecidableEq (primaryFactors (idEnd x))]
    (hp2 : p ≠ 2) {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hA : IsPGroup p ↥A)
    (hAle : A ≤ idStab x)
    (hκ : Nat.card (adjointOrbits h (toLinU h n (liftUnitary x))) < p) (a : ↥A) :
    L.FixesIdempotents hAle a := by
  have hα := conj_eq_of_mem_idStab (hAle a.2)
  obtain ⟨⟨M, σ⟩, hMσ⟩ := surjective_primeFormPsi L.three_le L.four_le
    (a : MulAut (primeFormP h (idGram K n)))
  obtain ⟨k, hk⟩ := hA a
  have hσk : σ ^ p ^ k = 1 := by
    have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n))
        ((⟨M, σ⟩ : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
          (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) ^ p ^ k) = 1 := by
      rw [map_pow, hMσ]
      have := congrArg Subtype.val hk
      simpa using this
    have h2 := ((primeFormPsi_eq_one_iff' L.three_le L.four_le _).mp h1).1
    have h3 := map_pow (SemidirectProduct.rightHom) (⟨M, σ⟩ : primeFormUnitary h (idGram K n) ⋊[
      primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) (p ^ k)
    exact h3.symm.trans h2
  have H := L.primaryData
  have hfix : ∀ b ∈ primaryFactors (idEnd x), b.map (σ : K →+* K) = b := by
    refine fix_of_card_orbits_lt (S := (primaryFactors (idEnd x) : Set K[X]))
      (Finset.finite_toSet _) (Polynomial.map (σ : K →+* K)) (dualPoly h.bar) ?_ ?_ ?_ ?_
      (k := k) L.prime hp2 ?_ hκ
    · intro b hb
      exact L.map_mem_primaryFactors hα hMσ hb
    · intro b hb
      exact dualPoly_mem_primaryFactors H hb
    · intro b hb
      exact dualPoly_dualPoly_of_mem H hb
    · intro b _
      exact (dualPoly_map_comm h σ b).symm
    · intro b _
      exact map_iterate_eq σ _ hσk b
  exact L.fixesIdempotents_of_proj hAle a fun i hi => L.actEnd_primaryProjection hα hMσ hfix hi

@[expose] def idAdjointOrbits (x : gramSU h (idGram K n)) :
    Set (Set (Module.End K (Fin n → K))) :=
  {O | ∃ r : ↥(idCommutant x), IsPrimitiveCentralIdempotent K r ∧
    O = {(r : Module.End K (Fin n → K)),
      hermAdjoint (idForm_isSymm h n) (idForm_separatingLeft h n)
        (r : Module.End K (Fin n → K))}}

include L in
theorem LiftData.primaryProjection_injOn :
    Set.InjOn (primaryProjection (idEnd x)) (primaryFactors (idEnd x) : Set K[X]) := by
  intro a ha b hb hab
  by_contra hne
  have hsq := L.squarefree_idEnd
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  apply hv0
  have h1 : primaryProjection (idEnd x) a v = v := primaryProjection_of_mem hsq ha hv
  have h2 : primaryProjection (idEnd x) b v = 0 :=
    primaryProjection_of_mem_ne hsq hb ha hne hv
  rw [← h1, hab, h2]

include L in
theorem LiftData.idAdjointOrbits_eq :
    idAdjointOrbits x = (fun O : Set K[X] => primaryProjection (idEnd x) '' O) ''
      adjointOrbits h (toLinU h n (liftUnitary x)) := by
  have hsq := L.squarefree_idEnd
  have H := L.primaryData
  have hadj : ∀ a ∈ primaryFactors (idEnd x),
      hermAdjoint (idForm_isSymm h n) (idForm_separatingLeft h n)
        ((primaryProjectionR (idEnd x) a : ↥(idCommutant x)) : Module.End K (Fin n → K)) =
      primaryProjection (idEnd x) (dualPoly h.bar a) := fun a ha => adj_primaryProjection H ha
  ext O
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (isPrimitiveCentralIdempotent_iff hsq r).mp hr
    refine ⟨{a, dualPoly h.bar a}, ⟨a, ha, rfl⟩, ?_⟩
    simp only [Set.image_pair]
    rw [hadj a ha]
    rfl
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨primaryProjectionR (idEnd x) a, (isPrimitiveCentralIdempotent_iff hsq _).mpr
      ⟨a, ha, rfl⟩, ?_⟩
    simp only [Set.image_pair]
    rw [hadj a ha]
    rfl

include L in
theorem LiftData.card_idAdjointOrbits :
    Nat.card ↥(idAdjointOrbits x) = Nat.card ↥(adjointOrbits h (toLinU h n (liftUnitary x))) := by
  have H := L.primaryData
  rw [L.idAdjointOrbits_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  refine Set.InjOn.ncard_image ?_
  have hsub : ∀ O ∈ adjointOrbits h (toLinU h n (liftUnitary x)),
      O ⊆ (primaryFactors (idEnd x) : Set K[X]) := by
    rintro _ ⟨a, ha, rfl⟩ b hb
    rcases hb with rfl | hb
    · exact ha
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact dualPoly_mem_primaryFactors H ha
  intro O hO O' hO' hOO'
  exact ((L.primaryProjection_injOn).image_eq_image_iff (hsub O hO) (hsub O' hO')).mp hOO'

include L in
theorem LiftData.pow_toLinU :
    ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ p = 1 := by
  have hxp : (toLinU h n (liftUnitary x)) ^ p = 1 := by
    rw [← map_pow]
    have : (liftUnitary x) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact congrArg Subtype.val L.pow_eq_one)
    rw [this, map_one]
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (g : Module.End K (Fin n → K))) hxp
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h2

end CFSG.RankThree.PartOne.KCUnitaryModel
