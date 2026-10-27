module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Assembly
public import CFSG.SignalizerFunctorTheorem.McBride.Models.FrameItems
public import CFSG.SignalizerFunctorTheorem.NearModels.Main

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

theorem near_aut_pSubgroup_card_dvd
    (h : NearSimple p X) (P : Subgroup (MulAut X))
    (hP : IsPGroup p P) : Nat.card P ∣ p :=
  NearModels.nearSimpleModel_card_pSubgroup_dvd h.prime h.model h.coprime P hP

theorem near_aut_sylow_cyclic
    (h : NearSimple p X) (P : Subgroup (MulAut X))
    (hP : IsPGroup p P) : IsCyclic P := by
  have hd := near_aut_pSubgroup_card_dvd h P hP
  rcases (Nat.dvd_prime h.prime).mp hd with h1 | h1
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have := Fact.mk h.prime
    exact isCyclic_of_prime_card h1

omit [Finite X] in
theorem near_exists_aut
    (h : NearSimple p X) : ∃ f : MulAut X, orderOf f = p :=
  exists_aut_of_nearSimple h

omit [Finite X] in
theorem near_aut_centralizer_pGroup
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    IsPGroup p (fixingSubgroup (MulAut X) (signalizerFixedSubgroup f : Set X)) :=
  itemC_of_nearSimple h hf

theorem near_unique_maximal
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    signalizerFixedSubgroup f ≤ fixedNormalizer f ∧ fixedNormalizer f ≠ ⊤ ∧
      Group.IsSolvable (fixedNormalizer f) ∧
      ∀ H : Subgroup X, signalizerFixedSubgroup f ≤ H → H ≠ ⊤ → H ≤ fixedNormalizer f := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.unique_maximal

theorem near_unique_maximal_coatom
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    signalizerFixedSubgroup f ≤ fixedNormalizer f ∧ IsCoatom (fixedNormalizer f) ∧
      ∀ H : Subgroup X, IsCoatom H → signalizerFixedSubgroup f ≤ H → H = fixedNormalizer f := by
  obtain ⟨hCM, hMtop, -, hH⟩ := near_unique_maximal h hf
  refine ⟨hCM, ⟨hMtop, fun H hMH => ?_⟩, fun H hmax hCH => ?_⟩
  · by_contra hne
    exact (not_le_of_gt hMH) (hH H (hCM.trans hMH.le) hne)
  · have hHM : H ≤ fixedNormalizer f := hH H hCH hmax.1
    by_contra hne
    exact hMtop (hmax.2 _ (lt_of_le_of_ne hHM hne))

theorem near_frobenius
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    IsFrobeniusWithKernel (fixedCore1 f) (fixedFitting f) ∧
      IsFrobeniusWithKernel (signalizerFixedSubgroup f) (fixedFitting f) ∧
      IsFrobeniusWithKernel (fixedNormalizer f) (CFSG.fittingSubgroupOf (fixedNormalizer f)) ∧
      IsMulCommutative (fixedFitting f) ∧
      IsMulCommutative (CFSG.fittingSubgroupOf (fixedNormalizer f)) := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.frobenius

theorem near_fitting_eq_centralizer
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    CFSG.fittingSubgroupOf (fixedNormalizer f) = Subgroup.centralizer (fixedFitting f : Set X) ∧
      (CFSG.fittingSubgroupOf (fixedNormalizer f) : Set X) *
        (signalizerFixedSubgroup f : Set X) = (fixedNormalizer f : Set X) := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.fitting_eq_centralizer

omit [Finite X] in
theorem near_coprime_aut_inner
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p)
    (g : MulAut X) (hg : Nat.Coprime p (orderOf g))
    (hM : ∀ m ∈ fixedNormalizer f, g m ∈ fixedNormalizer f)
    (hF : ∀ m ∈ fixedNormalizer f,
      m⁻¹ * g m ∈ CFSG.fittingSubgroupOf (fixedNormalizer f)) :
    ∃ m ∈ fixedNormalizer f, g = MulAut.conj m :=
  itemG_of_nearSimple h hf g hg hM hF

theorem near_minimal_normal
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    fixedFitting f ≠ ⊥ ∧ ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).Normal ∧
      ∀ N : Subgroup X, N ≤ signalizerFixedSubgroup f →
        (N.subgroupOf (signalizerFixedSubgroup f)).Normal → N ≠ ⊥ → fixedFitting f ≤ N := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.minimal_normal

theorem near_invariant_subgroup
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p)
    (Y : Subgroup X) (hY : Y ≠ ⊤)
    (hC : signalizerFixedSubgroup f ≤ Subgroup.normalizer (Y : Set X)) :
    fixedFitting f ≤ Y ∨ Y ≤ autCommutator f (CFSG.fittingSubgroupOf (fixedNormalizer f)) := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.invariant_subgroup Y hY hC

theorem autCommutator_fitting_eq
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    autCommutator f (CFSG.fittingSubgroupOf (fixedNormalizer f)) =
      autCommutator f (fixedNormalizer f) := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.autCommutator_fitting_eq

theorem near_nilpotent_le_fitting
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p)
    (Y : Subgroup X) (hY : Group.IsNilpotent Y)
    (hC : signalizerFixedSubgroup f ≤ Subgroup.normalizer (Y : Set X)) :
    Y ≤ CFSG.fittingSubgroupOf (fixedNormalizer f) := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.nilpotent_le_fitting Y hY hC

theorem near_conj_class
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p)
    (M' : Subgroup X) (hM' : Nonempty (M' ≃* fixedNormalizer f)) :
    ∃ g : X, M' = (fixedNormalizer f).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨ℓ, hF⟩ := frame_of_nearSimple h hf
  exact hF.conj_class M' hM'

theorem near_exists_prime_not_dvd
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f) :=
  (itemO_of_nearSimple h hf).1

theorem near_sylow_abelian
    (h : NearSimple p X) {f : MulAut X} (hf : orderOf f = p) {r : ℕ}
    (hr : r.Prime) (hrX : r ∣ Nat.card X) (hrM : ¬ r ∣ Nat.card (fixedNormalizer f))
    (R : Sylow r X) : IsMulCommutative (R : Subgroup X) :=
  (itemO_of_nearSimple h hf).2 r hr hrX hrM R

end CFSG.SignalizerFunctorTheorem.McBride
