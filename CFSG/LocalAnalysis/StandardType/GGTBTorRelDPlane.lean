module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import TauCeti.LinearAlgebra.Determinant
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import Mathlib.Algebra.CharP.CharAndCard
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

open scoped Classical

open Module QuadraticMap
open CFSG.ClassicalGroups.Orthogonal

namespace CFSG.StandardType

namespace RelDPlane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {U : Type} [AddCommGroup U] [Module K U]
  {Q : QuadraticForm K U}

theorem exists_map_ne_zero (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : ∃ u : U, Q u ≠ 0 := by
  classical
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  by_contra h
  push Not at h
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  refine hu (hQ.1 u fun v => ?_)
  simp [polarBilin_apply_apply, polar, h]

theorem not_scalar (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0) :
    ∀ a : K, (c : Module.End K U) ≠ a • 1 := by
  classical
  intro a ha
  obtain ⟨u, huQ⟩ := exists_map_ne_zero (Q := Q) hU hQ
  have hcu : c u = a • u := by
    have h := congrArg (fun f : Module.End K U => f u) ha
    simpa using h
  have hiso : Q (c u) = Q u :=
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hc u
  rw [hcu, map_smul_eq_sq] at hiso
  have hsq : a ^ 2 = 1 := by
    have h0 : (a ^ 2 - 1) * Q u = 0 := by linear_combination hiso
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h huQ
  have ha1 : a = 1 := by
    have hfac : (a - 1) * (a - 1) = 0 := by
      calc (a - 1) * (a - 1) = a ^ 2 - 2 * a + 1 := by ring
        _ = 1 - 0 + 1 := by rw [hsq, CharTwo.two_eq_zero, zero_mul]
        _ = 0 := by rw [sub_zero, one_add_one_eq_two, CharTwo.two_eq_zero]
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exact sub_eq_zero.mp h
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  apply hu
  apply hfix u
  have hcu' : c u = u := by
    have h := congrArg (fun f : Module.End K U => f u) ha
    simpa [ha1] using h
  exact hcu'

theorem exists_cyclic_vector (hU : Module.finrank K U = 2) {c : Module.End K U}
    (hcns : ∀ a : K, c ≠ a • 1) :
    ∃ v : U, LinearIndependent K ![v, c v] := by
  classical
  haveI : FiniteDimensional K U := .of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq K U hU
  by_contra h
  push Not at h
  have heig : ∀ v : U, ∃ a : K, c v = a • v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by rw [hv, map_zero, zero_smul]⟩
    · have hne : ∃ a : K, a • v = c v := by
        by_contra hc0
        push Not at hc0
        exact h v (by rwa [LinearIndependent.pair_iff' hv])
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha.symm⟩
  set a0 := Classical.choose (heig (b 0))
  have hb0 : c (b 0) = a0 • b 0 := Classical.choose_spec (heig (b 0))
  set a1 := Classical.choose (heig (b 1))
  have hb1 : c (b 1) = a1 • b 1 := Classical.choose_spec (heig (b 1))
  obtain ⟨a, ha⟩ := heig (b 0 + b 1)
  have hsum : a0 • b 0 + a1 • b 1 = a • b 0 + a • b 1 := by
    calc a0 • b 0 + a1 • b 1 = c (b 0 + b 1) := by rw [map_add, hb0, hb1]
      _ = a • (b 0 + b 1) := ha
      _ = a • b 0 + a • b 1 := smul_add _ _ _
  have hind : LinearIndependent K ![b 0, b 1] := by
    have h := b.linearIndependent
    have hfun : (⇑b : Fin 2 → U) = ![b 0, b 1] := by
      funext i; fin_cases i <;> rfl
    rwa [hfun] at h
  have hcoeff := hind.eq_of_pair hsum
  have ha0 : a0 = a := hcoeff.1
  have ha1 : a1 = a := hcoeff.2
  refine hcns a ?_
  apply LinearMap.ext
  intro u
  have hu : u = b.repr u 0 • b 0 + b.repr u 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr u, Fin.sum_univ_two]
  rw [hu]
  change c ((b.repr u) 0 • b 0 + (b.repr u) 1 • b 1) =
    (a • (1 : Module.End K U)) ((b.repr u) 0 • b 0 + (b.repr u) 1 • b 1)
  rw [map_add, map_smul, map_smul, hb0, hb1, ha0, ha1]
  simp only [LinearMap.smul_apply, Module.End.one_apply, smul_add, smul_smul]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem centralizer_eq_adjoin (hU : Module.finrank K U = 2) {c : Module.End K U}
    (hcns : ∀ a : K, c ≠ a • 1) :
    Subalgebra.centralizer K ({c} : Set (Module.End K U)) = Algebra.adjoin K {c} := by
  classical
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨v, hv⟩ := exists_cyclic_vector (K := K) (U := U) hU hcns
    haveI : FiniteDimensional K U := .of_finrank_pos (by omega)
    let b : Basis (Fin 2) K U :=
      basisOfLinearIndependentOfCardEqFinrank (b := ![v, c v]) hv (by simp [hU])
    have hb0 : b 0 = v := by
      dsimp only [b]
      simp
    have hb1 : b 1 = c v := by
      dsimp only [b]
      simp
    set a0 : K := b.repr (g v) 0
    set a1 : K := b.repr (g v) 1
    set p : Module.End K U := a0 • 1 + a1 • c
    have hp : p ∈ Algebra.adjoin K ({c} : Set (Module.End K U)) := by
      have h1 : (1 : Module.End K U) ∈ Algebra.adjoin K ({c} : Set (Module.End K U)) :=
        (Algebra.adjoin K ({c} : Set (Module.End K U))).one_mem
      have hc' : c ∈ Algebra.adjoin K ({c} : Set (Module.End K U)) :=
        Algebra.self_mem_adjoin_singleton K c
      have h2 : a0 • (1 : Module.End K U) ∈
          Algebra.adjoin K ({c} : Set (Module.End K U)) := Subalgebra.smul_mem _ h1 a0
      have h3 : a1 • c ∈ Algebra.adjoin K ({c} : Set (Module.End K U)) :=
        Subalgebra.smul_mem _ hc' a1
      exact Subalgebra.add_mem _ h2 h3
    have hrepr : g v = a0 • b 0 + a1 • b 1 := by
      conv_lhs => rw [← b.sum_repr (g v), Fin.sum_univ_two]
    have hgv : g v = p v := by
      rw [hrepr, hb0, hb1]
      simp [p, LinearMap.add_apply, LinearMap.smul_apply]
    have hgc : c * g = g * c := (Subalgebra.mem_centralizer_iff _).1 hg c rfl
    have hgc_apply (w : U) : g (c w) = c (g w) := by
      have h := congrArg (fun f : Module.End K U => f w) hgc
      simpa [Module.End.mul_apply] using h.symm
    have hpc : c * p = p * c := by
      have hadj_le : Algebra.adjoin K ({c} : Set (Module.End K U)) ≤
          Subalgebra.centralizer K ({c} : Set (Module.End K U)) := by
        refine Algebra.adjoin_le ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (Subalgebra.mem_centralizer_iff _).2 fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (Commute.refl y).eq
      exact (Subalgebra.mem_centralizer_iff _).1 (hadj_le hp) c rfl
    have hgw : ∀ w : U, g w = p w := by
      intro w
      have hw : w = b.repr w 0 • b 0 + b.repr w 1 • b 1 := by
        conv_lhs => rw [← b.sum_repr w, Fin.sum_univ_two]
      rw [hw, map_add, map_smul, map_smul]
      have hg0 : g (b 0) = p (b 0) := by rw [hb0]; exact hgv
      have hg1 : g (b 1) = p (b 1) := by
        rw [hb1, hgc_apply, hgv]
        have h := congrArg (fun f : Module.End K U => f v) hpc
        simpa [Module.End.mul_apply] using h
      rw [hg0, hg1, map_add, map_smul, map_smul]
    have hg_eq : g = p := LinearMap.ext hgw
    rwa [hg_eq]
  · refine Algebra.adjoin_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (Subalgebra.mem_centralizer_iff _).2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Commute.refl y).eq

theorem mem_adjoin_of_mem_centralizer_group (hU : Module.finrank K U = 2)
    {c : U ≃ₗ[K] U} (hcns : ∀ a : K, (c : Module.End K U) ≠ a • 1)
    {g : U ≃ₗ[K] U}
    (hg : g ∈ Subgroup.centralizer ({c} : Set (U ≃ₗ[K] U))) :
    (g : Module.End K U) ∈
      Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U)) := by
  have hcent_eq := centralizer_eq_adjoin (K := K) (U := U) hU hcns
  have hg' : c * g = g * c := Subgroup.mem_centralizer_iff.1 hg c rfl
  have hg_cent : (g : Module.End K U) ∈
      Subalgebra.centralizer K ({(c : Module.End K U)} : Set (Module.End K U)) := by
    refine (Subalgebra.mem_centralizer_iff _).2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hg']
  rwa [hcent_eq] at hg_cent

theorem centralizer_comm (hU : Module.finrank K U = 2)
    {c : U ≃ₗ[K] U} (hcns : ∀ a : K, (c : Module.End K U) ≠ a • 1)
    {g h : U ≃ₗ[K] U}
    (hg : g ∈ Subgroup.centralizer ({c} : Set (U ≃ₗ[K] U)))
    (hh : h ∈ Subgroup.centralizer ({c} : Set (U ≃ₗ[K] U))) : g * h = h * g := by
  have hg_adj := mem_adjoin_of_mem_centralizer_group (K := K) (U := U) (c := c) hU hcns hg
  have hh_adj := mem_adjoin_of_mem_centralizer_group (K := K) (U := U) (c := c) hU hcns hh
  letI : IsMulCommutative (Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U))) :=
    Algebra.isMulCommutative_adjoin_singleton (R := K) (x := (c : Module.End K U))
  have hcomm_sub :
      (⟨(g : Module.End K U), hg_adj⟩ :
        Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U))) *
      (⟨(h : Module.End K U), hh_adj⟩ :
        Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U))) =
      (⟨(h : Module.End K U), hh_adj⟩ :
        Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U))) *
      (⟨(g : Module.End K U), hg_adj⟩ :
        Algebra.adjoin K ({(c : Module.End K U)} : Set (Module.End K U))) :=
    mul_comm _ _
  have hcomm : (g : Module.End K U) * (h : Module.End K U) =
      (h : Module.End K U) * (g : Module.End K U) := congrArg Subtype.val hcomm_sub
  apply LinearEquiv.ext
  intro u
  change g (h u) = h (g u)
  exact LinearMap.congr_fun hcomm u

theorem hypPair_linearIndependent {P : HypPair Q} :
    LinearIndependent K ![P.e, P.f] := by
  rw [linearIndependent_fin2]
  change P.f ≠ 0 ∧ ∀ a : K, a • P.f ≠ P.e
  refine ⟨P.f_ne_zero, fun a ha => ?_⟩
  have h := congrArg (polar Q P.f) ha
  rw [polar_smul_right_eq, P.polar_ff, mul_zero, P.polar_fe] at h
  exact one_ne_zero h.symm

noncomputable def hypPairBasis (hU : Module.finrank K U = 2) (P : HypPair Q) :
    Basis (Fin 2) K U :=
  basisOfLinearIndependentOfCardEqFinrank (b := ![P.e, P.f])
    (hypPair_linearIndependent (Q := Q)) (by simp [hU])

@[simp] theorem hypPairBasis_zero (hU : Module.finrank K U = 2) (P : HypPair Q) :
    hypPairBasis (Q := Q) hU P 0 = P.e := by
  dsimp only [hypPairBasis]; simp

@[simp] theorem hypPairBasis_one (hU : Module.finrank K U = 2) (P : HypPair Q) :
    hypPairBasis (Q := Q) hU P 1 = P.f := by
  dsimp only [hypPairBasis]; simp

theorem isPlusType_iff_exists_singular (hU : Module.finrank K U = 2) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ ∃ u : U, u ≠ 0 ∧ Q u = 0 := by
  constructor
  · rintro ⟨W, hWdim, hWQ⟩
    have hW1 : Module.finrank K W = 1 := by omega
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (M := W) (by rw [hW1]; norm_num)
    obtain ⟨u, hu0⟩ := exists_ne (0 : W)
    exact ⟨u, fun h => hu0 (Subtype.ext h), hWQ u u.2⟩
  · rintro ⟨u, hu0, huQ⟩
    refine ⟨Submodule.span K {u}, ?_, ?_⟩
    · rw [finrank_span_singleton (K := K) hu0]
      omega
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul_eq_sq, huQ, mul_zero]

theorem card_orthogonalGroup_of_isPlusType (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * (Nat.card K - 1) := by
  haveI : FiniteDimensional K U := .of_finrank_pos (by rw [hU]; norm_num)
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := K) (V := U)
    (Q := Q) hQ (m := 0) (by rw [hU]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty] at h
  simp only [Nat.zero_mul, Nat.zero_add, pow_zero, pow_one, mul_one, one_mul] at h
  have hq : 1 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
  have hcast : ((2 * (Nat.card K - 1) : ℕ) : ℤ) = 2 * ((Nat.card K : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_ofNat, Nat.cast_one]
  rw [← hcast] at h
  exact_mod_cast h

theorem even_natCard (h2 : (2 : K) = 0) : Even (Nat.card K) := by
  letI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hdvd : 2 ∣ Nat.card K := by
    have h := (prime_dvd_char_iff_dvd_card (R := K) 2).mp (by rw [hchar])
    simpa [Nat.card_eq_fintype_card] using h
  exact (even_iff_two_dvd).mpr hdvd

theorem coprime_natCard_sub_one_add_one (h2 : (2 : K) = 0) :
    Nat.Coprime (Nat.card K - 1) (Nat.card K + 1) := by
  have hqeven : Even (Nat.card K) := even_natCard (K := K) h2
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := (even_iff_exists_two_mul).mp hqeven
  have hkpos : 1 ≤ k := by omega
  have hodd : Odd (Nat.card K - 1) := by
    refine ⟨k - 1, ?_⟩
    omega
  have h : Nat.card K + 1 = 2 + (Nat.card K - 1) := by omega
  rw [h, Nat.coprime_add_self_right]
  exact Nat.coprime_two_right.mpr hodd

theorem hyperbolic_isometry_eq_one_of_pow_card_add_one (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {h : U ≃ₗ[K] U} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hpow : h ^ (Nat.card K + 1) = 1) : h = 1 := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let ho : O := ⟨h, hh⟩
  have hOcard : Nat.card O = 2 * (Nat.card K - 1) :=
    card_orthogonalGroup_of_isPlusType (Q := Q) hU hQ hplus
  have horder_add : orderOf ho ∣ Nat.card K + 1 := by
    rw [← Subgroup.orderOf_coe ho]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hqeven : Even (Nat.card K) := even_natCard (K := K) CharTwo.two_eq_zero
  have hodd_add : Odd (Nat.card K + 1) := hqeven.add_one
  have hodd : Odd (orderOf ho) :=
    Nat.not_even_iff_odd.mp fun heven =>
      hodd_add.not_two_dvd_nat (heven.two_dvd.trans horder_add)
  have horder_O : orderOf ho ∣ Nat.card O := orderOf_dvd_natCard ho
  rw [hOcard] at horder_O
  have hcop2 : Nat.Coprime (orderOf ho) 2 := Nat.coprime_two_right.mpr hodd
  have horder_sub : orderOf ho ∣ Nat.card K - 1 :=
    hcop2.dvd_of_dvd_mul_left horder_O
  have hcop : Nat.Coprime (Nat.card K - 1) (Nat.card K + 1) :=
    coprime_natCard_sub_one_add_one (K := K) CharTwo.two_eq_zero
  have horder_one : orderOf ho = 1 := by
    have hdvd : orderOf ho ∣ Nat.gcd (Nat.card K - 1) (Nat.card K + 1) :=
      Nat.dvd_gcd horder_sub horder_add
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hdvd
    exact Nat.dvd_one.mp hdvd
  have ho1 : ho = 1 := orderOf_eq_one_iff.mp horder_one
  exact Subtype.ext_iff.mp ho1

theorem hyperbolic_isometry_eq_one_of_pow_card_add_one_of_exists_singular
    (hU : Module.finrank K U = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hsing : ∃ u : U, u ≠ 0 ∧ Q u = 0) {h : U ≃ₗ[K] U}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hpow : h ^ (Nat.card K + 1) = 1) :
    h = 1 :=
  hyperbolic_isometry_eq_one_of_pow_card_add_one (Q := Q) hU hQ
    ((isPlusType_iff_exists_singular (Q := Q) hU).mpr hsing) hh hpow

end RelDPlane

end CFSG.StandardType

end
