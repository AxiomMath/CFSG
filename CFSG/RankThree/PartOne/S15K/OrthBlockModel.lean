module

public import CFSG.RankThree.PartOne.S15K.OrthFixedModel
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.OrthLayerT
public import CFSG.RankThree.PartOne.S15K.PSylowSub

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow QuadraticMap
open scoped commutatorElement

section Paired

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem nonempty_mulEquiv_componentImage_paired
    (hinj : Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h)
    (hΩ : specialBlock Q x h ≤ orthDerived Q) :
    Nonempty (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h) ≃*
      ↥(componentImage Q x h)) := by
  classical
  set m := primaryMultiplicity x.toLinearMap h with hmdef
  let b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  let e₂ : ↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) :=
    e₁.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  let e₃ : Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) ≃*
      ↥((specialBlock Q x h).subgroupOf (orthDerived Q)) :=
    e₂.symm.trans (Subgroup.subgroupOfEquivOfLe hΩ).symm
  exact ⟨e₃.trans (Subgroup.equivMapOfInjective _ _ hinj)⟩

end Paired

section Family

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_layerFamily_models (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) {f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hq : 3 < Nat.card K)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ (x : orthDerived Q) (Rep : Finset K[X]) (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      (QuotientGroup.mk x : ProjOrthDerived Q) = a ∧ orderOf x = p ∧
      IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧
      (⨆ i, C i) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
      LayerFamily p a (orthFamily Q (x : V ≃ₗ[K] V) Rep C) ∧
      ∀ i, BlockModel p ↥(orthFamily Q (x : V ≃ₗ[K] V) Rep C i) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := inferInstance
  have hpq' : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  obtain ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, hFam⟩ :=
    exists_layerFamily hQ hT hdim hp hp5 hq A hA hAcard a haA ha1
  refine ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, hFam, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := mk_injective_orth hQ
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup x.2
  have hxp' : orderOf (x : V ≃ₗ[K] V) = p := by rw [Subgroup.orderOf_coe]; exact hxp
  obtain ⟨-, hmain⟩ := orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl a
    (orderOf_eq_prime (hA.2 a haA) ha1) x hxa hxp
  obtain ⟨hNeq, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
  have hNeq' : centralizerImage Q (x : V ≃ₗ[K] V) =
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := hNeq.symm
  have hno : ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
      h ≠ reciprocalPolynomial h := by
    intro h hmem hne1 hself
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hmem⟩
    obtain ⟨d, H, hdeg, hroot, -⟩ := hx.exists_selfDual_hermitian hpodd hmem hne1 hself
    have hdvd := hx.dvd_card_pow_add_one hp hmem hne1 hroot
    exact false_of_dvd_pow_add_one hp5 Nat.card_pos hpq' hdvd
  have hW : ¬ IsPlusType ((Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) :=
    not_isPlusType_fixedSpace hx hno hV
  obtain ⟨mW, hmW⟩ := hx.even_finrank_fixed
  have hW2 : 2 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V)) := by
    by_contra hlt
    have h0 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 0 := by omega
    have : Subsingleton (fixedSpace (x : V ≃ₗ[K] V)) := Module.finrank_zero_iff.mp h0
    exact hW (isPlusType_of_subsingleton _)
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hW6 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) ≤ 6 := by
    by_contra hgt
    have h8 : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 := by
      have := Submodule.finrank_le (fixedSpace (x : V ≃ₗ[K] V))
      omega
    have htop := Submodule.eq_top_of_finrank_eq (K := K) (S := fixedSpace (x : V ≃ₗ[K] V))
      (by rw [h8, hdim])
    apply hx1
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ fixedSpace (x : V ≃ₗ[K] V) := by rw [htop]; trivial
    exact mem_fixedSpace.mp hv
  obtain ⟨T, hTV, -, -, -, hTdim⟩ := exists_halfSpace hx hno hRep
  have hT3 : finrank K T ≤ 3 := by omega
  have hC' : ∀ j : Fin n, CFSG.IsQuasisimple ↥(C j) ∧ C j ≤ centralizerImage Q (x : V ≃ₗ[K] V) ∧
      ((C j).subgroupOf (centralizerImage Q (x : V ≃ₗ[K] V))).IsSubnormal := by
    intro j
    have hle := hFam.le (Sum.inr j)
    have hcomp := hFam.comp (Sum.inr j)
    rw [orthFamily_inr] at hle hcomp
    rw [← hNeq'] at hle hcomp
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hcomp.1, hle,
      hcomp.2⟩
  rintro (⟨h, hmem, hne1, hm⟩ | j)
  · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hmem)⟩
    have hself := hno h (hRep.1 hmem) hne1
    have hΩ := hx.specialBlock_le_orthDerived hp hp3 (hRep.1 hmem) hne1 hm
    obtain ⟨e⟩ := nonempty_mulEquiv_componentImage_paired hinj hx (hRep.1 hmem) hself hΩ
    have hdeg : 1 ≤ h.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors (hRep.1 hmem))
    have hVh : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h ≤ T := hTV h hmem hne1
    have hfin := Submodule.finrank_mono hVh
    have hfpc : finrank K (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) =
        h.natDegree * primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h :=
      finrank_primaryComponent (x : V ≃ₗ[K] V).toLinearMap h
    have hm1 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ≤
        h.natDegree * primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h :=
      Nat.le_mul_of_pos_left _ hdeg
    have hm3 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ≤ 3 := by omega
    have hm2 : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := hm
    have hE : Nat.card (AdjoinRoot h) = 2 ^ (f * h.natDegree) := by
      rw [KCLinPlane.natCard_adjoinRoot, hK, ← pow_mul]
    have hfin : Finite (AdjoinRoot h) := Nat.finite_of_card_ne_zero (by rw [hE]; positivity)
    have hg : 2 ≤ f * h.natDegree := le_trans hf (Nat.le_mul_of_pos_right f hdeg)
    have hpg : p ∣ 2 ^ (f * h.natDegree) - 1 := by
      have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ h.natDegree - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 h.natDegree
      rw [← pow_mul] at h1
      exact hpq.trans h1
    have hchar : CharP (AdjoinRoot h) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
    exact ⟨f * h.natDegree, AdjoinRoot h, inferInstance, hfin, hchar, hE, hg, hpg,
      Or.inl ⟨primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h, by omega, ⟨e.symm⟩⟩⟩
  · exact blockModel_fixedLayer_component hQ hx hK hf hpq hW hW6 hCsup hC' j

end Family

end CFSG.RankThree.PartOne.S15K
