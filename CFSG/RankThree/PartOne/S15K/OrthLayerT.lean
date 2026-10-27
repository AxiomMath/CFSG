module

public import CFSG.RankThree.PartOne.S15K.OrthDerived
public import CFSG.RankThree.PartOne.S15K.OrthCenter
public import CFSG.RankThree.PartOne.S15K.OrthMult
public import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

structure LayerFamily {T : Type*} [Group T] (p : ℕ) (a : T) {ι : Type*} (F : ι → Subgroup T) :
    Prop where
  le : ∀ i, F i ≤ Subgroup.centralizer ({a} : Set T)
  comp : ∀ i, IsComponent ((F i).subgroupOf (Subgroup.centralizer ({a} : Set T)))
  derived : ⁅Subgroup.centralizer ({a} : Set T), Subgroup.centralizer ({a} : Set T)⁆ = ⨆ i, F i
  factor : ∀ y ∈ Subgroup.centralizer ({a} : Set T), y ^ p = 1 →
    ∃ z k : T, y = z * k ∧ (∀ n ∈ Subgroup.centralizer ({a} : Set T), z * n = n * z) ∧
      k ∈ ⨆ i, F i
  center : ∀ i, ∀ u ∈ F i, (∀ f ∈ F i, u * f = f * u) → u ^ p = 1 → u = 1

section Family

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev OrthIdx (x : V ≃ₗ[K] V) (Rep : Finset K[X]) (n : ℕ) : Type :=
  {h : K[X] // h ∈ Rep ∧ h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h} ⊕ Fin n

@[expose] noncomputable def orthFamily (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (Rep : Finset K[X]) {n : ℕ}
    (C : Fin n → Subgroup (ProjOrthDerived Q)) : OrthIdx x Rep n → Subgroup (ProjOrthDerived Q) :=
  Sum.elim (fun h => componentImage Q x h.1) C

omit [Finite K] [FiniteDimensional K V] in
theorem orthFamily_inr (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (Rep : Finset K[X]) {n : ℕ}
    (C : Fin n → Subgroup (ProjOrthDerived Q)) (j : Fin n) :
    orthFamily Q x Rep C (Sum.inr j) = C j := rfl

omit [Finite K] [FiniteDimensional K V] in
theorem iSup_orthFamily (x : V ≃ₗ[K] V) (Rep : Finset K[X]) {n : ℕ}
    (C : Fin n → Subgroup (ProjOrthDerived Q)) :
    (⨆ i, orthFamily Q x Rep C i) = componentProduct Q x Rep ⊔ ⨆ i, C i := by
  rw [orthFamily, iSup_sum]
  congr 1
  apply le_antisymm
  · exact iSup_le fun h => le_iSup₂_of_le h.1 h.2.1 (le_iSup_of_le ⟨h.2.2.1, h.2.2.2⟩ le_rfl)
  · refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    exact le_iSup (fun h : {h : K[X] // h ∈ Rep ∧ h ≠ X - 1 ∧
      2 ≤ primaryMultiplicity x.toLinearMap h} => componentImage Q x h.1) ⟨h, hh, hne.1, hne.2⟩

theorem le_commutator_of_isQuasisimple {T : Type*} [Group T] {N F : Subgroup T}
    (hF : CFSG.IsQuasisimple ↥F) (hFN : F ≤ N) : F ≤ ⁅N, N⁆ := by
  have h1 := (Subgroup.isPerfect_iff).1 hF.1
  calc F = ⁅F, F⁆ := h1.symm
    _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hFN hFN

theorem exists_layerFamily [CharP K 2] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 3 < Nat.card K) (A : Subgroup (ProjOrthDerived Q))
    (hA : Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q)
    (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ (x : orthDerived Q) (Rep : Finset K[X]) (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      (QuotientGroup.mk x : ProjOrthDerived Q) = a ∧ orderOf x = p ∧
      IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧
      (⨆ i, C i) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
      LayerFamily p a (orthFamily Q (x : V ≃ₗ[K] V) Rep C) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have ha : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := mk_injective_orth hQ
  obtain ⟨x, hxa⟩ := QuotientGroup.mk_surjective a
  have hxp : orderOf x = p := by
    rw [← ha, ← hxa]
    exact (orderOf_injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) hinj
      x).symm
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup x.2
  set B : Subgroup (MulAut (ProjOrthDerived Q)) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range with hBdef
  obtain ⟨⟨Rep, hRep⟩, hmain⟩ := orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3
    hpl B le_rfl a ha x hxa hxp
  obtain ⟨hNeq, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
  obtain ⟨n, C, hCsup, hC, hCcomm⟩ := exists_fixedLayer_family hx
  obtain ⟨-, -, -, hfull, -⟩ := orthogonal_inner_plane_local_core_centralization_full hQ hT hp hp3
    hpl B le_rfl A hA hAcard a haA ha1 x hxa hxp
  obtain ⟨hfspec, -, -, -, hffac⟩ := hfull Rep hRep
  have hxp' : orderOf (x : V ≃ₗ[K] V) = p := by rw [Subgroup.orderOf_coe]; exact hxp
  have hpm : ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := fun h hh hne =>
    not_dvd_multiplicity hQ hp hp5 hpl hxO hxp' hdim hh hne
  have hNeq' : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := hNeq
  refine ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, ?_⟩
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set F := orthFamily Q xe Rep C with hFdef
  have hmember : ∀ i, F i ≤ N ∧ CFSG.IsQuasisimple ↥(F i) ∧ ((F i).subgroupOf N).IsSubnormal := by
    rintro (⟨h, hmem, hne, hm⟩ | j)
    · obtain ⟨-, -, h3, h4, h5, -⟩ := hfspec h hmem hne hm
      exact ⟨h4, h3, h5⟩
    · obtain ⟨h1, h2, h3⟩ := hC j
      refine ⟨by rw [hNeq']; exact h2, h1, ?_⟩
      rw [hNeq']
      exact h3
  have hjoin : (⨆ i, F i) = componentProduct Q xe Rep ⊔ fixedLayerImage Q xe := by
    rw [hFdef, iSup_orthFamily, hCsup]
  have hcomp : ∀ i, IsComponent ((F i).subgroupOf N) := fun i =>
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hmember i).1).symm
      (hmember i).2.1, (hmember i).2.2⟩
  refine ⟨fun i => (hmember i).1, hcomp, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ (iSup_le fun i => le_commutator_of_isQuasisimple (hmember i).2.1
      (hmember i).1)
    rw [hjoin]
    exact commutator_centralizer_le_layerProduct hQ hT hp hp3 hpl hq a ha x hxa hxp hRep
  ·
    intro y hy hyp
    by_cases hy1 : y = 1
    · exact ⟨1, 1, by rw [hy1, mul_one], fun n _ => by rw [one_mul, mul_one], one_mem _⟩
    · have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
      obtain ⟨z, k, hyzk, -, -, hzc, -, hkD, -⟩ := hffac hpm y hy hyo
      exact ⟨z, k, hyzk, fun n hn => (hzc n hn).eq, by rw [hjoin]; exact hkD⟩
  ·
    rintro (⟨h, hmem, hne, hm⟩ | j) u hu hc hup
    · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hmem)⟩
      have hu' : u ∈ componentImage Q xe h := hu
      unfold componentImage at hu'
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hu'
      have hΩ : specialBlock Q xe h ≤ orthDerived Q := (hfspec h hmem hne hm).1
      have hg'S : (g' : V ≃ₗ[K] V) ∈ specialBlock Q xe h := Subgroup.mem_subgroupOf.mp hg'
      have hcomm : ∀ g'' ∈ specialBlock Q xe h, (g' : V ≃ₗ[K] V) * g'' = g'' * g' := by
        intro g'' hg''
        have hmem'' : (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
            ⟨g'', hΩ hg''⟩ ∈ F (Sum.inl ⟨h, hmem, hne, hm⟩) :=
          Subgroup.mem_map.mpr ⟨⟨g'', hΩ hg''⟩, Subgroup.mem_subgroupOf.mpr hg'', rfl⟩
        have h1 := hc _ hmem''
        rw [← map_mul, ← map_mul] at h1
        exact congrArg Subtype.val (hinj h1)
      have hgp : (g' : V ≃ₗ[K] V) ^ p = 1 := by
        have : g' ^ p = 1 := hinj (by rw [map_pow, hup, map_one])
        simpa using congrArg Subtype.val this
      have hpm' := hpm h (hRep.1 hmem) hne
      have hg1 : (g' : V ≃ₗ[K] V) = 1 := by
        by_cases hself : h = reciprocalPolynomial h
        · exact specialBlock_center_pow_selfDual hx hp hp3 (hRep.1 hmem) hne hself hm hpm' hg'S
            hcomm hgp
        · exact specialBlock_center_pow_paired hx hp (hRep.1 hmem) hself (by omega) hpm' hg'S
            hcomm hgp
      have : g' = 1 := Subtype.ext hg1
      rw [this, map_one]
    · exact fixedLayer_center hinj hq hx hCsup hCcomm j hu hc

end Family

end CFSG.RankThree.PartOne.S15K
