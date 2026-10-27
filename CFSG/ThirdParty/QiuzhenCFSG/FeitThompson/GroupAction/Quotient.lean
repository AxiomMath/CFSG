module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SchurZassenhaus

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Basic

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative commutatorElement

section QuotientSubgroupRange

/-- Cardinality of a quotient by a kernel equals the cardinality of the range. -/
public lemma CFSG.natCard_quotient_eq_card_range_of_ker_eq {A B : Type*} [Group A] [Finite A]
    [Group B] (φ : A →* B) (H : Subgroup A) [H.Normal] (hφker : φ.ker = H) :
    Nat.card (A ⧸ H) = Nat.card φ.range := by
  simpa [hφker] using Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv

/-- Cardinality of a quotient by a kernel, rewritten along an explicit range subgroup. -/
public lemma CFSG.natCard_quotient_eq_card_of_ker_eq_of_range_eq {A B : Type*} [Group A]
    [Finite A] [Group B] (φ : A →* B) (H : Subgroup A) [H.Normal] (S : Subgroup B)
    (hφker : φ.ker = H) (hφrange : φ.range = S) :
    Nat.card (A ⧸ H) = Nat.card S := by
  rw [natCard_quotient_eq_card_range_of_ker_eq φ H hφker, hφrange]

/-- The range of the quotient map restricted to a subgroup has the quotient cardinality. -/
public lemma CFSG.natCard_map_mk'_eq {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) [N.Normal] :
    Nat.card (K.map (QuotientGroup.mk' N)) = Nat.card (K ⧸ N.subgroupOf K) := by
  let φ : K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hφker : φ.ker = N.subgroupOf K := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = K.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hyK, rfl⟩
      exact ⟨⟨y, hyK⟩, rfl⟩
  symm
  exact natCard_quotient_eq_card_of_ker_eq_of_range_eq φ (N.subgroupOf K)
    (K.map (QuotientGroup.mk' N)) hφker hφrange

/-- The quotient of a subgroup by the induced normal subgroup is the range of the quotient map. -/
@[expose]
public noncomputable def CFSG.quotientSubgroupRangeEquiv {G : Type*} [Group G]
    (K N : Subgroup G) [N.Normal] :
    (↥K ⧸ N.subgroupOf K) ≃* K.map (QuotientGroup.mk' N) := by
  let φ : K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hφker : φ.ker = N.subgroupOf K := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = K.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hyK, rfl⟩
      exact ⟨⟨y, hyK⟩, rfl⟩
  exact
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))

public theorem CFSG.quotientSubgroupRangeEquiv_apply_mk
    {G : Type*} [Group G] (K N : Subgroup G) [N.Normal] (x : K) :
    ((quotientSubgroupRangeEquiv K N) (QuotientGroup.mk' (N.subgroupOf K) x) :
        G ⧸ N) =
      QuotientGroup.mk' N (x : G) := by
  let φ : K →* G ⧸ N := (QuotientGroup.mk' N).comp K.subtype
  have hφker : φ.ker = N.subgroupOf K := by
    ext y
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφrange : φ.range = K.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hzK, rfl⟩
      exact ⟨⟨z, hzK⟩, rfl⟩
  change (((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange)))
      (QuotientGroup.mk' (N.subgroupOf K) x) : G ⧸ N) =
    QuotientGroup.mk' N (x : G)
  rfl

end QuotientSubgroupRange

section CoprimeCocycle

open scoped Pointwise

variable {A N : Type*} [Group A] [Finite A] [CommGroup N] [Finite N]
variable [MulDistribMulAction A N]

/-- A (multiplicative) 1-cocycle for an action. -/
@[expose]
public def CFSG.IsCocycle₁ (c : A → N) : Prop :=
  ∀ a b : A, c (a * b) = c a * (a • c b)

/-- If `c : A → N` is a 1-cocycle and `|A|` is coprime to `|N|`, then `c` is a 1-coboundary.

This is the elementary “`H¹(A, N) = 0` for coprime finite actions” statement, specialized to
`Nat.card` and proved by an explicit averaging/product argument. -/
public lemma CFSG.exists_coboundary_of_cocycle_of_coprime_card
    (c : A → N) (hc : IsCocycle₁ (A := A) (N := N) c)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    ∃ n : N, ∀ a : A, c a = (a • n)⁻¹ * n := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype N := Fintype.ofFinite N
  let m : ℕ := Fintype.card A
  let t : N := (Finset.univ : Finset A).prod c

  have hsmul_t (b : A) :
      b • t = (c b)⁻¹ ^ m * t := by
    have hbca (a : A) : b • c a = (c b)⁻¹ * c (b * a) := by
      -- Rearrange the cocycle identity: `c (b*a) = c b * (b • c a)`.
      have := hc b a
      -- Multiply by `(c b)⁻¹` on the left.
      have := congrArg (fun x : N => (c b)⁻¹ * x) this
      -- Simplify.
      simpa [mul_assoc] using this.symm
    have hreindex :
        (Finset.univ : Finset A).prod (fun a : A => c (b * a)) =
          (Finset.univ : Finset A).prod c := by
      -- Reindex by the bijection `a ↦ b*a`.
      -- We use `prod_bij` since the map depends on membership proofs.
      simpa using
        (Finset.prod_bij
          (s := (Finset.univ : Finset A))
          (t := (Finset.univ : Finset A))
          (i := fun a _ha => b * a)
          (f := fun a : A => c (b * a))
          (g := c)
          (hi := by intro a ha; simp)
          (i_inj := by
            intro a₁ ha₁ a₂ ha₂ h
            exact mul_left_cancel h)
          (i_surj := by
            intro a ha
            refine ⟨b⁻¹ * a, by simp, ?_⟩
            simp)
          (h := by intro a ha; rfl))
    calc
      b • t
          = (Finset.univ : Finset A).prod (fun a : A => b • c a) := by
              simpa [t] using
                (Finset.smul_prod' (r := b) (f := c) (s := (Finset.univ : Finset A)))
      _ = (Finset.univ : Finset A).prod (fun a : A => (c b)⁻¹ * c (b * a)) := by
              refine Finset.prod_congr rfl (fun a ha => ?_)
              simp [hbca]
      _ = ((Finset.univ : Finset A).prod (fun _a : A => (c b)⁻¹)) *
            (Finset.univ : Finset A).prod (fun a : A => c (b * a)) := by
              simp [Finset.prod_mul_distrib]
      _ = (c b)⁻¹ ^ m * (Finset.univ : Finset A).prod (fun a : A => c (b * a)) := by
              simp [Finset.prod_const, m]
      _ = (c b)⁻¹ ^ m * t := by
              simpa [t] using congrArg (fun x => (c b)⁻¹ ^ m * x) hreindex

  -- Choose an `m`-th root of `t` in `N` using coprimality of `m` with `|N|`.
  have hpow : Nat.Coprime (Nat.card N) m := by
    simpa [m, Nat.card_eq_fintype_card] using hcop.symm
  let e : N ≃ N := powCoprime (G := N) (n := m) hpow
  let n : N := e.symm t
  have hn_pow : n ^ m = t := by
    -- Unfold `n` and use the defining property of `powCoprime`.
    simpa [n, e] using (e.apply_symm_apply t)

  refine ⟨n, ?_⟩
  intro b
  have ht_rel : t * (b • t)⁻¹ = (c b) ^ m := by
    have hb : b • t = (c b)⁻¹ ^ m * t := hsmul_t b
    have hb' : (b • t) * t⁻¹ = (c b)⁻¹ ^ m := by
      simpa [mul_assoc] using congrArg (fun x => x * t⁻¹) hb
    calc
      t * (b • t)⁻¹ = ((b • t) * t⁻¹)⁻¹ := by
        -- in a commutative group: `(x * y⁻¹)⁻¹ = y * x⁻¹`
        simp
      _ = ((c b)⁻¹ ^ m)⁻¹ := by simp [hb']
      _ = (c b) ^ m := by simp
  -- Now compare `m`-th powers of `(b • n)⁻¹ * n` and `c b`.
  have hpow_eq : ((b • n)⁻¹ * n) ^ m = (c b) ^ m := by
    have hbn_pow : (b • n) ^ m = b • t := by
      -- `b • (n^m) = (b•n)^m`.
      have : b • (n ^ m) = (b • n) ^ m := by simp
      simpa [hn_pow] using this.symm
    calc
      ((b • n)⁻¹ * n) ^ m
          = (b • n)⁻¹ ^ m * (n ^ m) := by
              simp [mul_pow, mul_comm]
      _ = ((b • n) ^ m)⁻¹ * t := by
              simp [hn_pow]
      _ = (b • t)⁻¹ * t := by
              simp [hbn_pow]
      _ = t * (b • t)⁻¹ := by
              simp [mul_comm]
      _ = (c b) ^ m := by simp [ht_rel]
  -- Use injectivity of the `m`-th power map on `N`.
  have hinj : Function.Injective fun x : N => x ^ m :=
    (powCoprime (G := N) (n := m) hpow).injective
  exact (hinj hpow_eq).symm

end CoprimeCocycle

section QuotientActionInfrastructure

open MulAction

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

/-- If a subgroup `H` is `A`-invariant (in the sense of `IsInvariant`), then the action descends to
`G ⧸ H`. -/
public lemma CFSG.quotientAction_of_isInvariant (H : Subgroup G) (hH : IsInvariant A G H) :
    MulAction.QuotientAction A H where
  inv_mul_mem a {g g'} hg := by
    -- Use invariance of `H` and the fact `a` acts by an automorphism.
    have hH' : ∀ a : A, ∀ g : G, g ∈ H ↔ a • g ∈ H := by
      exact IsInvariant.invariant
    have : a • (g⁻¹ * g') ∈ H := (hH' a (g⁻¹ * g')).1 hg
    simpa [smul_mul_assoc, smul_inv_smul] using this

/-- A `MulDistribMulAction` on `G ⧸ H` induced by an `A`-action on `G` that preserves `H`. -/
@[reducible, expose]
public noncomputable def CFSG.quotientMulDistribMulAction (H : Subgroup G) (hH : IsInvariant A G H)
    [H.Normal] : MulDistribMulAction A (G ⧸ H) := by
  classical
  -- First, install the descended `MulAction`.
  letI : MulAction.QuotientAction A H := quotientAction_of_isInvariant (A := A) H hH
  -- Then, upgrade it to a `MulDistribMulAction`.
  let base : MulAction A (G ⧸ H) := inferInstance
  refine
    { smul := base.smul
      one_smul := base.one_smul
      mul_smul := base.mul_smul
      smul_mul := by
        intro a x y
        refine Quotient.inductionOn₂' x y (fun g h => ?_)
        change a • ((g : G ⧸ H) * (h : G ⧸ H)) =
            ((a • g : G) : G ⧸ H) * ((a • h : G) : G ⧸ H)
        calc
          a • ((g : G ⧸ H) * (h : G ⧸ H))
              = a • (((g * h : G) : G ⧸ H)) := by
                  simp only [QuotientGroup.mk_mul]
          _ = ((a • (g * h : G) : G) : G ⧸ H) := by
                  simpa using (MulAction.Quotient.smul_coe (H := H) a (g * h))
          _ = (((a • g : G) * (a • h : G) : G) : G ⧸ H) := by
                  simp [smul_mul']
          _ = ((a • g : G) : G ⧸ H) * ((a • h : G) : G ⧸ H) := by
                  simp only [QuotientGroup.mk_mul]
      smul_one := by
        intro a
        change a • ((1 : G) : G ⧸ H) = (1 : G ⧸ H)
        simpa using (MulAction.Quotient.smul_coe (H := H) a (1 : G)) }

/-- For the induced action on `G ⧸ H`, the image of fixed points in `G` lies in fixed points of
the quotient. -/
public theorem CFSG.fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient
    (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H) :
    letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
    (fixedPointSubgroup A G).map (QuotientGroup.mk' H) ≤ fixedPointSubgroup A (G ⧸ H) := by
  letI : IsInvariant A G H := hH
  letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
  letI : MulAction.QuotientAction A H := quotientAction_of_isInvariant (A := A) H hH
  intro q hq
  rcases Subgroup.mem_map.mp hq with ⟨g, hg, rfl⟩
  change ∀ a : A, a • ((g : G) : G ⧸ H) = ((g : G) : G ⧸ H)
  intro a
  have hg_fixed : ∀ b : A, b • g = g := by
    simpa [fixedPointSubgroup] using hg
  calc
    a • ((g : G) : G ⧸ H) = ((a • g : G) : G ⧸ H) := by
      simp
    _ = ((g : G) : G ⧸ H) := by
      simp [hg_fixed a]

/-- If `H` is an abelian `A`-invariant normal subgroup with `(|A|,|H|)=1`, then fixed points in
`G ⧸ H` are exactly the image of fixed points in `G`. -/
public theorem CFSG.fixedPointSubgroup_quotient_eq_map_of_isMulCommutative
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H)
    [IsMulCommutative H]
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card H)) :
    letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
    fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  letI : IsInvariant A G H := hH
  letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
  letI : MulAction.QuotientAction A H := quotientAction_of_isInvariant (A := A) H hH
  letI : CommGroup H := by infer_instance
  refine le_antisymm ?_ ?_
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro g hq
    have hqfix : ∀ a : A, a • ((g : G) : G ⧸ H) = ((g : G) : G ⧸ H) := by
      simpa [fixedPointSubgroup] using hq
    let c : A → H := fun a =>
      ⟨g⁻¹ * (a • g), by
        have hqeq : (QuotientGroup.mk' H) (a • g) = (QuotientGroup.mk' H) g :=
          (MulAction.Quotient.smul_mk (H := H) a g).trans (hqfix a)
        have hdiv_mem : (a • g) / g ∈ H := (QuotientGroup.eq_iff_div_mem).1 hqeq
        have hmul_mem : (a • g) * g⁻¹ ∈ H := by
          simpa [div_eq_mul_inv] using hdiv_mem
        have hconj_mem : g⁻¹ * ((a • g) * g⁻¹) * (g⁻¹)⁻¹ ∈ H :=
          (inferInstance : H.Normal).conj_mem _ hmul_mem g⁻¹
        simpa [mul_assoc] using hconj_mem⟩
    have hcocycle : IsCocycle₁ (A := A) (N := H) c := by
      intro a b
      ext
      change g⁻¹ * ((a * b) • g) =
        (g⁻¹ * (a • g)) * (a • (g⁻¹ * (b • g)))
      simp [mul_assoc, smul_mul', smul_smul]
    obtain ⟨n, hn⟩ :=
      exists_coboundary_of_cocycle_of_coprime_card (A := A) (N := H) c hcocycle hcoprime
    let x : G := g * (n : G)
    have hxfix : ∀ a : A, a • x = x := by
      intro a
      have hcn : (g⁻¹ * (a • g) : G) = (((a • n)⁻¹ * n : H) : G) := by
        exact congrArg Subtype.val (by simpa [c] using hn a)
      calc
        a • x = (a • g) * (a • (n : G)) := by
          simp [x, smul_mul']
        _ = g * (g⁻¹ * (a • g)) * (a • (n : G)) := by
          simp
        _ = g * ((((a • n)⁻¹ * n : H) : G) * (a • (n : G))) := by
          rw [hcn]
          simp [mul_assoc]
        _ = g * (n : G) := by
          have hsmul_coe : a • (n : G) = ((a • n : H) : G) := rfl
          rw [hsmul_coe]
          norm_num [mul_assoc, mul_left_comm, mul_comm]
        _ = x := by
          simp [x]
    refine ⟨x, ?_, ?_⟩
    · simpa [fixedPointSubgroup] using hxfix
    · simp [x]
  · exact fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient (A := A) (G := G) H hH

universe u v

/-- Under solvability and coprime action assumptions, fixed points commute with quotienting by any
`A`-invariant normal subgroup. -/
public theorem CFSG.fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    ∀ (H : Subgroup G) [H.Normal] (hH : IsInvariant A G H),
      letI : MulDistribMulAction A (G ⧸ H) := quotientMulDistribMulAction (A := A) (G := G) H hH
      fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u) [Group G'] [Finite G'] [MulDistribMulAction A G'],
      Nat.card G' = n →
        Group.IsSolvable G' →
          Nat.Coprime (Nat.card A) (Nat.card G') →
            ∀ (H' : Subgroup G') [H'.Normal] (hH' : IsInvariant A G' H'),
              letI : MulDistribMulAction A (G' ⧸ H') :=
                quotientMulDistribMulAction (A := A) (G := G') H' hH'
              fixedPointSubgroup A (G' ⧸ H') = (fixedPointSubgroup A G').map (QuotientGroup.mk' H')
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ _ hcard hsolv' hcop' H' _hH'Normal hH'
    letI : IsInvariant A G' H' := hH'
    letI : MulAction.QuotientAction A H' := quotientAction_of_isInvariant (A := A) H' hH'
    letI : MulDistribMulAction A (G' ⧸ H') :=
      quotientMulDistribMulAction (A := A) (G := G') H' hH'
    by_cases hHbot : H' = ⊥
    · subst hHbot
      have hcop_bot : Nat.Coprime (Nat.card A) (Nat.card (⊥ : Subgroup G')) := by simp
      simpa using
        (fixedPointSubgroup_quotient_eq_map_of_isMulCommutative (G := G') (A := A)
          (H := (⊥ : Subgroup G')) (hH := hH') hcop_bot)
    · haveI : Group.IsSolvable H' := by infer_instance
      haveI : Nontrivial H' := (Subgroup.nontrivial_iff_ne_bot H').2 hHbot
      let pds : ℕ → Prop := fun i => derivedSeries H' i = ⊥
      have hpds : ∃ i, pds i := Group.IsSolvable.solvable (G := H')
      let i : ℕ := Nat.find hpds
      have hi_spec : derivedSeries H' i = ⊥ := Nat.find_spec hpds
      have hi_ne_zero : i ≠ 0 := by
        intro hi0
        have htop_bot : (⊤ : Subgroup H') = (⊥ : Subgroup H') := by
          calc
            (⊤ : Subgroup H') = derivedSeries H' 0 := by simp [derivedSeries_zero]
            _ = derivedSeries H' i := by simp [i, hi0]
            _ = ⊥ := hi_spec
        exact top_ne_bot htop_bot
      let N0 : Subgroup H' := derivedSeries H' (i - 1)
      have hN0_ne_bot : N0 ≠ ⊥ := by
        have hi_lt : i - 1 < i := Nat.sub_one_lt hi_ne_zero
        have : ¬ pds (i - 1) := Nat.find_min hpds hi_lt
        exact fun hbot => this (by simpa [pds, N0] using hbot)
      haveI : N0.Characteristic := derivedSeries_characteristic (G := H') (i - 1)
      let N : Subgroup G' := N0.map H'.subtype
      have hN_le_H' : N ≤ H' := by
        simpa [N] using (Subgroup.map_subtype_le (H := H') (K := N0))
      have hN_ne_bot : N ≠ ⊥ := by
        intro hNbot
        have hN0_bot : N0 = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (H := N0) (f := H'.subtype)
            H'.subtype_injective).1 (by simpa [N] using hNbot)
        exact hN0_ne_bot hN0_bot
      have hcomm_bot0 : ⁅N0, N0⁆ = ⊥ := by
        have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi_ne_zero)
        have hderived : derivedSeries H' i = ⁅N0, N0⁆ := by
          calc
            derivedSeries H' i = derivedSeries H' (i - 1 + 1) := by simp [hi1]
            _ = ⁅derivedSeries H' (i - 1), derivedSeries H' (i - 1)⁆ := by
              simp [derivedSeries_succ]
            _ = ⁅N0, N0⁆ := by simp [N0]
        simpa [hderived] using hi_spec
      have hcomm_botN : ⁅N, N⁆ = ⊥ := by
        have hmap_comm : (⁅N0, N0⁆).map H'.subtype = ⁅N, N⁆ := by
          simpa [N] using (Subgroup.map_commutator (H₁ := N0) (H₂ := N0) H'.subtype)
        calc
          ⁅N, N⁆ = (⁅N0, N0⁆).map H'.subtype := hmap_comm.symm
          _ = ⊥ := by simp [hcomm_bot0]
      have hN_le_cent : N ≤ Subgroup.centralizer (N : Set G') :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).1 hcomm_botN
      haveI : IsMulCommutative N :=
        (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).1 hN_le_cent
      haveI : IsInvariant A H' N0 := by
        refine ⟨?_⟩
        intro a g
        have hfixed :
            N0.comap (MulDistribMulAction.toMulAut A H' a).toMonoidHom = N0 :=
          (inferInstance : N0.Characteristic).fixed (MulDistribMulAction.toMulAut A H' a)
        constructor
        · intro hg
          have hg' : g ∈ N0.comap (MulDistribMulAction.toMulAut A H' a).toMonoidHom := by
            rw [hfixed]
            exact hg
          simpa [Subgroup.mem_comap] using hg'
        · intro hg
          have hg' : g ∈ N0.comap (MulDistribMulAction.toMulAut A H' a).toMonoidHom := by
            simpa [Subgroup.mem_comap] using hg
          have hg'' := hg'
          rw [hfixed] at hg''
          exact hg''
      have hNinv : IsInvariant A G' N := by
        refine ⟨?_⟩
        intro a g
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨a • x, (IsInvariant.invariant (A := A) (G := H') (H := N0) a x).1 hx, ?_⟩
          rfl
        · rintro ⟨x, hx, hxg⟩
          refine ⟨a⁻¹ • x, (IsInvariant.invariant (A := A) (G := H') (H := N0) a⁻¹ x).1 hx, ?_⟩
          have : ((a⁻¹ • x : H') : G') = g := by
            calc
              ((a⁻¹ • x : H') : G') = a⁻¹ • (x : G') := by rfl
              _ = a⁻¹ • (a • g) := by simpa using congrArg (fun t : G' => a⁻¹ • t) hxg
              _ = g := inv_smul_smul a g
          simp [this]
      letI : IsInvariant A G' N := hNinv
      letI : MulAction.QuotientAction A N := quotientAction_of_isInvariant (A := A) N hNinv
      let Q := G' ⧸ N
      letI : Group Q := by infer_instance
      letI : Finite Q := by infer_instance
      letI : MulDistribMulAction A Q :=
        quotientMulDistribMulAction (A := A) (G := G') N hNinv
      have hQ_solv : Group.IsSolvable Q := by infer_instance
      have hQ_coprime : Nat.Coprime (Nat.card A) (Nat.card Q) := by
        have hdvd : Nat.card Q ∣ Nat.card G' := Subgroup.card_quotient_dvd_card (s := N)
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      have hQ_lt : Nat.card Q < n := by
        have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G') (s := N))
        have hN_one_lt : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
        have hQ_pos : 0 < Nat.card Q := Nat.card_pos (α := Q)
        have hlt : Nat.card Q < Nat.card Q * Nat.card N := by
          simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hN_one_lt hQ_pos
        have hEq : Nat.card Q * Nat.card N = n := by
          simpa [Q, hcard] using hmul.symm
        simpa [hEq] using hlt
      let fN : G' →* Q := QuotientGroup.mk' N
      let Hbar : Subgroup Q := H'.map fN
      have hHbar_inv : IsInvariant A Q Hbar := by
        refine ⟨?_⟩
        intro a q
        constructor
        · rintro ⟨g, hg, rfl⟩
          refine ⟨a • g, (IsInvariant.invariant (A := A) (G := G') (H := H') a g).1 hg, ?_⟩
          change (QuotientGroup.mk' N) (a • g) = a • ((QuotientGroup.mk' N) g)
          exact MulAction.Quotient.smul_mk (H := N) a g
        · rintro ⟨g, hg, hq⟩
          refine ⟨a⁻¹ • g, (IsInvariant.invariant (A := A) (G := G') (H := H') a⁻¹ g).1 hg, ?_⟩
          have : fN (a⁻¹ • g) = a⁻¹ • fN g := by
            change (QuotientGroup.mk' N) (a⁻¹ • g) = a⁻¹ • ((QuotientGroup.mk' N) g)
            exact MulAction.Quotient.smul_mk (H := N) (a⁻¹) g
          simp [this, hq]
      letI : IsInvariant A Q Hbar := hHbar_inv
      letI : MulAction.QuotientAction A Hbar := quotientAction_of_isInvariant (A := A) Hbar hHbar_inv
      letI : MulDistribMulAction A (Q ⧸ Hbar) :=
        quotientMulDistribMulAction (A := A) (G := Q) Hbar hHbar_inv
      have hIH_Hbar :
          fixedPointSubgroup A (Q ⧸ Hbar) = (fixedPointSubgroup A Q).map (QuotientGroup.mk' Hbar) :=
        (ih (Nat.card Q) hQ_lt) Q rfl hQ_solv hQ_coprime Hbar hHbar_inv
      have hN_coprime : Nat.Coprime (Nat.card A) (Nat.card N) := by
        have hdvd : Nat.card N ∣ Nat.card G' := Subgroup.card_subgroup_dvd_card N
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      have hfixed_N :
          fixedPointSubgroup A Q = (fixedPointSubgroup A G').map (QuotientGroup.mk' N) := by
        simpa [Q] using
          (fixedPointSubgroup_quotient_eq_map_of_isMulCommutative (G := G') (A := A)
            (H := N) (hH := hNinv) hN_coprime)
      have hforward :
          (fixedPointSubgroup A G').map (QuotientGroup.mk' H') ≤ fixedPointSubgroup A (G' ⧸ H') :=
        fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient (A := A) (G := G') H' hH'
      have hreverse :
          fixedPointSubgroup A (G' ⧸ H') ≤ (fixedPointSubgroup A G').map (QuotientGroup.mk' H') := by
        intro q
        refine QuotientGroup.induction_on q ?_
        intro g hq
        have hqfix : ∀ a : A, a • ((g : G') : G' ⧸ H') = ((g : G') : G' ⧸ H') := by
          simpa [fixedPointSubgroup] using hq
        let gbar : Q := (QuotientGroup.mk' N) g
        have hqbar : ((gbar : Q) : Q ⧸ Hbar) ∈ fixedPointSubgroup A (Q ⧸ Hbar) := by
          change ∀ a : A, a • ((gbar : Q) : Q ⧸ Hbar) = ((gbar : Q) : Q ⧸ Hbar)
          intro a
          have hqeq : (QuotientGroup.mk' H') (a • g) = (QuotientGroup.mk' H') g :=
            (MulAction.Quotient.smul_mk (H := H') a g).trans (hqfix a)
          have hdivH : (a • g) / g ∈ H' := (QuotientGroup.eq_iff_div_mem).1 hqeq
          have hmulH : (a • g) * g⁻¹ ∈ H' := by simpa [div_eq_mul_inv] using hdivH
          have hmulHbar : (a • gbar) * gbar⁻¹ ∈ Hbar := by
            refine ⟨(a • g) * g⁻¹, hmulH, ?_⟩
            change (QuotientGroup.mk' N) ((a • g) * g⁻¹) =
              (a • ((QuotientGroup.mk' N) g)) * ((QuotientGroup.mk' N) g)⁻¹
            simp
          exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hmulHbar)
        have hqbar_map :
            ((gbar : Q) : Q ⧸ Hbar) ∈ (fixedPointSubgroup A Q).map (QuotientGroup.mk' Hbar) := by
          simpa [hIH_Hbar] using hqbar
        rcases Subgroup.mem_map.mp hqbar_map with ⟨ybar, hybar_fix, hybar_eq⟩
        have hybar_in_mapN : ybar ∈ (fixedPointSubgroup A G').map (QuotientGroup.mk' N) := by
          simpa [hfixed_N] using hybar_fix
        rcases Subgroup.mem_map.mp hybar_in_mapN with ⟨y, hy_fix, hy_eq⟩
        have hy_eq' : ybar = (QuotientGroup.mk' N) y := hy_eq.symm
        have hybar_eq'' :
            (QuotientGroup.mk' Hbar) ybar = (QuotientGroup.mk' Hbar) ((QuotientGroup.mk' N) g) := by
          simpa [gbar, fN] using hybar_eq
        have hybar_eq' :
            (QuotientGroup.mk' Hbar) ((QuotientGroup.mk' N) y) =
              (QuotientGroup.mk' Hbar) ((QuotientGroup.mk' N) g) := by
          simpa [hy_eq'] using hybar_eq''
        have hydivHbar : ((QuotientGroup.mk' N) y) / ((QuotientGroup.mk' N) g) ∈ Hbar :=
          (QuotientGroup.eq_iff_div_mem).1 hybar_eq'
        have hydiv_comap : y / g ∈ Subgroup.comap (QuotientGroup.mk' N) Hbar := by
          change (QuotientGroup.mk' N) (y / g) ∈ Hbar
          simpa using hydivHbar
        have hcomap_Hbar : Subgroup.comap (QuotientGroup.mk' N) Hbar = H' := by
          calc
            Subgroup.comap (QuotientGroup.mk' N) Hbar = N ⊔ H' := by
              change Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) H') = N ⊔ H'
              exact QuotientGroup.comap_map_mk' (N := N) (H := H')
            _ = H' := sup_eq_right.mpr hN_le_H'
        have hydivH : y / g ∈ H' := by
          simpa [hcomap_Hbar] using hydiv_comap
        have hy_eq_g : (QuotientGroup.mk' H') y = (QuotientGroup.mk' H') g :=
          (QuotientGroup.eq_iff_div_mem).2 hydivH
        exact ⟨y, hy_fix, hy_eq_g⟩
      exact le_antisymm hreverse hforward
  exact hP (Nat.card G) G rfl hsolv hcoprime

end QuotientActionInfrastructure

public lemma CFSG.card_quotient_subgroupOf_comap_eq
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (H : Subgroup Q) :
    Nat.card ((H.comap f) ⧸ (f.ker.subgroupOf (H.comap f))) = Nat.card H := by
  classical
  let K : Subgroup G := H.comap f
  let φ : K →* Q := f.comp K.subtype
  have hker : φ.ker = f.ker.subgroupOf K := by
    ext x
    simp [φ, K, Subgroup.mem_subgroupOf]
  have hrange : φ.range = H := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : G) ∈ K := x.property
      dsimp [K] at hx
      change f (x : G) ∈ H
      exact hx
    · intro hy
      rcases hf y with ⟨g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      dsimp [K]
      exact hy
  have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  simpa [K, hker, hrange] using hcard

section IsInvariantQuotient

open QuotientGroup

public lemma CFSG.isInvariant_map_quotient {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {N : Subgroup G} [N.Normal] [IsInvariant A G N]
    (H : Subgroup G) [IsInvariant A G H] :
    letI : MulDistribMulAction A (G ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := G) N inferInstance
    IsInvariant A (G ⧸ N) (H.map (mk' N)) := by
  letI : MulAction.QuotientAction A N :=
    quotientAction_of_isInvariant (A := A) (G := G) N inferInstance
  letI : MulDistribMulAction A (G ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := G) N inferInstance
  refine ⟨?_⟩
  intro a q
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨a • g, (IsInvariant.invariant (A := A) (G := G) (H := H) a g).1 hg, ?_⟩
    -- Show that `(a • g : G) ⧸ N = a • (g : G ⧸ N)`
    -- This holds because the quotient action is defined via `QuotientAction`.
    exact (MulAction.Quotient.smul_coe (H := N) (a : A) (g : G)).symm
  · rintro ⟨g, hg, hq⟩
    refine ⟨a⁻¹ • g, (IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ g).1 hg, ?_⟩
    have hsmul := congrArg (fun z : G ⧸ N => a⁻¹ • z) hq
    simpa [inv_smul_smul] using hsmul

public lemma CFSG.isInvariant_comap_quotient {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {N : Subgroup G} [N.Normal] [IsInvariant A G N]
    (H : Subgroup (G ⧸ N))
    [hQ : MulDistribMulAction A (G ⧸ N)] [IsInvariant A (G ⧸ N) H]
    (hq : ∀ a : A, ∀ g : G, a • ((mk' N) g) = (mk' N) (a • g)) :
    IsInvariant A G (H.comap (mk' N)) := by
  refine ⟨?_⟩
  intro a g
  constructor
  · intro hg
    change (mk' N) (a • g) ∈ H
    rw [← hq a g]
    exact (IsInvariant.invariant (A := A) (G := G ⧸ N) (H := H) a ((mk' N) g)).1 hg
  · intro hg
    change (mk' N) g ∈ H
    have hg' : a⁻¹ • ((mk' N) (a • g)) ∈ H :=
      (IsInvariant.invariant (A := A) (G := G ⧸ N) (H := H) a⁻¹ ((mk' N) (a • g))).1 hg
    have hcalc : a⁻¹ • ((mk' N) (a • g)) = (mk' N) g := by
      calc
        a⁻¹ • ((mk' N) (a • g)) = (mk' N) (a⁻¹ • (a • g)) := by
          rw [← hq a⁻¹ (a • g)]
        _ = (mk' N) g := by simp
    rw [hcalc] at hg'
    exact hg'

end IsInvariantQuotient
