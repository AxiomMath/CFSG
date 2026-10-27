module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.StdBasis
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.HomocyclicLift

namespace CFSG
end CFSG
open CFSG

/-!
# Subgroup rectangular packages for Wielandt fixed-point arguments

This file contains the subgroup action decompositions, coordinate splits,
and rectangular linear-map/matrix adapters used by the homocyclic
Wielandt fixed-point infrastructure. The source-core theorems that construct
these packages remain in `FeitThompson.Wielandt`.
-/

noncomputable section

open scoped IsMulCommutative

namespace CFSG.Wielandt

universe u

/-- Prime-power residue rings are local.

This supplies the finite-local-ring input used to turn the projective factor
modules in the Wielandt rectangular split into free coordinate modules. -/
public theorem zmod_prime_pow_isLocalRing {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    IsLocalRing (ZMod (p ^ e)) := by
  classical
  have hp_pow_pos : 0 < p ^ e := pow_pos hp.pos e
  have : NeZero (p ^ e) := ⟨Nat.ne_of_gt hp_pow_pos⟩
  have : Nontrivial (ZMod (p ^ e)) := by
    rw [ZMod.nontrivial_iff]
    exact ne_of_gt (Nat.one_lt_pow (Nat.ne_of_gt he) hp.one_lt)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro a
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · right
    have hnot_coprime : ¬ Nat.Coprime a.val (p ^ e) := by
      intro hc
      have hval : (a.val : ZMod (p ^ e)) = a := ZMod.natCast_zmod_val a
      exact ha (by
        simpa [hval] using ((ZMod.isUnit_iff_coprime a.val (p ^ e)).2 hc))
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnot_coprime with
      ⟨q, hq, hq_dvd_val, hq_dvd_pe⟩
    have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hq_dvd_pe
    have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hq_dvd_p
    have hp_dvd_val : p ∣ a.val := by
      simpa [hq_eq_p] using hq_dvd_val
    have hpow_zero : a ^ e = 0 := by
      have hcast : (a.val : ZMod (p ^ e)) = a := ZMod.natCast_zmod_val a
      rw [← hcast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow_of_dvd hp_dvd_val e
    exact IsNilpotent.isUnit_one_sub ⟨e, hpow_zero⟩

/-- Cardinality of a finite free module over a finite semiring. -/
public theorem finite_free_natCard_eq_pow_finrank
    {R M : Type*} [Semiring R] [StrongRankCondition R] [Fintype R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] [Fintype M] :
    Nat.card M = Nat.card R ^ Module.finrank R M := by
  classical
  let b := Module.finBasis R M
  let e : M ≃ (Fin (Module.finrank R M) → R) :=
    b.repr.toEquiv.trans
      (Finsupp.equivFunOnFinite (α := Fin (Module.finrank R M)) (M := R))
  have hcard : Fintype.card M = Fintype.card (Fin (Module.finrank R M) → R) :=
    Fintype.card_congr e
  rw [Nat.card_eq_fintype_card, hcard, Fintype.card_fun]
  simp [Nat.card_eq_fintype_card]

/-- Recover the finite-free rank from a cardinality written as a power of the
base ring cardinality. -/
public theorem finite_free_finrank_eq_of_natCard_eq_pow
    {R M : Type*} [Semiring R] [StrongRankCondition R] [Fintype R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] [Fintype M]
    {q n : ℕ} (hR : Nat.card R = q) (hq : 2 ≤ q)
    (hM : Nat.card M = q ^ n) :
    Module.finrank R M = n := by
  apply Nat.pow_right_injective hq
  have hfree := finite_free_natCard_eq_pow_finrank (R := R) (M := M)
  calc
    q ^ Module.finrank R M = Nat.card R ^ Module.finrank R M := by rw [hR]
    _ = Nat.card M := hfree.symm
    _ = q ^ n := hM

/-- The kernel of multiplication by `p` on `ZMod (p ^ e)` has cardinality `p`. -/
public theorem zmod_prime_pow_mul_p_kernel_natCard
    {p e : ℕ} [Fact p.Prime] (he : 0 < e) :
    Nat.card {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} = p := by
  classical
  have : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : Nat.Prime p).ne_zero⟩
  let φ : {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} ≃
      ((powMonoidHom p :
          Multiplicative (ZMod (p ^ e)) →* Multiplicative (ZMod (p ^ e))).ker) := by
    refine {
      toFun := fun x => ⟨Multiplicative.ofAdd x.1, ?_⟩
      invFun := fun x => ⟨Multiplicative.toAdd x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · change Multiplicative.ofAdd (p • x.1) = 1
      rw [show p • x.1 = (p : ZMod (p ^ e)) * x.1 by simp [nsmul_eq_mul]]
      rw [x.2]
      rfl
    · have hx := x.2
      change x.1 ^ p = 1 at hx
      have htoAdd := congrArg Multiplicative.toAdd hx
      simpa [nsmul_eq_mul] using htoAdd
    · intro x
      ext
      rfl
    · intro x
      ext
      rfl
  calc
    Nat.card {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} =
        Nat.card ((powMonoidHom p :
          Multiplicative (ZMod (p ^ e)) →* Multiplicative (ZMod (p ^ e))).ker) :=
      Nat.card_congr φ
    _ = p := by
      have h :=
        IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (p ^ e))) p
      rw [h]
      have hcard : Nat.card (Multiplicative (ZMod (p ^ e))) = p ^ e := by
        rw [Nat.card_eq_fintype_card]
        exact
          Fintype.card_congr
            (Multiplicative.toAdd : Multiplicative (ZMod (p ^ e)) ≃ ZMod (p ^ e))
          |>.trans (by simp [ZMod.card])
      rw [hcard]
      exact Nat.gcd_eq_right (dvd_pow_self p (Nat.ne_of_gt he))

/-- Coordinatewise kernel count for multiplication by `p` on a finite product
of `ZMod (p ^ e)`. -/
public theorem zmod_prime_pow_mul_p_function_kernel_natCard
    {ι : Type*} [Fintype ι]
    {p e : ℕ} [Fact p.Prime] (he : 0 < e) :
    Nat.card {x : ι → ZMod (p ^ e) // ∀ i, (p : ZMod (p ^ e)) * x i = 0} =
      p ^ Fintype.card ι := by
  classical
  let eker : {x : ι → ZMod (p ^ e) // ∀ i, (p : ZMod (p ^ e)) * x i = 0} ≃
      (ι → {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0}) :=
    Equiv.subtypePiEquivPi
      (p := fun (_i : ι) (x : ZMod (p ^ e)) => (p : ZMod (p ^ e)) * x = 0)
  calc
    Nat.card {x : ι → ZMod (p ^ e) // ∀ i, (p : ZMod (p ^ e)) * x i = 0} =
        Nat.card (ι → {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0}) :=
      Nat.card_congr eker
    _ = ∏ _i : ι, Nat.card {x : ZMod (p ^ e) // (p : ZMod (p ^ e)) * x = 0} :=
      Nat.card_pi
    _ = ∏ _i : ι, p := by
      congr
      ext i
      exact zmod_prime_pow_mul_p_kernel_natCard (p := p) (e := e) he
    _ = p ^ Fintype.card ι := by
      simp

/-- Kernel count for multiplication by `p` on a finite free
`ZMod (p ^ e)`-module. -/
public theorem finite_free_zmod_prime_pow_mul_p_ker_natCard
    {p e : ℕ} [Fact p.Prime] (he : 0 < e)
    {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ e)) M]
    [StrongRankCondition (ZMod (p ^ e))]
    [Module.Free (ZMod (p ^ e)) M] [Module.Finite (ZMod (p ^ e)) M] [Fintype M] :
    Nat.card {x : M // (p : ZMod (p ^ e)) • x = 0} =
      p ^ Module.finrank (ZMod (p ^ e)) M := by
  classical
  let R := ZMod (p ^ e)
  let b := Module.finBasis R M
  let coord : M ≃ₗ[R] (Fin (Module.finrank R M) → R) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite R R (Fin (Module.finrank R M)))
  let eker : {x : M // (p : R) • x = 0} ≃
      {x : Fin (Module.finrank R M) → R // ∀ i, (p : R) * x i = 0} := by
    refine {
      toFun := fun x => ⟨coord x.1, ?_⟩
      invFun := fun x => ⟨coord.symm x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro i
      have hxcoord : coord ((p : R) • x.1) = 0 := by
        rw [x.2]
        simp
      have hcoord : (p : R) • coord x.1 = 0 := by
        simpa using (coord.map_smul (p : R) x.1).symm.trans hxcoord
      have hi := congrFun hcoord i
      simpa [Pi.smul_apply, smul_eq_mul] using hi
    · apply coord.injective
      funext i
      have hx := x.2 i
      simpa [Pi.smul_apply, smul_eq_mul] using hx
    · intro x
      ext
      simp [coord]
    · intro x
      ext
      simp [coord]
  calc
    Nat.card {x : M // (p : R) • x = 0} =
        Nat.card {x : Fin (Module.finrank R M) → R // ∀ i, (p : R) * x i = 0} :=
      Nat.card_congr eker
    _ = p ^ Fintype.card (Fin (Module.finrank R M)) :=
      zmod_prime_pow_mul_p_function_kernel_natCard
        (ι := Fin (Module.finrank R M)) (p := p) (e := e) he
    _ = p ^ Module.finrank R M := by
      simp

/-- The subgroup of `d`-th powers in a commutative group is characteristic. -/
public theorem powMonoidHom_range_characteristic
    {H : Type*} [CommGroup H] (d : Nat) :
    ((powMonoidHom d : H →* H).range).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨z, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨e z, by simp [powMonoidHom_apply]⟩
  · intro hx
    rcases MonoidHom.mem_range.mp hx with ⟨y, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(e.symm y) ^ d, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨e.symm y, rfl⟩
    · simp [powMonoidHom_apply]

/-- The kernel of the `d`-th power map in a commutative group is
characteristic. -/
public theorem powMonoidHom_ker_characteristic
    {H : Type*} [CommGroup H] (d : Nat) :
    ((powMonoidHom d : H →* H).ker).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hy' : y ^ d = 1 := by
      simpa [powMonoidHom_apply] using hy
    have hmap := congrArg e.toMonoidHom hy'
    simpa [powMonoidHom_apply] using hmap
  · intro hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, ?_⟩
    · have hx' : x ^ d = 1 := by
        simpa [powMonoidHom_apply] using hx
      have hmap := congrArg e.symm.toMonoidHom hx'
      simpa [powMonoidHom_apply] using hmap
    · simp

/-- Fixed-point subgroups transport through equivariant multiplicative
equivalences. -/
public noncomputable def fixedPointSubgroupMulEquiv
    {A M N : Type*} [Group A] [Group M] [Group N]
    [MulDistribMulAction A M] [MulDistribMulAction A N]
    (e : M ≃* N) (he : ∀ a : A, ∀ x : M, e (a • x) = a • e x) :
    fixedPointSubgroup A M ≃* fixedPointSubgroup A N := by
  refine {
    toFun := fun x => ⟨e x.1, ?_⟩
    invFun := fun y => ⟨e.symm y.1, ?_⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · intro a
    rw [← he a x.1]
    have hx := x.2 a
    rw [hx]
  · intro a
    apply e.injective
    rw [he a (e.symm y.1), e.apply_symm_apply]
    exact y.2 a
  · intro x
    ext
    simp
  · intro y
    ext
    simp
  · intro x y
    ext
    simp

/-- Fixed points in the quotient by the kernel of the `p`-power map transport
to fixed points in the range of that map. -/
public noncomputable def fixedPointSubgroupPowQuotientKerEquivRange
    {A M : Type*} [Group A] [CommGroup M] [MulDistribMulAction A M]
    (p : ℕ) :
    let hker : IsInvariant A M ((powMonoidHom p : M →* M).ker) := by
      have : ((powMonoidHom p : M →* M).ker).Characteristic :=
        powMonoidHom_ker_characteristic (H := M) p
      exact isInvariant_of_characteristic ((powMonoidHom p : M →* M).ker)
    let hrange : IsInvariant A M ((powMonoidHom p : M →* M).range) := by
      have : ((powMonoidHom p : M →* M).range).Characteristic :=
        powMonoidHom_range_characteristic (H := M) p
      exact isInvariant_of_characteristic ((powMonoidHom p : M →* M).range)
    letI : IsInvariant A M ((powMonoidHom p : M →* M).ker) := hker
    letI : IsInvariant A M ((powMonoidHom p : M →* M).range) := hrange
    letI : MulDistribMulAction A (M ⧸ (powMonoidHom p : M →* M).ker) :=
      quotientMulDistribMulAction (A := A) (G := M) _ hker
    letI : MulDistribMulAction A ((powMonoidHom p : M →* M).range) :=
      instMulDistribMulAction_subtype (A := A) (G := M)
        (H := (powMonoidHom p : M →* M).range)
    fixedPointSubgroup A (M ⧸ (powMonoidHom p : M →* M).ker) ≃*
      fixedPointSubgroup A ((powMonoidHom p : M →* M).range) := by
  classical
  let φ : M →* M := powMonoidHom p
  haveI : φ.ker.Characteristic := by
    simpa [φ] using powMonoidHom_ker_characteristic (H := M) p
  haveI : φ.range.Characteristic := by
    simpa [φ] using powMonoidHom_range_characteristic (H := M) p
  let hker : IsInvariant A M φ.ker :=
    isInvariant_of_characteristic φ.ker
  let hrange : IsInvariant A M φ.range :=
    isInvariant_of_characteristic φ.range
  letI : IsInvariant A M φ.ker := hker
  letI : IsInvariant A M φ.range := hrange
  letI : MulDistribMulAction A (M ⧸ φ.ker) :=
    quotientMulDistribMulAction (A := A) (G := M) φ.ker hker
  letI : MulDistribMulAction A φ.range :=
    instMulDistribMulAction_subtype (A := A) (G := M) (H := φ.range)
  refine fixedPointSubgroupMulEquiv (A := A)
    (M := M ⧸ φ.ker) (N := φ.range)
    (QuotientGroup.quotientKerEquivRange φ) ?_
  intro a x
  refine QuotientGroup.induction_on x ?_
  intro m
  ext
  change (a • m) ^ p = a • (m ^ p)
  exact (map_pow (MulDistribMulAction.toMulAut A M a) m p).symm

/-- In a finite abelian `p`-group, the Frattini subgroup is the subgroup of
`p`-th powers. -/
public theorem frattini_eq_powMonoidHom_range_of_isPGroup_commutative
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] [IsMulCommutative R] :
    frattini R = (powMonoidHom p : R →* R).range := by
  classical
  have hcomm : _root_.commutator R = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    apply eq_top_iff.mpr
    intro x _hx
    exact Subgroup.mem_center_iff.mpr
      (fun y => ((IsMulCommutative.is_comm (M := R)).comm x y).symm)
  rw [frattini_eq_closure_commutator_union_powers (R := R) (p := p)]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le (K := (powMonoidHom p : R →* R).range)).2 ?_
    intro x hx
    rcases hx with hxcomm | hxpow
    · have hxbot : x ∈ (⊥ : Subgroup R) := by
        simpa [hcomm] using hxcomm
      have hx1 : x = 1 := by
        simpa using hxbot
      subst x
      exact ⟨1, by simp⟩
    · simpa [powMonoidHom] using hxpow
  · intro x hx
    exact Subgroup.subset_closure (Or.inr (by simpa [powMonoidHom] using hx))

/-- The action of a subgroup `A ≤ G` on a fixed Frattini cover, obtained by
restricting the lifted `G`-action stored in `L`. -/
public abbrev homocyclicFrattiniCoverSubgroupAction
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (A : Subgroup G)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    letI : Group L.cover := L.instGroupCover
    MulDistribMulAction A L.cover := by
  letI : Group L.cover := L.instGroupCover
  exact MulDistribMulAction.compHom L.cover (L.coverAction.comp A.subtype)


public structure HomocyclicFrattiniCoverSubgroupActionDecomposition
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  commutatorSubgroup :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    Subgroup L.cover
  fixedSubgroup :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    Subgroup L.cover
  commutatorSubgroup_eq :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    commutatorSubgroup = commutatorAction (A := A) (G := L.cover)
  fixedSubgroup_eq :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    fixedSubgroup = fixedPointSubgroup A L.cover
  coprime_card :
    letI : Group L.cover := L.instGroupCover
    Nat.Coprime (Nat.card A) (Nat.card L.cover)
  isCompl :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    IsCompl fixedSubgroup commutatorSubgroup


public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedSubgroup_isComplement'_commutatorSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    D.fixedSubgroup.IsComplement' D.commutatorSubgroup := by
  classical
  let : Group L.cover := L.instGroupCover
  let : IsMulCommutative L.cover := L.cover_commutative
  let : CommGroup L.cover := IsMulCommutative.instCommGroup
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · exact D.isCompl.disjoint
  · rw [← Subgroup.mul_normal, D.isCompl.sup_eq_top]
    rfl

/-- The commutator and fixed-point factors also form a complement in the
source order `[W,A] × C_W(A)`. -/
public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorSubgroup_isComplement'_fixedSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    D.commutatorSubgroup.IsComplement' D.fixedSubgroup := by
  classical
  let : Group L.cover := L.instGroupCover
  exact D.fixedSubgroup_isComplement'_commutatorSubgroup.symm

/-- Multiplicative product equivalence in the source order
`[W,A] × C_W(A) ≃ W`. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorFixedMulEquiv
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    D.commutatorSubgroup × D.fixedSubgroup ≃* L.cover := by
  classical
  letI : Group L.cover := L.instGroupCover
  let : IsMulCommutative L.cover := L.cover_commutative
  let : CommGroup L.cover := IsMulCommutative.instCommGroup
  let φ : D.commutatorSubgroup × D.fixedSubgroup →* L.cover := {
    toFun := fun x => (x.1 : L.cover) * (x.2 : L.cover)
    map_one' := by simp
    map_mul' := by
      intro x y
      simp [mul_left_comm, mul_comm] }
  exact MulEquiv.ofBijective φ D.commutatorSubgroup_isComplement'_fixedSubgroup


/-- The ambient cover as a `ZMod (p ^ e)`-module through its exponent. -/
@[reducible] public def HomocyclicFrattiniCoverLinearLift.additiveCoverZModModule
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    Module (ZMod (p ^ e)) (Additive L.cover) := by
  classical
  letI : Group L.cover := L.instGroupCover
  let : IsMulCommutative L.cover := L.cover_commutative
  let : CommGroup L.cover := IsMulCommutative.instCommGroup
  exact AddCommGroup.zmodModule (n := p ^ e) (by
    intro x
    apply Additive.toMul.injective
    have hpow : Additive.toMul x ^ (p ^ e) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [L.cover_exponent])
        (Additive.toMul x)
    simpa using hpow)

/-- Additive product equivalence in the source order
`[W,A] × C_W(A) ≃ W`. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorFixedAddEquiv
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃+ Additive L.cover :=
  letI : Group L.cover := L.instGroupCover
  ((AddEquiv.prodAdditive (G := D.commutatorSubgroup)
    (H := D.fixedSubgroup)).symm.trans
    (MulEquiv.toAdditive D.commutatorFixedMulEquiv))

/-- Linear product equivalence in the source order
`[W,A] × C_W(A) ≃ W`. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorFixedLinearEquiv
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃ₗ[ZMod (p ^ e)]
      Additive L.cover := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  exact D.commutatorFixedAddEquiv.toLinearEquiv
    (fun (c : ZMod (p ^ e)) (x : Additive D.commutatorSubgroup ×
        Additive D.fixedSubgroup) => by
    simpa using (ZMod.map_smul D.commutatorFixedAddEquiv.toAddMonoidHom c x))

/-- The commutator factor embeds linearly as a direct summand of the cover. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorSection
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Additive D.commutatorSubgroup →ₗ[ZMod (p ^ e)] Additive L.cover := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let eLin : (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃ₗ[ZMod (p ^ e)]
      Additive L.cover :=
    D.commutatorFixedLinearEquiv
  exact (LinearEquiv.toLinearMap eLin).comp
      (LinearMap.inl (ZMod (p ^ e)) (Additive D.commutatorSubgroup)
        (Additive D.fixedSubgroup))

/-- The linear projection from the cover onto the commutator factor. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorProjection
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Additive L.cover →ₗ[ZMod (p ^ e)] Additive D.commutatorSubgroup := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let eLin : (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃ₗ[ZMod (p ^ e)]
      Additive L.cover :=
    D.commutatorFixedLinearEquiv
  exact (LinearMap.fst (ZMod (p ^ e)) (Additive D.commutatorSubgroup)
    (Additive D.fixedSubgroup)).comp
      (LinearEquiv.toLinearMap eLin.symm)

/-- The fixed factor embeds linearly as a direct summand of the cover. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedSection
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Additive D.fixedSubgroup →ₗ[ZMod (p ^ e)] Additive L.cover := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let eLin : (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃ₗ[ZMod (p ^ e)]
      Additive L.cover :=
    D.commutatorFixedLinearEquiv
  exact (LinearEquiv.toLinearMap eLin).comp
      (LinearMap.inr (ZMod (p ^ e)) (Additive D.commutatorSubgroup)
        (Additive D.fixedSubgroup))

/-- The linear projection from the cover onto the fixed factor. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedProjection
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Additive L.cover →ₗ[ZMod (p ^ e)] Additive D.fixedSubgroup := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let eLin : (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) ≃ₗ[ZMod (p ^ e)]
      Additive L.cover :=
    D.commutatorFixedLinearEquiv
  exact (LinearMap.snd (ZMod (p ^ e)) (Additive D.commutatorSubgroup)
    (Additive D.fixedSubgroup)).comp
      (LinearEquiv.toLinearMap eLin.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The commutator projection splits the commutator section. -/
public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorProjection_comp_section
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    D.commutatorProjection.comp D.commutatorSection = LinearMap.id := by
  classical
  let _ : Group L.cover := L.instGroupCover
  let _ : IsMulCommutative L.cover := L.cover_commutative
  let _ : CommGroup L.cover := IsMulCommutative.instCommGroup
  let _ : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  let _ : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let _ : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  apply DFunLike.ext _ _
  intro x
  simp [HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorProjection,
    HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorSection]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed projection splits the fixed section. -/
public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedProjection_comp_section
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    D.fixedProjection.comp D.fixedSection = LinearMap.id := by
  classical
  let _ : Group L.cover := L.instGroupCover
  let _ : IsMulCommutative L.cover := L.cover_commutative
  let _ : CommGroup L.cover := IsMulCommutative.instCommGroup
  let _ : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  let _ : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let _ : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  apply DFunLike.ext _ _
  intro x
  simp [HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedProjection,
    HomocyclicFrattiniCoverSubgroupActionDecomposition.fixedSection]

/-- The commutator factor is a projective `ZMod (p ^ e)`-module. -/
public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.projective_commutatorSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Module.Projective (ZMod (p ^ e)) (Additive D.commutatorSubgroup) := by
  classical
  let : Group L.cover := L.instGroupCover
  let : IsMulCommutative L.cover := L.cover_commutative
  let : CommGroup L.cover := IsMulCommutative.instCommGroup
  let : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  let : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let R := ZMod (p ^ e)
  let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  have : Finite L.matrixIndex := Finite.of_fintype L.matrixIndex
  let coverLinear : (L.matrixIndex → R) ≃ₗ[R] Additive L.cover :=
    L.coordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul L.coordinateEquiv.toAddMonoidHom c x))
  have : Module.Projective R (Additive L.cover) :=
    Module.Projective.of_equiv' coverLinear
  exact Module.Projective.of_split D.commutatorSection D.commutatorProjection
    D.commutatorProjection_comp_section

/-- The fixed factor is a projective `ZMod (p ^ e)`-module. -/
public theorem
    HomocyclicFrattiniCoverSubgroupActionDecomposition.projective_fixedSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Module.Projective (ZMod (p ^ e)) (Additive D.fixedSubgroup) := by
  classical
  let : Group L.cover := L.instGroupCover
  let : IsMulCommutative L.cover := L.cover_commutative
  let : CommGroup L.cover := IsMulCommutative.instCommGroup
  let : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  let : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let R := ZMod (p ^ e)
  let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  have : Finite L.matrixIndex := Finite.of_fintype L.matrixIndex
  let coverLinear : (L.matrixIndex → R) ≃ₗ[R] Additive L.cover :=
    L.coordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul L.coordinateEquiv.toAddMonoidHom c x))
  have : Module.Projective R (Additive L.cover) :=
    Module.Projective.of_equiv' coverLinear
  exact Module.Projective.of_split D.fixedSection D.fixedProjection
    D.fixedProjection_comp_section


public structure HomocyclicFrattiniCoverSubgroupBlockDecomposition
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  leftIndex : Type u
  rightIndex : Type u
  [instFintypeLeftIndex : Fintype leftIndex]
  [instFintypeRightIndex : Fintype rightIndex]
  [instDecidableEqLeftIndex : DecidableEq leftIndex]
  [instDecidableEqRightIndex : DecidableEq rightIndex]
  indexEquiv :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    L.toCommonMatrixLift.matrixIndex ≃ leftIndex ⊕ rightIndex
  card_right :
    Fintype.card rightIndex = fixedSubspaceFinrank (G := G) (V := V) (p := p) A
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype leftIndex := instFintypeLeftIndex
    letI : Fintype rightIndex := instFintypeRightIndex
    letI : DecidableEq leftIndex := instDecidableEqLeftIndex
    letI : DecidableEq rightIndex := instDecidableEqRightIndex
    ∀ a : A,
      identityBlockBottomRow (R := ZMod (p ^ e)) (l := leftIndex) (r := rightIndex) *
          Matrix.reindex indexEquiv indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)) *
        identityBlockRightColumn (R := ZMod (p ^ e)) (l := leftIndex) (r := rightIndex) = 1
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype leftIndex := instFintypeLeftIndex
    letI : Fintype rightIndex := instFintypeRightIndex
    letI : DecidableEq leftIndex := instDecidableEqLeftIndex
    letI : DecidableEq rightIndex := instDecidableEqRightIndex
    (∑ a : A,
      identityBlockTopRow (R := ZMod (p ^ e)) (l := leftIndex) (r := rightIndex) *
          Matrix.reindex indexEquiv indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)) *
        identityBlockLeftColumn (R := ZMod (p ^ e)) (l := leftIndex) (r := rightIndex)) = 0


/-- Coordinate blocks and the rank comparison before proving the canonical
matrix-action identities for those blocks. -/
public structure HomocyclicFrattiniCoverSubgroupCoordinateSplit
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  leftIndex : Type u
  rightIndex : Type u
  [instFintypeLeftIndex : Fintype leftIndex]
  [instFintypeRightIndex : Fintype rightIndex]
  [instDecidableEqLeftIndex : DecidableEq leftIndex]
  [instDecidableEqRightIndex : DecidableEq rightIndex]
  indexEquiv :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    L.toCommonMatrixLift.matrixIndex ≃ leftIndex ⊕ rightIndex
  card_right :
    Fintype.card rightIndex = fixedSubspaceFinrank (G := G) (V := V) (p := p) A

/-- Establish the action-side decomposition of the cover for one subgroup.

This is the checked step that turns the restricted action of `A` on the cover
into the complementary subgroups `[W,A₁]` and `C_W(A₁)` before coordinate
blocks are chosen. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_action_decomposition_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupActionDecomposition
        (G := G) (V := V) (p := p) A L) := by
  classical
  let : Group L.cover := L.instGroupCover
  let : Finite L.cover := L.instFiniteCover
  let : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  have hcopAcover : Nat.Coprime (Nat.card A) (Nat.card L.cover) := by
    have hpA : Nat.Coprime p (Nat.card A) := by
      have hpG : Nat.Coprime p (Nat.card G) := by
        have hpV : p ∣ Nat.card V := by
          have hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
          rcases (IsPGroup.iff_card (p := p) (G := V)).1 hVp with ⟨n, hn⟩
          have hn0 : n ≠ 0 := by
            intro hn0
            have hcard1 : Nat.card V = 1 := by
              simpa [hn0] using hn
            have hsub : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hcard1).1
            exact not_subsingleton V hsub
          rw [hn]
          exact dvd_pow_self p hn0
        exact Nat.Coprime.of_dvd_left hpV hcop
      exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card A) hpG
    rcases (IsPGroup.iff_card (p := p) (G := L.cover)).1 L.cover_isPGroup with ⟨n, hn⟩
    rw [hn]
    exact hpA.symm.pow_right n
  have hcoverSolvable : Group.IsSolvable L.cover := by
    let : IsMulCommutative L.cover := L.cover_commutative
    exact Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := L.cover)).comm x y
  have hcompl : IsCompl (fixedPointSubgroup A L.cover)
      (commutatorAction (A := A) (G := L.cover)) := by
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := L.cover) (A := A) hcoverSolvable hcopAcover L.cover_commutative
  refine ⟨{
    commutatorSubgroup := commutatorAction (A := A) (G := L.cover)
    fixedSubgroup := fixedPointSubgroup A L.cover
    commutatorSubgroup_eq := rfl
    fixedSubgroup_eq := rfl
    coprime_card := hcopAcover
    isCompl := hcompl }⟩

/-- Choose coordinate blocks and prove the right-block rank comparison from a
fixed action decomposition on the cover.

This lower wrapper only uses the fixed Frattini cover and its card/rank data;
the global source hypotheses have already been consumed before the action
decomposition is available. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_coordinate_split_of_fixed_decomposition
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupCoordinateSplit
        (G := G) (V := V) (p := p) A L D) := by
  classical
  let : CommGroup V := IsMulCommutative.instCommGroup
  let : Group L.cover := L.instGroupCover
  let : Finite L.cover := L.instFiniteCover
  let : Finite V :=
    Finite.of_equiv (L.cover ⧸ frattini L.cover) L.frattiniQuotientEquiv.toEquiv
  let κ := L.toCommonMatrixLift.matrixIndex
  let : Fintype κ := L.toCommonMatrixLift.instFintypeMatrixIndex
  let n := Fintype.card κ
  let r := fixedSubspaceFinrank (G := G) (V := V) (p := p) A
  have hle : r ≤ n := by
    have hsub : fixedSubspaceFinrank (G := G) (V := V) (p := p) A ≤
        Module.finrank (ZMod p) (Additive V) := by
      dsimp [fixedSubspaceFinrank]
      exact Submodule.finrank_le _
    have hcard : Fintype.card κ = Module.finrank (ZMod p) (Additive V) := by
      exact L.card_matrixIndex
    simpa [n, r, hcard] using hsub
  let leftIndex : Type u := ULift (Fin (n - r))
  let rightIndex : Type u := ULift (Fin r)
  have hsum : Fintype.card (leftIndex ⊕ rightIndex) = n := by
    simp [leftIndex, rightIndex, Nat.sub_add_cancel hle]
  refine ⟨{
    leftIndex := leftIndex
    rightIndex := rightIndex
    instFintypeLeftIndex := inferInstance
    instFintypeRightIndex := inferInstance
    instDecidableEqLeftIndex := inferInstance
    instDecidableEqRightIndex := inferInstance
    indexEquiv := ?_
    card_right := ?_ }⟩
  · exact (Fintype.equivFin κ).trans (Fintype.equivFinOfCardEq hsum).symm
  · simp [rightIndex, r]


/-- The canonical right-block and left-block identities after the subgroup
coordinate split has been chosen. -/
public structure HomocyclicFrattiniCoverSubgroupCoordinateBlockIdentities
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    ∀ a : A,
      identityBlockBottomRow (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex) *
          Matrix.reindex C.indexEquiv C.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)) *
        identityBlockRightColumn (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex) = 1
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    (∑ a : A,
      identityBlockTopRow (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex) *
          Matrix.reindex C.indexEquiv C.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)) *
        identityBlockLeftColumn (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex)) = 0


/-- Convert an adapted subgroup coordinate split directly into the raw
rectangular trace-data interface.

The rectangular matrices are the canonical block inclusions/projections. The
adapted split and the two identities are carried by `H`; this adapter only
repackages them for the trace layer. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupCoordinateSplit.toRectangularReindexedBlockTraceData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D)
    (H : HomocyclicFrattiniCoverSubgroupCoordinateBlockIdentities
      (G := G) (V := V) (p := p) A L D C) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    RectangularReindexedBlockTraceData
      (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
      A (p ^ e) L.toCommonMatrixLift.matrixLift
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) A) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
  letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
  exact {
    leftIndex := C.leftIndex
    rightIndex := C.rightIndex
    instFintypeLeftIndex := C.instFintypeLeftIndex
    instFintypeRightIndex := C.instFintypeRightIndex
    instDecidableEqLeftIndex := C.instDecidableEqLeftIndex
    instDecidableEqRightIndex := C.instDecidableEqRightIndex
    indexEquiv := C.indexEquiv
    leftColumn :=
      identityBlockLeftColumn (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex)
    rightColumn :=
      identityBlockRightColumn (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex)
    topRow :=
      identityBlockTopRow (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex)
    bottomRow :=
      identityBlockBottomRow (R := ZMod (p ^ e)) (l := C.leftIndex) (r := C.rightIndex)
    card_right := C.card_right
    inverse_blocks := by
      rw [matrixOfIdentityBlockColumns_eq_one, matrixOfIdentityBlockRows_eq_one]
      simp
    bottom_right_identity := H.bottom_right_identity
    top_left_sum_zero := H.top_left_sum_zero }


public structure HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockInverseMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  leftColumn :
    Matrix (C.leftIndex ⊕ C.rightIndex) C.leftIndex (ZMod (p ^ e))
  rightColumn :
    Matrix (C.leftIndex ⊕ C.rightIndex) C.rightIndex (ZMod (p ^ e))
  topRow :
    Matrix C.leftIndex (C.leftIndex ⊕ C.rightIndex) (ZMod (p ^ e))
  bottomRow :
    Matrix C.rightIndex (C.leftIndex ⊕ C.rightIndex) (ZMod (p ^ e))
  inverse_blocks :
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    matrixOfBlockColumns leftColumn rightColumn *
      matrixOfBlockRows topRow bottomRow = 1


public structure HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularLinearMaps
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  leftColumnMap :
    (C.leftIndex → ZMod (p ^ e)) →ₗ[ZMod (p ^ e)]
      (C.leftIndex ⊕ C.rightIndex → ZMod (p ^ e))
  rightColumnMap :
    (C.rightIndex → ZMod (p ^ e)) →ₗ[ZMod (p ^ e)]
      (C.leftIndex ⊕ C.rightIndex → ZMod (p ^ e))
  topRowMap :
    (C.leftIndex ⊕ C.rightIndex → ZMod (p ^ e)) →ₗ[ZMod (p ^ e)]
      (C.leftIndex → ZMod (p ^ e))
  bottomRowMap :
    (C.leftIndex ⊕ C.rightIndex → ZMod (p ^ e)) →ₗ[ZMod (p ^ e)]
      (C.rightIndex → ZMod (p ^ e))
  inverse_blocks :
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    ∀ x : C.leftIndex ⊕ C.rightIndex → ZMod (p ^ e),
      leftColumnMap (topRowMap x) + rightColumnMap (bottomRowMap x) = x
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    ∀ (a : A) (x : C.rightIndex → ZMod (p ^ e)),
      bottomRowMap
          (Matrix.toLin'
            (Matrix.reindex C.indexEquiv C.indexEquiv
              (L.toCommonMatrixLift.matrixLift (a : G)))
            (rightColumnMap x)) = x
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    ∀ x : C.leftIndex → ZMod (p ^ e),
      (∑ a : A,
        topRowMap
          (Matrix.toLin'
            (Matrix.reindex C.indexEquiv C.indexEquiv
              (L.toCommonMatrixLift.matrixLift (a : G)))
            (leftColumnMap x))) = 0


public structure HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  leftColumn :
    Matrix (C.leftIndex ⊕ C.rightIndex) C.leftIndex (ZMod (p ^ e))
  rightColumn :
    Matrix (C.leftIndex ⊕ C.rightIndex) C.rightIndex (ZMod (p ^ e))
  topRow :
    Matrix C.leftIndex (C.leftIndex ⊕ C.rightIndex) (ZMod (p ^ e))
  bottomRow :
    Matrix C.rightIndex (C.leftIndex ⊕ C.rightIndex) (ZMod (p ^ e))
  inverse_blocks :
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    matrixOfBlockColumns leftColumn rightColumn *
      matrixOfBlockRows topRow bottomRow = 1
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    ∀ a : A,
      bottomRow * Matrix.reindex C.indexEquiv C.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * rightColumn = 1
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    (∑ a : A,
      topRow * Matrix.reindex C.indexEquiv C.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * leftColumn) = 0

/-- Convert source-side rectangular linear maps into the raw rectangular matrix
package for the same coordinate split. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularLinearMaps.toRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    (M : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularLinearMaps
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D C := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
  letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
  exact {
    leftColumn := LinearMap.toMatrix' M.leftColumnMap
    rightColumn := LinearMap.toMatrix' M.rightColumnMap
    topRow := LinearMap.toMatrix' M.topRowMap
    bottomRow := LinearMap.toMatrix' M.bottomRowMap
    inverse_blocks := by
      rw [Matrix.ext_iff_mulVec]
      intro x
      change
        Matrix.toLin'
          (matrixOfBlockColumns (LinearMap.toMatrix' M.leftColumnMap)
              (LinearMap.toMatrix' M.rightColumnMap) *
            matrixOfBlockRows (LinearMap.toMatrix' M.topRowMap)
              (LinearMap.toMatrix' M.bottomRowMap)) x =
          Matrix.toLin' (1 : Matrix (C.leftIndex ⊕ C.rightIndex)
            (C.leftIndex ⊕ C.rightIndex) (ZMod (p ^ e))) x
      rw [Matrix.toLin'_mul_apply]
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_one]
      rw [matrixOfBlockRows_toMatrix_mulVec, matrixOfBlockColumns_toMatrix_mulVec]
      simpa using M.inverse_blocks x
    bottom_right_identity := by
      intro a
      rw [Matrix.ext_iff_mulVec]
      intro x
      change
        Matrix.toLin'
          (LinearMap.toMatrix' M.bottomRowMap *
              Matrix.reindex C.indexEquiv C.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G)) *
            LinearMap.toMatrix' M.rightColumnMap) x =
          Matrix.toLin' (1 : Matrix C.rightIndex C.rightIndex (ZMod (p ^ e))) x
      rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
      rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
      rw [M.bottom_right_identity a x]
      simp
    top_left_sum_zero := by
      rw [Matrix.ext_iff_mulVec]
      intro x
      calc
        Matrix.mulVec
            (∑ a : A,
              LinearMap.toMatrix' M.topRowMap *
                  Matrix.reindex C.indexEquiv C.indexEquiv
                    (L.toCommonMatrixLift.matrixLift (a : G)) *
                LinearMap.toMatrix' M.leftColumnMap) x =
            ∑ a : A,
              Matrix.mulVec
                (LinearMap.toMatrix' M.topRowMap *
                    Matrix.reindex C.indexEquiv C.indexEquiv
                      (L.toCommonMatrixLift.matrixLift (a : G)) *
                  LinearMap.toMatrix' M.leftColumnMap) x := by
          rw [Matrix.sum_mulVec]
        _ =
            ∑ a : A,
              M.topRowMap
                (Matrix.toLin'
                  (Matrix.reindex C.indexEquiv C.indexEquiv
                    (L.toCommonMatrixLift.matrixLift (a : G)))
                  (M.leftColumnMap x)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          change
            Matrix.toLin'
              (LinearMap.toMatrix' M.topRowMap *
                  Matrix.reindex C.indexEquiv C.indexEquiv
                    (L.toCommonMatrixLift.matrixLift (a : G)) *
                LinearMap.toMatrix' M.leftColumnMap) x =
              M.topRowMap
                (Matrix.toLin'
                  (Matrix.reindex C.indexEquiv C.indexEquiv
                    (L.toCommonMatrixLift.matrixLift (a : G)))
                  (M.leftColumnMap x))
          rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
          rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
        _ = Matrix.mulVec 0 x := by
          rw [M.top_left_sum_zero x]
          simp }


/-- The lower-right action identity for raw rectangular matrices relative to a
chosen coordinate split. -/
public structure HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockBottomRightIdentity
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D)
    (B : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D C) :
    Type (u + 1) where
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    ∀ a : A,
      B.bottomRow * Matrix.reindex C.indexEquiv C.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * B.rightColumn = 1

/-- The upper-left zero-sum identity for raw rectangular matrices relative to a
chosen coordinate split. -/
public structure HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockTopLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D)
    (B : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D C) :
    Type (u + 1) where
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
    letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
    (∑ a : A,
      B.topRow * Matrix.reindex C.indexEquiv C.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * B.leftColumn) = 0

/-- Assemble the inverse block equation and the two action identities into the
raw rectangular matrix package relative to the same coordinate split. -/
public def
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockInverseMatrices.toRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    (B : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D C)
    (H22 : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockBottomRightIdentity
      (G := G) (V := V) (p := p) A L D C B)
    (H11 : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockTopLeftSumZero
      (G := G) (V := V) (p := p) A L D C B) :
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D C where
  leftColumn := B.leftColumn
  rightColumn := B.rightColumn
  topRow := B.topRow
  bottomRow := B.bottomRow
  inverse_blocks := B.inverse_blocks
  bottom_right_identity := H22.bottom_right_identity
  top_left_sum_zero := H11.top_left_sum_zero


public structure HomocyclicFrattiniCoverSubgroupChosenSplitRectangularLinearMaps
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  linearMaps :
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularLinearMaps
      (G := G) (V := V) (p := p) A L D coordinateSplit


public structure HomocyclicFrattiniCoverSubgroupProductCoordinates
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  productCoordinateEquiv :
    ((coordinateSplit.leftIndex ⊕ coordinateSplit.rightIndex) → ZMod (p ^ e)) ≃ₗ[ZMod (p ^ e)]
      ((coordinateSplit.leftIndex → ZMod (p ^ e)) ×
        (coordinateSplit.rightIndex → ZMod (p ^ e)))

/-- The lower-right identity for a chosen product-coordinate equivalence. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightIdentity
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ (a : A) (x : P.coordinateSplit.rightIndex → ZMod (p ^ e)),
      (LinearMap.snd (ZMod (p ^ e))
          (P.coordinateSplit.leftIndex → ZMod (p ^ e))
          (P.coordinateSplit.rightIndex → ZMod (p ^ e)))
        (P.productCoordinateEquiv
          (Matrix.toLin'
            (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
              (L.toCommonMatrixLift.matrixLift (a : G)))
            (P.productCoordinateEquiv.symm
              ((0 : P.coordinateSplit.leftIndex → ZMod (p ^ e)), x)))) = x

/-- Product-coordinate statement that the transported right factor is fixed by
the restricted linear action. This is the direct coordinate form of
`C_W(A)` being fixed pointwise. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateRightFixed
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  right_fixed :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ (a : A) (x : P.coordinateSplit.rightIndex → ZMod (p ^ e)),
      Matrix.toLin'
          (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)))
          (P.productCoordinateEquiv.symm
            ((0 : P.coordinateSplit.leftIndex → ZMod (p ^ e)), x)) =
        P.productCoordinateEquiv.symm
          ((0 : P.coordinateSplit.leftIndex → ZMod (p ^ e)), x)

/-- Product-coordinate statement that the transported right factor lands in
the fixed subgroup `C_W(A)`. This is the subgroup-level form behind
right-factor fixedness. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateRightInFixedSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  right_mem_fixedSubgroup :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ x : P.coordinateSplit.rightIndex → ZMod (p ^ e),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                P.coordinateSplit.indexEquiv)
              (P.productCoordinateEquiv.symm
                ((0 : P.coordinateSplit.leftIndex → ZMod (p ^ e)), x)))) ∈
        D.fixedSubgroup

/-- Membership of the transported right factor in the fixed subgroup gives
coordinate right-factor fixedness. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateRightInFixedSubgroup.toRightFixed
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateRightInFixedSubgroup
      (G := G) (V := V) (p := p) A L D P) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateRightFixed
      (G := G) (V := V) (p := p) A L D P where
  right_fixed := by
    classical
    let : Group L.cover := L.instGroupCover
    let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    let : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
    let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
    let : DecidableEq L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instDecidableEqMatrixIndex
    let : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    let : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    let : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    let : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    intro a x
    let R := ZMod (p ^ e)
    let y : P.coordinateSplit.leftIndex ⊕ P.coordinateSplit.rightIndex → R :=
      P.productCoordinateEquiv.symm
        ((0 : P.coordinateSplit.leftIndex → R), x)
    let z : L.matrixIndex → R :=
      (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y
    have hmem : Additive.toMul (L.coordinateEquiv z) ∈ D.fixedSubgroup := by
      simpa [R, y, z] using H.right_mem_fixedSubgroup x
    have hfixed :
        L.coverAction (a : G) (Additive.toMul (L.coordinateEquiv z)) =
          Additive.toMul (L.coordinateEquiv z) := by
      let : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
      have hmem' : Additive.toMul (L.coordinateEquiv z) ∈ fixedPointSubgroup A L.cover := by
        simpa [D.fixedSubgroup_eq] using hmem
      have hfix_all : ∀ b : A,
          b • Additive.toMul (L.coordinateEquiv z) =
            Additive.toMul (L.coordinateEquiv z) := by
        simpa [fixedPointSubgroup] using hmem'
      exact hfix_all a
    have hcoord :
        L.coordinateEquiv
            (((L.linearLift (a : G) :
                (Module.End R (L.matrixIndex → R))ˣ) :
              Module.End R (L.matrixIndex → R)) z) =
          L.coordinateEquiv z := by
      simpa [R, hfixed] using L.linearLift_coordinate (a : G) z
    have hz :
        (((L.linearLift (a : G) :
            (Module.End R (L.matrixIndex → R))ˣ) :
          Module.End R (L.matrixIndex → R)) z) = z := by
      exact L.coordinateEquiv.injective hcoord
    change
      Matrix.toLin'
          (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G))) y = y
    rw [Matrix.toLin'_reindex]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    simp only [HomocyclicFrattiniCoverLinearLift.toCommonMatrixLift,
      HomocyclicFrattiniCoverLinearLift.toHomocyclicCoverLinearLift,
      HomocyclicCoverLinearLift.toHomocyclicQuotientLinearLift,
      HomocyclicQuotientLinearLift.toHomocyclicCommonLinearLift,
      HomocyclicCommonLinearLift.toCommonMatrixLift]
    let f : (L.matrixIndex → R) →ₗ[R] L.matrixIndex → R :=
      (((L.linearLift (a : G) :
          (Module.End R (L.matrixIndex → R))ˣ) :
        Module.End R (L.matrixIndex → R)))
    have htoLin :
        Matrix.toLin' (LinearMap.toMatrix' f) = f := Matrix.toLin'_toMatrix' f
    change
      (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv.symm)
          ((Matrix.toLin' (LinearMap.toMatrix' f))
            ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y)) = y
    rw [htoLin]
    change
      (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv.symm)
          (((L.linearLift (a : G) :
              (Module.End R (L.matrixIndex → R))ˣ) :
            Module.End R (L.matrixIndex → R)) z) = y
    rw [hz]
    simpa [z, LinearEquiv.funCongrLeft_symm] using
      (LinearEquiv.symm_apply_apply
        (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y)

/-- A fixed right factor gives the lower-right product-coordinate identity. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateRightFixed.toBottomRightIdentity
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateRightFixed
      (G := G) (V := V) (p := p) A L D P) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightIdentity
      (G := G) (V := V) (p := p) A L D P where
  bottom_right_identity := by
    intro a x
    let R := ZMod (p ^ e)
    let X := P.coordinateSplit.leftIndex → R
    let Y := P.coordinateSplit.rightIndex → R
    have h := H.right_fixed a x
    have h' :=
      congrArg
        (fun y : P.coordinateSplit.leftIndex ⊕ P.coordinateSplit.rightIndex → R =>
          (LinearMap.snd R X Y) (P.productCoordinateEquiv y))
        h
    simpa [R, X, Y] using h'

/-- The upper-left zero-sum identity for a chosen product-coordinate
equivalence. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ x : P.coordinateSplit.leftIndex → ZMod (p ^ e),
      (∑ a : A,
        (LinearMap.fst (ZMod (p ^ e))
            (P.coordinateSplit.leftIndex → ZMod (p ^ e))
            (P.coordinateSplit.rightIndex → ZMod (p ^ e)))
          (P.productCoordinateEquiv
            (Matrix.toLin'
              (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G)))
              (P.productCoordinateEquiv.symm
                (x, (0 : P.coordinateSplit.rightIndex → ZMod (p ^ e))))))) = 0

/-- Product-coordinate statement that the transformed left-factor orbit sum is
zero in the full ambient coordinate module. This is the direct coordinate form
of the commutator-factor cancellation step. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ x : P.coordinateSplit.leftIndex → ZMod (p ^ e),
      (∑ a : A,
        Matrix.toLin'
          (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G)))
          (P.productCoordinateEquiv.symm
            (x, (0 : P.coordinateSplit.rightIndex → ZMod (p ^ e))))) = 0

/-- Product-coordinate statement that the transported left factor lands in the
commutator subgroup `[W,A]`. This is the subgroup-level form behind the
left-factor orbit cancellation. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateLeftInCommutatorSubgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  left_mem_commutatorSubgroup :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ x : P.coordinateSplit.leftIndex → ZMod (p ^ e),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                P.coordinateSplit.indexEquiv)
              (P.productCoordinateEquiv.symm
                (x, (0 : P.coordinateSplit.rightIndex → ZMod (p ^ e)))))) ∈
        D.commutatorSubgroup


public structure HomocyclicFrattiniCoverSubgroupDirectProductCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  rightCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (coordinateSplit.rightIndex → ZMod (p ^ e)) ≃+
      Additive D.fixedSubgroup
  leftCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (coordinateSplit.leftIndex → ZMod (p ^ e)) ≃+
      Additive D.commutatorSubgroup
  coordinate_decompose :
    letI : Group L.cover := L.instGroupCover
    ∀ (xL : coordinateSplit.leftIndex → ZMod (p ^ e))
      (xR : coordinateSplit.rightIndex → ZMod (p ^ e)),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                coordinateSplit.indexEquiv)
              ((LinearEquiv.sumPiEquivProdPi (ZMod (p ^ e))
                  coordinateSplit.leftIndex coordinateSplit.rightIndex
                  (fun _ => ZMod (p ^ e))).symm (xL, xR)))) =
        ((Additive.toMul (leftCoordinateEquiv xL) : D.commutatorSubgroup) :
            L.cover) *
          ((Additive.toMul (rightCoordinateEquiv xR) : D.fixedSubgroup) :
            L.cover)


public structure HomocyclicFrattiniCoverSubgroupFactorCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  leftCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (coordinateSplit.leftIndex → ZMod (p ^ e)) ≃+
      Additive D.commutatorSubgroup
  rightCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (coordinateSplit.rightIndex → ZMod (p ^ e)) ≃+
      Additive D.fixedSubgroup


public structure HomocyclicFrattiniCoverSubgroupFactorCoordinateEquivs
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  leftCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (C.leftIndex → ZMod (p ^ e)) ≃+
      Additive D.commutatorSubgroup
  rightCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (C.rightIndex → ZMod (p ^ e)) ≃+
      Additive D.fixedSubgroup

/-- Reattach source-chosen factor coordinates to the split they were chosen
over. -/
public def HomocyclicFrattiniCoverSubgroupFactorCoordinateEquivs.toFactorCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupFactorCoordinateEquivs
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupFactorCoordinateData
      (G := G) (V := V) (p := p) A L D where
  coordinateSplit := C
  leftCoordinateEquiv := H.leftCoordinateEquiv
  rightCoordinateEquiv := H.rightCoordinateEquiv

/-- Finite-free rank data for the two action factors relative to an already
chosen coordinate split.

This is the precise rank comparison needed to choose `ZMod (p ^ e)`
coordinates on `[W,A]` and `C_W(A)`. The checked adapter below turns these
rank equalities into additive coordinate equivalences using the projectivity
facts for the two complementary summands. -/
public structure HomocyclicFrattiniCoverSubgroupFactorFinrankData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  left_finrank :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Fintype C.leftIndex := C.instFintypeLeftIndex
    Module.finrank (ZMod (p ^ e)) (Additive D.commutatorSubgroup) =
      Fintype.card C.leftIndex
  right_finrank :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    letI : Fintype C.rightIndex := C.instFintypeRightIndex
    Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) =
      Fintype.card C.rightIndex


public structure HomocyclicFrattiniCoverSubgroupFixedFactorCardData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  fixed_card :
    letI : Group L.cover := L.instGroupCover
    Nat.card D.fixedSubgroup =
      (p ^ e) ^ fixedSubspaceFinrank (G := G) (V := V) (p := p) A

/-- Fixed points in the Frattini quotient of a lifted cover transport to fixed
points in the original elementary-abelian group through the stored quotient
equivalence. -/
public noncomputable def
    HomocyclicFrattiniCoverLinearLift.fixedPointSubgroupFrattiniQuotientEquiv
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
      isInvariant_of_characteristic (frattini L.cover)
    letI : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
      quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
    letI : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
    fixedPointSubgroup A (L.cover ⧸ frattini L.cover) ≃ fixedPointSubgroup A V := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
    isInvariant_of_characteristic (frattini L.cover)
  letI : IsInvariant A L.cover (frattini L.cover) := hΦinv
  letI : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
    quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
  letI : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
  refine
    { toFun := fun x => ⟨L.frattiniQuotientEquiv x.1, ?_⟩
      invFun := fun y => ⟨L.frattiniQuotientEquiv.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro a
    rcases QuotientGroup.mk'_surjective (frattini L.cover) x.1 with ⟨w, hw⟩
    have hxfix : a • x.1 = x.1 :=
      (FixedPoints.mem_subgroup (M := A) (a := x.1)).1 x.2 a
    have hx' := congrArg L.frattiniQuotientEquiv hxfix
    have hact :
        L.frattiniQuotientEquiv (a • x.1) =
          a • L.frattiniQuotientEquiv x.1 := by
      calc
        L.frattiniQuotientEquiv (a • x.1) =
            L.frattiniQuotientEquiv
              (a • QuotientGroup.mk' (frattini L.cover) w) := by
              rw [← hw]
        _ = L.frattiniQuotientEquiv
              (QuotientGroup.mk' (frattini L.cover) (L.coverAction (a : G) w)) := by
              congr 1
        _ = a • L.frattiniQuotientEquiv
              (QuotientGroup.mk' (frattini L.cover) w) := by
              change L.frattiniQuotientEquiv
                (QuotientGroup.mk' (frattini L.cover) (L.coverAction (a : G) w)) =
                (a : G) • L.frattiniQuotientEquiv
                  (QuotientGroup.mk' (frattini L.cover) w)
              exact L.quotientEquiv_action (a : G) w
        _ = a • L.frattiniQuotientEquiv x.1 := by rw [hw]
    exact hact.symm.trans hx'
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro a
    apply L.frattiniQuotientEquiv.injective
    rcases QuotientGroup.mk'_surjective (frattini L.cover)
        (L.frattiniQuotientEquiv.symm y.1) with ⟨w, hw⟩
    have hyfix : a • y.1 = y.1 :=
      (FixedPoints.mem_subgroup (M := A) (a := y.1)).1 y.2 a
    calc
      L.frattiniQuotientEquiv (a • L.frattiniQuotientEquiv.symm y.1)
          = L.frattiniQuotientEquiv (a • QuotientGroup.mk' (frattini L.cover) w) := by
            rw [hw]
      _ = L.frattiniQuotientEquiv
            (QuotientGroup.mk' (frattini L.cover) (L.coverAction (a : G) w)) := by
            congr 1
      _ = a • L.frattiniQuotientEquiv (QuotientGroup.mk' (frattini L.cover) w) := by
            change L.frattiniQuotientEquiv
              (QuotientGroup.mk' (frattini L.cover) (L.coverAction (a : G) w)) =
              (a : G) • L.frattiniQuotientEquiv
                (QuotientGroup.mk' (frattini L.cover) w)
            exact L.quotientEquiv_action (a : G) w
      _ = a • y.1 := by rw [hw, L.frattiniQuotientEquiv.apply_symm_apply]
      _ = y.1 := hyfix
      _ = L.frattiniQuotientEquiv (L.frattiniQuotientEquiv.symm y.1) := by
            rw [L.frattiniQuotientEquiv.apply_symm_apply]
  · intro x
    ext
    simp
  · intro y
    ext
    simp

/-- Fixed points in the Frattini quotient of the cover have the cardinality
dictated by the fixed subspace of the original elementary-abelian action. -/
public theorem
    HomocyclicFrattiniCoverLinearLift.fixedPointSubgroup_frattiniQuotient_card
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
      isInvariant_of_characteristic (frattini L.cover)
    letI : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
      quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
    Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) =
      p ^ fixedSubspaceFinrank (G := G) (V := V) (p := p) A := by
  classical
  let : Group L.cover := L.instGroupCover
  let : Finite L.cover := L.instFiniteCover
  let : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
    isInvariant_of_characteristic (frattini L.cover)
  let : IsInvariant A L.cover (frattini L.cover) := hΦinv
  let : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
    quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
  let : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
  let : Finite V :=
    Finite.of_equiv (L.cover ⧸ frattini L.cover) L.frattiniQuotientEquiv.toEquiv
  calc
    Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) =
        Nat.card (fixedPointSubgroup A V) :=
      Nat.card_congr L.fixedPointSubgroupFrattiniQuotientEquiv
    _ = p ^ fixedSubspaceFinrank (G := G) (V := V) (p := p) A := by
      simpa [fixedSubspaceFinrank] using
        (fixedPointSubgroup_card_eq_prime_pow_finrank
          (A := A) (M := V) (p := p))


public structure HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  fixed_frattini_card :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
      isInvariant_of_characteristic (frattini L.cover)
    letI : IsInvariant A L.cover (frattini L.cover) := hΦinv
    letI : MulDistribMulAction A (frattini L.cover) :=
      instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := frattini L.cover)
    Nat.card (fixedPointSubgroup A (frattini L.cover)) =
      p ^ ((e - 1) * fixedSubspaceFinrank (G := G) (V := V) (p := p) A)

/-- Convert the residual Frattini fixed-point count into the fixed-factor
cardinality comparison.

The quotient factor is checked from the stored Frattini quotient equivalence;
the cover fixed-point count then factors by coprime action through
`Φ(W)`. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData.toFixedFactorCardData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupFixedFactorCardData
      (G := G) (V := V) (p := p) A L D C := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
    isInvariant_of_characteristic (frattini L.cover)
  letI : IsInvariant A L.cover (frattini L.cover) := hΦinv
  letI : MulDistribMulAction A (frattini L.cover) :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := frattini L.cover)
  letI : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
    quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
  let r := fixedSubspaceFinrank (G := G) (V := V) (p := p) A
  have hsolv : Group.IsSolvable L.cover := by
    let : IsMulCommutative L.cover := L.cover_commutative
    exact Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := L.cover)).comm x y
  have hfactor :
      Nat.card (fixedPointSubgroup A L.cover) =
        Nat.card (fixedPointSubgroup A (frattini L.cover)) *
          Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) := by
    simpa using
      (fixedPointSubgroup_card_eq_mul_quotient_action
        (A := A) (M := L.cover) (N := frattini L.cover)
        hΦinv hsolv D.coprime_card)
  have hfixed :
      Nat.card (fixedPointSubgroup A L.cover) =
        p ^ ((e - 1) * r) * p ^ r := by
    calc
      Nat.card (fixedPointSubgroup A L.cover) =
          Nat.card (fixedPointSubgroup A (frattini L.cover)) *
            Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) := hfactor
      _ = p ^ ((e - 1) * r) * p ^ r := by
        rw [H.fixed_frattini_card]
        simpa [r] using
          congrArg (fun n =>
            p ^ ((e - 1) * r) * n)
            (L.fixedPointSubgroup_frattiniQuotient_card
              (G := G) (V := V) (p := p) (A := A))
  have harith :
      p ^ ((e - 1) * r) * p ^ r = (p ^ e) ^ r := by
    have hpred : e - 1 + 1 = e := Nat.sub_add_cancel (Nat.succ_le_of_lt he)
    calc
      p ^ ((e - 1) * r) * p ^ r = p ^ ((e - 1) * r + r) := by
        rw [← pow_add]
      _ = p ^ (e * r) := by
        congr 1
        have hmul : (e - 1 + 1) * r = e * r := by
          rw [hpred]
        simpa [Nat.add_mul] using hmul
      _ = (p ^ e) ^ r := by
        rw [pow_mul]
  exact {
    fixed_card := by
      calc
        Nat.card D.fixedSubgroup = Nat.card (fixedPointSubgroup A L.cover) := by
          rw [D.fixedSubgroup_eq]
        _ = p ^ ((e - 1) * r) * p ^ r := hfixed
        _ = (p ^ e) ^ r := harith
        _ = (p ^ e) ^ fixedSubspaceFinrank (G := G) (V := V) (p := p) A := by
          rfl }


public structure HomocyclicFrattiniCoverSubgroupFixedFactorFinrankData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  fixed_finrank :
    letI : Group L.cover := L.instGroupCover
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
      L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) =
      fixedSubspaceFinrank (G := G) (V := V) (p := p) A

/-- Convert a fixed-factor cardinality comparison into the corresponding
finite-free rank comparison. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupFixedFactorCardData.toFixedFactorFinrankData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    [IsLocalRing (ZMod (p ^ e))]
    (H : HomocyclicFrattiniCoverSubgroupFixedFactorCardData
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupFixedFactorFinrankData
      (G := G) (V := V) (p := p) A L D C := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Fintype L.cover := L.instFintypeCover
  letI : Finite L.cover := L.instFiniteCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  let R := ZMod (p ^ e)
  letI : Module R (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module R (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  haveI : Module.Finite R (Additive D.fixedSubgroup) := Module.Finite.of_finite
  haveI : Module.Projective R (Additive D.fixedSubgroup) :=
    D.projective_fixedSubgroup
  haveI : Module.Flat R (Additive D.fixedSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Free R (Additive D.fixedSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  have hR : Nat.card R = p ^ e := by
    simp [R, Nat.card_eq_fintype_card, ZMod.card]
  have hR_ge : 2 ≤ p ^ e :=
    Nat.one_lt_pow (Nat.ne_of_gt he) (Fact.out : Nat.Prime p).one_lt
  have h_add_card :
      Nat.card (Additive D.fixedSubgroup) = Nat.card D.fixedSubgroup :=
    Nat.card_congr
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hcard :
      Nat.card (Additive D.fixedSubgroup) =
        (p ^ e) ^ fixedSubspaceFinrank (G := G) (V := V) (p := p) A :=
    h_add_card.trans H.fixed_card
  exact {
    fixed_finrank :=
      finite_free_finrank_eq_of_natCard_eq_pow
        (R := R) (M := Additive D.fixedSubgroup)
        (q := p ^ e)
        (n := fixedSubspaceFinrank (G := G) (V := V) (p := p) A)
        hR hR_ge hcard }

/-- The fixed-factor rank comparison determines the complementary commutator
rank because the two factors linearly multiply to the ambient homocyclic cover. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupFixedFactorFinrankData.toFactorFinrankData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    [IsLocalRing (ZMod (p ^ e))]
    (H : HomocyclicFrattiniCoverSubgroupFixedFactorFinrankData
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupFactorFinrankData
      (G := G) (V := V) (p := p) A L D C := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  let R := ZMod (p ^ e)
  letI : Module R (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module R (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module R (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  letI : Fintype L.toCommonMatrixLift.matrixIndex :=
    L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  haveI : Finite C.leftIndex := Finite.of_fintype C.leftIndex
  haveI : Finite C.rightIndex := Finite.of_fintype C.rightIndex
  haveI : Module.Finite R (Additive D.commutatorSubgroup) := Module.Finite.of_finite
  haveI : Module.Finite R (Additive D.fixedSubgroup) := Module.Finite.of_finite
  haveI : Module.Projective R (Additive D.commutatorSubgroup) :=
    D.projective_commutatorSubgroup
  haveI : Module.Projective R (Additive D.fixedSubgroup) :=
    D.projective_fixedSubgroup
  haveI : Module.Flat R (Additive D.commutatorSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Flat R (Additive D.fixedSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Free R (Additive D.commutatorSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free R (Additive D.fixedSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  let coverLinear : (L.matrixIndex → R) ≃ₗ[R] Additive L.cover :=
    L.coordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul L.coordinateEquiv.toAddMonoidHom c x))
  let reindex :
      (C.leftIndex ⊕ C.rightIndex → R) ≃ₗ[R] (L.matrixIndex → R) :=
    LinearEquiv.funCongrLeft R R C.indexEquiv
  let productLinear :
      (C.leftIndex ⊕ C.rightIndex → R) ≃ₗ[R]
        Additive D.commutatorSubgroup × Additive D.fixedSubgroup :=
    (reindex.trans coverLinear).trans D.commutatorFixedLinearEquiv.symm
  have hdomain_prod :
      Module.finrank R (C.leftIndex ⊕ C.rightIndex → R) =
        Module.finrank R ((C.leftIndex → R) × (C.rightIndex → R)) :=
    (LinearEquiv.sumPiEquivProdPi R C.leftIndex C.rightIndex
      (fun _ => R)).finrank_eq
  have hdomain :
      Module.finrank R (C.leftIndex ⊕ C.rightIndex → R) =
        Fintype.card C.leftIndex + Fintype.card C.rightIndex := by
    rw [hdomain_prod, Module.finrank_prod]
    rw [Module.finrank_eq_card_basis (Pi.basisFun R C.leftIndex),
      Module.finrank_eq_card_basis (Pi.basisFun R C.rightIndex)]
  have hprod :
      Module.finrank R (C.leftIndex ⊕ C.rightIndex → R) =
        Module.finrank R
          (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) :=
    productLinear.finrank_eq
  have hfactors :
      Module.finrank R
          (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) =
        Module.finrank R (Additive D.commutatorSubgroup) +
          Module.finrank R (Additive D.fixedSubgroup) := by
    rw [Module.finrank_prod]
  have hright :
      Module.finrank R (Additive D.fixedSubgroup) =
        Fintype.card C.rightIndex := by
    exact H.fixed_finrank.trans C.card_right.symm
  have hsum :
      Fintype.card C.leftIndex + Fintype.card C.rightIndex =
        Module.finrank R (Additive D.commutatorSubgroup) +
          Fintype.card C.rightIndex := by
    calc
      Fintype.card C.leftIndex + Fintype.card C.rightIndex =
          Module.finrank R (C.leftIndex ⊕ C.rightIndex → R) := hdomain.symm
      _ = Module.finrank R
            (Additive D.commutatorSubgroup × Additive D.fixedSubgroup) := hprod
      _ = Module.finrank R (Additive D.commutatorSubgroup) +
            Module.finrank R (Additive D.fixedSubgroup) := hfactors
      _ = Module.finrank R (Additive D.commutatorSubgroup) +
            Fintype.card C.rightIndex := by rw [hright]
  exact {
    left_finrank := by
      exact Nat.add_right_cancel hsum.symm
    right_finrank := hright }

/-- Over a finite local ring, projective factor modules with the prescribed
finite rank have additive coordinate equivalences from the corresponding
coordinate functions. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupFactorFinrankData.toFactorCoordinateEquivs
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    [IsLocalRing (ZMod (p ^ e))]
    (H : HomocyclicFrattiniCoverSubgroupFactorFinrankData
      (G := G) (V := V) (p := p) A L D C) :
    HomocyclicFrattiniCoverSubgroupFactorCoordinateEquivs
      (G := G) (V := V) (p := p) A L D C := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  let R := ZMod (p ^ e)
  letI : Module R (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module R (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module R (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  haveI : Finite C.leftIndex := Finite.of_fintype C.leftIndex
  haveI : Finite C.rightIndex := Finite.of_fintype C.rightIndex
  haveI : Module.Finite R (Additive D.commutatorSubgroup) := Module.Finite.of_finite
  haveI : Module.Finite R (Additive D.fixedSubgroup) := Module.Finite.of_finite
  haveI : Module.Projective R (Additive D.commutatorSubgroup) :=
    D.projective_commutatorSubgroup
  haveI : Module.Projective R (Additive D.fixedSubgroup) :=
    D.projective_fixedSubgroup
  haveI : Module.Flat R (Additive D.commutatorSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Flat R (Additive D.fixedSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Free R (Additive D.commutatorSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free R (Additive D.fixedSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  have left_fun_finrank :
      Module.finrank R (C.leftIndex → R) = Fintype.card C.leftIndex := by
    exact Module.finrank_eq_card_basis (Pi.basisFun R C.leftIndex)
  have right_fun_finrank :
      Module.finrank R (C.rightIndex → R) = Fintype.card C.rightIndex := by
    exact Module.finrank_eq_card_basis (Pi.basisFun R C.rightIndex)
  let leftLinear : (C.leftIndex → R) ≃ₗ[R] Additive D.commutatorSubgroup :=
    LinearEquiv.ofFinrankEq (C.leftIndex → R) (Additive D.commutatorSubgroup)
      (left_fun_finrank.trans H.left_finrank.symm)
  let rightLinear : (C.rightIndex → R) ≃ₗ[R] Additive D.fixedSubgroup :=
    LinearEquiv.ofFinrankEq (C.rightIndex → R) (Additive D.fixedSubgroup)
      (right_fun_finrank.trans H.right_finrank.symm)
  exact {
    leftCoordinateEquiv := leftLinear.toAddEquiv
    rightCoordinateEquiv := rightLinear.toAddEquiv }


public structure HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  productCoordinates :
    HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D
  rightCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e)) ≃+
      Additive D.fixedSubgroup
  rightCoordinate_compatible :
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instDecidableEqRightIndex
    ∀ x : productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                productCoordinates.coordinateSplit.indexEquiv)
              (productCoordinates.productCoordinateEquiv.symm
                ((0 : productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e)), x)))) =
        ((Additive.toMul (rightCoordinateEquiv x) : D.fixedSubgroup) : L.cover)
  leftCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e)) ≃+
      Additive D.commutatorSubgroup
  leftCoordinate_compatible :
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instDecidableEqRightIndex
    ∀ x : productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                productCoordinates.coordinateSplit.indexEquiv)
              (productCoordinates.productCoordinateEquiv.symm
                (x, (0 : productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e)))))) =
        ((Additive.toMul (leftCoordinateEquiv x) : D.commutatorSubgroup) : L.cover)


public structure HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  productCoordinates :
    HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D
  rightCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e)) ≃+
      Additive D.fixedSubgroup
  leftCoordinateEquiv :
    letI : Group L.cover := L.instGroupCover
    (productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e)) ≃+
      Additive D.commutatorSubgroup
  coordinate_decompose :
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq productCoordinates.coordinateSplit.leftIndex :=
      productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq productCoordinates.coordinateSplit.rightIndex :=
      productCoordinates.coordinateSplit.instDecidableEqRightIndex
    ∀ (xL : productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e))
      (xR : productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e)),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                productCoordinates.coordinateSplit.indexEquiv)
              (productCoordinates.productCoordinateEquiv.symm (xL, xR)))) =
        ((Additive.toMul (leftCoordinateEquiv xL) : D.commutatorSubgroup) :
            L.cover) *
          ((Additive.toMul (rightCoordinateEquiv xR) : D.fixedSubgroup) :
            L.cover)

set_option backward.isDefEq.respectTransparency false in
/-- Separate subgroup-factor coordinates assemble to arbitrary product
coordinates and a full product-coordinate decomposition.

The only nontrivial group step is the checked complement product equivalence
`[W,A] × C_W(A) ≃ W`; scalar compatibility of the resulting additive
equivalence is automatic for `ZMod (p ^ e)` modules. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupFactorCoordinateData.toProductCoordinateDecompositionData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (H : HomocyclicFrattiniCoverSubgroupFactorCoordinateData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData
      (G := G) (V := V) (p := p) A L D := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) := AddCommGroup.zmodModule (n := p ^ e) (by
    intro x
    apply Additive.toMul.injective
    have hpow : Additive.toMul x ^ (p ^ e) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [L.cover_exponent])
        (Additive.toMul x)
    simpa using hpow)
  letI : Module (ZMod (p ^ e)) (Additive D.commutatorSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.commutatorSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  let C := H.coordinateSplit
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  let R := ZMod (p ^ e)
  let X := C.leftIndex → R
  let Y := C.rightIndex → R
  let E := C.leftIndex ⊕ C.rightIndex → R
  let leftLinear : X ≃ₗ[R] Additive D.commutatorSubgroup :=
    H.leftCoordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul H.leftCoordinateEquiv.toAddMonoidHom c x))
  let rightLinear : Y ≃ₗ[R] Additive D.fixedSubgroup :=
    H.rightCoordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul H.rightCoordinateEquiv.toAddMonoidHom c x))
  let factorAddEquiv : X × Y ≃+ Additive L.cover :=
    (AddEquiv.prodCongr leftLinear.toAddEquiv rightLinear.toAddEquiv).trans
      ((AddEquiv.prodAdditive (G := D.commutatorSubgroup)
        (H := D.fixedSubgroup)).symm.trans
        (MulEquiv.toAdditive D.commutatorFixedMulEquiv))
  let factorLinear : (X × Y) ≃ₗ[R] Additive L.cover :=
    factorAddEquiv.toLinearEquiv (fun (c : R) (x : X × Y) => by
      simpa using (ZMod.map_smul factorAddEquiv.toAddMonoidHom c x))
  let coverLinear : (L.matrixIndex → R) ≃ₗ[R] Additive L.cover :=
    L.coordinateEquiv.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul L.coordinateEquiv.toAddMonoidHom c x))
  let reindex : E ≃ₗ[R] L.matrixIndex → R :=
    LinearEquiv.funCongrLeft R R C.indexEquiv
  let productCoordinateEquiv : E ≃ₗ[R] (X × Y) :=
    (reindex.trans coverLinear).trans factorLinear.symm
  exact {
    productCoordinates := {
      coordinateSplit := C
      productCoordinateEquiv := productCoordinateEquiv }
    rightCoordinateEquiv := H.rightCoordinateEquiv
    leftCoordinateEquiv := H.leftCoordinateEquiv
    coordinate_decompose := by
      intro xL xR
      change
        Additive.toMul
            (L.coordinateEquiv
              (reindex (productCoordinateEquiv.symm (xL, xR)))) =
          ((Additive.toMul (H.leftCoordinateEquiv xL) : D.commutatorSubgroup) :
              L.cover) *
            ((Additive.toMul (H.rightCoordinateEquiv xR) : D.fixedSubgroup) :
              L.cover)
      have hprod :
          productCoordinateEquiv.symm (xL, xR) =
            reindex.symm (coverLinear.symm (factorLinear (xL, xR))) := by
        simp [productCoordinateEquiv]
      rw [hprod]
      have hpair :
          (AddEquiv.prodCongr leftLinear.toAddEquiv rightLinear.toAddEquiv)
              (xL, xR) =
            (H.leftCoordinateEquiv xL, H.rightCoordinateEquiv xR) := by
        ext <;> rfl
      simp [coverLinear, factorLinear, factorAddEquiv, leftLinear, rightLinear,
        HomocyclicFrattiniCoverSubgroupActionDecomposition.commutatorFixedMulEquiv,
        hpair]
      congr 1 <;> rw [L.coordinateEquiv.apply_symm_apply] <;> rfl }

/-- Axis compatibility for arbitrary product coordinates gives the full
product-coordinate subgroup decomposition. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupCoordinateData.toProductCoordinateDecompositionData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupCoordinateData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData
      (G := G) (V := V) (p := p) A L D where
  productCoordinates := H.productCoordinates
  rightCoordinateEquiv := H.rightCoordinateEquiv
  leftCoordinateEquiv := H.leftCoordinateEquiv
  coordinate_decompose := by
    classical
    let : Group L.cover := L.instGroupCover
    let P := H.productCoordinates
    let C := P.coordinateSplit
    let R := ZMod (p ^ e)
    let X := C.leftIndex → R
    let Y := C.rightIndex → R
    let E := C.leftIndex ⊕ C.rightIndex → R
    let productCoordinateEquiv : E ≃ₗ[R] X × Y := P.productCoordinateEquiv
    let reindex : E ≃ₗ[R] L.matrixIndex → R :=
      LinearEquiv.funCongrLeft R R C.indexEquiv
    intro xL xR
    have hsplit :
        productCoordinateEquiv.symm (xL, xR) =
          productCoordinateEquiv.symm (xL, (0 : Y)) +
            productCoordinateEquiv.symm ((0 : X), xR) := by
      calc
        productCoordinateEquiv.symm (xL, xR) =
            productCoordinateEquiv.symm ((xL, (0 : Y)) + ((0 : X), xR)) := by
              simp [X, Y]
        _ =
            productCoordinateEquiv.symm (xL, (0 : Y)) +
              productCoordinateEquiv.symm ((0 : X), xR) := by
              rw [map_add]
    have hreindex :
        reindex (productCoordinateEquiv.symm (xL, xR)) =
          reindex (productCoordinateEquiv.symm (xL, (0 : Y))) +
            reindex (productCoordinateEquiv.symm ((0 : X), xR)) := by
      simp [hsplit]
    have hleft :
        Additive.toMul
            (L.coordinateEquiv
              (reindex (productCoordinateEquiv.symm (xL, (0 : Y))))) =
          ((Additive.toMul (H.leftCoordinateEquiv xL) : D.commutatorSubgroup) :
            L.cover) := by
      exact H.leftCoordinate_compatible xL
    have hright :
        Additive.toMul
            (L.coordinateEquiv
              (reindex (productCoordinateEquiv.symm ((0 : X), xR)))) =
          ((Additive.toMul (H.rightCoordinateEquiv xR) : D.fixedSubgroup) :
            L.cover) := by
      exact H.rightCoordinate_compatible xR
    calc
      Additive.toMul
          (L.coordinateEquiv (reindex (productCoordinateEquiv.symm (xL, xR)))) =
          Additive.toMul
              (L.coordinateEquiv
                (reindex (productCoordinateEquiv.symm (xL, (0 : Y))))) *
            Additive.toMul
              (L.coordinateEquiv
                (reindex (productCoordinateEquiv.symm ((0 : X), xR)))) := by
            rw [hreindex]
            have hmap :
                L.coordinateEquiv
                    (reindex (productCoordinateEquiv.symm (xL, (0 : Y))) +
                      reindex (productCoordinateEquiv.symm ((0 : X), xR))) =
                  L.coordinateEquiv
                      (reindex (productCoordinateEquiv.symm (xL, (0 : Y)))) +
                    L.coordinateEquiv
                      (reindex (productCoordinateEquiv.symm ((0 : X), xR))) := by
              exact map_add L.coordinateEquiv _ _
            rw [hmap]
            exact toMul_add _ _
      _ = ((Additive.toMul (H.leftCoordinateEquiv xL) : D.commutatorSubgroup) :
            L.cover) *
          ((Additive.toMul (H.rightCoordinateEquiv xR) : D.fixedSubgroup) :
            L.cover) := by
            rw [hleft, hright]

/-- A canonical direct-product coordinate decomposition is a product-coordinate
decomposition for the canonical product equivalence. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupDirectProductCoordinateData.toProductCoordinateDecompositionData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (H : HomocyclicFrattiniCoverSubgroupDirectProductCoordinateData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData
      (G := G) (V := V) (p := p) A L D where
  productCoordinates := {
    coordinateSplit := H.coordinateSplit
    productCoordinateEquiv :=
      LinearEquiv.sumPiEquivProdPi (ZMod (p ^ e))
        H.coordinateSplit.leftIndex H.coordinateSplit.rightIndex
        (fun _ => ZMod (p ^ e)) }
  rightCoordinateEquiv := H.rightCoordinateEquiv
  leftCoordinateEquiv := H.leftCoordinateEquiv
  coordinate_decompose := by
    classical
    let : Group L.cover := L.instGroupCover
    intro xL xR
    simpa using H.coordinate_decompose xL xR


public structure HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  productCoordinates :
    HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D
  rightInFixedSubgroup :
    HomocyclicFrattiniCoverSubgroupProductCoordinateRightInFixedSubgroup
      (G := G) (V := V) (p := p) A L D productCoordinates
  leftInCommutatorSubgroup :
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftInCommutatorSubgroup
      (G := G) (V := V) (p := p) A L D productCoordinates

/-- A full product-coordinate subgroup decomposition gives the two axis
membership facts used by the checked action-identity adapters. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData.toSubgroupMembershipData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateDecompositionData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipData
      (G := G) (V := V) (p := p) A L D where
  productCoordinates := H.productCoordinates
  rightInFixedSubgroup := by
    classical
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqRightIndex
    refine ⟨?_⟩
    intro x
    have h := H.coordinate_decompose
      (0 : H.productCoordinates.coordinateSplit.leftIndex → ZMod (p ^ e)) x
    rw [h]
    simp
  leftInCommutatorSubgroup := by
    classical
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqRightIndex
    refine ⟨?_⟩
    intro x
    have h := H.coordinate_decompose x
      (0 : H.productCoordinates.coordinateSplit.rightIndex → ZMod (p ^ e))
    rw [h]
    simp


/-- The explicit subgroup-coordinate source package implies the membership
package used by the checked action-identity adapters. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupCoordinateData.toSubgroupMembershipData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupCoordinateData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipData
      (G := G) (V := V) (p := p) A L D where
  productCoordinates := H.productCoordinates
  rightInFixedSubgroup := by
    classical
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqRightIndex
    refine ⟨?_⟩
    intro x
    rw [H.rightCoordinate_compatible x]
    exact (Additive.toMul (H.rightCoordinateEquiv x) : D.fixedSubgroup).property
  leftInCommutatorSubgroup := by
    classical
    letI : Group L.cover := L.instGroupCover
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instFintypeLeftIndex
    letI : Fintype H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.leftIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq H.productCoordinates.coordinateSplit.rightIndex :=
      H.productCoordinates.coordinateSplit.instDecidableEqRightIndex
    refine ⟨?_⟩
    intro x
    rw [H.leftCoordinate_compatible x]
    exact (Additive.toMul (H.leftCoordinateEquiv x) : D.commutatorSubgroup).property


public structure HomocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  commutator_orbit_sum_zero :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    letI : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    letI : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    ∀ y : P.coordinateSplit.leftIndex ⊕ P.coordinateSplit.rightIndex → ZMod (p ^ e),
      Additive.toMul
          (L.coordinateEquiv
            ((LinearEquiv.funCongrLeft (ZMod (p ^ e)) (ZMod (p ^ e))
                P.coordinateSplit.indexEquiv) y)) ∈
        D.commutatorSubgroup →
      (∑ a : A,
        Matrix.toLin'
          (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G))) y) = 0

/-- Left-factor membership in the commutator subgroup plus commutator orbit
cancellation gives the ambient left-factor sum cancellation. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftInCommutatorSubgroup.toLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D}
    (Hleft : HomocyclicFrattiniCoverSubgroupProductCoordinateLeftInCommutatorSubgroup
      (G := G) (V := V) (p := p) A L D P)
    (Hcomm : HomocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
      (G := G) (V := V) (p := p) A L D P) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZero
      (G := G) (V := V) (p := p) A L D P where
  left_sum_zero := by
    intro x
    simpa using
      Hcomm.commutator_orbit_sum_zero
        (P.productCoordinateEquiv.symm
          (x, (0 : P.coordinateSplit.rightIndex → ZMod (p ^ e))))
        (Hleft.left_mem_commutatorSubgroup x)

/-- In a commutative group, the additive orbit sum over `A` of any element in
the action commutator subgroup is zero. -/
public theorem commutatorAction_orbit_additive_sum_eq_zero
    {G A : Type u} [Group G] [IsMulCommutative G] [Group A] [MulDistribMulAction A G]
    [Fintype A] {x : G}
    (hx : x ∈ commutatorAction (A := A) (G := G)) :
    (∑ a : A, Additive.ofMul (a • x) : Additive G) = 0 := by
  classical
  let : CommGroup G := { (inferInstance : Group G) with
    mul_comm := fun x y => (IsMulCommutative.is_comm (M := G)).comm x y }
  rw [commutatorAction_eq_closure (G := G) (A := A)] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => (∑ a : A, Additive.ofMul (a • x) : Additive G) = 0)
    ?mem ?one ?mul ?inv hx
  · intro y hy
    rcases hy with ⟨a0, g, rfl⟩
    calc
      (∑ a : A, Additive.ofMul (a • (g⁻¹ * (a0 • g))) : Additive G)
          = ∑ a : A,
              (-Additive.ofMul (a • g) + Additive.ofMul ((a * a0) • g) : Additive G) := by
            apply Finset.sum_congr rfl
            intro a _ha
            simp [smul_mul', smul_inv', mul_smul]
      _ = -(∑ a : A, Additive.ofMul (a • g) : Additive G) +
            (∑ a : A, Additive.ofMul ((a * a0) • g) : Additive G) := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      _ = 0 := by
            have hperm : Function.Bijective (fun a : A => a * a0) :=
              (Equiv.mulRight a0).bijective
            have hsum : (∑ a : A, Additive.ofMul ((a * a0) • g) : Additive G) =
                ∑ a : A, Additive.ofMul (a • g) := by
              exact Finset.sum_bijective (fun a : A => a * a0) hperm
                (by intro a; simp) (by intro a _ha; rfl)
            rw [hsum]
            simp
  · simp
  · intro y z _hy _hz hys hzs
    calc
      (∑ a : A, Additive.ofMul (a • (y * z)) : Additive G)
          = ∑ a : A,
              (Additive.ofMul (a • y) + Additive.ofMul (a • z) : Additive G) := by
            apply Finset.sum_congr rfl
            intro a _ha
            simp [smul_mul']
      _ = 0 := by
            rw [Finset.sum_add_distrib, hys, hzs]
            simp
  · intro y _hy hys
    calc
      (∑ a : A, Additive.ofMul (a • y⁻¹) : Additive G)
          = ∑ a : A, (-Additive.ofMul (a • y) : Additive G) := by
            apply Finset.sum_congr rfl
            intro a _ha
            simp [smul_inv']
      _ = 0 := by
            rw [Finset.sum_neg_distrib, hys]
            simp

/-- The generic commutator orbit-sum cancellation theorem in product
coordinates. -/
public def homocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D} :
    HomocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
      (G := G) (V := V) (p := p) A L D P where
  commutator_orbit_sum_zero := by
    classical
    let : Group L.cover := L.instGroupCover
    let : IsMulCommutative L.cover := L.cover_commutative
    let : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    let : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
    let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
    let : DecidableEq L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instDecidableEqMatrixIndex
    let : Fintype P.coordinateSplit.leftIndex := P.coordinateSplit.instFintypeLeftIndex
    let : Fintype P.coordinateSplit.rightIndex := P.coordinateSplit.instFintypeRightIndex
    let : DecidableEq P.coordinateSplit.leftIndex :=
      P.coordinateSplit.instDecidableEqLeftIndex
    let : DecidableEq P.coordinateSplit.rightIndex :=
      P.coordinateSplit.instDecidableEqRightIndex
    intro y hy
    let R := ZMod (p ^ e)
    let E := P.coordinateSplit.leftIndex ⊕ P.coordinateSplit.rightIndex → R
    let F := L.matrixIndex → R
    let reindex : E ≃ₗ[R] F :=
      LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv
    let xcover : L.cover := Additive.toMul (L.coordinateEquiv (reindex y))
    have hy' : xcover ∈ commutatorAction (A := A) (G := L.cover) := by
      rw [← D.commutatorSubgroup_eq]
      exact hy
    have hsumCover : (∑ a : A, Additive.ofMul (a • xcover) : Additive L.cover) = 0 :=
      commutatorAction_orbit_additive_sum_eq_zero (G := L.cover) (A := A) hy'
    apply reindex.injective
    change reindex (∑ a : A,
        Matrix.toLin'
          (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
            (L.toCommonMatrixLift.matrixLift (a : G))) y) = reindex 0
    rw [map_sum]
    simp only [map_zero]
    apply L.coordinateEquiv.injective
    calc
      L.coordinateEquiv (∑ a : A,
          reindex
            (Matrix.toLin'
              (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G))) y))
          = ∑ a : A, L.coordinateEquiv
              (reindex
                (Matrix.toLin'
                  (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
                    (L.toCommonMatrixLift.matrixLift (a : G))) y)) := by
            exact map_sum L.coordinateEquiv _ Finset.univ
      _ = ∑ a : A, Additive.ofMul (a • xcover) := by
            apply Finset.sum_congr rfl
            intro a _ha
            have hterm :
                reindex
                  (Matrix.toLin'
                    (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
                      (L.toCommonMatrixLift.matrixLift (a : G))) y) =
                (((L.linearLift (a : G) :
                    (Module.End R (L.matrixIndex → R))ˣ) :
                  Module.End R (L.matrixIndex → R)) (reindex y)) := by
              change
                (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv)
                  (Matrix.toLin'
                    (Matrix.reindex P.coordinateSplit.indexEquiv P.coordinateSplit.indexEquiv
                      (L.toCommonMatrixLift.matrixLift (a : G))) y) =
                (((L.linearLift (a : G) :
                    (Module.End R (L.matrixIndex → R))ˣ) :
                  Module.End R (L.matrixIndex → R))
                  ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y))
              rw [Matrix.toLin'_reindex]
              simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
              simp only [HomocyclicFrattiniCoverLinearLift.toCommonMatrixLift,
                HomocyclicFrattiniCoverLinearLift.toHomocyclicCoverLinearLift,
                HomocyclicCoverLinearLift.toHomocyclicQuotientLinearLift,
                HomocyclicQuotientLinearLift.toHomocyclicCommonLinearLift,
                HomocyclicCommonLinearLift.toCommonMatrixLift]
              let f : (L.matrixIndex → R) →ₗ[R] L.matrixIndex → R :=
                (((L.linearLift (a : G) :
                    (Module.End R (L.matrixIndex → R))ˣ) :
                  Module.End R (L.matrixIndex → R)))
              have htoLin : Matrix.toLin' (LinearMap.toMatrix' f) = f :=
                Matrix.toLin'_toMatrix' f
              change
                (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv)
                  ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv.symm)
                    ((Matrix.toLin' (LinearMap.toMatrix' f))
                      ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y))) =
                  f ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y)
              rw [htoLin]
              exact
                LinearEquiv.apply_symm_apply
                  (LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv)
                  (f ((LinearEquiv.funCongrLeft R R P.coordinateSplit.indexEquiv) y))
            rw [hterm]
            change L.coordinateEquiv
                (((L.linearLift (a : G) :
                    (Module.End R (L.matrixIndex → R))ˣ) :
                  Module.End R (L.matrixIndex → R)) (reindex y)) =
              Additive.ofMul
                (L.coverAction (a : G)
                  (Additive.toMul (L.coordinateEquiv (reindex y))))
            exact L.linearLift_coordinate (a : G) (reindex y)
      _ = 0 := hsumCover
      _ = L.coordinateEquiv 0 := by simp

/-- An ambient left-factor sum cancellation gives the top-left
product-coordinate identity. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZero.toTopLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZero
      (G := G) (V := V) (p := p) A L D P) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZero
      (G := G) (V := V) (p := p) A L D P where
  top_left_sum_zero := by
    intro x
    let R := ZMod (p ^ e)
    let X := P.coordinateSplit.leftIndex → R
    let Y := P.coordinateSplit.rightIndex → R
    let E := P.coordinateSplit.leftIndex ⊕ P.coordinateSplit.rightIndex → R
    have h := H.left_sum_zero x
    have h' :=
      congrArg
        (fun y : E => (LinearMap.fst R X Y) (P.productCoordinateEquiv y))
        h
    simpa [R, X, Y, E] using h'


/-- Product coordinates chosen together with the lower-right action identity.

This is the first source-side package that can safely carry the choice of
coordinates: the lower-right identity is only expected for the adapted product
coordinates, not for every possible product-coordinate equivalence. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  productCoordinates :
    HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D
  bottomRightIdentity :
    HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightIdentity
      (G := G) (V := V) (p := p) A L D productCoordinates


/-- Add the upper-left zero-sum identity to product coordinates already chosen
with their lower-right identity. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZeroData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (B : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  topLeftSumZero :
    HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZero
      (G := G) (V := V) (p := p) A L D B.productCoordinates

/-- Product coordinates with lower-right data and the ambient left-factor
sum-cancellation statement. -/
public structure HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZeroData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (B : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  leftSumZero :
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZero
      (G := G) (V := V) (p := p) A L D B.productCoordinates

/-- Turn ambient left-factor cancellation into top-left zero-sum data for the
same product coordinates. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZeroData.toTopLeftSumZeroData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {B : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D}
    (H : HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZeroData
      (G := G) (V := V) (p := p) A L D B) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZeroData
      (G := G) (V := V) (p := p) A L D B where
  topLeftSumZero := H.leftSumZero.toTopLeftSumZero


public structure HomocyclicFrattiniCoverSubgroupProductCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  productCoordinateEquiv :
    ((coordinateSplit.leftIndex ⊕ coordinateSplit.rightIndex) → ZMod (p ^ e)) ≃ₗ[ZMod (p ^ e)]
      ((coordinateSplit.leftIndex → ZMod (p ^ e)) ×
        (coordinateSplit.rightIndex → ZMod (p ^ e)))
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype coordinateSplit.leftIndex := coordinateSplit.instFintypeLeftIndex
    letI : Fintype coordinateSplit.rightIndex := coordinateSplit.instFintypeRightIndex
    letI : DecidableEq coordinateSplit.leftIndex := coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq coordinateSplit.rightIndex := coordinateSplit.instDecidableEqRightIndex
    ∀ (a : A) (x : coordinateSplit.rightIndex → ZMod (p ^ e)),
      (LinearMap.snd (ZMod (p ^ e))
          (coordinateSplit.leftIndex → ZMod (p ^ e))
          (coordinateSplit.rightIndex → ZMod (p ^ e)))
        (productCoordinateEquiv
          (Matrix.toLin'
            (Matrix.reindex coordinateSplit.indexEquiv coordinateSplit.indexEquiv
              (L.toCommonMatrixLift.matrixLift (a : G)))
            (productCoordinateEquiv.symm
              ((0 : coordinateSplit.leftIndex → ZMod (p ^ e)), x)))) = x
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype coordinateSplit.leftIndex := coordinateSplit.instFintypeLeftIndex
    letI : Fintype coordinateSplit.rightIndex := coordinateSplit.instFintypeRightIndex
    letI : DecidableEq coordinateSplit.leftIndex := coordinateSplit.instDecidableEqLeftIndex
    letI : DecidableEq coordinateSplit.rightIndex := coordinateSplit.instDecidableEqRightIndex
    ∀ x : coordinateSplit.leftIndex → ZMod (p ^ e),
      (∑ a : A,
        (LinearMap.fst (ZMod (p ^ e))
            (coordinateSplit.leftIndex → ZMod (p ^ e))
            (coordinateSplit.rightIndex → ZMod (p ^ e)))
          (productCoordinateEquiv
            (Matrix.toLin'
              (Matrix.reindex coordinateSplit.indexEquiv coordinateSplit.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G)))
              (productCoordinateEquiv.symm
                (x, (0 : coordinateSplit.rightIndex → ZMod (p ^ e))))))) = 0

/-- Assemble product coordinates and their two action identities into the
single product-coordinate data package used by the rectangular adapter. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinates.toProductCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinates
      (G := G) (V := V) (p := p) A L D)
    (H22 : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightIdentity
      (G := G) (V := V) (p := p) A L D P)
    (H11 : HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZero
      (G := G) (V := V) (p := p) A L D P) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateData
      (G := G) (V := V) (p := p) A L D where
  coordinateSplit := P.coordinateSplit
  productCoordinateEquiv := P.productCoordinateEquiv
  bottom_right_identity := H22.bottom_right_identity
  top_left_sum_zero := H11.top_left_sum_zero

/-- Assemble lower-right product-coordinate data and the upper-left zero-sum
identity into the single product-coordinate data package used by the
rectangular adapter. -/
public def
    HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData.toProductCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (B : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D)
    (H11 : HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZeroData
      (G := G) (V := V) (p := p) A L D B) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateData
      (G := G) (V := V) (p := p) A L D :=
  B.productCoordinates.toProductCoordinateData B.bottomRightIdentity H11.topLeftSumZero

/-- Transport source-side product coordinates into the existing rectangular
linear-map package. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupProductCoordinateData.toChosenSplitRectangularLinearMaps
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (P : HomocyclicFrattiniCoverSubgroupProductCoordinateData
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupChosenSplitRectangularLinearMaps
      (G := G) (V := V) (p := p) A L D := by
  classical
  let C := P.coordinateSplit
  let R := ZMod (p ^ e)
  let X := C.leftIndex → R
  let Y := C.rightIndex → R
  let E := C.leftIndex ⊕ C.rightIndex → R
  let productCoordinateEquiv : E ≃ₗ[R] X × Y := P.productCoordinateEquiv
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
  letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
  let leftColumnMap : X →ₗ[R] E :=
    productCoordinateEquiv.symm.toLinearMap.comp (LinearMap.inl R X Y)
  let rightColumnMap : Y →ₗ[R] E :=
    productCoordinateEquiv.symm.toLinearMap.comp (LinearMap.inr R X Y)
  let topRowMap : E →ₗ[R] X :=
    (LinearMap.fst R X Y).comp productCoordinateEquiv.toLinearMap
  let bottomRowMap : E →ₗ[R] Y :=
    (LinearMap.snd R X Y).comp productCoordinateEquiv.toLinearMap
  refine ⟨C, ?_⟩
  exact {
    leftColumnMap := leftColumnMap
    rightColumnMap := rightColumnMap
    topRowMap := topRowMap
    bottomRowMap := bottomRowMap
    inverse_blocks := by
      intro x
      change
        productCoordinateEquiv.symm ((productCoordinateEquiv x).1, 0) +
          productCoordinateEquiv.symm (0, (productCoordinateEquiv x).2) = x
      rw [← productCoordinateEquiv.symm.map_add]
      simp
    bottom_right_identity := by
      intro a x
      simpa [C, R, X, Y, E, productCoordinateEquiv, rightColumnMap, bottomRowMap] using
        P.bottom_right_identity a x
    top_left_sum_zero := by
      intro x
      simpa [C, R, X, Y, E, productCoordinateEquiv, leftColumnMap, topRowMap] using
        P.top_left_sum_zero x }

/-- A coordinate split chosen together with the two canonical block identities.

This is the lower source boundary for the rectangular step after the direct
product decomposition has chosen adapted coordinates: the checked adapters use
canonical block inclusions and projections for the four rectangular maps. -/
public structure HomocyclicFrattiniCoverSubgroupChosenSplitCoordinateBlockIdentities
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  blockIdentities :
    HomocyclicFrattiniCoverSubgroupCoordinateBlockIdentities
      (G := G) (V := V) (p := p) A L D coordinateSplit


/-- Convert adapted canonical block identities into the four rectangular linear
maps. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupChosenSplitCoordinateBlockIdentities.toChosenSplitRectangularLinearMaps
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    (B : HomocyclicFrattiniCoverSubgroupChosenSplitCoordinateBlockIdentities
      (G := G) (V := V) (p := p) A L D) :
    HomocyclicFrattiniCoverSubgroupChosenSplitRectangularLinearMaps
      (G := G) (V := V) (p := p) A L D := by
  classical
  let C := B.coordinateSplit
  let R := ZMod (p ^ e)
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
  letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
  let leftColumnMap :
      (C.leftIndex → R) →ₗ[R] (C.leftIndex ⊕ C.rightIndex → R) :=
    Matrix.toLin'
      (identityBlockLeftColumn (R := R) (l := C.leftIndex) (r := C.rightIndex))
  let rightColumnMap :
      (C.rightIndex → R) →ₗ[R] (C.leftIndex ⊕ C.rightIndex → R) :=
    Matrix.toLin'
      (identityBlockRightColumn (R := R) (l := C.leftIndex) (r := C.rightIndex))
  let topRowMap :
      (C.leftIndex ⊕ C.rightIndex → R) →ₗ[R] (C.leftIndex → R) :=
    Matrix.toLin'
      (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
  let bottomRowMap :
      (C.leftIndex ⊕ C.rightIndex → R) →ₗ[R] (C.rightIndex → R) :=
    Matrix.toLin'
      (identityBlockBottomRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
  refine ⟨C, ?_⟩
  exact {
    leftColumnMap := leftColumnMap
    rightColumnMap := rightColumnMap
    topRowMap := topRowMap
    bottomRowMap := bottomRowMap
    inverse_blocks := by
      intro x
      have hmat :
          matrixOfBlockColumns
              (identityBlockLeftColumn (R := R) (l := C.leftIndex) (r := C.rightIndex))
              (identityBlockRightColumn (R := R) (l := C.leftIndex) (r := C.rightIndex)) *
            matrixOfBlockRows
              (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
              (identityBlockBottomRow (R := R) (l := C.leftIndex) (r := C.rightIndex)) =
              (1 : Matrix (C.leftIndex ⊕ C.rightIndex) (C.leftIndex ⊕ C.rightIndex) R) := by
        rw [matrixOfIdentityBlockColumns_eq_one, matrixOfIdentityBlockRows_eq_one]
        simp
      have hx :=
        congrArg
          (fun M : Matrix (C.leftIndex ⊕ C.rightIndex) (C.leftIndex ⊕ C.rightIndex) R =>
            Matrix.mulVec M x)
          hmat
      rw [matrixOfBlockColumns_mul_matrixOfBlockRows, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hx
      change
        Matrix.mulVec
              (identityBlockLeftColumn
                (R := R) (l := C.leftIndex) (r := C.rightIndex))
              (Matrix.mulVec
                (identityBlockTopRow
                  (R := R) (l := C.leftIndex) (r := C.rightIndex)) x) +
            Matrix.mulVec
              (identityBlockRightColumn
                (R := R) (l := C.leftIndex) (r := C.rightIndex))
              (Matrix.mulVec
                (identityBlockBottomRow
                  (R := R) (l := C.leftIndex) (r := C.rightIndex)) x) = x
      exact hx
    bottom_right_identity := by
      intro a x
      have hmatrix := B.blockIdentities.bottom_right_identity a
      rw [Matrix.ext_iff_mulVec] at hmatrix
      have hx := hmatrix x
      change
        Matrix.toLin'
          (identityBlockBottomRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
              Matrix.reindex C.indexEquiv C.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G)) *
            identityBlockRightColumn (R := R) (l := C.leftIndex) (r := C.rightIndex)) x =
          Matrix.toLin' (1 : Matrix C.rightIndex C.rightIndex R) x at hx
      rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply, Matrix.toLin'_one] at hx
      simpa [rightColumnMap, bottomRowMap] using hx
    top_left_sum_zero := by
      intro x
      have hmatrix := B.blockIdentities.top_left_sum_zero
      rw [Matrix.ext_iff_mulVec] at hmatrix
      have hx := hmatrix x
      calc
        (∑ a : A,
          topRowMap
            (Matrix.toLin'
              (Matrix.reindex C.indexEquiv C.indexEquiv
                (L.toCommonMatrixLift.matrixLift (a : G)))
              (leftColumnMap x))) =
            Matrix.toLin'
              (∑ a : A,
                identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
                    Matrix.reindex C.indexEquiv C.indexEquiv
                      (L.toCommonMatrixLift.matrixLift (a : G)) *
                  identityBlockLeftColumn (R := R) (l := C.leftIndex) (r := C.rightIndex))
              x := by
              conv_rhs => rw [Matrix.toLin'_apply, Matrix.sum_mulVec]
              apply Finset.sum_congr rfl
              intro a _ha
              change
                Matrix.toLin'
                    (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
                    (Matrix.toLin'
                      (Matrix.reindex C.indexEquiv C.indexEquiv
                        (L.toCommonMatrixLift.matrixLift (a : G)))
                      (Matrix.toLin'
                        (identityBlockLeftColumn (R := R) (l := C.leftIndex)
                          (r := C.rightIndex)) x)) =
                  Matrix.toLin'
                    ((identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
                        Matrix.reindex C.indexEquiv C.indexEquiv
                          (L.toCommonMatrixLift.matrixLift (a : G))) *
                      identityBlockLeftColumn (R := R) (l := C.leftIndex)
                        (r := C.rightIndex)) x
              calc
                Matrix.toLin'
                    (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
                    (Matrix.toLin'
                      (Matrix.reindex C.indexEquiv C.indexEquiv
                        (L.toCommonMatrixLift.matrixLift (a : G)))
                      (Matrix.toLin'
                        (identityBlockLeftColumn (R := R) (l := C.leftIndex)
                          (r := C.rightIndex)) x)) =
                    Matrix.toLin'
                      (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
                        Matrix.reindex C.indexEquiv C.indexEquiv
                          (L.toCommonMatrixLift.matrixLift (a : G)))
                      (Matrix.toLin'
                        (identityBlockLeftColumn (R := R) (l := C.leftIndex)
                          (r := C.rightIndex)) x) := by
                    exact
                      (Matrix.toLin'_mul_apply
                        (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex))
                        (Matrix.reindex C.indexEquiv C.indexEquiv
                          (L.toCommonMatrixLift.matrixLift (a : G)))
                        (Matrix.toLin'
                          (identityBlockLeftColumn (R := R) (l := C.leftIndex)
                            (r := C.rightIndex)) x)).symm
                _ =
                    Matrix.toLin'
                      ((identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
                          Matrix.reindex C.indexEquiv C.indexEquiv
                            (L.toCommonMatrixLift.matrixLift (a : G))) *
                        identityBlockLeftColumn (R := R) (l := C.leftIndex)
                          (r := C.rightIndex)) x := by
                    exact
                      (Matrix.toLin'_mul_apply
                        (identityBlockTopRow (R := R) (l := C.leftIndex) (r := C.rightIndex) *
                          Matrix.reindex C.indexEquiv C.indexEquiv
                            (L.toCommonMatrixLift.matrixLift (a : G)))
                        (identityBlockLeftColumn (R := R) (l := C.leftIndex)
                          (r := C.rightIndex)) x).symm
        _ = 0 := by
              rw [Matrix.toLin'_apply]
              simpa using hx }


public structure HomocyclicFrattiniCoverSubgroupChosenSplitRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  coordinateSplit :
    HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D
  rectangularMatrices :
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D coordinateSplit

/-- Convert raw rectangular matrices relative to a coordinate split into the
existing reindexed rectangular trace-data interface. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices.toRectangularReindexedBlockTraceData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L}
    {C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D}
    (M : HomocyclicFrattiniCoverSubgroupCoordinateSplitRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D C) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    RectangularReindexedBlockTraceData
      (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
      A (p ^ e) L.toCommonMatrixLift.matrixLift
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) A) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype C.leftIndex := C.instFintypeLeftIndex
  letI : Fintype C.rightIndex := C.instFintypeRightIndex
  letI : DecidableEq C.leftIndex := C.instDecidableEqLeftIndex
  letI : DecidableEq C.rightIndex := C.instDecidableEqRightIndex
  exact {
    leftIndex := C.leftIndex
    rightIndex := C.rightIndex
    instFintypeLeftIndex := C.instFintypeLeftIndex
    instFintypeRightIndex := C.instFintypeRightIndex
    instDecidableEqLeftIndex := C.instDecidableEqLeftIndex
    instDecidableEqRightIndex := C.instDecidableEqRightIndex
    indexEquiv := C.indexEquiv
    leftColumn := M.leftColumn
    rightColumn := M.rightColumn
    topRow := M.topRow
    bottomRow := M.bottomRow
    card_right := C.card_right
    inverse_blocks := M.inverse_blocks
    bottom_right_identity := M.bottom_right_identity
    top_left_sum_zero := M.top_left_sum_zero }


public structure HomocyclicFrattiniCoverSubgroupRectangularBlockInverseMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  leftColumn :
    Matrix (D.leftIndex ⊕ D.rightIndex) D.leftIndex (ZMod (p ^ e))
  rightColumn :
    Matrix (D.leftIndex ⊕ D.rightIndex) D.rightIndex (ZMod (p ^ e))
  topRow :
    Matrix D.leftIndex (D.leftIndex ⊕ D.rightIndex) (ZMod (p ^ e))
  bottomRow :
    Matrix D.rightIndex (D.leftIndex ⊕ D.rightIndex) (ZMod (p ^ e))
  leftColumn_eq :
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    leftColumn = identityBlockLeftColumn (R := ZMod (p ^ e)) (l := D.leftIndex) (r := D.rightIndex)
  rightColumn_eq :
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    rightColumn = identityBlockRightColumn (R := ZMod (p ^ e)) (l := D.leftIndex) (r := D.rightIndex)
  topRow_eq :
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    topRow = identityBlockTopRow (R := ZMod (p ^ e)) (l := D.leftIndex) (r := D.rightIndex)
  bottomRow_eq :
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    bottomRow = identityBlockBottomRow (R := ZMod (p ^ e)) (l := D.leftIndex) (r := D.rightIndex)
  inverse_blocks :
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    matrixOfBlockColumns leftColumn rightColumn *
      matrixOfBlockRows topRow bottomRow = 1

/-- The lower-right identity for the rectangular block matrices. -/
public structure HomocyclicFrattiniCoverSubgroupRectangularBlockBottomRightIdentity
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L)
    (B : HomocyclicFrattiniCoverSubgroupRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    ∀ a : A,
      B.bottomRow * Matrix.reindex D.indexEquiv D.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * B.rightColumn = 1

/-- The upper-left zero-sum identity for the rectangular block matrices. -/
public structure HomocyclicFrattiniCoverSubgroupRectangularBlockTopLeftSumZero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L)
    (B : HomocyclicFrattiniCoverSubgroupRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D) :
    Type (u + 1) where
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    (∑ a : A,
      B.topRow * Matrix.reindex D.indexEquiv D.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * B.leftColumn) = 0


public structure HomocyclicFrattiniCoverSubgroupRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L) :
    Type (u + 1) where
  leftColumn :
    Matrix (D.leftIndex ⊕ D.rightIndex) D.leftIndex (ZMod (p ^ e))
  rightColumn :
    Matrix (D.leftIndex ⊕ D.rightIndex) D.rightIndex (ZMod (p ^ e))
  topRow :
    Matrix D.leftIndex (D.leftIndex ⊕ D.rightIndex) (ZMod (p ^ e))
  bottomRow :
    Matrix D.rightIndex (D.leftIndex ⊕ D.rightIndex) (ZMod (p ^ e))
  inverse_blocks :
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    matrixOfBlockColumns leftColumn rightColumn *
      matrixOfBlockRows topRow bottomRow = 1
  bottom_right_identity :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    ∀ a : A,
      bottomRow * Matrix.reindex D.indexEquiv D.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * rightColumn = 1
  top_left_sum_zero :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    letI : Fintype D.leftIndex := D.instFintypeLeftIndex
    letI : Fintype D.rightIndex := D.instFintypeRightIndex
    letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
    letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
    (∑ a : A,
      topRow * Matrix.reindex D.indexEquiv D.indexEquiv
          (L.toCommonMatrixLift.matrixLift (a : G)) * leftColumn) = 0

/-- Assemble the inverse block matrices and the two action identities into the
older rectangular block matrix package. -/
public def
    HomocyclicFrattiniCoverSubgroupRectangularBlockInverseMatrices.toRectangularBlockMatrices
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L}
    (B : HomocyclicFrattiniCoverSubgroupRectangularBlockInverseMatrices
      (G := G) (V := V) (p := p) A L D)
    (H22 : HomocyclicFrattiniCoverSubgroupRectangularBlockBottomRightIdentity
      (G := G) (V := V) (p := p) A L D B)
    (H11 : HomocyclicFrattiniCoverSubgroupRectangularBlockTopLeftSumZero
      (G := G) (V := V) (p := p) A L D B) :
    HomocyclicFrattiniCoverSubgroupRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D where
  leftColumn := B.leftColumn
  rightColumn := B.rightColumn
  topRow := B.topRow
  bottomRow := B.bottomRow
  inverse_blocks := B.inverse_blocks
  bottom_right_identity := H22.bottom_right_identity
  top_left_sum_zero := H11.top_left_sum_zero

/-- Convert rectangular matrices built relative to a subgroup decomposition into
the existing reindexed rectangular trace-data interface. -/
public noncomputable def
    HomocyclicFrattiniCoverSubgroupRectangularBlockMatrices.toRectangularReindexedBlockTraceData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    {D : HomocyclicFrattiniCoverSubgroupBlockDecomposition
      (G := G) (V := V) (p := p) A L}
    (M : HomocyclicFrattiniCoverSubgroupRectangularBlockMatrices
      (G := G) (V := V) (p := p) A L D) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    RectangularReindexedBlockTraceData
      (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
      A (p ^ e) L.toCommonMatrixLift.matrixLift
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) A) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  letI : Fintype D.leftIndex := D.instFintypeLeftIndex
  letI : Fintype D.rightIndex := D.instFintypeRightIndex
  letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
  letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
  exact {
    leftIndex := D.leftIndex
    rightIndex := D.rightIndex
    instFintypeLeftIndex := D.instFintypeLeftIndex
    instFintypeRightIndex := D.instFintypeRightIndex
    instDecidableEqLeftIndex := D.instDecidableEqLeftIndex
    instDecidableEqRightIndex := D.instDecidableEqRightIndex
    indexEquiv := D.indexEquiv
    leftColumn := M.leftColumn
    rightColumn := M.rightColumn
    topRow := M.topRow
    bottomRow := M.bottomRow
    card_right := D.card_right
    inverse_blocks := M.inverse_blocks
    bottom_right_identity := M.bottom_right_identity
    top_left_sum_zero := M.top_left_sum_zero }


end CFSG.Wielandt
