module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Field.ULift
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow

namespace CFSG
end CFSG
open CFSG
namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
public theorem hkt_regularSemidirect_range_inl_normal
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    ((SemidirectProduct.inl :
      A →* A ⋊[MulDistribMulAction.toMulAut B A] B).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

public theorem hkt_regularSemidirect_range_inl_inf_range_inr_eq_bot
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B)) ⊓
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  rcases hxA with ⟨a, ha⟩
  rcases hxB with ⟨b, hb⟩
  have hab :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) =
        SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b := by
    exact ha.trans hb.symm
  have ha_one : a = 1 := by
    have hleft := congrArg SemidirectProduct.left hab
    simpa using hleft
  have hx_one : x = 1 := by
    rw [← ha]
    simp [ha_one]
  simp [hx_one]


public theorem hkt_regularSemidirect_range_inl_isComplement_range_inr
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B)).IsComplement'
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    exact (hkt_regularSemidirect_range_inl_inf_range_inr_eq_bot (A := A) (B := B)).le
  · ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      rw [Set.mem_mul]
      refine ⟨SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) x.left,
        ?_, SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) x.right,
        ?_, ?_⟩
      · exact ⟨x.left, rfl⟩
      · exact ⟨x.right, rfl⟩
      · exact SemidirectProduct.inl_left_mul_inr_right x

public theorem hkt_regularSemidirect_range_inl_ne_bot_of_nontrivial
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    [Nontrivial A] :
    MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B) ≠ ⊥ := by
  rcases exists_ne (1 : A) with ⟨a, ha⟩
  intro hbot
  have ha_mem :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) ∈
        (⊥ : Subgroup (A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
    rw [← hbot]
    exact ⟨a, rfl⟩
  have ha_one : a = 1 := by
    have h := Subgroup.mem_bot.mp ha_mem
    have hleft := congrArg SemidirectProduct.left h
    simpa using hleft
  exact ha ha_one

public theorem hkt_regularSemidirect_range_inr_ne_bot_of_nontrivial
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    [Nontrivial B] :
    MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B) ≠ ⊥ := by
  rcases exists_ne (1 : B) with ⟨b, hb⟩
  intro hbot
  have hb_mem :
      (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b :
          A ⋊[MulDistribMulAction.toMulAut B A] B) ∈
        (⊥ : Subgroup (A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
    rw [← hbot]
    exact ⟨b, rfl⟩
  have hb_one : b = 1 := by
    have h := Subgroup.mem_bot.mp hb_mem
    have hright := congrArg SemidirectProduct.right h
    simpa using hright
  exact hb hb_one

public theorem hkt_regularSemidirect_range_inr_elementCentralizerIn_range_inl_eq_bot
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    (hregular : ActsRegularly B A)
    (x :
      MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B))
    (hx : x ≠ 1) :
    elementCentralizerIn
      (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B))
      (x : A ⋊[MulDistribMulAction.toMulAut B A] B) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases x.property with ⟨b, hb⟩
  have hb_ne : b ≠ 1 := by
    intro hb_one
    apply hx
    apply Subtype.ext
    simpa [hb_one] using hb.symm
  rcases hy with ⟨hyA, hycent⟩
  rcases hyA with ⟨a, ha⟩
  have hcomm :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) *
          SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b =
        SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b *
          SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a := by
    have hcomm_yx : (y : A ⋊[MulDistribMulAction.toMulAut B A] B) * (x : _) =
        (x : A ⋊[MulDistribMulAction.toMulAut B A] B) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent
    simpa [ha, hb] using hcomm_yx
  have hfix : b • a = a := by
    have hleft := congrArg SemidirectProduct.left hcomm
    simpa using hleft.symm
  have ha_fixed : a ∈ fixedPointSubgroup (↥(Subgroup.zpowers b)) A := by
    rw [FixedPoints.mem_subgroup]
    intro z
    exact smul_eq_self_of_mem_zpowers z.2 hfix
  have ha_bot : a ∈ (⊥ : Subgroup A) := by
    simpa [hregular b hb_ne] using ha_fixed
  have ha_one : a = 1 := Subgroup.mem_bot.mp ha_bot
  rw [← ha]
  simp [ha_one]

public theorem hkt_regularSemidirect_isFrobenius
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [MulDistribMulAction B A] [Nontrivial A] [Nontrivial B]
    (hregular : ActsRegularly B A) :
    IsFrobeniusGroupWithKernelComplement
      (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B))
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
  let φ : B →* MulAut A := MulDistribMulAction.toMulAut B A
  let SD := A ⋊[φ] B
  let : Finite SD := Finite.of_equiv (A × B) (SemidirectProduct.equivProd (φ := φ)).symm
  let K : Subgroup SD := MonoidHom.range (SemidirectProduct.inl : A →* SD)
  let R : Subgroup SD := MonoidHom.range (SemidirectProduct.inr : B →* SD)
  change IsFrobeniusGroupWithKernelComplement K R
  exact
    (lemma_3_1 (K := K) (R := R)
      (by
        simpa [K, SD, φ] using
          hkt_regularSemidirect_range_inl_ne_bot_of_nontrivial (A := A) (B := B))
      (by
        simpa [R, SD, φ] using
          hkt_regularSemidirect_range_inr_ne_bot_of_nontrivial (A := A) (B := B))
      (by
        simpa [K, SD, φ] using
          hkt_regularSemidirect_range_inl_normal (A := A) (B := B))
      (by
        simpa [K, R, SD, φ] using
          hkt_regularSemidirect_range_inl_isComplement_range_inr (A := A) (B := B))).2
      (by
        intro x hx
        simpa [K, R, SD, φ] using
          hkt_regularSemidirect_range_inr_elementCentralizerIn_range_inl_eq_bot
            (A := A) (B := B) hregular x hx)

/-- The reusable double-counting core inside BG section 3's Lemma 3.3:
if all conjugates of the Frobenius complement have zero subgroup-sum on `v`,
and the total norm is zero on `v`, then the Frobenius kernel sum is the
scalar `|K|` times `v`. -/
public theorem hkt_frobenius_kernel_sum_eq_card_smul_of_norm_and_conj_zero
    {G : Type u} [Group G] [Finite G] {F : Type v} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (v : V)
    (hconj_zero : ∀ x : K, subgroupSum ρ (R.conjBy (x : G)) v = 0)
    (hnorm_zero :
      letI : Fintype G := Fintype.ofFinite G
      ρ.norm v = 0) :
    subgroupSum ρ K v = (Nat.card K : F) • v := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
  let _ : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
  let s : V := ∑ g : {g : G // g ∉ K}, ρ g.1 v
  have hdouble :
      ∑ x : K, ∑ r : {r : R // r ≠ 1},
        ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v = s := by
    rw [← Fintype.sum_prod_type']
    simpa [s] using
      (Fintype.sum_bijective
        (fun xr : K × {r : R // r ≠ 1} =>
          (⟨(xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹, by
            intro hmemK
            have hr_memK : (xr.2.1 : G) ∈ K := by
              have hxconj :=
                hfrob.normal.conj_mem
                  ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹)
                  hmemK (xr.1 : G)⁻¹
              simpa [mul_assoc] using hxconj
            have hr_eq_one : (xr.2.1 : G) = 1 := by
              have hr_bot : (xr.2.1 : G) ∈ (⊥ : Subgroup G) :=
                (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint)
                  hr_memK xr.2.1.property
              simpa using hr_bot
            exact xr.2.2 (Subtype.ext hr_eq_one)⟩ : {g : G // g ∉ K}))
        (frobeniusConjPair_bijective K R hfrob hfrob.kernel_ne_bot hfrob.complement_ne_bot)
        (fun xr => ρ ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹) v)
        (fun g => ρ g.1 v)
        (fun _ => rfl))
  have hconj_expand :
      ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v =
        (Nat.card K : F) • v + s := by
    have hsum_rewrite :
        (fun x : K => subgroupSum ρ (R.conjBy (x : G)) v) =
          fun x : K => v + ∑ r : {r : R // r ≠ 1},
            ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
      funext x
      exact subgroupSum_conjBy_eq_add ρ R (x : G) v
    have hconst : (∑ _ : K, v) = (Nat.card K : F) • v := by
      simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
    calc
      ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v
          = ∑ x : K,
              (v + ∑ r : {r : R // r ≠ 1},
                ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v) := by
                rw [hsum_rewrite]
      _ = (∑ _ : K, v) + ∑ x : K, ∑ r : {r : R // r ≠ 1},
            ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
              simp [Finset.sum_add_distrib]
      _ = (Nat.card K : F) • v + ∑ x : K, ∑ r : {r : R // r ≠ 1},
            ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
              rw [hconst]
      _ = (Nat.card K : F) • v + s := by
            rw [hdouble]
  have hpartition : (Nat.card K : F) • v + s = 0 := by
    rw [← hconj_expand]
    have hsum_zero :
        ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v = ∑ _ : K, (0 : V) := by
      simp [hconj_zero]
    rw [hsum_zero]
    simp
  have hnorm_split : ρ.norm v = subgroupSum ρ K v + s := by
    simpa [s] using norm_eq_subgroupSum_add_sum_not_mem ρ K v
  have hKsum : subgroupSum ρ K v + s = 0 := by
    rw [← hnorm_split, hnorm_zero]
  have hEq : subgroupSum ρ K v + s = (Nat.card K : F) • v + s := by
    rw [hKsum, hpartition]
  exact add_right_cancel hEq

public theorem hkt_mulAut_pow_apply_iterate
    {Q : Type u} [Group Q] (φ : MulAut Q) (n : ℕ) (q : Q) :
    (φ ^ n) q = (fun q : Q => φ q)^[n] q := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      simp [pow_succ, Function.iterate_succ, ih]

public theorem hkt_mulAut_pow_eq_one_of_function_period
    {Q : Type u} [Group Q] (φ : MulAut Q) {p : ℕ}
    (hperiod : (fun q : Q => φ q)^[p] = id) :
    φ ^ p = 1 := by
  ext q
  have hq := congrFun hperiod q
  simpa [hkt_mulAut_pow_apply_iterate φ p q] using hq

/--
Restriction of the HKT automorphism to a subgroup invariant under it.
-/
@[expose]
public def invariantSubgroupAut
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) : MulAut N where
  toFun n := ⟨φ n, (hN n).mp n.2⟩
  invFun n := ⟨φ⁻¹ n, (hN (φ⁻¹ n)).mpr (by simp)⟩
  left_inv n := by
    ext
    simp
  right_inv n := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- Coercion formula for the restricted HKT automorphism. -/
public theorem invariantSubgroupAut_apply_coe
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) (x : N) :
    ((invariantSubgroupAut φ N hN x : N) : Q) = φ (x : Q) := by
  rfl

/-- Iterates of the restricted HKT automorphism agree with ambient iterates. -/
public theorem invariantSubgroupAut_iterate_coe
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    ∀ n (x : N),
      (((fun x : N => invariantSubgroupAut φ N hN x)^[n] x : N) : Q) =
        (fun q : Q => φ q)^[n] (x : Q) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      calc
        (((fun x : N => invariantSubgroupAut φ N hN x)^[n.succ] x : N) : Q)
            = (((fun x : N => invariantSubgroupAut φ N hN x)^[n]
                (invariantSubgroupAut φ N hN x) : N) : Q) := by
              rw [Function.iterate_succ_apply]
        _ = (fun q : Q => φ q)^[n] ((invariantSubgroupAut φ N hN x : N) : Q) :=
              ih (invariantSubgroupAut φ N hN x)
        _ = (fun q : Q => φ q)^[n] (φ (x : Q)) := rfl

/--
The HKT product identity is inherited by every subgroup invariant under the
automorphism.
-/
public theorem hkt_product_identity_of_invariant_subgroup
    {Q : Type u} [Group Q] (φ : MulAut Q) {p : ℕ} (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    ∀ n : N,
      ((List.range p).map
        (fun k ↦ (fun n : N => invariantSubgroupAut φ N hN n)^[k] n)).prod = 1 := by
  intro n
  apply Subtype.ext
  change
    (((List.range p).map
      (fun k ↦ (fun n : N => invariantSubgroupAut φ N hN n)^[k] n)).prod : Q) = 1
  have hcoe :
      ((List.range p).map
        (fun k ↦ (fun n : N => invariantSubgroupAut φ N hN n)^[k] n)).map
          (fun n : N => (n : Q)) =
        (List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] (n : Q)) := by
    rw [List.map_map]
    exact List.map_congr_left fun k _hk => invariantSubgroupAut_iterate_coe φ N hN k n
  calc
    (((List.range p).map
        (fun k ↦ (fun n : N => invariantSubgroupAut φ N hN n)^[k] n)).prod : Q)
        = (((List.range p).map
            (fun k ↦ (fun n : N => invariantSubgroupAut φ N hN n)^[k] n)).map
              (fun n : N => (n : Q))).prod := by
          rw [SubmonoidClass.coe_list_prod]
    _ = ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] (n : Q))).prod := by
          rw [hcoe]
    _ = 1 := hprod (n : Q)

/-- A subgroup invariant under the HKT automorphism is mapped onto itself. -/
public theorem hkt_invariant_subgroup_map_eq
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    N.map (φ : Q →* Q) = N := by
  apply le_antisymm
  · intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨x, hx, rfl⟩
    exact (hN x).mp hx
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨φ⁻¹ q, ?_, by simp⟩
    exact (hN (φ⁻¹ q)).mpr (by simpa using hq)

/-- Induced HKT automorphism on the quotient by an invariant normal subgroup. -/
@[expose]
public def invariantQuotientAut
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) : MulAut (Q ⧸ N) :=
  QuotientGroup.congr (G' := N) (H' := N) (e := φ)
    (hkt_invariant_subgroup_map_eq φ N hN)

/-- Representative formula for the induced HKT quotient automorphism. -/
public theorem invariantQuotientAut_mk'
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) (q : Q) :
    invariantQuotientAut φ N hN (QuotientGroup.mk' N q) =
      QuotientGroup.mk' N (φ q) := by
  rfl

/-- Iterates of the induced HKT quotient automorphism on representatives. -/
public theorem invariantQuotientAut_iterate_mk'
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    ∀ n q,
      (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[n]
          (QuotientGroup.mk' N q) =
        QuotientGroup.mk' N ((fun q : Q => φ q)^[n] q) := by
  intro n
  induction n with
  | zero => intro q; simp
  | succ n ih =>
      intro q
      calc
        (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[n.succ]
            (QuotientGroup.mk' N q)
            = (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[n]
                (invariantQuotientAut φ N hN (QuotientGroup.mk' N q)) := by
              rw [Function.iterate_succ_apply]
        _ = (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[n]
                (QuotientGroup.mk' N (φ q)) := by
              rw [invariantQuotientAut_mk']
        _ = QuotientGroup.mk' N ((fun q : Q => φ q)^[n] (φ q)) := ih (φ q)

/--
The HKT product identity descends to the quotient by an invariant normal
subgroup.
-/
public theorem hkt_product_identity_of_invariant_quotient
    {Q : Type u} [Group Q] (φ : MulAut Q) {p : ℕ} (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    ∀ x : Q ⧸ N,
      ((List.range p).map
        (fun k ↦ (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[k] x)).prod = 1 := by
  intro x
  rcases QuotientGroup.mk'_surjective N x with ⟨q, rfl⟩
  have hlist :
      (List.range p).map
          (fun k ↦ (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[k]
            (QuotientGroup.mk' N q)) =
        (List.range p).map
          (fun k ↦ QuotientGroup.mk' N ((fun q : Q => φ q)^[k] q)) := by
    exact List.map_congr_left fun k _hk => invariantQuotientAut_iterate_mk' φ N hN k q
  calc
    ((List.range p).map
        (fun k ↦ (fun x : Q ⧸ N => invariantQuotientAut φ N hN x)^[k]
          (QuotientGroup.mk' N q))).prod
        = ((List.range p).map
          (fun k ↦ QuotientGroup.mk' N ((fun q : Q => φ q)^[k] q))).prod := by
          rw [hlist]
    _ = QuotientGroup.mk' N
          (((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod) := by
          change (List.map
              ((QuotientGroup.mk' N) ∘ (fun k ↦ (fun q : Q => φ q)^[k] q))
              (List.range p)).prod =
            QuotientGroup.mk' N
              (((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod)
          rw [← List.map_map]
          exact (map_list_prod (QuotientGroup.mk' N)
            ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q))).symm
    _ = 1 := by
          rw [hprod q]
          simp

/-- A characteristic subgroup is invariant under the HKT automorphism. -/
public theorem hkt_characteristic_subgroup_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Characteristic] :
    ∀ q : Q, q ∈ N ↔ φ q ∈ N := by
  intro q
  have hmap : N.map (φ : Q →* Q) = N :=
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : N.Characteristic) φ
  constructor
  · intro hq
    have : φ q ∈ N.map (φ : Q →* Q) :=
      Subgroup.mem_map_of_mem (φ : Q →* Q) hq
    simpa [hmap] using this
  · intro hq
    have hmap' : N.map (φ.symm : Q →* Q) = N :=
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : N.Characteristic) φ.symm
    have : φ.symm (φ q) ∈ N.map (φ.symm : Q →* Q) :=
      Subgroup.mem_map_of_mem (φ.symm : Q →* Q) hq
    simpa [hmap'] using this

/-- The center is invariant under the HKT automorphism. -/
public theorem hkt_center_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) :
    ∀ q : Q, q ∈ Subgroup.center Q ↔ φ q ∈ Subgroup.center Q := by
  simpa using
    (hkt_characteristic_subgroup_invariant (Q := Q) φ (Subgroup.center Q))

/-- A nonnilpotent group cannot have full center. -/
public theorem hkt_center_ne_top_of_not_nilpotent
    {Q : Type u} [Group Q] (hnon_nil : ¬ Group.IsNilpotent Q) :
    Subgroup.center Q ≠ ⊤ := by
  intro htop
  exact hnon_nil (by
    let : CommGroup Q := Group.commGroupOfCenterEqTop htop
    infer_instance)

/--
The center-trivial branch of the HKT minimal-counterexample argument: if every
nontrivial center quotient is already nilpotent, then a nonnilpotent
counterexample has trivial center.
-/
public theorem hkt_center_eq_bot_of_minimal_branch
    {Q : Type u} [Group Q]
    (hnon_nil : ¬ Group.IsNilpotent Q)
    (hquot_nil_of_center_ne_bot : Subgroup.center Q ≠ ⊥ →
      Group.IsNilpotent (Q ⧸ Subgroup.center Q)) :
    Subgroup.center Q = ⊥ := by
  by_contra hne
  exact hnon_nil (Group.of_quotient_center_nilpotent (hquot_nil_of_center_ne_bot hne))

/-- A nonnilpotent group is nontrivial. -/
public theorem hkt_nontrivial_of_not_nilpotent
    {Q : Type u} [Group Q] (hnon_nil : ¬ Group.IsNilpotent Q) :
    Nontrivial Q := by
  by_contra hnt
  have : Subsingleton Q := not_nontrivial_iff_subsingleton.mp hnt
  exact hnon_nil inferInstance

/--
Convert invariance under the cyclic action generated by `φ` into the
membership-style `φ`-invariance used throughout the HKT helpers.
-/
public theorem hkt_zpowers_invariant_generator
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    [IsInvariant (Subgroup.zpowers φ) Q N] :
    ∀ q : Q, q ∈ N ↔ φ q ∈ N := by
  intro q
  have h :=
    IsInvariant.invariant (A := Subgroup.zpowers φ) (G := Q) (H := N)
      ⟨φ, Subgroup.mem_zpowers φ⟩ q
  simpa [MulAut.smul_def] using h

/--
If the generator `φ` preserves a subgroup, then the whole cyclic action
generated by `φ` preserves it.
-/
public theorem hkt_zpowers_invariant_of_generator
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    IsInvariant (Subgroup.zpowers φ) Q N := by
  let Stab : Subgroup (MulAut Q) := {
    carrier := {ψ | ∀ q : Q, q ∈ N ↔ ψ q ∈ N}
    one_mem' := by
      intro q
      simp
    mul_mem' := by
      intro ψ χ hψ hχ q
      exact (hχ q).trans (hψ (χ q))
    inv_mem' := by
      intro ψ hψ q
      have h := hψ (ψ⁻¹ q)
      constructor
      · intro hq
        exact h.mpr (by simpa using hq)
      · intro hq
        simpa using h.mp hq
  }
  have hle : Subgroup.zpowers φ ≤ Stab := (Subgroup.zpowers_le).2 hN
  refine ⟨?_⟩
  intro a q
  change q ∈ N ↔ (a : MulAut Q) q ∈ N
  exact hle a.2 q

/-- Choose a minimal nontrivial normal subgroup invariant under the cyclic HKT action. -/
public theorem hkt_exists_minimal_invariant_normal
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hnon_nil : ¬ Group.IsNilpotent Q) :
    ∃ M : Subgroup Q,
      M.Normal ∧ IsInvariant (Subgroup.zpowers φ) Q M ∧ M ≠ ⊥ ∧
        (∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
          K ≠ ⊥ → K ≤ M → K = M) := by
  let : Nontrivial Q := hkt_nontrivial_of_not_nilpotent hnon_nil
  exact exists_minimal_normal_isInvariant (G := Q) (A := Subgroup.zpowers φ)

/--
Choose a maximal proper normal subgroup invariant under the cyclic HKT action.
This is the source-faithful subgroup for Huppert V.8.13 step 3(a), where the
upper quotient is the chief-factor layer.
-/
public theorem hkt_exists_maximal_proper_invariant_normal
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hnon_nil : ¬ Group.IsNilpotent Q) :
    ∃ N : Subgroup Q,
      N.Normal ∧ IsInvariant (Subgroup.zpowers φ) Q N ∧ N ≠ ⊤ ∧
        (∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
          N ≤ K → K ≠ ⊤ → K = N) := by
  classical
  let : Nontrivial Q := hkt_nontrivial_of_not_nilpotent hnon_nil
  let A : Subgroup (MulAut Q) := Subgroup.zpowers φ
  let S : Set (Subgroup Q) :=
    {N | N.Normal ∧ IsInvariant A Q N ∧ N ≠ ⊤}
  have hS_finite : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊥, ?_, ?_, ?_⟩
    · infer_instance
    · refine ⟨?_⟩
      intro a q
      constructor
      · intro hq
        rw [Subgroup.mem_bot.mp hq]
        simp
      · intro hq
        rw [Subgroup.mem_bot]
        calc
          q = (a : MulAut Q).symm ((a : MulAut Q) q) := by
            simp
          _ = (a : MulAut Q).symm (a • q) := by
            rfl
          _ = 1 := by
            rw [hq]
            exact map_one (a : MulAut Q).symm
    · exact bot_ne_top
  rcases hS_finite.exists_maximal hS_nonempty with ⟨N, hN, hNmax⟩
  refine ⟨N, hN.1, hN.2.1, hN.2.2, ?_⟩
  intro K hKnorm hKinv hNK hKtop
  have hKS : K ∈ S := ⟨hKnorm, hKinv, hKtop⟩
  have hKN : K ≤ N := hNmax hKS hNK
  exact le_antisymm hKN hNK

/--
The quotient by a maximal proper invariant normal subgroup has no nontrivial
proper normal subgroup that is still invariant under the induced HKT action.
This is the formal chief-layer bridge for Huppert V.8.13 step (3a).
-/
public theorem hkt_quotient_no_proper_nontrivial_invariant_normal
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hNmax :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        N ≤ K → K ≠ ⊤ → K = N) :
    ∀ L : Subgroup (Q ⧸ N), L.Normal →
      IsInvariant (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) (Q ⧸ N) L →
      L ≠ ⊥ → L = ⊤ := by
  intro L hLnormal hLinv hL_ne_bot
  by_cases hLtop : L = ⊤
  · exact hLtop
  · let π : Q →* Q ⧸ N := QuotientGroup.mk' N
    let K : Subgroup Q := L.comap π
    have hKnormal : K.Normal := hLnormal.comap π
    have hLφbar : ∀ x : Q ⧸ N,
        x ∈ L ↔ invariantQuotientAut φ N hNφ x ∈ L := by
      have : IsInvariant (Subgroup.zpowers (invariantQuotientAut φ N hNφ))
          (Q ⧸ N) L := hLinv
      exact hkt_zpowers_invariant_generator (invariantQuotientAut φ N hNφ) L
    have hKφ : ∀ q : Q, q ∈ K ↔ φ q ∈ K := by
      intro q
      change QuotientGroup.mk' N q ∈ L ↔ QuotientGroup.mk' N (φ q) ∈ L
      simpa only [invariantQuotientAut_mk'] using
        hLφbar (QuotientGroup.mk' N q)
    have hKinv : IsInvariant (Subgroup.zpowers φ) Q K :=
      hkt_zpowers_invariant_of_generator φ K hKφ
    have hN_le_K : N ≤ K := by
      intro x hx
      change π x ∈ L
      have hx1 : π x = 1 := by
        simpa [π] using (QuotientGroup.eq_one_iff (N := N) x).2 hx
      simp [hx1]
    have hmapK : K.map π = L := by
      simpa [K, π] using
        (Subgroup.map_comap_eq_self_of_surjective (f := π)
          (h := QuotientGroup.mk'_surjective N) L)
    have hK_ne_top : K ≠ ⊤ := by
      intro hKtop
      apply hLtop
      calc
        L = K.map π := hmapK.symm
        _ = (⊤ : Subgroup Q).map π := by rw [hKtop]
        _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)
    have hK_eq_N : K = N := hNmax K hKnormal hKinv hN_le_K hK_ne_top
    have hNmap_bot : N.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      rw [QuotientGroup.ker_mk']
    have hLbot : L = ⊥ := by
      calc
        L = K.map π := hmapK.symm
        _ = N.map π := by rw [hK_eq_N]
        _ = ⊥ := hNmap_bot
    exact False.elim (hL_ne_bot hLbot)

/-- The commutator subgroup is nontrivial in a nonnilpotent group. -/
public theorem hkt_commutator_ne_bot_of_not_nilpotent
    {Q : Type u} [Group Q] (hnon_nil : ¬ Group.IsNilpotent Q) :
    commutator Q ≠ ⊥ := by
  intro hcomm_bot
  have hcenter_top : Subgroup.center Q = ⊤ :=
    (commutator_eq_bot_iff_center_eq_top (G := Q)).1 hcomm_bot
  exact hnon_nil (by
    let : CommGroup Q := Group.commGroupOfCenterEqTop hcenter_top
    infer_instance)

/-- In a solvable nonnilpotent group, the commutator subgroup is proper. -/
public theorem hkt_commutator_ne_top_of_solvable_not_nilpotent
    {Q : Type u} [Group Q] (hnon_nil : ¬ Group.IsNilpotent Q)
    (hsolv : Group.IsSolvable Q) :
    commutator Q ≠ ⊤ := by
  let : Group.IsSolvable Q := hsolv
  let : Nontrivial Q := hkt_nontrivial_of_not_nilpotent hnon_nil
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne

/--
In the solvable branch, a minimal invariant normal subgroup is proper.  If it
were all of `Q`, the commutator subgroup would be a smaller nontrivial normal
subgroup invariant under the cyclic automorphism action.
-/
public theorem hkt_minimal_invariant_normal_ne_top_of_solvable_branch
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hnon_nil : ¬ Group.IsNilpotent Q) (hsolv : Group.IsSolvable Q)
    (M : Subgroup Q) [M.Normal]
    (hMmin :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        K ≠ ⊥ → K ≤ M → K = M) :
    M ≠ ⊤ := by
  intro hMtop
  let D : Subgroup Q := commutator Q
  have hD_ne_bot : D ≠ ⊥ := by
    simp [D, hkt_commutator_ne_bot_of_not_nilpotent (Q := Q) hnon_nil]
  have hD_ne_top : D ≠ ⊤ := by
    simpa [D] using
      hkt_commutator_ne_top_of_solvable_not_nilpotent (Q := Q) hnon_nil hsolv
  have hD_normal : D.Normal := by infer_instance
  have hD_invariant : IsInvariant (Subgroup.zpowers φ) Q D :=
    isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := Q) D
  have hD_eq_M : D = M :=
    hMmin D hD_normal hD_invariant hD_ne_bot (by
      rw [hMtop]
      exact le_top)
  exact hD_ne_top (hD_eq_M.trans hMtop)

/--
In the HKT solvable branch, a nilpotent subgroup that is minimal among
nontrivial normal subgroups invariant under the cyclic automorphism action is a
`p`-group for some prime `p`.  This is the invariant-minimal analogue of the
usual Sylow step for a solvable minimal normal subgroup.
-/
public theorem hkt_minimal_invariant_nilpotent_exists_isPGroup
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (M : Subgroup Q) [M.Normal]
    (hMinv : IsInvariant (Subgroup.zpowers φ) Q M)
    (hM_ne_bot : M ≠ ⊥)
    (hMmin :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        K ≠ ⊥ → K ≤ M → K = M)
    (hM_nil : Group.IsNilpotent M) :
    ∃ r : ℕ, Nat.Prime r ∧ IsPGroup r M := by
  classical
  have hcard_ne_one : Nat.card M ≠ 1 := by
    have : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot (H := M)).2 hM_ne_bot
    exact ne_of_gt this
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card M) hcard_ne_one
  let : Fact r.Prime := ⟨hr_prime⟩
  let P : Sylow r M := default
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) (p := r) P hr_dvd
  have hP_normal_M : (P : Subgroup M).Normal :=
    Group.IsNilpotent.sylow_normal (G := M) hM_nil r P
  have hP_char : (P : Subgroup M).Characteristic :=
    Sylow.characteristic_of_normal (G := M) (p := r) P hP_normal_M
  let Pamb : Subgroup Q := (P : Subgroup M).map M.subtype
  have hPamb_normal : Pamb.Normal := by
    have : (P : Subgroup M).Characteristic := hP_char
    simpa [Pamb] using (inferInstance : Pamb.Normal)
  have hPamb_invariant : IsInvariant (Subgroup.zpowers φ) Q Pamb := by
    have : IsInvariant (Subgroup.zpowers φ) Q M := hMinv
    have : (P : Subgroup M).Characteristic := hP_char
    have hP_invariant_M : IsInvariant (Subgroup.zpowers φ) M (P : Subgroup M) := by
      simpa using
        isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := M) (P : Subgroup M)
    have : IsInvariant (Subgroup.zpowers φ) M (P : Subgroup M) := hP_invariant_M
    simpa [Pamb] using
      isInvariant_map_subtype (A := Subgroup.zpowers φ) (G := Q) M (P : Subgroup M)
  have hPamb_ne_bot : Pamb ≠ ⊥ := by
    intro hbot
    exact hP_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup M)) (f := M.subtype)
        M.subtype_injective).1 (by simpa [Pamb] using hbot))
  have hPamb_le_M : Pamb ≤ M := by
    simpa [Pamb] using Subgroup.map_subtype_le (H := M) (K := (P : Subgroup M))
  have hPamb_eq_M : Pamb = M :=
    hMmin Pamb hPamb_normal hPamb_invariant hPamb_ne_bot hPamb_le_M
  have hPamb_p : IsPGroup r Pamb := by
    simpa [Pamb] using P.isPGroup'.map M.subtype
  refine ⟨r, hr_prime, ?_⟩
  simpa using (hPamb_eq_M ▸ hPamb_p)

/-- A helper instance: a normal subgroup is characteristic enough for mapping characteristic
subgroups of it into the ambient group as normal subgroups. -/
public theorem hkt_map_characteristic_of_normal_normal
    {Q : Type u} [Group Q] (M : Subgroup Q) [M.Normal]
    (K : Subgroup M) [K.Characteristic] :
    ((K.map M.subtype : Subgroup Q).Normal) := by
  infer_instance

/--
For the invariant-minimal nilpotent subgroup in the HKT solvable branch, the
Frattini subgroup is trivial.  Otherwise its image in the ambient group is a
smaller nontrivial invariant normal subgroup.
-/
public theorem hkt_minimal_invariant_nilpotent_frattini_eq_bot
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (M : Subgroup Q) [M.Normal]
    (hMinv : IsInvariant (Subgroup.zpowers φ) Q M)
    (hM_ne_bot : M ≠ ⊥)
    (hMmin :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        K ≠ ⊥ → K ≤ M → K = M) :
    frattini M = ⊥ := by
  classical
  let Φ : Subgroup M := frattini M
  have hΦ_char : Φ.Characteristic := by
    simpa [Φ] using (frattini_characteristic (G := M))
  let Φamb : Subgroup Q := Φ.map M.subtype
  by_contra hΦ_ne_bot
  have hΦamb_ne_bot : Φamb ≠ ⊥ := by
    intro hbot
    exact hΦ_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective (H := Φ) (f := M.subtype)
        M.subtype_injective).1 (by simpa [Φamb] using hbot))
  have hΦamb_normal : Φamb.Normal := by
    have : Φ.Characteristic := hΦ_char
    simpa [Φamb] using
      (hkt_map_characteristic_of_normal_normal (Q := Q) M Φ)
  have hΦamb_invariant : IsInvariant (Subgroup.zpowers φ) Q Φamb := by
    have : IsInvariant (Subgroup.zpowers φ) Q M := hMinv
    have hΦ_invariant_M : IsInvariant (Subgroup.zpowers φ) M Φ := by
      have : Φ.Characteristic := hΦ_char
      simpa [Φ] using isInvariant_of_characteristic (A := Subgroup.zpowers φ) (G := M) Φ
    have : IsInvariant (Subgroup.zpowers φ) M Φ := hΦ_invariant_M
    simpa [Φamb] using isInvariant_map_subtype (A := Subgroup.zpowers φ) (G := Q) M Φ
  have hΦamb_le_M : Φamb ≤ M := by
    simpa [Φamb] using Subgroup.map_subtype_le (H := M) (K := Φ)
  have hΦamb_eq_M : Φamb = M :=
    hMmin Φamb hΦamb_normal hΦamb_invariant hΦamb_ne_bot hΦamb_le_M
  have hΦ_top : Φ = ⊤ := by
    have hinj : Function.Injective (Subgroup.map M.subtype) :=
      Subgroup.map_injective (f := M.subtype) M.subtype_injective
    have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    apply hinj
    simpa [Φamb, htop_map] using hΦamb_eq_M
  have hΦ_ne_top : frattini M ≠ ⊤ := by
    have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
    intro htop
    have hbot_top : (⊥ : Subgroup M) = ⊤ := by
      exact frattini_nongenerating (G := M) (K := ⊥) (by simp [htop])
    exact (bot_ne_top : (⊥ : Subgroup M) ≠ ⊤) hbot_top
  exact hΦ_ne_top (by simpa [Φ] using hΦ_top)

/--
The elementary-abelian layer supplied by the invariant-minimal nilpotent
subgroup in Huppert V.8.13 step 3.
-/
public theorem hkt_minimal_invariant_nilpotent_exists_isElementaryAbelian
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (M : Subgroup Q) [M.Normal]
    (hMinv : IsInvariant (Subgroup.zpowers φ) Q M)
    (hM_ne_bot : M ≠ ⊥)
    (hMmin :
      ∀ K : Subgroup Q, K.Normal → IsInvariant (Subgroup.zpowers φ) Q K →
        K ≠ ⊥ → K ≤ M → K = M)
    (hM_nil : Group.IsNilpotent M) :
    ∃ r : ℕ, Nat.Prime r ∧ IsElementaryAbelian r M := by
  obtain ⟨r, hr_prime, hM_p⟩ :=
    hkt_minimal_invariant_nilpotent_exists_isPGroup φ M hMinv hM_ne_bot hMmin hM_nil
  let : Fact r.Prime := ⟨hr_prime⟩
  let : Fact (IsPGroup r M) := ⟨hM_p⟩
  have hΦ_bot : frattini M = ⊥ :=
    hkt_minimal_invariant_nilpotent_frattini_eq_bot φ M hMinv hM_ne_bot hMmin
  exact ⟨r, hr_prime, (frattini_eq_bot_iff_isElementaryAbelian (R := M) (p := r)).1 hΦ_bot⟩

/-- Transfer elementary-abelian structure from the top subgroup back to the
ambient group. -/
public theorem hkt_isElementaryAbelian_of_top
    {G : Type u} [Group G] {r : ℕ}
    (h : IsElementaryAbelian r (⊤ : Subgroup G)) :
    IsElementaryAbelian r G := by
  let : IsElementaryAbelian r (⊤ : Subgroup G) := h
  refine
    { toIsMulCommutative := ?_
      exponent_dvd_p := ?_ }
  · exact
      { is_comm := ⟨fun x y =>
          congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := (⊤ : Subgroup G))).comm
              (⟨x, by simp⟩ : (⊤ : Subgroup G))
              (⟨y, by simp⟩ : (⊤ : Subgroup G)))⟩ }
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    have hxpow : (⟨x, by simp⟩ : (⊤ : Subgroup G)) ^ r = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p r (⊤ : Subgroup G))
        (⟨x, by simp⟩ : (⊤ : Subgroup G))
    exact congrArg Subtype.val hxpow

/-- A nontrivial cyclic elementary-abelian group has order equal to its prime. -/
public theorem hkt_natCard_eq_prime_of_cyclic_elementaryAbelian
    {r : ℕ} [Fact r.Prime] {G : Type u} [Group G] [Finite G]
    [Nontrivial G] [IsElementaryAbelian r G] (hcyc : IsCyclic G) :
    Nat.card G = r := by
  have hcard_dvd : Nat.card G ∣ r := by
    rw [← hcyc.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p r G
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime r)).1 hcard_dvd with hcard_one | hcard_r
  · exact False.elim <|
      (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial G)).ne' hcard_one
  · exact hcard_r

/-- In an elementary-abelian `r`-group, every prime divisor of the group order
is `r`. -/
public theorem hkt_prime_divisor_eq_of_isElementaryAbelian_card
    {r s : ℕ} [Fact r.Prime] {G : Type u} [Group G] [Finite G]
    [IsElementaryAbelian r G] (hs : Nat.Prime s) (hs_dvd : s ∣ Nat.card G) :
    s = r := by
  have hG_p : IsPGroup r G := IsElementaryAbelian.isPGroup r G
  obtain ⟨n, hcard⟩ := hG_p.exists_card_eq
  exact Nat.prime_eq_prime_of_dvd_pow hs (Fact.out : Nat.Prime r) (hcard ▸ hs_dvd)

/-- If a nontrivial finite group has order `p ^ n`, then the exponent `n` is
nonzero. -/
public theorem hkt_card_power_exponent_ne_zero_of_nontrivial
    {p n : ℕ} {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (hcard : Nat.card G = p ^ n) :
    n ≠ 0 := by
  intro hn0
  have hcard_one : Nat.card G = 1 := by
    simpa [hn0] using hcard
  exact (Finite.one_lt_card (α := G)).ne' hcard_one

/-- Arithmetic facts for the elementary-abelian quotient in Huppert V.8.13
step (3a).  Keeping these facts named prevents the solvable-branch core from
hiding elementary cardinal arithmetic inside the remaining source theorem. -/
public theorem elementaryAbelian_natCard_primePower_facts
    {r : ℕ} [Fact r.Prime] {G : Type u} [Group G] [Finite G]
    [Nontrivial G] [IsElementaryAbelian r G] :
    ∃ n : ℕ,
      Nat.card G = r ^ n ∧ n ≠ 0 ∧
        (∀ s : ℕ, Nat.Prime s → s ∣ Nat.card G → s = r) ∧
          (IsCyclic G → Nat.card G = r) := by
  have hG_p : IsPGroup r G := IsElementaryAbelian.isPGroup r G
  obtain ⟨n, hcard⟩ := hG_p.exists_card_eq
  refine ⟨n, hcard, ?_, ?_, ?_⟩
  · exact hkt_card_power_exponent_ne_zero_of_nontrivial hcard
  · intro s hs_prime hs_dvd
    exact hkt_prime_divisor_eq_of_isElementaryAbelian_card hs_prime hs_dvd
  · intro hcyc
    exact hkt_natCard_eq_prime_of_cyclic_elementaryAbelian hcyc


/--
Fixed points of an automorphism satisfying the HKT product identity are trivial
on an elementary-abelian group whose characteristic is different from the
period prime.  This is the local calculation used in Huppert V.8.13 step
(3b): a fixed point contributes `x ^ p` to the product, while elementary
abelian exponent gives `x ^ r`, and the two prime orders are coprime.
-/
public theorem hkt_fixed_eq_one_of_distinct_elementary_prime_product
    {G : Type u} [Group G] [Finite G] {r p : ℕ}
    [Fact r.Prime] [Fact p.Prime] [IsElementaryAbelian r G]
    (ψ : MulAut G) (hrp : r ≠ p)
    (hprod :
      ∀ x : G,
        ((List.range p).map (fun k ↦ (fun x : G => ψ x)^[k] x)).prod = 1)
    {x : G} (hx : ψ x = x) :
    x = 1 := by
  have hxp : x ^ p = 1 := by
    simpa [Function.iterate_fixed hx, List.prod_replicate] using hprod x
  have hxr : x ^ r = 1 := by
    simpa using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p r G) x)
  have horder_p : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have horder_r : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hxr
  have hcop : Nat.Coprime p r :=
    (Nat.coprime_primes (Fact.out : Nat.Prime p) (Fact.out : Nat.Prime r)).2 (by
      intro hpr
      exact hrp hpr.symm)
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder_p horder_r
  exact orderOf_eq_one_iff.mp horder_one


/-- Subgroup form of the same calculation: for a distinct elementary prime,
the fixed-point subgroup of the cyclic group generated by the induced
automorphism is trivial. -/
public theorem hkt_fixedPointSubgroup_zpowers_eq_bot_of_distinct_elementary_prime_product
    {G : Type u} [Group G] [Finite G] {r p : ℕ}
    [Fact r.Prime] [Fact p.Prime] [IsElementaryAbelian r G]
    (ψ : MulAut G) (hrp : r ≠ p)
    (hprod :
      ∀ x : G,
        ((List.range p).map (fun k ↦ (fun x : G => ψ x)^[k] x)).prod = 1) :
    fixedPointSubgroup (↥(Subgroup.zpowers ψ)) G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxfix : ∀ τ : Subgroup.zpowers ψ, τ • x = x := by
    simpa [fixedPointSubgroup, FixedPoints.mem_subgroup] using hx
  have hxψ : ψ x = x := by
    simpa using hxfix ⟨ψ, Subgroup.mem_zpowers ψ⟩
  exact hkt_fixed_eq_one_of_distinct_elementary_prime_product ψ hrp hprod hxψ

/-- Quotient fixed-point subgroup form of the distinct-prime HKT product
calculation. -/
public theorem hkt_invariant_quotient_fixedPointSubgroup_eq_bot_of_distinct_elementary_prime
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [IsElementaryAbelian r (Q ⧸ N)]
    (hrp : r ≠ p)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    fixedPointSubgroup (↥(Subgroup.zpowers (invariantQuotientAut φ N hNφ)))
        (Q ⧸ N) = ⊥ := by
  exact hkt_fixedPointSubgroup_zpowers_eq_bot_of_distinct_elementary_prime_product
    (ψ := invariantQuotientAut φ N hNφ) hrp
    (hkt_product_identity_of_invariant_quotient φ N hNφ hprod)

/-- The induced quotient automorphism has period dividing the ambient HKT
period. -/
public theorem hkt_invariant_quotient_orderOf_dvd_prime_period
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p : ℕ}
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    (hperiod : (fun q : Q => φ q)^[p] = id) :
    orderOf (invariantQuotientAut φ N hNφ) ∣ p := by
  let ψ : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  have hψp : ψ ^ p = 1 := by
    ext x
    rcases QuotientGroup.mk'_surjective N x with ⟨q, rfl⟩
    calc
      (ψ ^ p) (QuotientGroup.mk' N q)
          = (fun x : Q ⧸ N => ψ x)^[p] (QuotientGroup.mk' N q) := by
              exact hkt_mulAut_pow_apply_iterate ψ p (QuotientGroup.mk' N q)
      _ = QuotientGroup.mk' N ((fun q : Q => φ q)^[p] q) := by
              exact invariantQuotientAut_iterate_mk' φ N hNφ p q
      _ = QuotientGroup.mk' N q := by
              simpa using congrArg (QuotientGroup.mk' N) (congrFun hperiod q)
      _ = (1 : MulAut (Q ⧸ N)) (QuotientGroup.mk' N q) := by
              rfl
  exact orderOf_dvd_of_pow_eq_one hψp

/-- If the quotient elementary prime is different from the HKT period prime,
then the induced quotient automorphism has exact order `p`. -/

public theorem hkt_invariant_quotient_orderOf_eq_prime_of_distinct_elementary_prime
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hrp : r ≠ p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    orderOf (invariantQuotientAut φ N hNφ) = p := by
  let ψ : MulAut (Q ⧸ N) := invariantQuotientAut φ N hNφ
  have hψ_dvd_p : orderOf ψ ∣ p :=
    hkt_invariant_quotient_orderOf_dvd_prime_period φ N hNφ hperiod
  have hfix_bot : fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊥ := by
    simpa [ψ] using
      hkt_invariant_quotient_fixedPointSubgroup_eq_bot_of_distinct_elementary_prime
        φ N hNφ hrp hprod
  have hψ_ne_one : ψ ≠ 1 := by
    intro hψone
    have hfix_top : fixedPointSubgroup (↥(Subgroup.zpowers ψ)) (Q ⧸ N) = ⊤ := by
      rw [hψone]
      ext x
      simp [fixedPointSubgroup, FixedPoints.mem_subgroup]
    have htop_bot : (⊤ : Subgroup (Q ⧸ N)) = ⊥ := by
      rw [← hfix_top, hfix_bot]
    exact (top_ne_bot : (⊤ : Subgroup (Q ⧸ N)) ≠ ⊥) htop_bot
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf ψ) hψ_dvd_p with horder_one | horder_p
  · exact False.elim <| hψ_ne_one (orderOf_eq_one_iff.mp horder_one)
  · exact horder_p

/--
Huppert V.8.13 step (3b), quotient-action step: if the elementary
quotient prime differs from the HKT period prime, then the induced quotient
action is fixed-point-free and has exact prime order `p`.
-/
public theorem huppertV813_quotient_distinct_prime_action
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hrp : r ≠ p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    fixedPointSubgroup
        (↥(Subgroup.zpowers (invariantQuotientAut φ N hNφ))) (Q ⧸ N) = ⊥ ∧
      orderOf (invariantQuotientAut φ N hNφ) = p := by
  constructor
  · exact
      hkt_invariant_quotient_fixedPointSubgroup_eq_bot_of_distinct_elementary_prime
        φ N hNφ hrp hprod
  · exact
      hkt_invariant_quotient_orderOf_eq_prime_of_distinct_elementary_prime
        φ N hNφ hrp hperiod hprod

/-- A cyclic subgroup generated by an element of prime order has order that prime. -/
public theorem natCard_zpowers_eq_prime_of_orderOf_eq
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (g : G) (hg : orderOf g = p) :
    Nat.card (Subgroup.zpowers g) = p := by
  simp [hg, Nat.card_zpowers]

/-- A cyclic subgroup generated by one element is cyclic. -/
public theorem isCyclic_zpowers {G : Type u} [Group G] (g : G) :
    IsCyclic (Subgroup.zpowers g) :=
  Subgroup.isCyclic_zpowers g

/-- A cyclic subgroup generated by an element of prime order is a `p`-group. -/
public theorem isPGroup_zpowers_of_orderOf_eq_prime
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (g : G) (hg : orderOf g = p) :
    IsPGroup p (Subgroup.zpowers g) := by
  have hcard : Nat.card (Subgroup.zpowers g) = p :=
    natCard_zpowers_eq_prime_of_orderOf_eq g hg
  exact IsPGroup.of_card (p := p) (G := Subgroup.zpowers g) (n := 1) (by
    simp [hcard])

public noncomputable def zmodZPowersMulEquiv
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ψ : G) (hcard : Nat.card (Subgroup.zpowers ψ) = p) :
    Multiplicative (ZMod p) ≃* Subgroup.zpowers ψ :=
  zmodMulEquivOfGenerator
    (G := Subgroup.zpowers ψ)
    (g := ⟨ψ, Subgroup.mem_zpowers ψ⟩)
    (n := p)
    (fun x => by
      rw [Subgroup.mem_zpowers_iff]
      rcases Subgroup.mem_zpowers_iff.mp x.property with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      ext
      simpa using hk)
    hcard

@[expose]
public noncomputable def zmodZPowersMulAutHom
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ψ : MulAut G) (hcard : Nat.card (Subgroup.zpowers ψ) = p) :
    Multiplicative (ZMod p) →* MulAut G :=
  (Subgroup.zpowers ψ).subtype.comp
    ((zmodZPowersMulEquiv ψ hcard).toMonoidHom)

public theorem zmodZPowersMulAutHom_apply_ofAdd_intCast
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ψ : MulAut G) (hcard : Nat.card (Subgroup.zpowers ψ) = p) (i : ℤ) :
    zmodZPowersMulAutHom ψ hcard (Multiplicative.ofAdd (i : ZMod p)) = ψ ^ i := by
  simp [zmodZPowersMulAutHom, zmodZPowersMulEquiv]


@[expose]
public noncomputable def zmodPeriodMulAutHom
    {G : Type u} [Group G] {p : ℕ}
    (α : MulAut G) (hαp : α ^ p = 1) :
    Multiplicative (ZMod p) →* MulAut G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift p
      ⟨zmultiplesHom (Additive (MulAut G)) (Additive.ofMul α), by
        simp only [zmultiplesHom_apply]
        rw [← ofMul_zpow (p : ℤ) α]
        simp [hαp]⟩)

public theorem zmodPeriodMulAutHom_apply_ofAdd_intCast
    {G : Type u} [Group G] {p : ℕ}
    (α : MulAut G) (hαp : α ^ p = 1) (i : ℤ) :
    zmodPeriodMulAutHom α hαp (Multiplicative.ofAdd (i : ZMod p)) = α ^ i := by
  simp [zmodPeriodMulAutHom, ZMod.lift_coe]


/-- If the cyclic group generated by `ψ` has prime order and its fixed-point
subgroup on `G` is trivial, then the action is regular in the sense of BG
Section 3.  The only point is that every nonidentity element of a prime-order
cyclic group generates the same subgroup. -/
public theorem hkt_actsRegularly_of_zpowers_prime_order_fixedPointSubgroup_eq_bot
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ψ : MulAut G)
    (hcard : Nat.card (Subgroup.zpowers ψ) = p)
    (hfix : fixedPointSubgroup (↥(Subgroup.zpowers ψ)) G = ⊥) :
    ActsRegularly (Subgroup.zpowers ψ) G := by
  intro a ha
  have ha_order : orderOf a = p := by
    have horder_dvd : orderOf a ∣ p := by
      simpa [hcard] using orderOf_dvd_natCard a
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf a) horder_dvd with h1 | hp
    · exact False.elim (ha (orderOf_eq_one_iff.mp h1))
    · exact hp
  have hzp_card : Nat.card (Subgroup.zpowers a) = Nat.card (Subgroup.zpowers ψ) := by
    rw [Nat.card_zpowers, ha_order, hcard]
  have hzp_top : Subgroup.zpowers a = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).1 hzp_card
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx_all : x ∈ fixedPointSubgroup (↥(Subgroup.zpowers ψ)) G := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hb : b ∈ Subgroup.zpowers a := by
      simp [hzp_top]
    exact hx ⟨b, hb⟩
  simpa [hfix] using hx_all

/--
Expanded Huppert V.8.13 step (3b) quotient-action step.  Besides the
fixed-point-free action and exact order already proved above, this records the
cyclic prime-order `p`-group structure of the acting subgroup.  This is the
shape needed for the later Huppert V.8.12 / `proposition_3_9` contradiction.
-/
public theorem huppertV813_quotient_distinct_prime_regular_action
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup Q) [N.Normal]
    (hNφ : ∀ q : Q, q ∈ N ↔ φ q ∈ N)
    [Nontrivial (Q ⧸ N)] [IsElementaryAbelian r (Q ⧸ N)]
    (hrp : r ≠ p)
    (hperiod : (fun q : Q => φ q)^[p] = id)
    (hprod :
      ∀ q : Q,
        ((List.range p).map (fun k ↦ (fun q : Q => φ q)^[k] q)).prod = 1) :
    fixedPointSubgroup
        (↥(Subgroup.zpowers (invariantQuotientAut φ N hNφ))) (Q ⧸ N) = ⊥ ∧
      orderOf (invariantQuotientAut φ N hNφ) = p ∧
        Nat.card (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) = p ∧
          IsCyclic (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) ∧
            IsPGroup p (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) ∧
              ActsRegularly (Subgroup.zpowers (invariantQuotientAut φ N hNφ))
                (Q ⧸ N) := by
  obtain ⟨hfix, horder⟩ :=
    huppertV813_quotient_distinct_prime_action
      φ N hNφ hrp hperiod hprod
  have hcard : Nat.card (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) = p :=
    natCard_zpowers_eq_prime_of_orderOf_eq (invariantQuotientAut φ N hNφ) horder
  have hcyc : IsCyclic (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) :=
    isCyclic_zpowers (invariantQuotientAut φ N hNφ)
  have hpgroup : IsPGroup p (Subgroup.zpowers (invariantQuotientAut φ N hNφ)) :=
    isPGroup_zpowers_of_orderOf_eq_prime (invariantQuotientAut φ N hNφ) horder
  have hregular :
      ActsRegularly (Subgroup.zpowers (invariantQuotientAut φ N hNφ))
        (Q ⧸ N) :=
    hkt_actsRegularly_of_zpowers_prime_order_fixedPointSubgroup_eq_bot
      (invariantQuotientAut φ N hNφ) hcard hfix
  exact ⟨hfix, horder, hcard, hcyc, hpgroup, hregular⟩

end External
end CFSG.BenderSuzuki
