module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcE6

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.CentralCover

@[expose] def foldedTorusExp (t : TwistTag) {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin t.foldedTag.rank → ZMod p) →* (Fin t.tag.rank → Kˣ) :=
  Pi.monoidHom fun i => (zmodPowHom ζ hζ).comp
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) (t.orbitIndex i)))

theorem foldedTorusExp_ofAdd_apply (t : TwistTag) {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (v : Fin t.foldedTag.rank → ZMod p) (i : Fin t.tag.rank) :
    foldedTorusExp t ζ hζ (.ofAdd v) i = zmodPowHom ζ hζ (.ofAdd (v (t.orbitIndex i))) :=
  rfl

theorem foldedTorusExp_mem_compatSubgroup (t : TwistTag) {K : Type} [Field K] {p : ℕ}
    [NeZero p] (σ : K →+* K) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hσζ : Units.map σ.toMonoidHom ζ = ζ)
    (v : Multiplicative (Fin t.foldedTag.rank → ZMod p)) :
    foldedTorusExp t ζ hζ v ∈ compatSubgroup σ := by
  rw [mem_compatSubgroup]
  intro i
  show ζ ^ (v (t.orbitIndex (t.perm i))).val =
    Units.map σ.toMonoidHom (ζ ^ (v (t.orbitIndex i)).val)
  rw [t.orbitIndex_perm, map_pow, hσζ]

section Certificates

@[expose] def foldedTorusHom (t : TwistTag) {K : Type} [Field K] {p : ℕ} [NeZero p]
    (σ : K →+* K) (ζ : Kˣ) (hζ : ζ ^ p = 1) (hσζ : Units.map σ.toMonoidHom ζ = ζ) :
    Multiplicative (Fin t.foldedTag.rank → ZMod p) →* ↥(graphFixedRootGroup t K σ) :=
  let f : Multiplicative (Fin t.foldedTag.rank → ZMod p) →* ModGL t.tag K :=
    ((torusGroup t.tag K).subtype.comp (torusCoordHom t.tag K)).comp (foldedTorusExp t ζ hζ)
  f.codRestrict (graphFixedRootGroup t K σ) fun v =>
    compatTorus_le_graphFixedRootGroup (t := t) (σ := σ)
      ⟨foldedTorusExp t ζ hζ v, foldedTorusExp_mem_compatSubgroup t σ hζ hσζ v, rfl⟩

@[simp] theorem coe_foldedTorusHom (t : TwistTag) {K : Type} [Field K] {p : ℕ} [NeZero p]
    (σ : K →+* K) (ζ : Kˣ) (hζ : ζ ^ p = 1) (hσζ : Units.map σ.toMonoidHom ζ = ζ)
    (v : Multiplicative (Fin t.foldedTag.rank → ZMod p)) :
    ((foldedTorusHom t σ ζ hζ hσζ v : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) =
      (torusCoordHom t.tag K (foldedTorusExp t ζ hζ v) : ModGL t.tag K) := by
  simp [foldedTorusHom]

theorem foldedTorusHom_range_le_normalizer (t : TwistTag) {K : Type} [Field K] {p : ℕ}
    [NeZero p] (σ : K →+* K) (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hσζ : Units.map σ.toMonoidHom ζ = ζ) :
    (foldedTorusHom t σ ζ hζ hσζ).range ≤
      Subgroup.normalizer (((graphFixedPosUnipotent t K σ).subgroupOf
        (graphFixedRootGroup t K σ) : Subgroup ↥(graphFixedRootGroup t K σ)) :
          Set ↥(graphFixedRootGroup t K σ)) := by
  rintro _ ⟨v, rfl⟩
  refine uc22pwex_mem_normalizer_subgroupOf ?_
  exact graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent
    (compatTorus_le_graphFixedRootTorus (t := t) (σ := σ)
      ⟨foldedTorusExp t ζ hζ v, foldedTorusExp_mem_compatSubgroup t σ hζ hσζ v, rfl⟩)

theorem foldedTorusHom_injective (t : TwistTag) {K : Type} [Field K] {p : ℕ} [NeZero p]
    (σ : K →+* K) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hσζ : Units.map σ.toMonoidHom ζ = ζ)
    (hker : ∀ s : Fin t.foldedTag.rank → Kˣ, (∀ a, s a ^ p = 1) →
      torusCoordHom t.tag K (fun i => s (t.orbitIndex i)) = 1 → s = 1) :
    Function.Injective (foldedTorusHom t σ ζ hζ hσζ) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : torusCoordHom t.tag K (foldedTorusExp t ζ hζ v) = 1 := by
    have := congrArg (fun x : ↥(graphFixedRootGroup t K σ) => (x : ModGL t.tag K)) hv
    exact Subtype.ext (by simpa using this)
  have h1' : torusCoordHom t.tag K (fun i => ζ ^ (v (t.orbitIndex i)).val) = 1 := by
    rw [← h1]
    congr 1
  have h2 : (fun a => ζ ^ (v a).val) = 1 :=
    hker (fun a => ζ ^ (v a).val) (fun a => by
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) h1'
  apply Multiplicative.toAdd.injective
  funext a
  have h3 : ζ ^ (v a).val = 1 := congrFun h2 a
  have h4 : p ∣ (v a).val := by
    have := orderOf_dvd_of_pow_eq_one h3
    rwa [hζo] at this
  have h5 : (v a).val = 0 := Nat.eq_zero_of_dvd_of_lt h4 (ZMod.val_lt (v a))
  have h6 : v a = 0 := by
    rw [← ZMod.natCast_zmod_val (v a), h5, Nat.cast_zero]
  change v a = 0
  exact h6

end Certificates

@[expose] def e6FoldedCartan : Matrix (Fin TwistTag.E6.foldedTag.rank)
    (Fin TwistTag.E6.foldedTag.rank) ℤ := Tag.F4.cartan

theorem e6_cartan_orbit_sum_eq (a b : Fin TwistTag.E6.foldedTag.rank)
    {k : Fin TwistTag.E6.tag.rank} (hk : k ∈ TwistTag.E6.orbit a) :
    ∑ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = b),
      TwistTag.E6.tag.cartan j k = e6FoldedCartan a b := by
  revert k
  fin_cases a <;> fin_cases b <;>
    (intro k hk
     fin_cases k <;> first | exact absurd hk (by decide) | decide)

theorem e6FoldedCartan_self (a : Fin TwistTag.E6.foldedTag.rank) :
    e6FoldedCartan a a = 2 := by
  fin_cases a <;> decide

@[expose] def e6FoldedFunctional (p : ℕ) [NeZero p] (a : Fin TwistTag.E6.foldedTag.rank) :
    (Fin TwistTag.E6.foldedTag.rank → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ b, (e6FoldedCartan a b : ZMod p) • LinearMap.proj b

theorem e6FoldedFunctional_apply (p : ℕ) [NeZero p] (a : Fin TwistTag.E6.foldedTag.rank)
    (v : Fin TwistTag.E6.foldedTag.rank → ZMod p) :
    e6FoldedFunctional p a v = ∑ b, (e6FoldedCartan a b : ZMod p) * v b := by
  simp [e6FoldedFunctional, LinearMap.sum_apply]

theorem e6FoldedFunctional_single (p : ℕ) [NeZero p] (a : Fin TwistTag.E6.foldedTag.rank) :
    e6FoldedFunctional p a (Pi.single a 1) = 2 := by
  classical
  rw [e6FoldedFunctional_apply, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, mul_one, e6FoldedCartan_self]
    norm_num
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

@[expose] def e6FoldedRelation : Matrix (Fin TwistTag.E6.foldedTag.rank)
    (Fin TwistTag.E6.foldedTag.rank) ℤ :=
  fun a b => ∑ i ∈ Finset.univ.filter (fun i => TwistTag.E6.orbitIndex i = a),
    TwistTag.E6.tag.cartan i (TwistTag.E6.orbitMin b)

@[expose] def e6FoldedRelationInv : Matrix (Fin TwistTag.E6.foldedTag.rank)
    (Fin TwistTag.E6.foldedTag.rank) ℤ :=
  !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]

theorem e6FoldedRelation_mul_inv : e6FoldedRelation * e6FoldedRelationInv = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem e6_foldedTorus_kernel {K : Type} [Field K] {p : ℕ}
    {s : Fin TwistTag.E6.foldedTag.rank → Kˣ} (hs : ∀ a, s a ^ p = 1)
    (h : torusCoordHom TwistTag.E6.tag K
      (fun i => s (TwistTag.E6.orbitIndex i)) = 1) :
    s = 1 := by
  refine uc22pwex_eq_one_of_prod_zpow_eq_one (A := e6FoldedRelation)
    (B := e6FoldedRelationInv) (m := 1) (by simpa using e6FoldedRelation_mul_inv)
    (Nat.coprime_one_left p) hs ?_
  intro b
  have h' := torusCoordHom_apply_rootVec_single (R := K)
    (fun i => s (TwistTag.E6.orbitIndex i)) (TwistTag.E6.orbitMin b)
  rw [h, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
    rootVec_eq_single_of_isRoot (isRoot_single TwistTag.E6.tag (TwistTag.E6.orbitMin b))] at h'
  have h'' := congrArg (fun v : RootModule TwistTag.E6.tag K =>
    v (Sum.inr ⟨Pi.single (TwistTag.E6.orbitMin b) 1,
      isRoot_single TwistTag.E6.tag (TwistTag.E6.orbitMin b)⟩)) h'
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h''
  have h3 : (1 : Kˣ) = ∏ i, s (TwistTag.E6.orbitIndex i) ^
      Tag.E6.cartan i (TwistTag.E6.orbitMin b) := Units.ext h''
  rw [h3]
  rw [← Finset.prod_fiberwise Finset.univ TwistTag.E6.orbitIndex
    (fun i => s (TwistTag.E6.orbitIndex i) ^ Tag.E6.cartan i (TwistTag.E6.orbitMin b))]
  refine Finset.prod_congr rfl fun a _ => ?_
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => TwistTag.E6.orbitIndex i = a),
      s (TwistTag.E6.orbitIndex i) ^ Tag.E6.cartan i (TwistTag.E6.orbitMin b) =
      ∏ i ∈ Finset.univ.filter (fun i => TwistTag.E6.orbitIndex i = a),
        s a ^ Tag.E6.cartan i (TwistTag.E6.orbitMin b) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  rw [h1, prod_zpow_eq_zpow_sum, e6FoldedRelation]
  rfl

theorem e6_folded_exponent (p : ℕ) [NeZero p] (a : Fin TwistTag.E6.foldedTag.rank)
    {k : Fin TwistTag.E6.tag.rank} (hk : k ∈ TwistTag.E6.orbit a)
    (v : Fin TwistTag.E6.foldedTag.rank → ZMod p) :
    v a + ∑ j : Fin TwistTag.E6.tag.rank,
        ((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) * v (TwistTag.E6.orbitIndex j)
      = v a - e6FoldedFunctional p a v := by
  have hsum : ∑ j : Fin TwistTag.E6.tag.rank,
      (TwistTag.E6.tag.cartan j k : ZMod p) * v (TwistTag.E6.orbitIndex j)
      = e6FoldedFunctional p a v := by
    rw [← Finset.sum_fiberwise Finset.univ TwistTag.E6.orbitIndex
      (fun j => (TwistTag.E6.tag.cartan j k : ZMod p) * v (TwistTag.E6.orbitIndex j))]
    rw [e6FoldedFunctional_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc ∑ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = b),
          (TwistTag.E6.tag.cartan j k : ZMod p) * v (TwistTag.E6.orbitIndex j)
        = ∑ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = b),
            (TwistTag.E6.tag.cartan j k : ZMod p) * v b := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.1 hj).2]
      _ = (∑ j ∈ Finset.univ.filter (fun j => TwistTag.E6.orbitIndex j = b),
            (TwistTag.E6.tag.cartan j k : ZMod p)) * v b := by
          rw [Finset.sum_mul]
      _ = (e6FoldedCartan a b : ZMod p) * v b := by
          rw [← Int.cast_sum, e6_cartan_orbit_sum_eq a b hk]
  have hneg : ∑ j : Fin TwistTag.E6.tag.rank,
      ((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) * v (TwistTag.E6.orbitIndex j)
      = - ∑ j : Fin TwistTag.E6.tag.rank,
        (TwistTag.E6.tag.cartan j k : ZMod p) * v (TwistTag.E6.orbitIndex j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_neg, neg_mul]
  rw [hneg, hsum]
  ring

theorem e6_iterReflect_orbitWord {K : Type} [Field K] (p : ℕ) [NeZero p]
    (a : Fin TwistTag.E6.foldedTag.rank) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (v : Fin TwistTag.E6.foldedTag.rank → ZMod p) :
    iterReflect TwistTag.E6.tag (TwistTag.E6.orbitWord a)
        (foldedTorusExp TwistTag.E6 ζ hζ (.ofAdd v)) =
      foldedTorusExp TwistTag.E6 ζ hζ
        (.ofAdd (v - (e6FoldedFunctional p a v • Pi.single a 1))) := by
  funext k
  rw [iterReflect_eq (TwistTag.E6.nodup_orbitWord a)
      (CFSG.Timmesfeld.ExceptionalOrders.orthogonal_orbitWord (t := TwistTag.E6) a),
    list_prod_orbitWord_mulSingle, Pi.mul_apply]
  by_cases hk : k ∈ TwistTag.E6.orbit a
  · rw [if_pos hk]
    simp only [foldedTorusExp_ofAdd_apply]
    have hfac : ∀ j : Fin TwistTag.E6.tag.rank,
        (zmodPowHom ζ hζ (.ofAdd (v (TwistTag.E6.orbitIndex j)))) ^
          (-TwistTag.E6.tag.cartan j k) =
        zmodPowHom ζ hζ (.ofAdd (((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) *
          v (TwistTag.E6.orbitIndex j))) := fun j => by
      rw [← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
    have hprod : ∏ j : Fin TwistTag.E6.tag.rank,
        (zmodPowHom ζ hζ (.ofAdd (v (TwistTag.E6.orbitIndex j)))) ^
          (-TwistTag.E6.tag.cartan j k) =
        zmodPowHom ζ hζ (.ofAdd (∑ j : Fin TwistTag.E6.tag.rank,
          ((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) * v (TwistTag.E6.orbitIndex j))) := by
      calc ∏ j : Fin TwistTag.E6.tag.rank,
            (zmodPowHom ζ hζ (.ofAdd (v (TwistTag.E6.orbitIndex j)))) ^
              (-TwistTag.E6.tag.cartan j k)
          = ∏ j : Fin TwistTag.E6.tag.rank,
              zmodPowHom ζ hζ (.ofAdd (((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) *
                v (TwistTag.E6.orbitIndex j))) := Finset.prod_congr rfl fun j _ => hfac j
        _ = zmodPowHom ζ hζ (.ofAdd (∑ j : Fin TwistTag.E6.tag.rank,
              ((-TwistTag.E6.tag.cartan j k : ℤ) : ZMod p) * v (TwistTag.E6.orbitIndex j))) := by
              rw [← map_prod, ← ofAdd_sum]
    rw [hprod, ← map_mul, ← ofAdd_add]
    rw [show TwistTag.E6.orbitIndex k = a from (TwistTag.E6.mem_orbit_iff).1 hk]
    rw [e6_folded_exponent p a hk v]
    refine congrArg (zmodPowHom ζ hζ) ?_
    refine congrArg Multiplicative.ofAdd ?_
    simp [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  · rw [if_neg hk, mul_one]
    simp only [foldedTorusExp_ofAdd_apply]
    have hne : TwistTag.E6.orbitIndex k ≠ a :=
      fun h => hk ((TwistTag.E6.mem_orbit_iff).2 h)
    refine congrArg (zmodPowHom ζ hζ) ?_
    refine congrArg Multiplicative.ofAdd ?_
    simp [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne' (Ne.symm hne), smul_zero,
      sub_zero]

section Certificates

theorem e6_foldedTorusWeyl_conj {K : Type} [Field K] {p : ℕ} [NeZero p] {σ : K →+* K}
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hσζ : Units.map σ.toMonoidHom ζ = ζ)
    (a : Fin TwistTag.E6.foldedTag.rank) (v : Fin TwistTag.E6.foldedTag.rank → ZMod p) :
    (⟨orbitN TwistTag.E6 K σ a 1,
        orbitN_mem_graphFixedRootGroup (t := TwistTag.E6) σ a 1⟩ :
      ↥(graphFixedRootGroup TwistTag.E6 K σ)) *
      foldedTorusHom TwistTag.E6 σ ζ hζ hσζ (.ofAdd v) *
      (⟨orbitN TwistTag.E6 K σ a 1,
        orbitN_mem_graphFixedRootGroup (t := TwistTag.E6) σ a 1⟩ :
      ↥(graphFixedRootGroup TwistTag.E6 K σ))⁻¹ =
      foldedTorusHom TwistTag.E6 σ ζ hζ hσζ
        (.ofAdd (v - (e6FoldedFunctional p a v • Pi.single a 1))) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_foldedTorusHom]
  rw [coe_orbitN_one, list_prod_weylElt_conj_torusCoordHom, e6_iterReflect_orbitWord p a hζ v]

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UC22
