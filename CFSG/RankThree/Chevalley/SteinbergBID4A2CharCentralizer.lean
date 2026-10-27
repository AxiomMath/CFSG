module

public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab
public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open scoped Pointwise

variable (K : Type) [Field K]

@[expose] def d4A2Qv (v : WeylGroup Tag.D4) : Subgroup (ModGL Tag.D4 K) :=
  (subsystemGroup Tag.D4 K d4SuppA2).map
    (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) K v)).toMonoidHom

@[expose] def d4A2Tv (v : WeylGroup Tag.D4) : Subgroup (ModGL Tag.D4 K) :=
  (subsystemTorus Tag.D4 K d4SuppA2).map
    (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) K v)).toMonoidHom

variable {K}

theorem isRoot_of_mem_image_d4A2Sigma {v : WeylGroup Tag.D4} {α : Fin Tag.D4.rank → ℤ}
    (hα : α ∈ (fun β => v • β) '' d4A2Sigma) : IsRoot Tag.D4 α := by
  obtain ⟨β, hβ, rfl⟩ := hα
  exact IsRoot.smul (isRoot_of_mem_d4A2Sigma hβ) v

theorem d4A2Qv_eq_rootSpan
    (v : WeylGroup Tag.D4) :
    d4A2Qv K v = rootSpan Tag.D4 K ((fun α => v • α) '' d4A2Sigma) := by
  rw [d4A2Qv, subsystemGroup_eq_rootSpan, parabolicRoots_d4SuppA2]
  exact (canonical_weyl_root_transport Tag.D4 K).1 v d4A2Sigma fun α hα =>
    isRoot_of_mem_d4A2Sigma hα

theorem torusGroup_le_normalizer_d4A2Qv
    (v : WeylGroup Tag.D4) :
    torusGroup Tag.D4 K ≤ Subgroup.normalizer (d4A2Qv K v : Set (ModGL Tag.D4 K)) := by
  rw [d4A2Qv_eq_rootSpan]
  exact torusGroup_le_normalizer_rootSpan fun α hα => isRoot_of_mem_image_d4A2Sigma hα

@[expose] def d4A2QvEquiv
    (v : WeylGroup Tag.D4) : d4A2Qv K v ≃* SpecialLinearGroup (Fin 3) K :=
  (Subgroup.equivMapOfInjective _ _
    (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) K v)).injective).symm.trans
    (MulEquiv.ofBijective (d4A2Rep K) ⟨d4A2Rep_injective, d4A2Rep_surjective⟩)

theorem d4A2Qv_inf_torusGroup
    (v : WeylGroup Tag.D4) :
    d4A2Qv K v ⊓ torusGroup Tag.D4 K = d4A2Tv K v := by
  rw [d4A2Qv, d4A2Tv, ← subsystemGroup_inf_torusGroup,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) K v)).injective,
    map_conj_eq_of_mem_normalizer (canonicalRep_mem_normalizer v)]

theorem torusGroup_mul_comm {h h' : ModGL Tag.D4 K} (hh : h ∈ torusGroup Tag.D4 K)
    (hh' : h' ∈ torusGroup Tag.D4 K) : h * h' = h' * h := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh'
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem toralCentralizer_eq_toralRootGroup
    {τ : Tag} {a : Fin τ.rank → Kˣ}
    (h : rootCharStabilizerSubgroup a = kernelReflectionGroup a) :
    toralCentralizer τ K a = toralRootGroup τ K a := by
  obtain ⟨hle, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  refine le_antisymm (fun g hg => ?_) hle
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← h]
    exact w.2
  rw [hw1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem D4_odd_prime_A2_root_character_centralizer
    (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (_hpK : ringChar K ≠ p) (a : Fin Tag.D4.rank → Kˣ)
    (hord : orderOf (rootDiagUnit Tag.D4 a) = p) (v : WeylGroup Tag.D4)
    (hSig : rootCharKernel a = (fun α => v • α) '' d4A2Sigma) :
    rootCharStabilizerSubgroup a =
      Subgroup.closure ((fun α => rootReflection α) '' rootCharKernel a) ∧
    (toralCentralizer Tag.D4 K a : Set (ModGL Tag.D4 K)) =
      (torusGroup Tag.D4 K : Set (ModGL Tag.D4 K)) * (d4A2Qv K v : Set (ModGL Tag.D4 K)) ∧
    d4A2Qv K v ≤ toralCentralizer Tag.D4 K a ∧
    ((d4A2Qv K v).subgroupOf (toralCentralizer Tag.D4 K a)).Normal ∧
    Nonempty (d4A2Qv K v ≃* SpecialLinearGroup (Fin 3) K) ∧
    ⁅d4A2Qv K v, d4A2Qv K v⁆ = d4A2Qv K v ∧
    ⁅toralCentralizer Tag.D4 K a, toralCentralizer Tag.D4 K a⁆ = d4A2Qv K v ∧
    d4A2Qv K v ⊓ torusGroup Tag.D4 K = d4A2Tv K v ∧
    ∃ (_ : ((d4A2Qv K v).subgroupOf (toralCentralizer Tag.D4 K a)).Normal)
      (_ : ((d4A2Tv K v).subgroupOf (torusGroup Tag.D4 K)).Normal),
      Nonempty (toralCentralizer Tag.D4 K a ⧸ (d4A2Qv K v).subgroupOf (toralCentralizer Tag.D4 K a)
        ≃* torusGroup Tag.D4 K ⧸ (d4A2Tv K v).subgroupOf (torusGroup Tag.D4 K)) ∧
      ∀ x y : toralCentralizer Tag.D4 K a ⧸
        (d4A2Qv K v).subgroupOf (toralCentralizer Tag.D4 K a), x * y = y * x := by
  have ha := pow_eq_one_of_orderOf_rootDiagUnit hord
  obtain ⟨hstab, -⟩ := D4_A2_rootCharStabilizer_eq hp hp2 ha hSig
  set X := toralCentralizer Tag.D4 K a with hXdef
  set H := torusGroup Tag.D4 K with hHdef
  set Q := d4A2Qv K v with hQdef
  have hX : X = H ⊔ Q := by
    rw [hXdef, toralCentralizer_eq_toralRootGroup hstab, toralRootGroup, hSig, hQdef,
      d4A2Qv_eq_rootSpan]
  have hLE : H ≤ Subgroup.normalizer (Q : Set (ModGL Tag.D4 K)) :=
    torusGroup_le_normalizer_d4A2Qv v
  have hQX : Q ≤ X := hX ▸ le_sup_right
  have hHX : H ≤ X := hX ▸ le_sup_left
  have hXN : X ≤ Subgroup.normalizer (Q : Set (ModGL Tag.D4 K)) := by
    rw [hX]
    exact sup_le hLE Subgroup.le_normalizer
  have hnormal : (Q.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).2 hXN
  have hset : (X : Set (ModGL Tag.D4 K)) = (H : Set (ModGL Tag.D4 K)) * (Q : Set _) := by
    rw [hX]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE
  have hinf : Q ⊓ H = d4A2Tv K v := d4A2Qv_inf_torusGroup v
  have hcomm : ∀ x y : X ⧸ Q.subgroupOf X, x * y = y * x := by
    have hrep : ∀ g : X, ∃ h : H, (QuotientGroup.mk g : X ⧸ Q.subgroupOf X) =
        QuotientGroup.mk ⟨(h : ModGL Tag.D4 K), hHX h.2⟩ := by
      intro g
      have hg : (g : ModGL Tag.D4 K) ∈ (H : Set (ModGL Tag.D4 K)) * (Q : Set _) := by
        rw [← hset]
        exact g.2
      obtain ⟨h, hh, q, hq, hhq⟩ := hg
      refine ⟨⟨h, hh⟩, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : ((g⁻¹ * ⟨h, hHX hh⟩ : X) : ModGL Tag.D4 K) = q⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hhq]
        group
      rw [e]
      exact inv_mem hq
    intro x y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, hh⟩ := hrep g
    obtain ⟨h', hh'⟩ := hrep g'
    rw [hh, hh', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (torusGroup_mul_comm h.2 h'.2)
  have : (Q.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  have : (Q.subgroupOf (H ⊔ Q)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have hTQ : (d4A2Tv K v).subgroupOf H = Q.subgroupOf H := by
    rw [← hinf, Subgroup.inf_subgroupOf_right]
  have hnormT : ((d4A2Tv K v).subgroupOf H).Normal := hTQ ▸ inferInstance
  have hmap : (Q.subgroupOf X).map (MulEquiv.subgroupCongr hX : X →* (H ⊔ Q : Subgroup _)) =
      Q.subgroupOf (H ⊔ Q) := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨y, hy⟩, hyQ, hyx⟩
      have e : y = x := congrArg Subtype.val hyx
      rw [← e]
      exact hyQ
    · intro hxQ
      exact ⟨⟨x, hX ▸ hx⟩, hxQ, rfl⟩
  have e : X ⧸ Q.subgroupOf X ≃* H ⧸ (d4A2Tv K v).subgroupOf H :=
    (QuotientGroup.congr (Q.subgroupOf X) (Q.subgroupOf (H ⊔ Q)) (MulEquiv.subgroupCongr hX)
      hmap).trans
      ((QuotientGroup.quotientInfEquivProdNormalizerQuotient H Q hLE).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hTQ.symm))
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := (d4A2QvEquiv v).symm.toMonoidHom)
      (d4A2QvEquiv v).symm.surjective
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.commutator_eq_self
  have hder : ⁅X, X⁆ = Q := by
    refine le_antisymm ?_ ?_
    · have hc : IsMulCommutative (X ⧸ Q.subgroupOf X) := ⟨⟨hcomm⟩⟩
      have hle := Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hc
      rw [← Subgroup.map_subtype_commutator X]
      calc (_root_.commutator X).map X.subtype ≤ (Q.subgroupOf X).map X.subtype :=
            Subgroup.map_mono hle
        _ = Q ⊓ X := Subgroup.subgroupOf_map_subtype _ _
        _ ≤ Q := inf_le_left
    · calc Q = ⁅Q, Q⁆ := hperf.symm
        _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hQX hQX
  refine ⟨?_, hset, hQX, hnormal, ⟨d4A2QvEquiv v⟩, hperf, hder, hinf, hnormal, hnormT, ⟨e⟩,
    hcomm⟩
  rw [hstab, kernelReflectionGroup_eq_closure_rootReflection]

end CFSG.RankThree.Chevalley
