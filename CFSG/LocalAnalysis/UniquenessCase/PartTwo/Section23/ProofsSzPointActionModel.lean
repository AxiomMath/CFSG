module

public import CFSG.GroupTheory.SuzukiPointTorus.Transport
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOvoid
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.SzPointModel

open CFSG.GroupTheory
open CFSG.Holt
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.External
open scoped Matrix LinearAlgebra.Projectivization Pointwise

abbrev K (m : ℕ) : Type := BinaryGaloisField (2 * m + 1)

abbrev G (m : ℕ) : Type := SuzukiMatrixGroup m

abbrev q (m : ℕ) : ℕ := 2 ^ (2 * m + 1)

abbrev SzOvoid (m : ℕ) : Type :=
  {p : Projectivization (K m) (Fin 4 → K m) //
    p ∈ CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzukiOvoidSet m}

abbrev ovoidInfinity (m : ℕ) : SzOvoid m :=
  ⟨CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzukiOvoidInfinity m, Or.inl rfl⟩

attribute [local instance]
  CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzukiOvoidAction

theorem card_root (m : ℕ) (hm : 0 < m) :
    Nat.card (suzukiCoverRoot m) = q m ^ 2 :=
  (suzukiCoverRoot_structure m hm).2.1

private theorem isPGroup_root (m : ℕ) (hm : 0 < m) : IsPGroup 2 (suzukiCoverRoot m) :=
  (suzukiCoverRoot_structure m hm).1

private theorem commutator_root (m : ℕ) (hm : 0 < m) :
    commutator (suzukiCoverRoot m) = Subgroup.center (suzukiCoverRoot m) :=
  (suzukiCoverRoot_structure m hm).2.2.1

theorem frattini_root (m : ℕ) (hm : 0 < m) :
    frattini (suzukiCoverRoot m) = Subgroup.center (suzukiCoverRoot m) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 (suzukiCoverRoot m)) := ⟨isPGroup_root m hm⟩
  apply le_antisymm
  · rw [frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · rw [commutator_root m hm] at hx
      exact hx
    · obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m y
      have hsq : suzukiCoverRootElement m a b ^ 2 =
          suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) := by
        rw [pow_two, suzukiCoverRootElement_mul m hm]
        simp [CharTwo.add_self_eq_zero]
      change suzukiCoverRootElement m a b ^ 2 ∈ Subgroup.center (suzukiCoverRoot m)
      rw [hsq]
      rw [← commutator_root m hm]
      exact ((suzukiCoverRoot_structure m hm).2.2.2 _).mpr ⟨a * suzukiCoverTits m a, rfl⟩
  · rw [← commutator_root m hm]
    exact commutator_le_frattini_of_isPGroup (R := suzukiCoverRoot m) (p := 2)

theorem card_center_root (m : ℕ) (hm : 0 < m) :
    Nat.card (Subgroup.center (suzukiCoverRoot m)) = q m := by
  rw [← commutator_root m hm]
  exact suzukiCoverDerived_card m hm

private theorem card_torus (m : ℕ) (hm : 0 < m) :
    Nat.card (suzukiCoverTorus m) = q m - 1 :=
  suzukiCoverTorus_card m hm

private theorem isCyclic_torus (m : ℕ) (hm : 0 < m) : IsCyclic (suzukiCoverTorus m) :=
  (suzukiCoverTorusEquiv m hm).isCyclic.mp (inferInstance : IsCyclic (K m)ˣ)

private theorem normalizer_root (m : ℕ) (hm : 0 < m) :
    Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m)) =
      suzukiCoverRoot m ⊔ suzukiCoverTorus m :=
  suzukiCoverRoot_normalizer m hm

private theorem root_inf_torus (m : ℕ) (hm : 0 < m) :
    suzukiCoverRoot m ⊓ suzukiCoverTorus m = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx1 : ((x : G m) : GL (Fin 4) (K m)) = 1 := by
    rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdisjoint, _⟩
    exact Subgroup.disjoint_def.mp hdisjoint hx.1 hx.2
  simpa using hx1

private theorem card_normalizer_root (m : ℕ) (hm : 0 < m) :
    Nat.card (Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))) =
      q m ^ 2 * (q m - 1) := by
  have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := suzukiCoverTorus m) (K := suzukiCoverRoot m) (suzukiCoverTorus_le_normalizer m)
  rw [sup_comm, inf_comm, root_inf_torus m hm, Subgroup.card_bot, mul_one,
    card_torus m hm, card_root m hm] at hcard
  rw [normalizer_root m hm]
  simpa [mul_comm] using hcard

theorem isCyclic_normalizer_root_quotient (m : ℕ) (hm : 0 < m) :
    IsCyclic (↥(Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))) ⧸
      (suzukiCoverRoot m).subgroupOf
        (Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m)))) := by
  let N := Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))
  let R := suzukiCoverRoot m
  let T := suzukiCoverTorus m
  have hN_eq : N = suzukiCoverRoot m ⊔ suzukiCoverTorus m := normalizer_root m hm
  haveI : IsCyclic T := isCyclic_torus m hm
  have hT_le : T ≤ N := by
    rw [hN_eq]
    exact le_sup_right
  let φ : T →* ↥N ⧸ R.subgroupOf N :=
    (QuotientGroup.mk' (R.subgroupOf N)).comp (Subgroup.inclusion hT_le)
  have hφ_surj : Function.Surjective φ := by
    intro qq
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf N) qq
    obtain ⟨r, x, hrt⟩ := suzukiCoverRoot_normalizer_decomposition m hm n n.2
    let t : T := suzukiCoverTorusHom m x
    have htN : (t : G m) ∈ N := hT_le t.2
    have hrN : (r : G m) ∈ N := by
      rw [hN_eq]
      exact (show suzukiCoverRoot m ≤ suzukiCoverRoot m ⊔ suzukiCoverTorus m from
        le_sup_left) r.2
    have hprodN : (r : G m) * (t : G m) ∈ N := N.mul_mem hrN htN
    refine ⟨t, ?_⟩
    change QuotientGroup.mk' (R.subgroupOf N) (⟨(t : G m), htN⟩ : N) =
      QuotientGroup.mk' (R.subgroupOf N) n
    have hn : n = (⟨(r : G m) * (t : G m), hprodN⟩ : N) := by
      apply Subtype.ext
      simpa only [t] using hrt
    rw [hn, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change (t : G m)⁻¹ * ((r : G m) * (t : G m)) ∈ R
    have htinv : (t : G m)⁻¹ ∈ T := T.inv_mem t.2
    have hconj : (t : G m)⁻¹ * (r : G m) * ((t : G m)⁻¹)⁻¹ ∈ R := by
      have h := suzukiCoverTorus_le_normalizer m htinv
      rw [Subgroup.mem_normalizer_iff] at h
      exact (h (r : G m)).mp r.2
    convert hconj using 1
    group
  exact isCyclic_of_surjective φ hφ_surj

theorem card_normalizer_sylow (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    Nat.card (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))) = q m ^ 2 * (q m - 1) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (suzukiCoverSylow m hm) U
  have hmap : (suzukiCoverRoot m).map (MulAut.conj g).toMonoidHom = (U : Subgroup (G m)) := by
    rw [← suzukiCoverSylow_coe m hm]
    change (g • suzukiCoverSylow m hm : Sylow 2 (G m)).toSubgroup = U.toSubgroup
    rw [hg]
  have hN : Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) =
      (Subgroup.normalizer
        ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hmap, Subgroup.map_equiv_normalizer_eq]
  calc Nat.card (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)))
      = Nat.card ((Subgroup.normalizer
          ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))).map
          (MulAut.conj g).toMonoidHom) := by rw [hN]
    _ = Nat.card (Subgroup.normalizer
          ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))) :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = q m ^ 2 * (q m - 1) := card_normalizer_root m hm

theorem sylow_card_and_center (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    Nat.card (U : Subgroup (G m)) = q m ^ 2 ∧
      IsElementaryAbelian 2 (Subgroup.center (U : Subgroup (G m))) ∧
      Nat.card (Subgroup.center (U : Subgroup (G m))) = q m := by
  rcases CFSG.Open.bender_suzukiMatrixGroup_borel m hm U with ⟨-, -, hpow, hZcard, hcard⟩
  have hZel : IsElementaryAbelian 2 (Subgroup.center (U : Subgroup (G m))) :=
    { toIsMulCommutative := IsMulCommutative.of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun z =>
        Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hpow z z.2) }
  exact ⟨by simpa only [pow_two] using hcard, hZel, by simpa only [pow_two] using hZcard⟩

private theorem root_fixes_infinity (m : ℕ) (hm : 0 < m) (r : suzukiCoverRoot m) :
    (r : G m) • ovoidInfinity m = ovoidInfinity m := by
  by_cases h1 : r = 1
  · rw [h1]
    exact one_smul _ _
  · have h := (suzuki_root_unique_ovoid_fixed m hm r h1).1
    exact Subtype.ext h

theorem fixSet_root (m : ℕ) (hm : 0 < m) :
    fixSet (SzOvoid m) (suzukiCoverRoot m : Subgroup (G m)) =
      {ovoidInfinity m} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · rw [mem_fixSet_iff_le_stabilizer]
    intro r hr
    exact root_fixes_infinity m hm ⟨r, hr⟩
  · intro p hp
    let r0 : suzukiCoverRoot m := suzukiCoverRootElement m 1 0
    have hr0 : r0 ≠ 1 := by
      intro h
      have hc := suzukiCoverRootElement_injective m 1 0 0 0
        (h.trans (suzukiCoverRootElement_zero_zero m).symm)
      exact one_ne_zero hc.1
    have hr0fix : (r0 : G m) • p = p := by
      have := (mem_fixSet_iff_le_stabilizer.mp hp) r0.2
      exact this
    have huniq := (suzuki_root_unique_ovoid_fixed m hm r0 hr0).2
    have hval : (Matrix.GeneralLinearGroup.toLin ((r0 : G m) : GL (Fin 4) (K m))).toLinearEquiv •
        p.val = p.val := by
      exact congrArg Subtype.val hr0fix
    exact Subtype.ext (huniq p.val p.property hval)

private theorem fixSet_conj (m : ℕ) (g : G m) (S : Subgroup (G m)) :
    fixSet (SzOvoid m) (S.map (MulAut.conj g).toMonoidHom) =
      g • fixSet (SzOvoid m) S := by
  ext p
  constructor
  · intro hp
    refine ⟨g⁻¹ • p, ?_, by simp⟩
    rw [mem_fixSet_iff_le_stabilizer] at hp ⊢
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    have hmem : MulAut.conj g s ∈ S.map (MulAut.conj g).toMonoidHom := ⟨s, hs, rfl⟩
    have h := hp hmem
    rw [MulAction.mem_stabilizer_iff] at h
    have := congrArg (fun q : SzOvoid m => g⁻¹ • q) h
    simpa [MulAut.conj_apply, mul_smul] using this
  · rintro ⟨q, hq, rfl⟩
    rw [mem_fixSet_iff_le_stabilizer] at hq ⊢
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [MulAction.mem_stabilizer_iff]
    have h := hq hs
    rw [MulAction.mem_stabilizer_iff] at h
    simpa [MulAut.conj_apply, mul_smul] using congrArg (fun z : SzOvoid m => g • z) h

theorem coe_sylow_smul (m : ℕ) (g : G m) (U : Sylow 2 (G m)) :
    ((g • U : Sylow 2 (G m)) : Subgroup (G m)) =
      (U : Subgroup (G m)).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

private theorem fixSet_sylow (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    ∃ α : SzOvoid m, fixSet (SzOvoid m) (U : Subgroup (G m)) = {α} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (suzukiCoverSylow m hm) U
  refine ⟨g • ovoidInfinity m, ?_⟩
  rw [← hg, coe_sylow_smul, fixSet_conj, suzukiCoverSylow_coe, fixSet_root m hm]
  simp

noncomputable def sylowPoint (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    SzOvoid m :=
  Classical.choose (fixSet_sylow m hm U)

theorem fixSet_sylowPoint (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    fixSet (SzOvoid m) (U : Subgroup (G m)) = {sylowPoint m hm U} :=
  Classical.choose_spec (fixSet_sylow m hm U)

theorem sylowPoint_smul (m : ℕ) (hm : 0 < m) (g : G m) (U : Sylow 2 (G m)) :
    sylowPoint m hm (g • U) = g • sylowPoint m hm U := by
  have hp : sylowPoint m hm U ∈ fixSet (SzOvoid m) (U : Subgroup (G m)) := by
    rw [fixSet_sylowPoint m hm U]
    simp
  have hmem : g • sylowPoint m hm U ∈
      fixSet (SzOvoid m) ((U : Subgroup (G m)).map
        (MulAut.conj g).toMonoidHom) := by
    rw [fixSet_conj, fixSet_sylowPoint m hm U]
    exact Set.smul_mem_smul_set (by simp)
  rw [← coe_sylow_smul] at hmem
  rw [fixSet_sylowPoint m hm (g • U)] at hmem
  exact hmem.symm

theorem sylowPoint_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (sylowPoint m hm) := by
  haveI : MulAction.IsMultiplyPretransitive (G m) (SzOvoid m) 2 :=
    suzuki_ovoid_two_transitive m
  haveI : MulAction.IsPretransitive (G m) (SzOvoid m) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  intro p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (ovoidInfinity m) p
  refine ⟨g • suzukiCoverSylow m hm, ?_⟩
  have hroot : sylowPoint m hm (suzukiCoverSylow m hm) = ovoidInfinity m := by
    have h := fixSet_sylowPoint m hm (suzukiCoverSylow m hm)
    rw [suzukiCoverSylow_coe, fixSet_root m hm] at h
    simpa using h.symm
  rw [sylowPoint_smul, hroot, hg]

theorem card_sylow_eq_ovoid (m : ℕ) (hm : 0 < m) :
    Nat.card (Sylow 2 (G m)) = Nat.card (SzOvoid m) := by
  have hS :=
    (CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut.normalizer_and_card_sylow
      m hm).2
  rw [hS, suzuki_ovoid_card m]
  change Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut.rootSub m) + 1 =
    (2 ^ (2 * m + 1)) ^ 2 + 1
  rw [← card_root m hm]
  congr 1

noncomputable def sylowPointEquiv (m : ℕ) (hm : 0 < m) :
    Sylow 2 (G m) ≃ SzOvoid m := by
  haveI : Finite (Sylow 2 (G m)) := SuzukiTorusData.sylow_finite
  exact Equiv.ofBijective (sylowPoint m hm)
    ((Nat.bijective_iff_surjective_and_card (sylowPoint m hm)).mpr
      ⟨sylowPoint_surjective m hm, card_sylow_eq_ovoid m hm⟩)

private theorem ovoid_fixes_le_two (m : ℕ) (hm : 0 < m) {x : G m} (hx : x ≠ 1) :
    Nat.card {p : SzOvoid m // x • p = p} ≤ 2 := by
  classical
  letI : Fintype (SzOvoid m) := Fintype.ofFinite _
  by_contra h
  have h2 : 2 < Fintype.card {p : SzOvoid m // x • p = p} := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  exact suzuki_ovoid_three_point_free m hm x hx a.val b.val c.val
    (fun h => hab (Subtype.ext h)) (fun h => hac (Subtype.ext h))
    (fun h => hbc (Subtype.ext h)) ⟨a.2, b.2, c.2⟩

theorem fixes_le_two_model (m : ℕ) (hm : 0 < m) :
    ∀ x : G m, x ≠ 1 → Nat.card {U : Sylow 2 (G m) // x • U = U} ≤ 2 := by
  intro x hx
  let e : {U : Sylow 2 (G m) // x • U = U} ≃ {p : SzOvoid m // x • p = p} :=
    (sylowPointEquiv m hm).subtypeEquiv (fun U => by
      change (x • U = U) ↔ (x • sylowPointEquiv m hm U = sylowPointEquiv m hm U)
      rw [show sylowPointEquiv m hm U = sylowPoint m hm U from rfl]
      rw [← sylowPoint_smul]
      exact (sylowPointEquiv m hm).injective.eq_iff.symm)
  exact (Nat.card_congr e).trans_le (ovoid_fixes_le_two m hm hx)

theorem root_regular_point (m : ℕ) (hm : 0 < m) {a b : SzOvoid m}
    (ha : a ≠ ovoidInfinity m) (hb : b ≠ ovoidInfinity m) :
    ∃! r : suzukiCoverRoot m, r • a = b := by
  have ha' : (a.val : Projectivization (K m) (Fin 4 → K m)) ≠
      Projectivization.mk (K m) ![1, 0, 0, 0] (by simp) := fun h => ha (Subtype.ext h)
  have hb' : (b.val : Projectivization (K m) (Fin 4 → K m)) ≠
      Projectivization.mk (K m) ![1, 0, 0, 0] (by simp) := fun h => hb (Subtype.ext h)
  obtain ⟨r, hr, huniq⟩ := suzukiRootClosure_regular_on_ovoid_complement m
    (suzukiCoverTits m) (suzukiCoverTits_apply m) a.val b.val a.property b.property ha' hb'
  let rR : suzukiCoverRoot m := (suzukiCoverRootBridge m).symm r
  refine ⟨rR, ?_, ?_⟩
  · exact Subtype.ext hr
  · intro s hs
    apply (suzukiCoverRootBridge m).injective
    exact huniq ((suzukiCoverRootBridge m) s) (congrArg Subtype.val hs)

private theorem sylowPoint_rootSylow (m : ℕ) (hm : 0 < m) :
    sylowPoint m hm (suzukiCoverSylow m hm) = ovoidInfinity m := by
  have h := fixSet_sylowPoint m hm (suzukiCoverSylow m hm)
  rw [suzukiCoverSylow_coe, fixSet_root m hm] at h
  simpa using h.symm

theorem sylowPoint_eq_smul_infinity (m : ℕ) (hm : 0 < m) {U : Sylow 2 (G m)} {g : G m}
    (hg : g • suzukiCoverSylow m hm = U) :
    sylowPoint m hm U = g • ovoidInfinity m := by
  rw [← hg, sylowPoint_smul, sylowPoint_rootSylow m hm]

private theorem inv_smul_ovoidInfinity_ne (m : ℕ) {g : G m} {p : SzOvoid m}
    (hp : p ≠ g • ovoidInfinity m) : g⁻¹ • p ≠ ovoidInfinity m := by
  intro h
  apply hp
  calc p = g • (g⁻¹ • p) := by rw [← mul_smul, mul_inv_cancel, one_smul]
    _ = g • ovoidInfinity m := by rw [h]

theorem coe_eq_map_root_conj (m : ℕ) (hm : 0 < m) {U : Sylow 2 (G m)} {g : G m}
    (hg : g • suzukiCoverSylow m hm = U) :
    (U : Subgroup (G m)) = (suzukiCoverRoot m).map (MulAut.conj g).toMonoidHom := by
  have h := coe_sylow_smul m g (suzukiCoverSylow m hm)
  rw [hg] at h
  exact h

theorem normalizer_eq_map_root_conj (m : ℕ) (hm : 0 < m) {U : Sylow 2 (G m)} {g : G m}
    (hg : g • suzukiCoverSylow m hm = U) :
    Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) =
      (Subgroup.normalizer ((suzukiCoverRoot m : Subgroup (G m)) : Set (G m))).map
        (MulAut.conj g).toMonoidHom := by
  rw [coe_eq_map_root_conj m hm hg,
    Subgroup.map_equiv_normalizer_eq (suzukiCoverRoot m) (MulAut.conj g)]

private theorem exists_root_conj_of_smul_eq (m : ℕ) (hm : 0 < m) {U V W : Sylow 2 (G m)}
    {g : G m} (hg : g • suzukiCoverSylow m hm = U) {u : U}
    (hu : (u : G m) • V = W) :
    ∃ r : suzukiCoverRoot m,
      (r : G m) • (g⁻¹ • sylowPoint m hm V) = g⁻¹ • sylowPoint m hm W ∧
      (u : G m) = g * (r : G m) * g⁻¹ := by
  let pV : SzOvoid m := sylowPoint m hm V
  let pW : SzOvoid m := sylowPoint m hm W
  have hupoint : (u : G m) • pV = pW := by
    have h := congrArg (sylowPointEquiv m hm) hu
    change sylowPoint m hm ((u : G m) • V) = pW at h
    rw [sylowPoint_smul m hm (u : G m) V] at h
    exact h
  have humem : (u : G m) ∈ (U : Subgroup (G m)) := u.2
  rw [coe_eq_map_root_conj m hm hg] at humem
  obtain ⟨r', hr', hconj⟩ := Subgroup.mem_map.mp humem
  have hconj' : g * r' * g⁻¹ = (u : G m) := by
    simpa [MulAut.conj_apply] using hconj
  let a : SzOvoid m := g⁻¹ • pV
  let b : SzOvoid m := g⁻¹ • pW
  have hr'point : (⟨r', hr'⟩ : suzukiCoverRoot m) • a = b := by
    change (r' : G m) • a = b
    have h1 : g • ((r' : G m) • a) = g • b := by
      calc g • ((r' : G m) • a)
          = (g * r' * g⁻¹) • (g • a) := by simp [mul_smul]
        _ = (u : G m) • pV := by rw [hconj']; simp [a]
        _ = pW := hupoint
        _ = g • b := by simp [b]
    exact MulAction.injective g h1
  exact ⟨⟨r', hr'⟩, hr'point, hconj'.symm⟩

private theorem exists_root_regular (m : ℕ) (hm : 0 < m) {U V W : Sylow 2 (G m)} {g : G m}
    (hg : g • suzukiCoverSylow m hm = U) (hV : V ≠ U) (hW : W ≠ U) :
    ∃ r : suzukiCoverRoot m,
      (r : G m) • (g⁻¹ • sylowPoint m hm V) = g⁻¹ • sylowPoint m hm W ∧
      ∀ u : U, (u : G m) • V = W → (u : G m) = g * (r : G m) * g⁻¹ := by
  let pV : SzOvoid m := sylowPoint m hm V
  let pW : SzOvoid m := sylowPoint m hm W
  have hpU : sylowPoint m hm U = g • ovoidInfinity m := sylowPoint_eq_smul_infinity m hm hg
  have hpV : pV ≠ g • ovoidInfinity m := by
    intro h
    exact hV (by
      apply (sylowPointEquiv m hm).injective
      change sylowPoint m hm V = sylowPoint m hm U
      exact h.trans hpU.symm)
  have hpW : pW ≠ g • ovoidInfinity m := by
    intro h
    exact hW (by
      apply (sylowPointEquiv m hm).injective
      change sylowPoint m hm W = sylowPoint m hm U
      exact h.trans hpU.symm)
  let a : SzOvoid m := g⁻¹ • pV
  let b : SzOvoid m := g⁻¹ • pW
  have ha : a ≠ ovoidInfinity m := inv_smul_ovoidInfinity_ne m hpV
  have hb : b ≠ ovoidInfinity m := inv_smul_ovoidInfinity_ne m hpW
  obtain ⟨r, hr, huniq⟩ := root_regular_point m hm ha hb
  refine ⟨r, hr, ?_⟩
  intro u hu
  obtain ⟨r', hr'point, hconj'⟩ := exists_root_conj_of_smul_eq m hm hg hu
  have hreq : r' = r := huniq r' hr'point
  have hr'val : (r' : G m) = (r : G m) := congrArg Subtype.val hreq
  calc (u : G m) = g * (r' : G m) * g⁻¹ := hconj'
    _ = g * (r : G m) * g⁻¹ := by rw [hr'val]

theorem regular_sylow (m : ℕ) (hm : 0 < m) :
    ∀ U V W : Sylow 2 (G m), V ≠ U → W ≠ U →
      ∃! u : U, (u : G m) • V = W := by
  intro U V W hV hW
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G m) (suzukiCoverSylow m hm) U
  obtain ⟨r, hr, hcanon⟩ := exists_root_regular m hm hg hV hW
  have hUcoe := coe_eq_map_root_conj m hm hg
  have hmem : g * (r : G m) * g⁻¹ ∈ (U : Subgroup (G m)) := by
    rw [hUcoe]
    exact ⟨(r : G m), r.2, by simp [MulAut.conj_apply, mul_assoc]⟩
  let u : U := ⟨g * (r : G m) * g⁻¹, hmem⟩
  have huV : (u : G m) • V = W := by
    apply (sylowPointEquiv m hm).injective
    change sylowPoint m hm ((u : G m) • V) = sylowPoint m hm W
    rw [sylowPoint_smul m hm (u : G m) V]
    change (g * (r : G m) * g⁻¹) • sylowPoint m hm V = sylowPoint m hm W
    calc (g * (r : G m) * g⁻¹) • sylowPoint m hm V
        = g • ((r : G m) • (g⁻¹ • sylowPoint m hm V)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • sylowPoint m hm W) := by rw [hr]
      _ = sylowPoint m hm W := by rw [← mul_smul, mul_inv_cancel, one_smul]
  refine ⟨u, huV, fun u' hu' => ?_⟩
  apply Subtype.ext
  exact hcanon u' hu'

@[instance_reducible]
private noncomputable def sylowNormalizerAction (m : ℕ) (U : Sylow 2 (G m)) :
    MulAction ↥(Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)))
      {P : Sylow 2 (G m) // P ≠ U} where
  smul n P := ⟨(n : G m) • P.1, by
    intro h
    apply P.2
    have hn : (n : G m) • U = U := (Sylow.smul_eq_iff_mem_normalizer).mpr n.2
    have hn' : (n : G m)⁻¹ • U = U := by
      simpa using congrArg (fun X : Sylow 2 (G m) => (n : G m)⁻¹ • X) hn.symm
    have h' := congrArg (fun X : Sylow 2 (G m) => (n : G m)⁻¹ • X) h
    simpa [hn'] using h'⟩
  one_smul P := Subtype.ext
    (one_smul ↥(Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))) P.1)
  mul_smul n n' P := Subtype.ext (mul_smul n n' P.1)

private theorem card_other_sylow (m : ℕ) (hm : 0 < m) (U : Sylow 2 (G m)) :
    Nat.card {P : Sylow 2 (G m) // P ≠ U} = q m ^ 2 := by
  classical
  have hcardS : Nat.card (Sylow 2 (G m)) = q m ^ 2 + 1 := by
    rw [card_sylow_eq_ovoid m hm, suzuki_ovoid_card]
  haveI : Finite (Sylow 2 (G m)) := SuzukiTorusData.sylow_finite
  letI : Fintype (Sylow 2 (G m)) := Fintype.ofFinite _
  have h : Nat.card {P : Sylow 2 (G m) // P ≠ U} = Nat.card (Sylow 2 (G m)) - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Set.card_ne_eq U
  omega

private theorem card_inf_normalizer_aux (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) :
    Nat.card ↥(Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
        Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) * q m ^ 2 =
      Nat.card (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))) := by
  classical
  let N := Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))
  let D := N ⊓ Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))
  letI : MulAction ↥N {P : Sylow 2 (G m) // P ≠ U} := sylowNormalizerAction m U
  have htrans : MulAction.IsPretransitive ↥N {P : Sylow 2 (G m) // P ≠ U} :=
    ⟨fun P Q => by
      obtain ⟨u, hu, -⟩ := regular_sylow m hm U P.1 Q.1 P.2 Q.2
      exact ⟨⟨(u : G m), Subgroup.le_normalizer u.2⟩, Subtype.ext hu⟩⟩
  letI : MulAction.IsPretransitive ↥N {P : Sylow 2 (G m) // P ≠ U} := htrans
  let Vbar : {P : Sylow 2 (G m) // P ≠ U} := ⟨V, hUV.symm⟩
  have hidx := MulAction.index_stabilizer_of_transitive (↥N) Vbar
  let e : MulAction.stabilizer ↥N Vbar ≃ ↥D :=
    { toFun := fun w => ⟨(w.1 : G m), by
        refine ⟨w.1.2, ?_⟩
        have h : ((w.1 : G m) • V : Sylow 2 (G m)) = V := congrArg Subtype.val w.2
        exact (Sylow.smul_eq_iff_mem_normalizer).mp h⟩
      invFun := fun d => ⟨⟨(d.1 : G m), d.2.1⟩, by
        apply Subtype.ext
        exact (Sylow.smul_eq_iff_mem_normalizer).mpr d.2.2⟩
      left_inv := fun w => rfl
      right_inv := fun d => rfl }
  calc Nat.card D * q m ^ 2
      = Nat.card (MulAction.stabilizer ↥N Vbar) * q m ^ 2 := by
        rw [← Nat.card_congr e]
    _ = Nat.card (MulAction.stabilizer ↥N Vbar) *
          (MulAction.stabilizer ↥N Vbar).index := by
        rw [hidx, card_other_sylow m hm U]
    _ = Nat.card N := Subgroup.card_mul_index _

theorem card_inf_normalizer (m : ℕ) (hm : 0 < m) {U V : Sylow 2 (G m)}
    (hUV : U ≠ V) :
    Nat.card ↥(Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) = q m - 1 := by
  have haux := card_inf_normalizer_aux m hm hUV
  have hN : Nat.card (Subgroup.normalizer ((U : Subgroup (G m)) : Set (G m))) =
      q m ^ 2 * (q m - 1) := card_normalizer_sylow m hm U
  have hfinal : q m ^ 2 * Nat.card ↥(Subgroup.normalizer
      ((U : Subgroup (G m)) : Set (G m)) ⊓
      Subgroup.normalizer ((V : Subgroup (G m)) : Set (G m))) = q m ^ 2 * (q m - 1) := by
    rw [mul_comm, haux, hN]
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hfinal

end CFSG.LocalAnalysis.UniquenessCase.UC22.SzPointModel

end
