module

public import CFSG.Quasithin.Recognition.WBN.Weyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm
public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalModel
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Levi
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
import CFSG.LieType.Chevalley.GraphFixedParabolicCells
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqCard
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin.WBN

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.Sec53F.TriD4
  CFSG.LocalAnalysis.EvenBN.TrialityD4
open scoped Pointwise

private lemma d4_torus_range_eq
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (modelData hf K σ (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c) hσ hK
      (CFSG.Quasithin.H13.F431.D4q.NFq.card_d4k σ hf hK hσ)).torus.range =
      (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  change (Model.ctorus σ (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c)).range = _
  exact Model.ctorus_range σ _

private lemma d4_H_odd
    {K : Type} [Field K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Odd (Nat.card ↥((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hcard : Nat.card ↥((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = ((2 ^ f) ^ 3 - 1) * (2 ^ f - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
      (K := graphFixedRootGroup TwistTag.D4 K σ.toRingHom) inf_le_right).toEquiv]
    exact (triality_both_orientations_exact_finite_order 2 f
      Nat.prime_two hf K hK 1 (Or.inl rfl) σ.toRingHom (by simpa using hσ)).2.1
  rw [hcard]
  have h1 : Odd ((2 ^ f) ^ 3 - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow 3 (2 ^ f) (by positivity)) ?_ odd_one
    rw [← pow_mul]
    exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.mp (by omega)⟩
  have h2 : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two,
      Nat.pos_iff_ne_zero.mp (by omega)⟩) odd_one
  exact h1.mul h2

private lemma d4_sup_U_H
    {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) :
    CFSG.Quasithin.H13.F431.D4q.Struct.Ust σ ⊔
        (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      CFSG.Quasithin.H13.F431.D4q.Struct.Pst0 σ ⊓
        CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ := by
  rw [← CFSG.Quasithin.F112R.St84.normalizer_Ust_eq_inf σ]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ (d4_H_le σ)
    intro u hu
    exact Subgroup.le_normalizer hu
  · intro g hg
    obtain ⟨u, hu, h, hh, rfl⟩ := d4_B_eq σ g hg
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hh)

private lemma d4_cu_mem_Pst0
    {K : Type} [Field K] (σ : K ≃+* K) :
    Model.cu σ ∈ CFSG.Quasithin.H13.F431.D4q.Struct.Pst0 σ :=
  Subgroup.mem_subgroupOf.mpr
    ((canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (t := TwistTag.D4)
      (K := K) (σ := σ.toRingHom) σ.surjective
      (J := {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
      (a := (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))).2 (Set.mem_singleton _))

private lemma d4_cv_mem_Pst1
    {K : Type} [Field K] (σ : K ≃+* K) :
    Model.cv σ ∈ CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ :=
  Subgroup.mem_subgroupOf.mpr
    ((canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (t := TwistTag.D4)
      (K := K) (σ := σ.toRingHom) σ.surjective
      (J := {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)})
      (a := (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))).2 (Set.mem_singleton _))

private lemma d4_cu_mem_normalizer
    {K : Type} [Field K] (σ : K ≃+* K) :
    Model.cu σ ∈ Subgroup.normalizer
      (((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        Subgroup (CFSG.Quasithin.H13.F431.D4q.Struct.Cm σ)) :
        Set (CFSG.Quasithin.H13.F431.D4q.Struct.Cm σ)) := by
  rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) inf_le_right]
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
    ⟨CFSG.Quasithin.B42D4.nA_mem σ,
      canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus
        (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) ⟨0, by decide⟩⟩)

private lemma d4_cv_mem_normalizer
    {K : Type} [Field K] (σ : K ≃+* K) :
    Model.cv σ ∈ Subgroup.normalizer
      (((graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        Subgroup (CFSG.Quasithin.H13.F431.D4q.Struct.Cm σ)) :
        Set (CFSG.Quasithin.H13.F431.D4q.Struct.Cm σ)) := by
  rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) inf_le_right]
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
    ⟨CFSG.Quasithin.B42D4.nB_mem σ,
      canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus
        (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) ⟨1, by decide⟩⟩)

private lemma d4_cu_cv_cube_inverts
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {h : CFSG.Quasithin.H13.F431.D4q.Struct.Cm σ}
    (hh : h ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    (Model.cu σ * Model.cv σ) ^ 3 * h * ((Model.cu σ * Model.cv σ) ^ 3)⁻¹ = h⁻¹ := by
  let d := modelData hf K σ (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c) hσ hK
    (CFSG.Quasithin.H13.F431.D4q.NFq.card_d4k σ hf hK hσ)
  have hu : d.u = Model.cu σ := rfl
  have hv : d.v = Model.cv σ := rfl
  have hw : d.w₀ = (Model.cu σ * Model.cv σ) ^ 3 := by
    rw [d.w₀_eq]
    simp only [hu, hv, pow_succ, pow_zero, one_mul, mul_assoc]
  have hh' : h ∈ d.torus.range := by
    rw [show d.torus = (modelData hf K σ
      (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c) hσ hK
      (CFSG.Quasithin.H13.F431.D4q.NFq.card_d4k σ hf hK hσ)).torus from rfl,
      d4_torus_range_eq (σ := σ) hf hK hσ]
    exact hh
  obtain ⟨x, rfl⟩ := hh'
  rw [← hw, show d.w₀⁻¹ = d.w₀ from inv_eq_of_mul_eq_one_right d.w₀_mul_self]
  exact d.w₀_torus_eq x

theorem invertsByWeyl_d4
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {m : ℕ} (hm : Odd m) :
    InvertsByWeyl (CFSG.Quasithin.H13.F431.D4q.Struct.Pst0 σ)
      (CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ) m := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hU : IsPGroup 2 (CFSG.Quasithin.H13.F431.D4q.Struct.Ust σ) := (d4_sylow σ).2.1
  have hUn : ((CFSG.Quasithin.H13.F431.D4q.Struct.Ust σ).subgroupOf
      (CFSG.Quasithin.H13.F431.D4q.Struct.Pst0 σ ⊓
        CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (le_of_eq (CFSG.Quasithin.F112R.St84.normalizer_Ust_eq_inf σ).symm)
  refine InvertsByWeyl.of_torus (U := CFSG.Quasithin.H13.F431.D4q.Struct.Ust σ)
    (H := (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (P₀ := CFSG.Quasithin.H13.F431.D4q.Struct.Pst0 σ)
    (P₁ := CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ) hm hU hUn ?_
    (d4_H_odd σ hf hK hσ) (n₀ := Model.cu σ) (n₁ := Model.cv σ)
    (d4_cu_mem_Pst0 σ) (d4_cv_mem_Pst1 σ) (d4_cu_mem_normalizer σ)
    (d4_cv_mem_normalizer σ) 3 ?_
  · exact d4_sup_U_H σ
  · exact fun x hx _ => d4_cu_cv_cube_inverts σ hf hK hσ hx

theorem allInvertsByWeyl_d4
    {f : ℕ} (hf : 1 ≤ f) {m : ℕ} (hm : Odd m) :
    AllInvertsByWeyl (CFSG.Quasithin.IsLieOverTwo .trialityD4 0 f) m := by
  intro Y _ hY T M₁ M₂ hYam
  have hChev : ChevalleyExceptionalModel Y .trialityD4 2 f :=
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY (by decide)).2
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hChev
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact InvertsByWeyl.of_isYAmalgamPair
    (CFSG.Quasithin.F112R.St84.isYAmalgamPair_d4 σ hf hK hσ)
    (invertsByWeyl_d4 σ hf hK hσ hm) e hYam

end CFSG.Quasithin.WBN
