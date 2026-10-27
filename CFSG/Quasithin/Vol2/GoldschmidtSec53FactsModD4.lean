module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Trans
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.Quasithin.H13.Sec53F.TriD4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.QuasithinUnique.Setup.X6 (normalizer_subgroupOf_eq')

set_option linter.unusedSectionVars false

section Pullback

variable {G : Type} [Group G] {C : Subgroup G}

theorem perfectCore_subgroupOf_map {N : Subgroup G} (hN : N ≤ C) :
    (perfectCore (N.subgroupOf C)).map C.subtype = perfectCore N := by
  rw [← BA.perfectCore_map_inj C.subtype C.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hN]

theorem mem_perfectCore_subgroupOf {N : Subgroup G} (hN : N ≤ C) (x : C) :
    x ∈ perfectCore (N.subgroupOf C) ↔ (x : G) ∈ perfectCore N := by
  rw [← perfectCore_subgroupOf_map hN]
  exact (Subgroup.mem_map_iff_mem C.subtype_injective).symm

theorem mem_centerOf_subgroupOf_iff {N : Subgroup G} (hN : N ≤ C) (x : C) :
    x ∈ centerOf (perfectCore (N.subgroupOf C)) ↔ (x : G) ∈ centerOf (perfectCore N) := by
  set X := perfectCore (N.subgroupOf C) with hXdef
  have hX : perfectCore N = X.map C.subtype := (perfectCore_subgroupOf_map hN).symm
  rw [hX]
  constructor
  · rintro ⟨hxX, hxC⟩
    refine ⟨⟨x, hxX, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg C.subtype (Subgroup.mem_centralizer_iff.1 hxC y hy)
  · rintro ⟨hxX, hxC⟩
    refine ⟨(Subgroup.mem_map_iff_mem C.subtype_injective).1 hxX,
      Subgroup.mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hxC (y : G) ⟨y, hy, rfl⟩

theorem trans_subgroupOf {N : Subgroup G} (hN : N ≤ C)
    (h : ∀ a ∈ centerOf (perfectCore N), ∀ a' ∈ centerOf (perfectCore N), a ≠ 1 → a' ≠ 1 →
      ∃ m ∈ N, m * a * m⁻¹ = a') :
    ∀ a ∈ centerOf (perfectCore (N.subgroupOf C)), ∀ a' ∈ centerOf (perfectCore (N.subgroupOf C)),
      a ≠ 1 → a' ≠ 1 → ∃ m ∈ N.subgroupOf C, m * a * m⁻¹ = a' := by
  intro a ha a' ha' h1 h1'
  obtain ⟨m, hm, hma⟩ := h (a : G) ((mem_centerOf_subgroupOf_iff hN a).1 ha) (a' : G)
    ((mem_centerOf_subgroupOf_iff hN a').1 ha') (fun e => h1 (Subtype.ext e))
    (fun e => h1' (Subtype.ext e))
  exact ⟨⟨m, hN hm⟩, Subgroup.mem_subgroupOf.2 hm, Subtype.ext hma⟩

end Pullback


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom

theorem P0_inf_P1 : P0 σ ⊓ P1 σ = graphFixedRootBorel TwistTag.D4 K τ₀ := by
  have hB : graphFixedRootBorel TwistTag.D4 K τ₀ ≤ P0 σ ⊓ P1 σ :=
    le_inf (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hA : P0 σ ⊓ P1 σ ≤ graphFixedRootGroup TwistTag.D4 K τ₀ :=
    inf_le_left.trans (graphFixedParabolic_le _ _ _ _)
  have hJ : {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection a) ∈ P0 σ ⊓ P1 σ} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun a ha => ?_
    have h0 := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).1
      (Subgroup.mem_inf.1 ha).1
    have h1 := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).1
      (Subgroup.mem_inf.1 ha).2
    have := congrArg Fin.val ((Set.mem_singleton_iff.1 h0).symm.trans (Set.mem_singleton_iff.1 h1))
    exact absurd this (by decide)
  rw [eq_graphFixedParabolic_of_le σ.surjective hB hA, hJ, graphFixedParabolic_empty]

theorem B1_le_normalizer_posUnipotent : graphFixedRootBorel TwistTag.D4 K τ₀ ≤
    Subgroup.normalizer
      (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set (ModGL TwistTag.D4.tag K)) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  rw [← (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1]
  exact inf_le_right

variable [CharP K 2] (hσ3 : σ.toRingHom ^ 3 = 1)

include hσ3 in
theorem lieFactsOf_core (hK4 : 4 ≤ Nat.card K) (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    Yam.LieFactsOf
      ((graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀))
      ((P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ₀))
      ((P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ₀)) := by
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K τ₀
  have hP0C : P0 σ ≤ graphFixedRootGroup TwistTag.D4 K τ₀ := graphFixedParabolic_le _ _ _ _
  have hP1C : P1 σ ≤ graphFixedRootGroup TwistTag.D4 K τ₀ := graphFixedParabolic_le _ _ _ _
  have hBC : graphFixedRootBorel TwistTag.D4 K τ₀ ≤ graphFixedRootGroup TwistTag.D4 K τ₀ :=
    graphFixedRootBorel_le _ _ _
  have hinf : (P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ₀) ⊓
      (P1 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ₀) =
        (graphFixedRootBorel TwistTag.D4 K τ₀).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K τ₀) := by
    rw [← P0_inf_P1 σ]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  refine ⟨⟨?_, trans_subgroupOf hP0C (trans_P0 σ hσ3 hK4),
    trans_subgroupOf hP1C (trans_P1 σ hσ3 hk4)⟩, ?_, ?_, ?_⟩
  · rw [hinf]
    have : Group.IsSolvable ↥(graphFixedRootBorel TwistTag.D4 K τ₀) :=
      isSolvable_graphFixedRootBorel (t := TwistTag.D4) (K := K) (σ := τ₀) σ.surjective
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hBC).toMonoidHom) (MulEquiv.injective _)
  · rw [hinf, normalizer_subgroupOf_eq' hUC]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨x.2, B1_le_normalizer_posUnipotent σ
      (Subgroup.mem_subgroupOf.1 hx)⟩)
  · exact fun x hx => (mem_perfectCore_subgroupOf hP0C x).2
      (posUnipotent_le_perfectCore_P0 σ hσ3 hK4 (Subgroup.mem_subgroupOf.1 hx))
  · exact fun x hx => (mem_perfectCore_subgroupOf hP1C x).2
      (posUnipotent_le_perfectCore_P1 σ hσ3 hk4 (Subgroup.mem_subgroupOf.1 hx))

omit [CharP K 2] in
theorem d4_lieFactsOf {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Yam.LieFactsOf
      ((graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀))
      ((graphFixedParabolic TwistTag.D4 K τ₀ {⟨0, by decide⟩}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀))
      ((graphFixedParabolic TwistTag.D4 K τ₀ {⟨1, by decide⟩}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀)) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c =>
    (ringHom_pow_three_apply σ.toRingHom c).trans (ringEquiv_cube_apply_eq hK hσ c)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact hq4.trans (Nat.le_self_pow (by norm_num) _)
  obtain ⟨-, -, -, -, -, k, hk, hcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two (by omega : 1 ≤ f) K hK
  have hkeq : trialityFixedField K τ₀ = k := by
    apply SetLike.ext'
    rw [hk]
    ext c
    simp [mem_trialityFixedField, hσ]
  have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀) := by
    rw [hkeq, hcard]
    exact hq4
  exact lieFactsOf_core σ hσ3 hK4 hk4

end CFSG.Quasithin.H13.Sec53F.TriD4
