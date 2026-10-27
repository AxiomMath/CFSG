module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Good
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6TwistedRoot
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover

public section

namespace CFSG.StandardType

namespace AutSt

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem odd_card_of_pow_three {Q : Type*} [Group Q] [Finite Q] (h : ∀ a : Q, a ^ 3 = 1) :
    Odd (Nat.card Q) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
  have h3 := orderOf_dvd_of_pow_eq_one (h a)
  rw [ha] at h3
  omega

section Graph


variable {K : Type} [Field K] [Finite K]

theorem isSimpleGroup_fixSub_twGraph {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup (fixSub (fieldActor (t := TwistTag.E6) σ σ)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hσ0, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hf hK
    (σ := σ.toRingHom) hσ
  obtain ⟨-, ⟨η, hη, -, hJC, hfixJ, hJs, -⟩, -⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf
      (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K hk hK σ.toRingHom hσ
  have hησ : η = fieldActor (t := TwistTag.E6) σ σ :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη, hσ0])
  have hfix : fixSub (fieldActor (t := TwistTag.E6) σ σ) =
      ((twistedFixedGroup TwistTag.E6 (RingHom.eqLocusField σ.toRingHom (RingHom.id K))
        (RingHom.id _)).map (baseChangeGL (algebraMap
          (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) K))).subgroupOf
            (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    ext g
    rw [mem_fixSub, Subgroup.mem_subgroupOf, ← hfixJ g, hησ]
  rw [hfix]
  exact isSimpleGroup_subgroupOf hJC hJs

omit
    [Finite K] in
theorem charP_two_of_card_sq {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (show 1 ≤ 2 * f by omega) (by rw [hK, ← pow_mul, mul_comm])

theorem goodAut_twGraph {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {r : twistedE6RootGroup K σ} (g : twistedE6RootGroup K σ)
    {s : K} (hs : σ s = s)
    (hgr : ((g * r * g⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((xPar (rootOperatorFamily .E6) twE6Top s : adjointGroup .E6 K) : ModGL .E6 K))
    (a : twistedE6RootGroup K σ)
    (ha : (a : ModGL TwistTag.E6.tag K) =
      ((xPar (rootOperatorFamily .E6) (Pi.single (e6Node 3) 1) (1 : K) *
        xPar (rootOperatorFamily .E6) (-Pi.single (e6Node 3) 1) (1 : K) : adjointGroup .E6 K) :
          ModGL .E6 K)) :
    GGGoodAut r (fieldActor (t := TwistTag.E6) σ σ) := by
  have : CharP K 2 := charP_two_of_card_sq hf hK
  have key : ∀ x : adjointGroup .E6 K, Units.map (entrywiseHom σ.toRingHom) (x : ModGL .E6 K) =
      (entrywiseAdjointAut .E6 σ x : ModGL .E6 K) := fun x => (coe_entrywiseAdjointAut .E6 σ x).symm
  have ha3 : orderOf a = 3 := by
    rw [← Subgroup.orderOf_coe a]
    refine (congrArg orderOf ha).trans ((Subgroup.orderOf_coe _).trans ?_)
    exact orderOf_xPar_mul_xPar_neg (F := rootOperatorFamily .E6) (K := K) (i := e6Node 3)
      (k := e6Node 1) (by decide)
  refine goodAut_of_fixed_simple (isSimpleGroup_fixSub_twGraph hf hK σ hσ) g ?_ a ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [coe_fieldActor, hgr]
    exact (key _).trans (congrArg Subtype.val
      ((entrywiseAdjointAut_xPar σ twE6Top s).trans (by rw [hs])))
  · apply Subtype.ext
    rw [coe_fieldActor, ha]
    exact (key _).trans (congrArg Subtype.val (by
      rw [map_mul, entrywiseAdjointAut_xPar_one, entrywiseAdjointAut_xPar_one]))
  · apply Subtype.ext
    change (a : ModGL TwistTag.E6.tag K) *
        ((g * r * g⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((g * r * g⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (a : ModGL TwistTag.E6.tag K)
    rw [ha, hgr]
    exact congrArg Subtype.val
      (((commute_twE6Top_single (F := rootOperatorFamily .E6) s 1).symm.mul_left
        (commute_twE6Top_neg_single s 1).symm).eq)
  · intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  · rw [ha3]
    decide

end Graph

end AutSt

end CFSG.StandardType
