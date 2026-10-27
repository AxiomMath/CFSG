module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeU3Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSU)

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem rAlpha_inf_yAlpha_eq_bot_of_U3 {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    {i j : Fin 4} {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) {m : ℕ} (hm : 2 ≤ m)
    (e : ↥(yAlpha M X T c) ≃* projSU 3 2 m) :
    ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf
        (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map (QuotientGroup.mk'
          (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))) ⊓
      yAlpha M X T c = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  set Yb := yAlpha M X T c with hYbdef
  set Rb := (R.subgroupOf YR).map π with hRbdef
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKX : K ≤ X := le_sup_left.trans hKTX
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hKYR : K ≤ YR := hKY.trans le_sup_left
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRb2 : IsPGroup 2 Rb := (hR2.comap_subtype (K := YR)).map π
  let ψ : ↥K →* ↥Yb := (π.comp (Subgroup.inclusion hKYR)).codRestrict Yb
    fun k => ⟨Subgroup.inclusion hKYR k, hKY k.2, rfl⟩
  haveI : Group.IsPerfect ↥K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  set D := Rb.subgroupOf Yb with hDdef
  have hD2 : IsPGroup 2 D := hRb2.comap_subtype
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hψD : ψ.range ≤ Subgroup.normalizer (D : Set ↥Yb) := by
    rintro _ ⟨k, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun d hd => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hd ⊢
    obtain ⟨r, hr, hrd⟩ := Subgroup.mem_map.mp hd
    have hrR : (r : G) ∈ R := hr
    refine ⟨⟨k, hKYR k.2⟩ * r * ⟨k, hKYR k.2⟩⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKR k.2) r).mp hrR, ?_⟩
    rw [map_mul, map_mul, map_inv, hrd]
    rfl
  by_contra hne
  have hD1 : D ≠ ⊥ := by
    intro hD
    apply hne
    rw [eq_bot_iff]
    rintro z ⟨hzR, hzY⟩
    have hz : (⟨z, hzY⟩ : ↥Yb) ∈ D := hzR
    rw [hD, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz)
  have hbot := eq_bot_of_isPerfect_of_le_normalizer_U3 hm e hD2 hD1 (Group.IsPerfect.range ψ) hψD
  have hc3 := Res6.orderOf_c_of_setting204 hset
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hψc : ψ ⟨c, hcK⟩ ∈ ψ.range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hψc
  have h' : π ⟨c, hKYR hcK⟩ = 1 := congrArg Subtype.val hψc
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  have hdvd : orderOf (⟨c, hKYR hcK⟩ : ↥YR) ∣ Nat.card (CFSG.pPrimeCore 3 ↥YR) := by
    rw [← Subgroup.orderOf_mk _ h']
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hc3] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card hdvd

end AscBridge

open AscBridge in
theorem step204AscU3Even_holds : Step204AscU3Even := by
  intro G _ _ A M L N c T i j P hset X hX _ hm _ _ ⟨m, hme, hm0, ⟨e⟩⟩
  have hm2 : 2 ≤ m := by
    obtain ⟨k, rfl⟩ := hme
    omega
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, Ψ, hS, hL⟩ := hyp1411_of_simple hset hX hnab hG₀
  have hRY := rAlpha_inf_yAlpha_eq_bot_of_U3 hset hX hm2 e
  have hSL : ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ⊓
      (perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) = ⊥ := by
    apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
    rw [Subgroup.map_inf_eq _ _ _ Ψ.injective, hS, hL, hRY, Subgroup.map_bot]
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := asc82Item1411_U3even ↥G₀ _ _ hhyp hme hm2
    (Or.inr ⟨(Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr hL).trans e)⟩) hSL
  exact covered_of_fourChar_normal hset hX
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1 hG₀ h12 h1 h2 hn1 hn2

end CFSG.RankThree.PartTwo.Sec20
