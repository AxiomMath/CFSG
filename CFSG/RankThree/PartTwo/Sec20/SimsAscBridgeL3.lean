module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3Aut
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3Group
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3Linear
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.TwoElementSquare

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem rAlpha_inf_yAlpha_eq_bot_of_L3 {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    {i j : Fin 4} {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) {m : ℕ} (hm : Odd m)
    (e : ↥(yAlpha M X T c) ≃* projSL 3 (GaloisField 2 m)) :
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
  set K₀ := oThreePrimeYR M X T c with hK₀def
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
  have hkerO : ψ.ker ≤ CFSG.pCore 2 ↥K := by
    intro k hk
    have hk1 : π (Subgroup.inclusion hKYR k) = 1 := congrArg Subtype.val hk
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
    have hkK₀ : (k : G) ∈ K ⊓ K₀ := ⟨k.2, ⟨_, hk1, rfl⟩⟩
    have hkO := inf_inSubgroup_pPrimeCore_le hset hKYR hkK₀
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hkO
  have hker2 : IsPGroup 2 ψ.ker := by
    intro k
    obtain ⟨c', hc'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      ⟨(k : ↥K), (Subgroup.mem_map_iff_mem K.subtype_injective).mpr (hkerO k.2)⟩
    refine ⟨c', Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hc'
    simpa using this
  have hdvdY : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card ↥Yb := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h2
    obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hkerO
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have hrange : Nat.card ψ.range = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * t := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [← h2, h1, ht]
      ring
    exact (Dvd.intro t hrange.symm).trans (Subgroup.card_subgroup_dvd_card ψ.range)
  have hYcard : Nat.card ↥Yb = Nat.card (projSL 3 (GaloisField 2 m)) :=
    Nat.card_congr e.toEquiv
  rcases hset.kType with ⟨n, hn, ⟨eK⟩⟩ | ⟨n, hn, hn0, ⟨eK⟩⟩
  swap
  ·
    exfalso
    have h5 : 5 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Nat.card_congr eK.toEquiv]
      exact five_dvd_card_projSL2 hn hn0.ne'
    exact not_five_dvd_card_projSL3 hm (hYcard ▸ h5.trans hdvdY)
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
  set E : ↥Yb ≃* SL(3, GaloisField 2 m) := e.trans (slThreeEquivProjSL hm).symm with hE
  set ρ : ↥K →* SL(3, GaloisField 2 m) := E.toMonoidHom.comp ψ with hρ
  set D' := D.map E.toMonoidHom with hD'def
  have hD'2 : IsPGroup 2 D' := hD2.map _
  have hD'1 : D' ≠ ⊥ := by
    intro h
    exact hD1 ((Subgroup.map_eq_bot_iff_of_injective _ E.injective).mp h)
  have hρker : IsPGroup 2 ρ.ker := by
    have : ρ.ker = ψ.ker := by
      ext k
      simp only [hρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact E.map_eq_one_iff
    rw [this]
    exact hker2
  have hρD : ρ.range ≤ Subgroup.normalizer (D' : Set SL(3, GaloisField 2 m)) := by
    rintro _ ⟨k, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := hx
    have hkd := (Subgroup.mem_normalizer_iff.mp (hψD ⟨k, rfl⟩) d).mp hd
    refine ⟨ψ k * d * (ψ k)⁻¹, hkd, ?_⟩
    simp [hρ]
  have hsq : ∀ y : ↥K, (∃ a : ℕ, y ^ 2 ^ a = 1) →
      y ^ 2 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
    rintro y ⟨a, ha⟩
    rw [QuotientGroup.ker_mk']
    exact L3Linear.sq_mem_pCore_of_le_normalizer ρ hρker hD'2 hD'1 hρD ha
  obtain ⟨x, hx⟩ := exists_orderOf_eq_four_projSL3 hn
  have hx4 : eK.symm x ^ 2 ^ 2 = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hx, pow_orderOf_eq_one, map_one]
  have hx2 := CFSG.sq_eq_one_of_surjective_of_sq_mem_ker _ (QuotientGroup.mk'_surjective _) hsq
    ⟨2, hx4⟩
  have hdvd : orderOf (eK.symm x) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [MulEquiv.orderOf_eq, hx] at hdvd
  norm_num at hdvd

end AscBridge

open AscBridge in
theorem step204AscL3Even_holds : Step204AscL3Even := by
  intro G _ _ A M L N c T i j P hset X hX _ hm _ _ ⟨m, hmo, ⟨e⟩⟩
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, Ψ, hS, hL⟩ := hyp1411_of_simple hset hX hnab hG₀
  have hRY := rAlpha_inf_yAlpha_eq_bot_of_L3 hset hX hmo e
  have hSL : ((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ⊓
      (perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) = ⊥ := by
    apply Subgroup.map_injective (f := Ψ.toMonoidHom) Ψ.injective
    rw [Subgroup.map_inf_eq _ _ _ Ψ.injective, hS, hL, hRY, Subgroup.map_bot]
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := asc82Item1411_L3odd ↥G₀ _ _ hhyp hmo
    (Or.inr ⟨(Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr hL).trans e)⟩) hSL
  exact covered_of_fourChar_normal hset hX
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1 hG₀ h12 h1 h2 hn1 hn2

end CFSG.RankThree.PartTwo.Sec20
