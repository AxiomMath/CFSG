module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACTwE6Heart
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDescent
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaSmallThreeOdd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.USixTwo

noncomputable def twE6HeartQuot {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)) :
    ↥L →* twistedE6RootGroup K σ :=
  (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).toMonoidHom.comp
    (ggQuotHom θ)

theorem twE6HeartQuot_surjective {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)) :
    Function.Surjective (twE6HeartQuot θ) :=
  (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).surjective.comp
    (ggQuotHom_surjective θ)

theorem twE6HeartQuot_ker {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)) :
    (twE6HeartQuot θ).ker = Subgroup.center ↥L := by
  rw [twE6HeartQuot,
    MonoidHom.ker_comp_of_injective _ _
      (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).injective,
    ker_ggQuotHom]

theorem twE6HeartCenter_qmk_ne_one {L' : Type} [Group L'] [Finite L'] {z : L'}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : USixTwo.qmk L' z ≠ 1 := by
  intro h1
  have hz2 : z ∈ USixTwo.zTwo L' := (USixTwo.qmk_eq_one_iff).mp h1
  have h2 : orderOf z ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hz2.2
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have hcop : Nat.Coprime 3 (2 ^ Nat.card L') :=
    Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
  have h4 : orderOf z = 1 := by
    have hdvd : orderOf z ∣ Nat.gcd 3 (2 ^ Nat.card L') := Nat.dvd_gcd h3 h2
    rw [hcop.gcd_eq_one] at hdvd
    exact Nat.dvd_one.mp hdvd
  exact hz1 (orderOf_eq_one_iff.mp h4)

theorem twE6HeartCenter_qmk_mem_center {L' : Type} [Group L'] [Finite L'] {z : L'}
    (hz : z ∈ Subgroup.center L') : USixTwo.qmk L' z ∈ Subgroup.center (USixTwo.Qt L') := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨l, rfl⟩ := USixTwo.qmk_surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]

noncomputable def twE6HeartRecipe {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1) :
    USixTwo.Qt ↥L →* TwE6Delta.RecipeR K 1 :=
  ε.toMonoidHom.comp (USixTwo.qLift (twE6HeartQuot θ)
    (USixTwo.zTwo_le_ker (twE6HeartQuot_surjective θ)
      (exceptional_fixed_center_trivial TwistTag.E6 K σ)))

theorem twE6HeartRecipe_surjective {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1) :
    Function.Surjective (twE6HeartRecipe θ ε) := by
  unfold twE6HeartRecipe
  exact ε.surjective.comp
    (USixTwo.qLift_surjective
      (USixTwo.zTwo_le_ker (twE6HeartQuot_surjective θ)
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      (twE6HeartQuot_surjective θ))

theorem twE6HeartRecipe_ker_le_center {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1) :
    (twE6HeartRecipe θ ε).ker ≤ Subgroup.center (USixTwo.Qt ↥L) := by
  unfold twE6HeartRecipe
  rw [MonoidHom.ker_comp_of_injective _ _ ε.injective]
  exact USixTwo.qLift_ker_le_center
    (USixTwo.zTwo_le_ker (twE6HeartQuot_surjective θ)
      (exceptional_fixed_center_trivial TwistTag.E6 K σ))
    (le_of_eq (twE6HeartQuot_ker θ))

theorem twE6HeartRecipe_odd_ker {G : Type}
    [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1) :
    Odd (Nat.card (twE6HeartRecipe θ ε).ker) := by
  unfold twE6HeartRecipe
  rw [MonoidHom.ker_comp_of_injective _ _ ε.injective]
  exact USixTwo.qLift_odd_ker
    (USixTwo.zTwo_le_ker (twE6HeartQuot_surjective θ)
      (exceptional_fixed_center_trivial TwistTag.E6 K σ))
    (le_of_eq (twE6HeartQuot_ker θ))

theorem twE6HeartQuot_congr_ggBeta {G : Type}
    [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : Bs) (l : ↥L) :
    MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      (ggBeta L θ hN b) (twE6HeartQuot θ l) = twE6HeartQuot θ (ggGamma L hN b l) := by
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hψ : ∀ l : ↥L, twE6HeartQuot θ l = eR (ggQuotHom θ l) := fun l => rfl
  rw [hψ l, hψ (ggGamma L hN b l)]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  change eR (ggBeta L θ hN b (eR.symm (eR (ggQuotHom θ l)))) =
    eR (ggQuotHom θ (ggGamma L hN b l))
  rw [MulEquiv.symm_apply_apply]
  congr 1
  rw [ggBeta_eq, ggQuotHom_apply, ggLAut_apply, ggQuotHom_apply]
  exact congrArg (fun z : ↥L => θ (z : L ⧸ Subgroup.center L))
    (Subtype.ext (by rw [normalizerMonoidHom_coe, ggGamma_coe]))

theorem twE6HeartRecipe_exists_y {G : Type}
    [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1)
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hK1 : Nat.card K = (2 ^ 1) ^ 2) (hσ1 : ∀ c, σ c = c ^ 2 ^ 1)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hSlang : S ≤ TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g) :
    ∀ a ∈ (ggGamma L hN).range.map (USixTwo.qAutHom ↥L),
      ∃ y ∈ (TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g).map
        (MulAut.congr ε).toMonoidHom,
      ∀ l : USixTwo.Qt ↥L,
        y (twE6HeartRecipe θ ε l) = twE6HeartRecipe θ ε (a l) := by
  rintro a ⟨b, hb, rfl⟩
  obtain ⟨b0, rfl⟩ := hb
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  refine ⟨MulAut.congr ε (MulAut.congr eR (ggBeta L θ hN b0)), ?_, ?_⟩
  · refine Subgroup.mem_map_of_mem _ (hSlang ?_)
    rw [hSdef]
    refine Subgroup.mem_map_of_mem (MulAut.congr eR).toMonoidHom ?_
    rw [MonoidHom.range_eq_map]
    exact Subgroup.mem_map_of_mem (ggBeta L θ hN) (Subgroup.mem_top b0)
  · intro l
    have hx : ∀ l : ↥L, MulAut.congr eR (ggBeta L θ hN b0) (twE6HeartQuot θ l) =
        twE6HeartQuot θ (ggGamma L hN b0 l) :=
      fun l => twE6HeartQuot_congr_ggBeta θ hN b0 l
    have hq := USixTwo.qLift_qAut (USixTwo.zTwo_le_ker (twE6HeartQuot_surjective θ)
      (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      (ggGamma L hN b0) (MulAut.congr eR (ggBeta L θ hN b0)) hx l
    unfold twE6HeartRecipe
    rw [MonoidHom.comp_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.coe_toMonoidHom,
      MonoidHom.comp_apply]
    exact congrArg (fun z => ε z) hq

theorem twE6HeartRecipe_center_card
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1)
    (hK1 : Nat.card K = (2 ^ 1) ^ 2) (hperf : commutator ↥L = ⊤)
    {z : ↥L} (hzq : USixTwo.qmk ↥L z ≠ 1)
    (hzc : USixTwo.qmk ↥L z ∈ Subgroup.center (USixTwo.Qt ↥L)) (hz3 : z ^ 3 = 1) :
    Nat.card (Subgroup.center (USixTwo.Qt ↥L)) = 3 := by
  have hthree := SmallExc.TwE6DS3.card_center_eq_one_or_three (n := 1) le_rfl hK1
    (twE6HeartRecipe_surjective θ ε) (twE6HeartRecipe_ker_le_center θ ε)
    (USixTwo.qmk_perfect hperf) (twE6HeartRecipe_odd_ker θ ε)
  rcases hthree with h | h
  · exfalso
    have ho : orderOf (USixTwo.qmk ↥L z) = 3 := by
      refine orderOf_eq_prime ?_ hzq
      simpa using congrArg (USixTwo.qmk ↥L) hz3
    have hdvd : 3 ∣ Nat.card (Subgroup.center (USixTwo.Qt ↥L)) := by
      have h := orderOf_dvd_natCard
        (⟨USixTwo.qmk ↥L z, hzc⟩ : Subgroup.center (USixTwo.Qt ↥L))
      rwa [Subgroup.orderOf_mk, ho] at h
    rw [h] at hdvd
    norm_num at hdvd
  · exact h

theorem twE6HeartCenter_map_le_inf
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hA3 : IsPGroup 3 (ggGamma L hN).range)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {E : Subgroup (USixTwo.Qt ↥L)} (hE : IsElemAbelian 3 E)
    (hEfix : ∀ a ∈ (ggGamma L hN).range.map (USixTwo.qAutHom ↥L), ∀ e ∈ E, a e = e) :
    E ≤ (⊤ : Subgroup ↥(Bs ⊓ L)).map
      ((USixTwo.qmk ↥L).comp (Subgroup.inclusion inf_le_right)) := by
  intro e he
  obtain ⟨y, -, hyq, hy3, hyfix⟩ := USixTwo.exists_fixed_cube_lift
    (A := (ggGamma L hN).range) hA3 (H := ⊤) (fun a _ h _ => Subgroup.mem_top h)
    (by rw [Subgroup.map_top_of_surjective _ USixTwo.qmk_surjective]
        exact Subgroup.mem_top e)
    (fun a ha => hEfix (USixTwo.qAutHom ↥L a)
      (Subgroup.mem_map_of_mem (USixTwo.qAutHom ↥L) ha) e he)
    (hE.2 e he)
  have hyBs : (y : G) ∈ Bs := by
    refine hSC (y : G) ?_ ?_
    · show (y : G) ∈ Subgroup.centralizer (Bs : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro (b : G) hb
      have hmem : (⟨b, hb⟩ : ↥Bs) ∈ (⊤ : Subgroup ↥Bs) := Subgroup.mem_top _
      have hfixb := hyfix (ggGamma L hN ⟨b, hb⟩)
        (by simp [MonoidHom.range_eq_map])
      have hcoe := congrArg (fun z : ↥L => (z : G)) hfixb
      rw [ggGamma_coe] at hcoe
      calc b * (y : G) = b * (y : G) * b⁻¹ * b := by group
        _ = (y : G) * b := by rw [hcoe]
    · simpa using congrArg (fun z : ↥L => (z : G)) hy3
  exact Subgroup.mem_map.mpr ⟨⟨y, ⟨hyBs, y.2⟩⟩, Subgroup.mem_top _, hyq⟩

theorem twE6HeartCenter_center_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK1 : Nat.card K = (2 ^ 1) ^ 2)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1)
    (hxL : x ∈ L) :
    Nat.card (Subgroup.center (USixTwo.Qt ↥L)) = 3 := by
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hSS.2.2.2.1.2.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2.1.2.1.2 x (hS.1.1.2.1.1 hSS.2.1)
  have hx3' : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := by simpa using hx3
  have hx1' : (⟨x, hxL⟩ : ↥L) ≠ 1 := by
    intro h1
    exact hSS.2.2.1 (Subtype.ext_iff.mp h1)
  have hxq_ne : USixTwo.qmk ↥L ⟨x, hxL⟩ ≠ 1 :=
    twE6HeartCenter_qmk_ne_one hx3' hx1'
  have hxq_cent : USixTwo.qmk ↥L ⟨x, hxL⟩ ∈ Subgroup.center (USixTwo.Qt ↥L) :=
    twE6HeartCenter_qmk_mem_center (by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (mem_centralizer_of_le_centralizer hSS.2.2.2.1.1) l l.2))
  exact twE6HeartRecipe_center_card θ ε hK1 hperf hxq_ne hxq_cent hx3'

theorem twE6HeartCenter_langCube_data
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK1 : Nat.card K = (2 ^ 1) ^ 2) (hσ1 : ∀ c, σ c = c ^ 2 ^ 1)
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1)
    (hε : ∀ y : MulAut ↥(twistedE6RootGroup K σ),
      MulAut.congr ε y ∈ TwE6Delta.RecipeI K 1 ↔ y ∈ (RecipeExcLang.twConj K σ).range)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
      TwistedDiag.n0 (AlgebraicClosure K)) :
    IsElemAbelian 3 ((TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g).map
      (MulAut.congr ε).toMonoidHom) ∧
    Nat.card ((TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g).map
      (MulAut.congr ε).toMonoidHom) = 3 ^ 6 ∧
    ((TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g).map
      (MulAut.congr ε).toMonoidHom : Set (MulAut (TwE6Delta.RecipeR K 1))) ⊆
      TwE6Delta.RecipeI K 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact TableB.isElemAbelian_map
      (TwE6DD2.isElemAbelian_langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g) _
  · rw [Subgroup.card_map_of_injective (MulAut.congr ε).injective]
    exact TwE6DD2.card_langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr (by norm_num) hg hgn
  · rintro y ⟨z, hz, rfl⟩
    exact (hε z).2 (TwE6DD2.langCube_le_range (n := 1) le_rfl hK1 σ hσ1 Fr hFr g hz)

theorem twE6HeartCenter_exists_fixed
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK1 : Nat.card K = (2 ^ 1) ^ 2) (hσ1 : ∀ c, σ c = c ^ 2 ^ 1)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
    (ε : twistedE6RootGroup K σ ≃* TwE6Delta.RecipeR K 1)
    (hε : ∀ y : MulAut ↥(twistedE6RootGroup K σ),
      MulAut.congr ε y ∈ TwE6Delta.RecipeI K 1 ↔ y ∈ (RecipeExcLang.twConj K σ).range)
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g : ModGL Tag.E6 (AlgebraicClosure K)} (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hSlang : S ≤ TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g)
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
      TwistedDiag.n0 (AlgebraicClosure K))
    (hxL : x ∈ L) :
    ∃ E : Subgroup (USixTwo.Qt ↥L), IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E ∧
      E ≤ (⊤ : Subgroup ↥(Bs ⊓ L)).map
        ((USixTwo.qmk ↥L).comp (Subgroup.inclusion inf_le_right)) := by
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hSS.2.2.2.1.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  have hcenter : Nat.card (Subgroup.center (USixTwo.Qt ↥L)) = 3 :=
    twE6HeartCenter_center_card hS hK1 θ ε hxL
  have hA : IsElemAbelian 3 ((ggGamma L hN).range.map (USixTwo.qAutHom ↥L)) :=
    TableB.isElemAbelian_map (QTwoCav.gamma_hyps hS hN).1 _
  have hAcard : Nat.card ((ggGamma L hN).range.map (USixTwo.qAutHom ↥L)) = 3 ^ 5 := by
    rw [Subgroup.card_map_of_injective (USixTwo.qAutHom_injective hperf),
      QTwoCav.gamma_card hN, hidx]
  obtain ⟨hYea, hYcard, hYI⟩ :=
    twE6HeartCenter_langCube_data hK1 hσ1 ε hε hFr hg hgn
  have hAY := twE6HeartRecipe_exists_y θ hN ε hK1 hσ1 hFr hSdef hSlang
  obtain ⟨E, hEEA, hZE, hEcard, hEfix⟩ :=
    SmallExc.TwE6DS3.exists_fixed (n := 1) le_rfl hK1 (by norm_num)
      (twE6HeartRecipe_surjective θ ε) (twE6HeartRecipe_ker_le_center θ ε)
      (USixTwo.qmk_perfect hperf) (twE6HeartRecipe_odd_ker θ ε) hA hAcard.ge
      (fun a ha => let ⟨y, hy, hay⟩ := hAY a ha; ⟨y, hYI hy, hay⟩) hYea hYI hYcard hAY
  have hA3 : IsPGroup 3 (ggGamma L hN).range :=
    CFSG.StandardType.Line63.H5.isPGroup_three_of_isElemAbelian (QTwoCav.gamma_hyps hS hN).1
  refine ⟨E, hEEA, ?_, twE6HeartCenter_map_le_inf hN hA3 hSC hEEA hEfix⟩
  rw [hcenter] at hEcard
  calc 3 ^ 6 = 3 * 3 ^ 5 := by norm_num
    _ ≤ Nat.card E := hEcard

theorem twE6HeartCenter_card_bstar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5) :
    Nat.card Bs = 3 ^ 6 := by
  have hcardC : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf Bs) = 3 := by
    have hEq : (Subgroup.centralizer (L : Set G)).subgroupOf Bs =
        (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
      ext z
      exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩
    rw [hEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hS.1.1.card_bstar_inf_centralizer_L
  have h := Subgroup.card_mul_index ((Subgroup.centralizer (L : Set G)).subgroupOf Bs)
  rw [hidx, hcardC] at h
  norm_num at h ⊢
  exact h.symm

theorem ggQ2TwE6Heart_bstar_le_of_mem
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5)
    (hxL : x ∈ L) : Bs ≤ L := by
  obtain ⟨K, _, _, σ, hK1, hσ1, θ, hN, S, Fr, hFr, g, -, -, hSdef, -, -, hg, hgn,
    hSlang, -⟩ := QTwoE6.actual_beta_langCube_of_marking hS rfl hq2 htag hmark hidx le_rfl
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv (n := 1) le_rfl hK1 σ hσ1
  obtain ⟨E, -, hE6, hlift⟩ := twE6HeartCenter_exists_fixed hS hN hidx hK1 hσ1 θ ε hε hFr
    hSdef hSlang hg hgn hxL
  have hEle : Nat.card E ≤ Nat.card ↥(Bs ⊓ L) := by
    refine (Subgroup.card_le_of_le hlift).trans ?_
    have hd := Subgroup.card_map_dvd (⊤ : Subgroup ↥(Bs ⊓ L))
      ((USixTwo.qmk ↥L).comp (Subgroup.inclusion inf_le_right))
    rw [Subgroup.card_top] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hBsCard := twE6HeartCenter_card_bstar hS hidx
  have hEq : Bs ⊓ L = Bs := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hBsCard]
    exact hE6.trans hEle
  intro b hb
  rw [← hEq] at hb
  exact hb.2

theorem ggQTwoAutomizer_four_of_twE6_of_mem
    (hCav : GGQ2CavOfTBFull) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .twE6) p Bs L)
    (hxL : x ∈ L) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  subst hp
  have hLkeep := hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  have hsplit : LargeEvenSplit 3 lab := Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htag],
    by simp [htag], by rw [hn1]; norm_num⟩)
  have hmarkTB : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hθ⟩ := h
        exact ⟨hs, hna, θ, ⟨⟨htag, rfl, by rw [hn1]; norm_num⟩, hsplit,
          hθ.2.1, hθ.2.2⟩⟩) hraw⟩
  rcases ggQ2TwE6_index hS rfl (hN := hN) (ggQ2TwE6_lower hS rfl hmarkTB (hN := hN))
    (ggQ2TwE6_upper hS rfl hLkeep (hN := hN)) with h6 | h5
  · exact ggQTwoAutomizer_four_of_twE6Full hCav hS rfl hmarkLab hq htag
      (by simpa [GGQ2LieRank, htag] using h6)
  · have hmark := QTwoCav.innerDiagOnLabel_of_marking (p := 3) hS.1.2.2.1.1 hmarkLab
    have hsup : Bs ≤ L ⊔ Subgroup.zpowers x :=
      (ggQ2TwE6Heart_bstar_le_of_mem hS hq htag hmark h5 hxL).trans
        (le_sup_left : L ≤ L ⊔ Subgroup.zpowers x)
    have hTB : GGQ2TBHeart 3 Bs L :=
      ⟨lab, hq, hmarkLab, Or.inr htag, by simpa [GGQ2LieRank, htag] using h5⟩
    by_cases hJ : CFSG.AGLEmbedding.IsAltTwoP 3 J
    · rw [QTwoB2Cav.card_automizer_original_of_setting hS rfl hN hJ]
    · have h4 := ggQ2_cavOfTBHeartInner_holds hS rfl hTB hsup hJ hN
      rwa [QTwoCav.card_automizer_inner_image_eq_of_setting hS Nat.prime_three
        (by norm_num) hN] at h4

theorem ggQTwoGuardFailsOn_twE6
    (hCav : GGQ2CavOfTBFull) :
    GGQTwoGuardFailsOn (fun p lab => GGLabQTwo p lab ∧ lab.tag = .twE6) := by
  intro G _ _ p B Bs x L D J hS hp hL
  subst hp
  have hLkeep := hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  have hsplit : LargeEvenSplit 3 lab := Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htag],
    by simp [htag], by rw [hn1]; norm_num⟩)
  have hmarkTB : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hθ⟩ := h
        exact ⟨hs, hna, θ, ⟨⟨htag, rfl, by rw [hn1]; norm_num⟩, hsplit,
          hθ.2.1, hθ.2.2⟩⟩) hraw⟩
  rcases ggQ2TwE6_index hS rfl (hN := hN) (ggQ2TwE6_lower hS rfl hmarkTB (hN := hN))
    (ggQ2TwE6_upper hS rfl hLkeep (hN := hN)) with h6 | h5
  · exact ggQTwoAutomizer_four_of_twE6Full hCav hS rfl hmarkLab hq htag
      (by simpa [GGQ2LieRank, htag] using h6)
  · by_cases hxL : x ∈ L
    · exact ggQTwoAutomizer_four_of_twE6_of_mem hCav hS rfl hLkeep hxL
    · exact ggQTwoAutomizer_four_of_twE6_of_not_mem hCav hS rfl hLkeep hxL

theorem ggQTwoGuardFailsOn_exc_of_e6
    (hCav : GGQ2CavOfTBFull)
    (hE6 : GGQTwoGuardFailsOn (fun p lab => GGLabQTwo p lab ∧ lab.tag = .E6)) :
    GGQTwoGuardFailsOn GGQ2VACLabExc := by
  intro G _ _ p B Bs x L D J hS hp hL
  have hall : GGInnerDiagOnLabel (fun p lab => (GGLabQTwo p lab ∧ lab.tag = .E6) ∨
      GGQ2VACLabExcNotE6TwE6 p lab ∨ (GGLabQTwo p lab ∧ lab.tag = .twE6)) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨?_, h.2⟩) hL
    obtain ⟨hq, htag | htag | htag | htag | htag⟩ := h.1
    · exact Or.inr (Or.inl ⟨hq, Or.inl htag⟩)
    · exact Or.inl ⟨hq, htag⟩
    · exact Or.inr (Or.inl ⟨hq, Or.inr (Or.inl htag)⟩)
    · exact Or.inr (Or.inl ⟨hq, Or.inr (Or.inr htag)⟩)
    · exact Or.inr (Or.inr ⟨hq, htag⟩)
  rcases hall.elim_or with h | h
  · exact hE6 G p B Bs x L D J hS hp h
  rcases h.elim_or with h | h
  · exact ggQTwoGuardFailsOn_excNotE6TwE6_of_cav hCav G p B Bs x L D J hS hp h
  · exact ggQTwoGuardFailsOn_twE6 hCav G p B Bs x L D J hS hp h

end CFSG.StandardType
