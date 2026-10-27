module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.LargeEvenClassification.ElementarySubgroupPathsCore
public import CFSG.LocalAnalysis.LargeEvenClassification.ProductLocalRank
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreDeltaTransfer
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly
open CFSG.LargeEvenClassification.Helpers

private theorem a3_transport {G : Type} [Group G] {K : Subgroup G}
    (hz : Subgroup.center K = ⊥) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    {U_R E_R : Subgroup R} (hU : U_R ≠ ⊥) (hUp : IsPGroup 2 U_R)
    (hE : E_R ≤ Subgroup.normalizer (U_R : Set R)) (hEab : IsElemAbelian 3 E_R) :
    ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧
      Nat.card E = Nat.card E_R := by
  let π : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hz]
  have hmk_inj : Function.Injective (QuotientGroup.mk' (Subgroup.center K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hinj : Function.Injective π := θ.injective.comp hmk_inj
  have hsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  let U₀ : Subgroup K := U_R.comap π
  let E₀ : Subgroup K := E_R.comap π
  have hU₀map : U₀.map π = U_R :=
    Subgroup.map_comap_eq_self_of_surjective hsurj U_R
  have hE₀map : E₀.map π = E_R :=
    Subgroup.map_comap_eq_self_of_surjective hsurj E_R
  have hU₀ne : U₀ ≠ ⊥ := by
    intro h
    apply hU
    rw [← hU₀map, h, Subgroup.map_bot]
  have hE₀norm : E₀ ≤ Subgroup.normalizer (U₀ : Set K) := by
    have hmono : E₀ ≤ (Subgroup.normalizer (U_R : Set R)).comap π := by
      change E_R.comap π ≤ (Subgroup.normalizer (U_R : Set R)).comap π
      exact Subgroup.comap_mono hE
    rwa [Subgroup.comap_normalizer_eq_of_surjective U_R hsurj] at hmono
  let U : Subgroup G := U₀.map K.subtype
  let E : Subgroup G := E₀.map K.subtype
  have hUle : U ≤ K := Subgroup.map_subtype_le U₀
  have hEle : E ≤ K := Subgroup.map_subtype_le E₀
  have hUne : U ≠ ⊥ := by
    intro h
    exact hU₀ne
      ((Subgroup.map_eq_bot_iff_of_injective U₀ K.subtype_injective).mp h)
  have hUp : IsPGroup 2 U :=
    (hUp.comap_of_injective π hinj).map K.subtype
  have hEab' : IsElemAbelian 3 E :=
    elementary_map E₀ (elementary_comap_injective π hinj E_R hEab) K.subtype
  have hEnorm : E ≤ Subgroup.normalizer (U : Set G) := by
    have hmono : E₀.map K.subtype ≤ (Subgroup.normalizer (U₀ : Set K)).map K.subtype :=
      Subgroup.map_mono hE₀norm
    exact hmono.trans (Subgroup.le_normalizer_map K.subtype)
  have hEcard : Nat.card E = Nat.card E_R := by
    have h1 : Nat.card E = Nat.card E₀ :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective E₀ K.subtype K.subtype_injective).toEquiv).symm
    have h2 : Nat.card E₀ = Nat.card E_R := by
      have h := Nat.card_congr (Subgroup.equivMapOfInjective E₀ π hinj).toEquiv
      rwa [hE₀map] at h
    exact h1.trans h2
  exact ⟨U, E, hUle, hEle, hUne, hUp, hEnorm, hEab', hEcard⟩

theorem twoLocalPrimeRank_centralizer_eq_of_local {G : Type} [Group G] [Finite G]
    {B : Subgroup G} (hB : LargeEvenIsBmax 3 B) {r : ℕ} (hcard : Nat.card B = 3 ^ (r + 1))
    {y : G} (hy : y ∈ B) (hy1 : y ≠ 1) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({y} : Set G)) (hz : Subgroup.center K = ⊥)
    (hloc : ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r) :
    twoLocalPrimeRank 3 (Subgroup.centralizer ({y} : Set G)) = twoLocalPrimeRank 3 G := by
  unfold LargeEvenIsBmax LargeEvenTwoLocalRank at hB
  obtain ⟨hBab, hBcard, -⟩ := hB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder_y : orderOf y = 3 := orderOf_eq_prime (hBab.2 y hy) hy1
  have hm : twoLocalPrimeRank 3 G = r + 1 := by
    have hp : (3 : ℕ) ^ (r + 1) = 3 ^ twoLocalPrimeRank 3 G := hcard ▸ hBcard
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hp).symm
  obtain ⟨U, E, hU_le_K, hE_le_K, hU_ne, hU_p, hE_norm, hEab, hEcard⟩ := hloc
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCdef
  have hE_le_C : E ≤ C := hE_le_K.trans hK
  have hU_le_C : U ≤ C := hU_le_K.trans hK
  have hb : twoLocalPrimeRank 3 C ≤ twoLocalPrimeRank 3 G :=
    twoLocalPRank_subgroup_le (by norm_num : 1 < 3) C
  have hyC : y ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro z hz'
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    rfl
  have hyK : y ∉ K := by
    intro hyKin
    have hmem : (⟨y, hyKin⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hK k.property) y (by simp)).symm
    rw [hz] at hmem
    have hone : (⟨y, hyKin⟩ : ↥K) = 1 := Subgroup.mem_bot.mp hmem
    exact hy1 (by simpa using congrArg Subtype.val hone)
  let yC : ↥C := ⟨y, hyC⟩
  let EC : Subgroup ↥C := E.subgroupOf C
  let UC : Subgroup ↥C := U.subgroupOf C
  let F : Subgroup ↥C := Subgroup.zpowers yC
  have horder_yC : orderOf yC = 3 := (Subgroup.orderOf_mk y hyC).trans horder_y
  have hy_notin_EC : yC ∉ EC := by
    intro hyEC
    apply hyK
    have : y ∈ E := hyEC
    exact hE_le_K this
  have hdisjoint : Disjoint F EC :=
    (elementary_path_zpowers_disjoint Nat.prime_three EC yC horder_yC hy_notin_EC).symm
  have hyC_cent_E : yC ∈ Subgroup.centralizer (EC : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    apply Subtype.ext
    have heE : e.val ∈ E := he
    exact (Subgroup.mem_centralizer_iff.mp (hE_le_C heE) y (by simp)).symm
  have hcommutes : F ≤ Subgroup.centralizer (EC : Set ↥C) :=
    Subgroup.zpowers_le.mpr hyC_cent_E
  have hF_elem : IsElemAbelian 3 F :=
    elementary_prime_cyclic Nat.prime_three yC horder_yC
  have hEC_elem : IsElemAbelian 3 EC :=
    elementary_comap_injective C.subtype C.subtype_injective E hEab
  have hFcard : Nat.card F = 3 ^ 1 := by
    change Nat.card (Subgroup.zpowers yC) = 3 ^ 1
    rw [Nat.card_zpowers, horder_yC, pow_one]
  have hECcard : Nat.card EC = 3 ^ r := by
    change Nat.card (E.subgroupOf C) = 3 ^ r
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_C).toEquiv, hEcard]
  obtain ⟨Combined, -, -, hComb_elem, hComb_card, hComb_le_sup⟩ :=
    commuting_disjoint_elementary_product F EC hF_elem hEC_elem hFcard hECcard hcommutes hdisjoint
  have hyC_cent_U : yC ∈ Subgroup.centralizer (UC : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    have huU : u.val ∈ U := hu
    exact (Subgroup.mem_centralizer_iff.mp (hK (hU_le_K huU)) y (by simp)).symm
  have hyC_normalizes : F ≤ Subgroup.normalizer (UC : Set ↥C) :=
    (Subgroup.zpowers_le.mpr hyC_cent_U).trans (Subgroup.centralizer_le_normalizer _)
  have hEC_normalizes : EC ≤ Subgroup.normalizer (UC : Set ↥C) := by
    have hmono : EC ≤ (Subgroup.normalizer (U : Set G)).subgroupOf C := by
      change E.subgroupOf C ≤ (Subgroup.normalizer (U : Set G)).subgroupOf C
      exact Subgroup.comap_mono hE_norm
    rwa [Subgroup.subgroupOf_normalizer_eq hU_le_C] at hmono
  have hCombinedLe : Combined ≤ Subgroup.normalizer (UC : Set ↥C) :=
    hComb_le_sup.trans (sup_le hyC_normalizes hEC_normalizes)
  have hUCne : UC ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map C.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le hU_le_C, Subgroup.map_bot] at hmap
    exact hU_ne hmap
  have hUCp : IsPGroup 2 UC := hU_p.comap_of_injective C.subtype C.subtype_injective
  have hlocal : IsTwoLocal (Subgroup.normalizer (UC : Set ↥C)) :=
    ⟨UC, hUCne, hUCp, rfl⟩
  have hrankCombined : @CFSG.Open.pRank 3 ↥C _ _ Combined = 1 + r :=
    elementary_pRank_card (Ambient := ↥C) (by norm_num : 1 < 3) Combined hComb_elem hComb_card
  have h1 : r + 1 ≤ @CFSG.Open.pRank 3 ↥C _ _ (Subgroup.normalizer (UC : Set ↥C)) := by
    have hmono := pRank_mono (Ambient := ↥C) (by norm_num : 1 < 3) hCombinedLe
    rw [hrankCombined] at hmono
    omega
  have hc : r + 1 ≤ twoLocalPrimeRank 3 ↥C := by
    have hle : @CFSG.Open.pRank 3 ↥C _ _ (Subgroup.normalizer (UC : Set ↥C)) ≤
        twoLocalPrimeRank 3 ↥C := by
      have := pRank_le_twoLocalPRank (Ambient := ↥C) (by norm_num : 1 < 3)
        (Subgroup.normalizer (UC : Set ↥C)) hlocal
      simpa only [CFSG.LargeEvenClassification.Helpers.twoLocalPRank] using this
    exact h1.trans hle
  refine le_antisymm hb ?_
  rw [hm]
  exact hc

theorem exists_twoLocal_three_of_D6 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hz : Subgroup.center K = ⊥)
    (hmark : LargeEvenMarking K fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :
    ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨-, lab, _hlab, hraw⟩ := hmark
  have hP : lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1 := by
    obtain ⟨R, _hRg, _I, _F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, hP⟩ := hQ.2.2
    exact hP
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, rfl, rfl⟩ := hP
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K', hField, hFiniteK, hcardK, hQ⟩ := hraw
  have hK2 : Nat.card K' = 2 := by rw [hcardK]; norm_num
  obtain ⟨U_R, E_R, hUR_ne, hUR_p, hER_norm, hER_ab, hER_card⟩ :=
    OrthRestTail.torus_plus (K := K') (m := 6) hK2 (by norm_num)
  obtain ⟨θ, -⟩ := hQ.2.2
  obtain ⟨U, E, hUle, hEle, hUne, hUp, hEnorm, hEab, hEcard⟩ :=
    a3_transport hz θ hUR_ne hUR_p hER_norm hER_ab
  refine ⟨U, E, hUle, hEle, hUne, hUp, hEnorm, hEab, ?_⟩
  rw [hEcard, hER_card]

theorem exists_twoLocal_three_of_twD7 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hz : Subgroup.center K = ⊥)
    (hmark : LargeEvenMarking K fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) :
    ∃ U E : Subgroup G, U ≤ K ∧ E ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨-, lab, _hlab, hraw⟩ := hmark
  have hP : lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1 := by
    obtain ⟨R, _hRg, _I, _F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, hP⟩ := hQ.2.2
    exact hP
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, rfl, rfl⟩ := hP
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K', hField, hFiniteK, hcardK, b, c, hirr, hQ⟩ := hraw
  haveI : CharP K' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl hcardK
  obtain ⟨U_R, E_R, hUR_ne, hUR_p, hER_norm, hER_ab, hER_card⟩ :=
    OrthRestTail.torus_minus (K := K') (m := 6) (n := 1) (p := 3) b c hcardK
      (by norm_num) Nat.prime_three (by norm_num) (by norm_num) hirr
  obtain ⟨θ, -⟩ := hQ.2.2
  obtain ⟨U, E, hUle, hEle, hUne, hUp, hEnorm, hEab, hEcard⟩ :=
    a3_transport hz θ hUR_ne hUR_p hER_norm hER_ab
  refine ⟨U, E, hUle, hEle, hUne, hUp, hEnorm, hEab, ?_⟩
  rw [hEcard, hER_card]

end CFSG.StandardType.FrameRoute
