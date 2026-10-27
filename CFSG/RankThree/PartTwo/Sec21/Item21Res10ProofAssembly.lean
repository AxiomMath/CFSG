module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res8ProofJON
public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofSteps
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwelve
public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofConj

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup
open scoped commutatorElement

@[expose] def KF2110HJThetaOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → Nonempty (lBar L ≃* NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J ∈ thetaComponentsAt 3 d, iOf218 L d ≤ J →
        Sec4.IsTripleCover (lBar (iOf218 L d)) (alternatingGroup (Fin 6)) →
        Sec4.IsTripleCover (lBar J) NativeSporadic.ON →
        Odd (Nat.card (aschbacherSolvableCore 3 ↥L))

namespace Item21Res10Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_one (S : Subgroup G) : S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  ext x
  simp

end Item21Res10Proof

open Item21Res10Proof

section Main


theorem item2110JONHJ_of_res10 (h211 : Item211) (h45 : Sec4.Item4_5) (h219 : Item219)
    (hAL : Item2110ALInI) (h612 : Sec6.Item6_12) (hθ : KF2110HJThetaOdd) : Item2110JONHJ := by
  intro G _ _ A E U c L hpair hL hJ2 d hdA hd1 hdcen J hJ hIJ hIA6 hJON
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hθL := hθ G A E U c L hpair hL hJ2 d hdA hd1 hdcen J hJ hIJ hIA6 hJON
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hmax : ∀ E' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E' → A ≤ E' → E' = A :=
    hpair.mem_S.1.2.1
  have hG := hpair.standing.toTheoremFourHyp
  have h27' : Nat.card A = 3 ^ 3 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  obtain ⟨hdI, -⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hIL : iOf218 L d ≤ L := (map_subtype_le _).trans inf_le_left
  have hIC : iOf218 L d ≤ centralizer ({d} : Set G) := (map_subtype_le _).trans inf_le_right
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) h27'
  have hALI : A ⊓ L ≤ iOf218 L d := hAL G A E U c L hpair hL d hdA hd1 hdcen
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLcomp : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAcL : zpowers c ⊔ (A ⊓ L) = A := by
    have hle : zpowers c ⊔ (A ⊓ L) ≤ A := sup_le (zpowers_le.mpr hcA) inf_le_left
    have hlt : A ⊓ L < zpowers c ⊔ (A ⊓ L) := by
      refine lt_of_le_of_ne le_sup_right fun h => hcL ?_
      have hc' : c ∈ zpowers c ⊔ (A ⊓ L) := mem_sup_left (mem_zpowers c)
      rw [← h] at hc'
      exact hc'.2
    have hdvd : Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) ∣ 3 ^ 3 := by
      rw [← h27']
      exact card_dvd_of_le hle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 9 < Nat.card (zpowers c ⊔ (A ⊓ L) : Subgroup G) := by
      rw [← h9]
      exact card_lt_of_lt hlt
    have hj3 : j = 3 := by
      rcases j with _ | _ | _ | _ | j
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rw [hjc] at hgt; norm_num at hgt
      · rfl
      · omega
    exact eq_of_le_of_card_ge hle (by rw [hjc, hj3, h27'])
  have hAJ : A ≤ normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hdA hd1 J hJ
  have hJd : J ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
  have hcJ : c ∈ J := Sec13.ON134.mem_of_maximal hAe hmax hcA inf_le_left h9
    (hALI.trans hIJ) hAcL.symm (hAJ hcA) ⟨hdA, hdL⟩ hd1 hJd hq hJON
  have hAJ' : A ≤ J := by
    rw [← hAcL]
    exact sup_le (zpowers_le.mpr hcJ) (hALI.trans hIJ)
  have h27L : 27 ∣ Nat.card (L ⊓ centralizer ({d} : Set G) : Subgroup G) := by
    have hI27 : 3 ^ 3 ∣ Nat.card (iOf218 L d) := by
      refine (show 3 ^ 3 ∣ Nat.card (lBar (iOf218 L d)) by
        rw [Sec13.card_eq_of_isTripleCover_six hIA6]; norm_num).trans ?_
      exact Item2110Res3Proof.card_lBar_dvd _
    exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ hI27.trans (card_dvd_of_le (le_inf hIL hIC))
  obtain ⟨a, haAL, had⟩ : ∃ a ∈ A ⊓ L, a ∉ zpowers d := by
    by_contra hne
    push Not at hne
    have := card_le_of_le (show A ⊓ L ≤ zpowers d from hne)
    rw [h9, Sec13.card_zpowers_of_pow_three hd3 hd1] at this
    omega
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hA3.to_le inf_le_left
  obtain ⟨Y, hYL, hYab, hY4, hBY, haY, hfpf⟩ :=
    exists_four_lift h415 hθL hJ2 inf_le_right hB3 h9 ⟨hdA, hdL⟩ hd1 h27L haAL had
  have hcY : c ∈ centralizer (Y : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hLc (hYL hy))
  have hAY : A ≤ normalizer (Y : Set G) := by
    rw [← hAcL]
    exact sup_le (zpowers_le.mpr (centralizer_le_normalizer _ hcY)) hBY
  have hY1 : Y ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hY4
    omega
  obtain ⟨⟨y₀, hy₀⟩, hy₀1⟩ := ne_bot_iff_exists_ne_one.mp hY1
  have hy₀1' : y₀ ≠ 1 := fun h => hy₀1 (Subtype.ext h)
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := 2) (by rw [hY4]; norm_num)
  have hAE : A ∈ partTwoE G := ⟨hAe, by rw [h27']; norm_num, Y, hY1, hY2, hAY⟩
  have hYU : Y ∈ fourGroups A := mem_fourGroups_iff.mpr ⟨hAY, hYab, hY4⟩
  obtain ⟨b, hbA, hb1, X, hX, hYX, -, -, hXV⟩ :=
    h612 G hpair.standing A hpair.mem_S A (mem_collectionIn_iff.mpr ⟨hAE, le_rfl⟩) Y hYU
  have hXb : X ∈ thetaComponentsAt 3 b := hX.1
  have hX0 : X ∈ lZeroUnion A := hX.2.1
  have hAX : A ≤ normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 X hXb
  by_cases hbd : b ∈ zpowers d
  ·
    have hCb : centralizer ({b} : Set G) = centralizer ({d} : Set G) := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hbd
      have hk3 : ¬ (3 : ℤ) ∣ k := by
        rintro ⟨k', rfl⟩
        apply hb1
        rw [zpow_mul, show d ^ (3 : ℤ) = 1 by rw [zpow_ofNat, hd3], one_zpow]
      exact PartOne.S11d.centralizer_zpow_eq Nat.prime_three hd3 hk3
    have hXd : X ∈ thetaComponentsAt 3 d := by
      rwa [← PartOne.S11d.thetaComponentsAt_congr hCb]
    have hXJ : X = J := by
      by_contra hne
      exact false_of_lZeroUnion_of_triv hX0 fun a' ha' =>
        triv_of_ne hXd hJ hne (hAX ha') (one_mem _) (hAJ' ha') (one_mul a').symm
    exact false_of_normalizes_of_mem (hIJ hdI) hJd (hXJ ▸ hYX) (hAY hdA) hfpf hy₀ hy₀1'
  have hcnd : c ∉ zpowers d := fun h => hcL (zpowers_le.mpr hdL h)
  have hE27 : Late.IsE27 A := ⟨hAe, by rw [h27']; norm_num⟩
  obtain ⟨g, ⟨hgJ, hgA⟩, hgb⟩ :=
    exists_conj_mem_of_le hE27 hAJ' hdA hd1 hJd hq hJON hbA hcA hbd hcnd
  have hgd : g⁻¹ * d * g⁻¹⁻¹ = d := by
    rw [inv_inv, mem_centralizer_singleton_iff.mp (inv_mem (hJd hgJ)), inv_mul_cancel_right]
  set L₁ := L.map (MulAut.conj g⁻¹).toMonoidHom with hL₁def
  have hzb : (zpowers c).map (MulAut.conj g⁻¹).toMonoidHom = zpowers b := by
    rw [← hgb, Item21Res8Proof.map_conj_map_conj', inv_mul_cancel, map_conj_one]
  have hCb' : centralizer ({g⁻¹ * c * g⁻¹⁻¹} : Set G) = centralizer ({b} : Set G) := by
    apply KFacts.KS14.centralizer_eq_of_zpowers_eq
    rw [← hzb, MonoidHom.map_zpowers]
    rfl
  have hL₁b : L₁ ∈ thetaComponentsAt 3 b := by
    have h1 := Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hLcomp g⁻¹
    rwa [PartOne.S11d.thetaComponentsAt_congr hCb'] at h1
  have hL₁C : L₁ ≤ centralizer ({b} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hL₁b
  have hAmap : A.map (MulAut.conj g⁻¹).toMonoidHom = A :=
    map_conj_eq_of_mem_normalizer (inv_mem hgA)
  have hAL₁ : (A ⊓ L).map (MulAut.conj g⁻¹).toMonoidHom = A ⊓ L₁ := by
    rw [map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective, hAmap]
  have hAbL₁ : A = zpowers b ⊔ (A ⊓ L₁) := by
    have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hAcL
    rw [Subgroup.map_sup, hzb, hAL₁, hAmap] at h1
    exact h1.symm
  have hdec : ∀ x ∈ A, ∃ i : ℕ, ∃ l ∈ L₁, x = b ^ i * l := fun x hx => by
    obtain ⟨i, -, l, hl, rfl⟩ := Sec13.exists_pow_mul_of_mem hAe hbA hAbL₁ hx
    exact ⟨i, l, hl.2, rfl⟩
  have hbX : b ∈ centralizer (X : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (Sec6.le_centralizer_of_mem_thetaComponentsAt hXb hx)
  have hXL₁ : X = L₁ := by
    by_contra hne
    refine false_of_lZeroUnion_of_triv hX0 fun x hx => ?_
    obtain ⟨i, l, hl, rfl⟩ := hdec x hx
    exact triv_of_ne hXb hL₁b hne (hAX hx) (pow_mem hbX i) hl rfl
  have hdL₁ : d ∈ L₁ := ⟨d, hdL, by simpa [MulAut.conj_apply] using hgd⟩
  have hYL₁ : Y ≤ L₁ := le_of_normalizes hYab hY4 (hXL₁ ▸ hYX) hdL₁ (hAY hdA) hfpf
  have hZL : center (lBar L) = ⊥ := Item2113Proof.center_lBar_eq_bot_of_isList218 hL
  let e₁ : L ≃* L₁ := L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have hZ : ∀ v : G, center (lBar (L₁.map (MulAut.conj v).toMonoidHom)) = ⊥ := by
    intro v
    let e₂ : L₁ ≃* L₁.map (MulAut.conj v).toMonoidHom :=
      L₁.equivMapOfInjective _ (MulAut.conj v).injective
    exact Item2113Proof.center_eq_bot_of_mulEquiv hZL (Sec14.quotThetaEquiv (e₁.trans e₂)).symm
  set V₀ := inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) ⊓
    centralizer ({b} : Set G) with hV₀
  set C := A ⊓ centralizer (Y : Set G) with hC
  have hV₀N : V₀ ≤ normalizer (L₁ : Set G) :=
    le_normalizer_of_pCore hpair.mem_S hbA hb1 hL₁b hZ hYL₁ hYab hdA (hAY hdA) hfpf hY1
  have hVL₁ : ⁅V₀, C⁆ ≤ L₁ :=
    commutator_le_of_dec hV₀N inf_le_right hL₁C (fun x hx => hdec x hx.1)
  have hCV₀ : C ≤ normalizer (V₀ : Set G) := by
    intro x hx
    have h1 : x ∈ normalizer
        (inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map _ _
        inferInstance (le_normalizer hx.2)
    have hxb : x ∈ centralizer ({b} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hcomm x hx.1 b hbA)
    have h2 : x ∈ normalizer (centralizer ({b} : Set G) : Set G) := le_normalizer hxb
    refine mem_normalizer_fintype fun v hv => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp h1 v).mp hv.1
    · exact (mem_normalizer_iff.mp h2 v).mp hv.2
  have hQ : ⁅V₀, C⁆ ≤ inSubgroup (CFSG.pCore 2) (centralizer (Y : Set G)) ⊓ L₁ :=
    le_inf ((le_normalizer_iff_commutator_le_left.mp hCV₀).trans inf_le_left) hVL₁
  have hθL₁ : Odd (Nat.card (aschbacherSolvableCore 3 ↥L₁)) := by
    rw [← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₁,
      card_map_of_injective e₁.injective]
    exact hθL
  have hJ2₁ : Nonempty (lBar L₁ ≃* NativeSporadic.J2) :=
    ⟨(Sec14.quotThetaEquiv e₁).symm.trans hJ2.some⟩
  have h9₁ : Nat.card (A ⊓ L₁ : Subgroup G) = 9 := by
    rw [← hAL₁, card_map_of_injective (MulAut.conj g⁻¹).injective, h9]
  have hCd : (centralizer ({d} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({d} : Set G) :=
    map_conj_eq_of_mem_normalizer (le_normalizer (inv_mem (hJd hgJ)))
  have h27₁ : 27 ∣ Nat.card (L₁ ⊓ centralizer ({d} : Set G) : Subgroup G) := by
    have h1 : (L ⊓ centralizer ({d} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        L₁ ⊓ centralizer ({d} : Set G) := by
      rw [map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective, hCd]
    rw [← h1, card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact h27L
  have hB₁3 : IsPGroup 3 (A ⊓ L₁ : Subgroup G) := hA3.to_le inf_le_left
  obtain ⟨e, heC₀, heB, he1⟩ :
      ∃ e, e ∈ zpowers c ⊔ zpowers a ∧ e ∈ A ⊓ L₁ ∧ e ≠ 1 := by
    have hca : c ∉ zpowers a := fun h => hcL (zpowers_le.mpr haAL.2 h)
    have ha1 : a ≠ 1 := fun h => had (h ▸ one_mem _)
    have ha3 : a ^ 3 = 1 := hAe.2 a haAL.1
    have hC₀ : Nat.card (zpowers c ⊔ zpowers a : Subgroup G) = 9 := by
      obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers c)
        (zpowers a) (fun x hx y hy =>
          hcomm x (zpowers_le.mpr hcA hx) y (zpowers_le.mpr haAL.1 hy))
      rw [Sec13.zpowers_inf_eq_bot hc3 hca, card_bot, mul_one,
        Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three ha3 ha1] at hcard
      exact hcard
    have hC₀A : zpowers c ⊔ zpowers a ≤ A := sup_le (zpowers_le.mpr hcA) (zpowers_le.mpr haAL.1)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (zpowers c ⊔ zpowers a) (A ⊓ L₁) (fun x hx y hy => hcomm x (hC₀A hx) y hy.1)
    rw [hC₀, h9₁] at hcard
    have hle : Nat.card ((zpowers c ⊔ zpowers a) ⊔ (A ⊓ L₁) : Subgroup G) ≤ 27 := by
      have := card_le_of_le
        (show (zpowers c ⊔ zpowers a) ⊔ (A ⊓ L₁) ≤ A from sup_le hC₀A inf_le_left)
      rw [h27'] at this
      norm_num at this ⊢
      exact this
    have hne : (zpowers c ⊔ zpowers a) ⊓ (A ⊓ L₁) ≠ ⊥ := by
      intro h
      rw [h, card_bot, mul_one] at hcard
      omega
    obtain ⟨⟨e, he⟩, he1⟩ := ne_bot_iff_exists_ne_one.mp hne
    exact ⟨e, he.1, he.2, fun h => he1 (Subtype.ext h)⟩
  have heY : e ∈ centralizer (Y : Set G) :=
    sup_le (zpowers_le.mpr hcY) (zpowers_le.mpr haY) heC₀
  have hed : e ∉ zpowers d := by
    intro h
    have hze := Item2110Res2Proof.zpowers_eq_of_mem_cube hd3 h he1
    have hdY : d ∈ centralizer (Y : Set G) :=
      zpowers_le.mpr heY (hze ▸ mem_zpowers d)
    apply hy₀1'
    apply hfpf y₀ hy₀
    rw [← (mem_centralizer_iff.mp hdY) y₀ hy₀, mul_inv_cancel_right]
  have hlift := commutator_mem_theta_lift h415 hθL₁ hJ2₁ inf_le_right hB₁3 h9₁ ⟨hdA, hdL₁⟩ hd1
    h27₁ hYL₁ hY4 (fun x hx => hAY hx.1) heB heY hed
  have hVθ : ⁅⁅V₀, C⁆, C⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L₁ := by
    rw [commutator_le]
    intro v hv x hx
    obtain ⟨i, l, hl, rfl⟩ := hdec x hx.1
    have hvQ := hQ hv
    have hbY : b ∈ centralizer (Y : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hL₁C (hYL₁ hy))
    have hlA : l ∈ A := by
      have : l = (b ^ i)⁻¹ * (b ^ i * l) := by group
      rw [this]
      exact mul_mem (inv_mem (pow_mem hbA i)) hx.1
    have hlY : l ∈ centralizer (Y : Set G) := by
      have : l = (b ^ i)⁻¹ * (b ^ i * l) := by group
      rw [this]
      exact mul_mem (inv_mem (pow_mem hbY i)) hx.2
    have hw := hlift v hvQ l ⟨⟨hlA, hl⟩, hlY⟩
    have hwL : v * l * v⁻¹ * l⁻¹ ∈ L₁ :=
      mul_mem (mul_mem (mul_mem hvQ.2 hl) (inv_mem hvQ.2)) (inv_mem hl)
    rw [commutatorElement_pow_mul (mem_centralizer_singleton_iff.mp (hL₁C hvQ.2))
      (mem_centralizer_singleton_iff.mp (hL₁C hwL)) i]
    exact hw
  have hcop : ⁅V₀, C⁆ ≤ ⁅⁅V₀, C⁆, C⁆ := by
    refine ClassicalInvolution.commutator_le_commutator_commutator_of_coprime V₀ C hCV₀ ?_
    obtain ⟨i, hi⟩ := (hA3.to_le (inf_le_left : C ≤ A)).exists_card_eq
    have hV₀2 : IsPGroup 2 V₀ :=
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥(centralizer (Y : Set G)))).map _).to_le inf_le_left
    obtain ⟨j, hj⟩ := hV₀2.exists_card_eq
    rw [hi, hj]
    exact Nat.Coprime.pow i j (by norm_num)
  rw [hXL₁] at hXV
  have hL₁θ : L₁ ≤ inSubgroup (aschbacherSolvableCore 3) L₁ := by
    calc L₁ = ⁅L₁, ⁅V₀, C⁆⁆ := hXV.symm
      _ ≤ ⁅L₁, inSubgroup (aschbacherSolvableCore 3) L₁⁆ :=
          commutator_mono le_rfl (hcop.trans hVθ)
      _ ≤ inSubgroup (aschbacherSolvableCore 3) L₁ := by
          rw [commutator_comm]
          exact le_normalizer_iff_commutator_le_left.mp (Sec6.le_normalizer_theta L₁)
  have htop : aschbacherSolvableCore 3 ↥L₁ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht, hte⟩ := hL₁θ x.2
    rwa [show t = x from Subtype.ext hte] at ht
  have : Subsingleton (lBar L₁) := by
    change Subsingleton (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have h1 : Nat.card (lBar L₁) = 1 := Nat.card_unique
  rw [KFacts.KS14.card_eq_of_j2 hJ2₁] at h1
  norm_num at h1

theorem item2110JON_of_res10 (h211 : Item211)
    (h45 : Sec4.Item4_5) (h219 : Item219) (hAL : Item2110ALInI) (h612 : Sec6.Item6_12)
    (hθ : KF2110HJThetaOdd) : Item2110JON :=
  item2110JON_of_res8 h211 h45 h219 hAL (item2110JONHJ_of_res10 h211 h45 h219 hAL h612 hθ)

end Main

end CFSG.RankThree.PartTwo.Sec21
