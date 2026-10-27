module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item21Res12ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup
open scoped commutatorElement

namespace Item21Res12Proof

variable {G : Type} [Group G] [Finite G]

theorem conj_involution {A : Subgroup G} {c x g t : G} (hgA : g ∈ normalizer (A : Set G))
    (hgx : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers c)
    (htθ : t ∈ inSubgroup (aschbacherSolvableCore 3) (centralizer ({c} : Set G)))
    (htA : t ∈ centralizer (A : Set G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    g⁻¹ * t * g ∈ inSubgroup (aschbacherSolvableCore 3) (centralizer ({x} : Set G)) ∧
      g⁻¹ * t * g ∈ centralizer (A : Set G) ∧ (g⁻¹ * t * g) ^ 2 = 1 ∧ g⁻¹ * t * g ≠ 1 := by
  have hzx : (zpowers c).map (MulAut.conj g⁻¹).toMonoidHom = zpowers x := by
    rw [← hgx, Item21Res8Proof.map_conj_map_conj', inv_mul_cancel, Item21Res10Proof.map_conj_one]
  have hCx : centralizer ({g⁻¹ * c * g⁻¹⁻¹} : Set G) = centralizer ({x} : Set G) := by
    apply KFacts.KS14.centralizer_eq_of_zpowers_eq
    rw [← hzx, MonoidHom.map_zpowers]
    rfl
  have hθmap : (inSubgroup (aschbacherSolvableCore 3) (centralizer ({c} : Set G))).map
      (MulAut.conj g⁻¹).toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({x} : Set G)) := by
    rw [map_inSubgroup_aschbacherSolvableCore, map_centralizer_singleton, MulAut.conj_apply, hCx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hθmap]
    exact ⟨t, htθ, by simp⟩
  · rw [mem_centralizer_iff]
    intro y hy
    have hy' : g * y * g⁻¹ ∈ A := (mem_normalizer_iff.mp hgA y).mp hy
    have hc : g * y * g⁻¹ * t = t * (g * y * g⁻¹) := (mem_centralizer_iff.mp htA) _ hy'
    calc y * (g⁻¹ * t * g) = g⁻¹ * (g * y * g⁻¹ * t) * g := by group
      _ = g⁻¹ * (t * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * t * g * y := by group
  · have htt : t * t = 1 := by rw [← pow_two, ht2]
    rw [pow_two]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  · intro h
    apply ht1
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem false_of_four
    (h45 : Sec4.Item4_5) (h69 : Sec6.Item6_9) {A E U L J B T : Subgroup G} {c d : G}
    (hpair : Sec21Pair G A E U c L) (hJ2 : Nonempty (lBar L ≃* NativeSporadic.J2))
    (hLcomp : L ∈ thetaComponentsAt 3 c) (h27 : Nat.card A = 3 ^ 3)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAcL : zpowers c ⊔ (A ⊓ L) = A) (hAJ : A ≤ J)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hJd : J ≤ centralizer ({d} : Set G))
    (hq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J))
    (hJON : Sec4.IsTripleCover (J ⧸ aschbacherSolvableCore 3 J) NativeSporadic.ON)
    (hcA : c ∈ A) (hcnd : c ∉ zpowers d) (hBA : B ≤ A)
    (hBab : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBd : ∀ b ∈ B, b ≠ 1 → b ∉ zpowers d) (hTA : T ≤ centralizer (A : Set G))
    (hTab : CFSG.Assembly.IsElemAbelian 2 T) (hT4 : Nat.card T = 4) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := hpair.mem_S.1.1
  have hG := hpair.standing.toTheoremFourHyp
  have hE27 : Late.IsE27 A := ⟨hAe, by rw [h27]; norm_num⟩
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) h27
  have hAT : A ≤ centralizer (T : Set G) := le_centralizer_iff.mp hTA
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hT4
    omega
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hAE : A ∈ partTwoE G :=
    ⟨hAe, by rw [h27]; norm_num, T, hT1, hT2, hAT.trans (centralizer_le_normalizer _)⟩
  have hTU : T ∈ fourGroupsPlus A :=
    mem_fourGroupsPlus_iff.mpr
      ⟨mem_fourGroups_iff.mpr ⟨hAT.trans (centralizer_le_normalizer _), hTab, hT4⟩, hAT⟩
  obtain ⟨b, hbB, hb1, X, hX, hXT⟩ :=
    h69 G hpair.standing A hpair.mem_S A (mem_collectionIn_iff.mpr ⟨hAE, le_rfl⟩) T hTU B hBA
      hBab hB9
  have hbA := hBA hbB
  have hbd := hBd b hbB hb1
  have hX0 : X ∈ lZeroUnion A := hX.1
  have hXb : X ∈ thetaComponentsAt 3 b := hX.2
  have hAX : A ≤ normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hbA hb1 X hXb
  obtain ⟨g, ⟨-, hgA⟩, hgb⟩ :=
    Item21Res10Proof.exists_conj_mem_of_le hE27 hAJ hdA hd1 hJd hq hJON hbA hcA hbd hcnd
  set L₁ := L.map (MulAut.conj g⁻¹).toMonoidHom with hL₁def
  have hzb : (zpowers c).map (MulAut.conj g⁻¹).toMonoidHom = zpowers b := by
    rw [← hgb, Item21Res8Proof.map_conj_map_conj', inv_mul_cancel, Item21Res10Proof.map_conj_one]
  have hCb' : centralizer ({g⁻¹ * c * g⁻¹⁻¹} : Set G) = centralizer ({b} : Set G) := by
    apply KFacts.KS14.centralizer_eq_of_zpowers_eq
    rw [← hzb, MonoidHom.map_zpowers]
    rfl
  have hL₁b : L₁ ∈ thetaComponentsAt 3 b := by
    have h1 := Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hLcomp g⁻¹
    rwa [PartOne.S11d.thetaComponentsAt_congr hCb'] at h1
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
    refine Item21Res10Proof.false_of_lZeroUnion_of_triv hX0 fun x hx => ?_
    obtain ⟨i, l, hl, rfl⟩ := hdec x hx
    exact Item21Res10Proof.triv_of_ne hXb hL₁b hne (hAX hx) (pow_mem hbX i) hl rfl
  rw [hXL₁] at hXT hX0 hAX hbX
  have hTN : ∀ t ∈ T, t ∈ normalizer (L₁ : Set G) := by
    intro t ht
    by_contra htN
    have htb : t ∈ centralizer ({b} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hTA ht)) b hbA).symm
    have hL₂b : L₁.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 b :=
      Sec6.map_conj_mem_thetaComponentsAt htb hL₁b
    have hne : L₁ ≠ L₁.map (MulAut.conj t).toMonoidHom :=
      fun h => htN (mem_normalizer_iff_map_conj_eq.mpr h.symm)
    refine Item21Res10Proof.false_of_lZeroUnion_of_triv hX0 fun x hx => ?_
    obtain ⟨i, l, hl, rfl⟩ := hdec x hx
    have hlA : l ∈ A := by
      have : l = (b ^ i)⁻¹ * (b ^ i * l) := by group
      rw [this]
      exact mul_mem (inv_mem (pow_mem hbA i)) hx
    have hl₂ : l ∈ L₁.map (MulAut.conj t).toMonoidHom := by
      refine ⟨l, hl, ?_⟩
      change t * l * t⁻¹ = l
      rw [← (mem_centralizer_iff.mp (hTA ht)) l hlA, mul_inv_cancel_right]
    exact Item21Res10Proof.triv_of_ne hL₁b hL₂b hne (hAX hx) (pow_mem hbX i) hl₂ rfl
  let e₁ : L ≃* L₁ := L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have hJ2₁ : Nonempty (lBar L₁ ≃* NativeSporadic.J2) :=
    ⟨(Sec14.quotThetaEquiv e₁).symm.trans hJ2.some⟩
  have h9₁ : Nat.card (A ⊓ L₁ : Subgroup G) = 9 := by
    rw [← hAL₁, card_map_of_injective (MulAut.conj g⁻¹).injective, h9]
  apply hXT
  rw [commutator_le]
  intro l hl t ht
  have h1 := Item21Res12Proof.conj_mul_inv_mem_theta_of_j2 hJ2₁ inf_le_right
    (hA3.to_le inf_le_left) h9₁ (hTN t ht) (hTab.2 t ht)
    (fun x hx => by rw [← (mem_centralizer_iff.mp (hTA ht)) x hx.1, mul_inv_cancel_right]) l hl
  have h2 : ⁅l, t⁆ = (t * l * t⁻¹ * l⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact inv_mem h1

end Item21Res12Proof

open Item21Res12Proof

section Main

theorem kf2110HJThetaOdd_of_res12 (h211 : Item211) (h45 : Sec4.Item4_5) (hAL : Item2110ALInI)
    (h69 : Sec6.Item6_9) : KF2110HJThetaOdd := by
  intro G _ _ A E U c L hpair hL hJ2 d hdA hd1 hdcen J hJ hIJ hIA6 hJON
  by_contra hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcA, hc1, hLc, hAN, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hmax : ∀ E' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E' → A ≤ E' → E' = A :=
    hpair.mem_S.1.2.1
  have hG := hpair.standing.toTheoremFourHyp
  have h27' : Nat.card A = 3 ^ 3 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Item2113Res3Proof.card_inf_eq_nine h211 h45 hpair hL
  have hdL : d ∈ L := Item2113Proof.mem_of_isCentral218 hdcen
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
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
  obtain ⟨a, haAL, had⟩ : ∃ a ∈ A ⊓ L, a ∉ zpowers d := by
    by_contra hne
    push Not at hne
    have := card_le_of_le (show A ⊓ L ≤ zpowers d from hne)
    rw [h9, Sec13.card_zpowers_of_pow_three hd3 hd1] at this
    omega
  have hcnd : c ∉ zpowers d := fun h => hcL (zpowers_le.mpr hdL h)
  have hE27 : Late.IsE27 A := ⟨hAe, by rw [h27']; norm_num⟩
  obtain ⟨t, htθ, htA, ht2, ht1⟩ :=
    exists_involution_of_even hpair.mem_S hcA hc1 hLcomp (hAN) hev
  have ha3 : a ^ 3 = 1 := hAe.2 a haAL.1
  have ha1 : a ≠ 1 := fun h => had (h ▸ one_mem _)
  have hca : c ∉ zpowers a := fun h => hcL (zpowers_le.mpr haAL.2 h)
  set B := zpowers c ⊔ zpowers a with hBdef
  have hBA : B ≤ A := sup_le (zpowers_le.mpr hcA) (zpowers_le.mpr haAL.1)
  have hB9 : Nat.card B = 9 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers c)
      (zpowers a) (fun x hx y hy =>
        hcomm x (zpowers_le.mpr hcA hx) y (zpowers_le.mpr haAL.1 hy))
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three ha3 ha1] at hcard
    exact hcard
  have hBab : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun u v => Subtype.ext (hcomm u (hBA u.2) v (hBA v.2))⟩⟩, fun x hx => hAe.2 x (hBA hx)⟩
  have hBd : ∀ b ∈ B, b ≠ 1 → b ∉ zpowers d := by
    intro b hbB hb1 hbd
    have hzd : zpowers b = zpowers d := Item2110Res2Proof.zpowers_eq_of_mem_cube hd3 hbd hb1
    have hdB : d ∈ B := zpowers_le.mpr hbB (hzd ▸ mem_zpowers d)
    have hC : Nat.card (zpowers a ⊔ zpowers d : Subgroup G) = 9 := by
      obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers a)
        (zpowers d) (fun x hx y hy =>
          hcomm x (zpowers_le.mpr haAL.1 hx) y (zpowers_le.mpr hdA hy))
      rw [Sec13.zpowers_inf_eq_bot ha3 had, card_bot, mul_one,
        Sec13.card_zpowers_of_pow_three ha3 ha1, Sec13.card_zpowers_of_pow_three hd3 hd1] at hcard
      exact hcard
    have hle : zpowers a ⊔ zpowers d ≤ B :=
      sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers a))) (zpowers_le.mpr hdB)
    have heq : zpowers a ⊔ zpowers d = B := eq_of_le_of_card_ge hle (by rw [hB9, hC])
    have hcB : c ∈ zpowers a ⊔ zpowers d := heq ▸ mem_sup_left (mem_zpowers c)
    exact hcL (sup_le (zpowers_le.mpr haAL.2) (zpowers_le.mpr hdL) hcB)
  have hno : ∀ T : Subgroup G, T ≤ centralizer (A : Set G) → CFSG.Assembly.IsElemAbelian 2 T →
      Nat.card T = 4 → False := fun T hTA hTab hT4 =>
    false_of_four h45 h69 hpair hJ2 hLcomp h27' h9 hAcL hAJ' hdA hd1 hJd hq hJON hcA hcnd hBA
      hBab hB9 hBd hTA hTab hT4
  have hall : ∀ x ∈ B, x ≠ 1 →
      t ∈ inSubgroup (aschbacherSolvableCore 3) (centralizer ({x} : Set G)) := by
    intro x hxB hx1
    obtain ⟨g, ⟨-, hgA⟩, hgx⟩ := Item21Res10Proof.exists_conj_mem_of_le hE27 hAJ' hdA hd1 hJd
      hq hJON (hBA hxB) hcA (hBd x hxB hx1) hcnd
    obtain ⟨hsθ, hsA, hs2, hs1⟩ := conj_involution hgA hgx htθ htA ht2 ht1
    have hXN : centralizer (A : Set G) ≤
        normalizer (inSubgroup (aschbacherSolvableCore 3) (centralizer ({x} : Set G)) : Set G) :=
      (centralizer_le (Set.singleton_subset_iff.mpr (hBA hxB))).trans
        (Sec6.le_normalizer_theta _)
    rcases mem_or_exists_commute hXN htA hsA ht2 hs2 hs1 hsθ with h | ⟨w, hwA, hw2, hw1, hwt, htw⟩
    · exact h
    · exfalso
      obtain ⟨hab, h4⟩ := four_of_commute ht2 hw2 ht1 hw1 (Ne.symm hwt) htw
      refine hno _ ((closure_le _).mpr ?_) hab h4
      rintro y (rfl | rfl)
      · exact htA
      · exact hwA
  have htT : t ∈ thetaT 3 B := by
    simp only [thetaT, mem_iInf]
    exact fun x hx hx1 => hall x hx hx1
  have hodd := hpair.mem_S.2.2 B hBA hB9
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdvd : 2 ∣ Nat.card (thetaT 3 B) := hord ▸ Subgroup.orderOf_dvd_natCard _ htT
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem item2110JON_of_res12 (h211 : Item211)
    (h45 : Sec4.Item4_5) (h219 : Item219) (hAL : Item2110ALInI) (h612 : Sec6.Item6_12)
    (h69 : Sec6.Item6_9) : Item2110JON :=
  item2110JON_of_res10 h211 h45 h219 hAL h612 (kf2110HJThetaOdd_of_res12 h211 h45 hAL h69)

end Main

end CFSG.RankThree.PartTwo.Sec21
