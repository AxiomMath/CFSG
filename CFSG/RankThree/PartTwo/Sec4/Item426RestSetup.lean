module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec4.Item426A6Models
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.Item426 (fixSub mem_fixSub fixSub_one thetaAut
  thetaAut_pow_eq_one map_mem_thetaComponentsIn_fixSub nonempty_quotTheta_map_equiv
  mem_normalizer_of_perfect_le eq_top_of_isPerfect_of_isSubnormal
  isQuasisimple_of_mem_thetaComponentsIn)

structure ConfigRest (X : Type) [Group X] [Finite X] (α : MulAut X) (P : Subgroup X) : Prop where
  quasisimple : IsQuasisimple X
  pow_three : α ^ 3 = 1
  mem : P ∈ thetaComponentsIn (fixSub α)
  central : ∃ z ∈ P, z ∈ Subgroup.center X ∧ z ≠ 1 ∧ z ^ 3 = 1

namespace ConfigRest

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem fixed (h : ConfigRest X α P) {x : X} (hx : x ∈ P) : α x = x :=
  le_of_mem_thetaComponentsIn h.mem hx

theorem isPerfect (h : ConfigRest X α P) : Group.IsPerfect P :=
  isPerfect_of_mem_thetaComponentsIn h.mem

theorem quotient_quasisimple (h : ConfigRest X α P) :
    IsQuasisimple (P ⧸ aschbacherSolvableCore 3 P) :=
  isQuasisimple_of_mem_thetaComponentsIn h.mem

theorem ne_bot (h : ConfigRest X α P) : P ≠ ⊥ := by
  obtain ⟨z, hz, -, hz1, -⟩ := h.central
  intro hP
  rw [hP, Subgroup.mem_bot] at hz
  exact hz1 hz

theorem false_of_center_eq_bot (h : ConfigRest X α P) (hZ : Subgroup.center X = ⊥) : False := by
  obtain ⟨z, -, hzZ, hz1, -⟩ := h.central
  rw [hZ, Subgroup.mem_bot] at hzZ
  exact hz1 hzZ

theorem center_ne_bot (h : ConfigRest X α P) : Subgroup.center X ≠ ⊥ :=
  fun hZ => h.false_of_center_eq_bot hZ

theorem three_dvd_card_center (h : ConfigRest X α P) : 3 ∣ Nat.card (Subgroup.center X) := by
  obtain ⟨z, -, hzZ, hz1, hz3⟩ := h.central
  have hord : orderOf (⟨z, hzZ⟩ : Subgroup.center X) = 3 := by
    refine orderOf_eq_prime (Subtype.ext ?_) (fun h' => hz1 (congrArg Subtype.val h'))
    simpa using hz3
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem eq_top_of_eq_one (h : ConfigRest X α P) (hα : α = 1) : P = ⊤ := by
  have hmem := h.mem
  rw [hα, fixSub_one] at hmem
  obtain ⟨P₀, hP₀, rfl⟩ := hmem
  have hs : (P₀.map (⊤ : Subgroup X).subtype).IsSubnormal :=
    hP₀.2.1.map (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  exact eq_top_of_isPerfect_of_isSubnormal h.quasisimple h.isPerfect hs h.ne_bot

theorem commute_of_eq_conj (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y) {p : X}
    (hp : p ∈ P) : y * p = p * y := by
  have h1 := h.fixed hp
  rw [hα, MulAut.conj_apply] at h1
  calc y * p = y * p * y⁻¹ * y := by group
    _ = p * y := by rw [h1]

theorem pow_three_mem_center (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y) :
    y ^ 3 ∈ Subgroup.center X := by
  have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, ← hα, h.pow_three]
  rw [Subgroup.mem_center_iff]
  intro g
  have h2 : y ^ 3 * g * (y ^ 3)⁻¹ = g := by
    have := congrArg (fun φ : MulAut X => φ g) h1
    simpa only [MulAut.conj_apply, MulAut.one_apply] using this
  calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
    _ = y ^ 3 * g := by group

end ConfigRest

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_pCore_center (K : Subgroup G) :
    IsPGroup 3 (inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G))) := by
  set Y := K ⊓ Subgroup.centralizer (K : Set G)
  rintro ⟨x, ⟨y, hy, rfl⟩⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Y)) ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : ((y : Y) : G) ^ 3 ^ k = 1 := by
    have := congrArg (fun u : CFSG.pCore 3 Y => ((u : Y) : G)) hk
    simpa using this
  simpa using h1

theorem configRest_of {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) {c : G}
    (hc3 : orderOf c = 3) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)))
    (hZne : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥)
    (hZc : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤
      Subgroup.center G) :
    3 ∣ Nat.card (Subgroup.center G) ∧ K ≤ L ∧
    ∃ hcN : c ∈ Subgroup.normalizer (L : Set G),
      ConfigRest (L ⧸ aschbacherSolvableCore 3 L) (thetaAut L hcN)
        ((K.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) with hZdef
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hKle := le_of_mem_thetaComponentsIn hK
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKle.trans inf_le_right
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hZK : Z ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2.1
  have hZ3 : IsPGroup 3 Z := isPGroup_pCore_center K
  have hZnt : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
  obtain ⟨n, hn, hcard⟩ := (hZ3.nontrivial_iff_card).mp hZnt
  have h3Z : 3 ∣ Nat.card Z := by
    rw [hcard]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨⟨w, hwZ⟩, hwo⟩ := exists_prime_orderOf_dvd_card' 3 h3Z
  have hwo' : orderOf w = 3 := by rwa [Subgroup.orderOf_mk] at hwo
  have hw1 : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hwo'
    norm_num at hwo'
  have hw3 : w ^ 3 = 1 := by rw [← hwo']; exact pow_orderOf_eq_one w
  have hwK : w ∈ K := hZK hwZ
  have hwc : w ∈ Subgroup.center G := hZc hwZ
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hwK
    exact hw1 hwK
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_perfect_le hL hKp hK1 hKL hKc
  have h3G : 3 ∣ Nat.card (Subgroup.center G) := by
    have hord : orderOf (⟨w, hwc⟩ : Subgroup.center G) = 3 := by rwa [Subgroup.orderOf_mk]
    rw [← hord]
    exact orderOf_dvd_natCard _
  refine ⟨h3G, hKL, hcN, hL.2.2, thetaAut_pow_eq_one L hcN hc3',
    map_mem_thetaComponentsIn_fixSub L hcN hc3' hK, ?_⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hwL : w ∈ L := hKL hwK
  have hwZL : (⟨w, hwL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hwc g)
  refine ⟨π ⟨w, hwL⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hwK), ?_, ?_, ?_⟩
  · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
      (Subgroup.mem_map_of_mem π hwZL)
  · rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    intro hmem
    have hord : orderOf (⟨⟨w, hwL⟩, hmem⟩ : N) ∣ 3 := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext ?_))
      simpa using hw3
    have hord2 : orderOf (⟨⟨w, hwL⟩, hmem⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have hθ3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · rw [orderOf_eq_one_iff] at h1
      exact hw1 (congrArg (fun u : N => ((u : L) : G)) h1)
    · exact hθ3 (h3 ▸ hord2)
  · rw [← map_pow]
    have : (⟨w, hwL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [this, map_one]

abbrev secQ {X : Type} [Group X] (P : Subgroup X) : Type :=
  (P ⧸ aschbacherSolvableCore 3 P) ⧸ Subgroup.center (P ⧸ aschbacherSolvableCore 3 P)

theorem center_secQ_eq_bot {X : Type} [Group X] {P : Subgroup X}
    (hP : IsQuasisimple (P ⧸ aschbacherSolvableCore 3 P)) : Subgroup.center (secQ P) = ⊥ := by
  have : Group.IsPerfect (P ⧸ aschbacherSolvableCore 3 P) := hP.1
  exact Item426.center_quotient_center_eq_bot
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))

theorem card_secQ_mul {X : Type} [Group X] (P : Subgroup X) :
    Nat.card (secQ P) * Nat.card (Subgroup.center (P ⧸ aschbacherSolvableCore 3 P)) =
      Nat.card (P ⧸ aschbacherSolvableCore 3 P) :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem threeMul_dvd {S : Type*} [Group S] [Finite S] {H : Subgroup S} {u : S}
    (hu : ∀ h ∈ H, u * h = h * u) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) {T : Type*} [Group T]
    (hT : Subgroup.center T = ⊥) {ψ : H →* T} (hψ : Function.Surjective ψ) :
    3 * Nat.card T ∣ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : Nat.card H = Nat.card T * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  by_cases huH : u ∈ H
  · have huZ : (⟨u, huH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hu g g.2).symm
    have hψu : ψ ⟨u, huH⟩ = 1 := by
      have h1 : ψ ⟨u, huH⟩ ∈ Subgroup.center T :=
        Subgroup.map_center_le_center hψ ⟨_, huZ, rfl⟩
      rw [hT] at h1
      exact h1
    have h3 : 3 ∣ Nat.card ψ.ker := by
      set x : ψ.ker := ⟨⟨u, huH⟩, hψu⟩ with hx
      have h := orderOf_dvd_natCard x
      have hxu : ((x : H) : S) = u := rfl
      rwa [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hxu, hord] at h
    have hdvd : 3 * Nat.card T ∣ Nat.card H := by
      obtain ⟨k, hk⟩ := h3
      rw [hH, hk]
      exact ⟨k, by ring⟩
    exact hdvd.trans (Subgroup.card_subgroup_dvd_card H)
  · have hdisj : H ⊓ Subgroup.zpowers u = ⊥ := by
      have hle : H ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers u := inf_le_right
      have hdvd : Nat.card (H ⊓ Subgroup.zpowers u : Subgroup S) ∣ 3 := by
        rw [← hord, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply huH
        have heq : H ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hord])
        have hm : u ∈ H ⊓ Subgroup.zpowers u := by
          rw [heq]
          exact Subgroup.mem_zpowers u
        exact hm.1
    have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (H : Set S) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hu h hh, mul_inv_cancel_right]
        exact hh
      · intro hh
        have hk := hu _ hh
        have h2 : u * h * u⁻¹ = h := by
          have h3 : u * (u * h * u⁻¹) = u * h := by rw [hk]; group
          exact mul_left_cancel h3
        rwa [h2] at hh
    have hcard := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hnorm hdisj
    rw [Nat.card_zpowers, hord] at hcard
    have hdvd : 3 * Nat.card T ∣ Nat.card (H ⊔ Subgroup.zpowers u : Subgroup S) := by
      rw [hcard, hH]
      exact ⟨Nat.card ψ.ker, by ring⟩
    exact hdvd.trans (Subgroup.card_subgroup_dvd_card _)

theorem card_dvd_card_centralizer {S : Type*} [Group S] [Finite S] {H : Subgroup S} {u : S}
    (hu : ∀ h ∈ H, u * h = h * u) {T : Type*} [Group T] {ψ : H →* T}
    (hψ : Function.Surjective ψ) : Nat.card T ∣ Nat.card (Subgroup.centralizer {u}) := by
  have hle : H ≤ Subgroup.centralizer {u} := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hu h hh).symm
  have hH : Nat.card H = Nat.card T * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  exact (Dvd.intro _ hH.symm).trans (Subgroup.card_dvd_of_le hle)

namespace ConfigRest

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem exists_surj (_h : ConfigRest X α P) :
    ∃ φ : P →* secQ P, Function.Surjective φ ∧
      ∀ p : P, (p : X) ∈ Subgroup.center X → φ p = 1 := by
  set θP := aschbacherSolvableCore 3 P with hθP
  set T := P ⧸ θP with hT
  refine ⟨(QuotientGroup.mk' (Subgroup.center T)).comp (QuotientGroup.mk' θP), ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  · intro p hp
    have hpZ : p ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hp g)
    have h1 : QuotientGroup.mk' θP p ∈ Subgroup.center T :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective θP) ⟨p, hpZ, rfl⟩
    change QuotientGroup.mk' (Subgroup.center T) (QuotientGroup.mk' θP p) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h1

theorem inner_image (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) :
    QuotientGroup.mk' (Subgroup.center X) y ≠ 1 ∧
      QuotientGroup.mk' (Subgroup.center X) y ^ 3 = 1 ∧
      (∀ q ∈ P.map (QuotientGroup.mk' (Subgroup.center X)),
        QuotientGroup.mk' (Subgroup.center X) y * q = q * QuotientGroup.mk' (Subgroup.center X) y) ∧
      ∃ ψ : P.map (QuotientGroup.mk' (Subgroup.center X)) →* secQ P,
        Function.Surjective ψ := by
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hy
  · rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h.pow_three_mem_center hα
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, h.commute_of_eq_conj hα hp]
  · obtain ⟨φ, hφ, hφZ⟩ := h.exists_surj
    let πP : P →* P.map π := π.subgroupMap P
    have hπP : Function.Surjective πP := π.subgroupMap_surjective P
    have hle : πP.ker ≤ φ.ker := by
      intro p hp
      have h1 : π p = 1 := congrArg Subtype.val hp
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hφZ p h1
    refine ⟨(QuotientGroup.lift πP.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective πP hπP).symm.toMonoidHom, ?_⟩
    intro a
    obtain ⟨p, rfl⟩ := hφ a
    refine ⟨πP p, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : (QuotientGroup.quotientKerEquivOfSurjective πP hπP).symm (πP p) =
        (p : P ⧸ πP.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl

theorem inner_dvd (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) :
    orderOf (QuotientGroup.mk' (Subgroup.center X) y) = 3 ∧
      3 * Nat.card (secQ P) ∣ Nat.card (X ⧸ Subgroup.center X) ∧
      Nat.card (secQ P) ∣
        Nat.card (Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center X) y}) := by
  obtain ⟨hu1, hu3, hu, ψ, hψ⟩ := h.inner_image hα hy
  exact ⟨orderOf_eq_prime hu3 hu1,
    threeMul_dvd hu hu1 hu3 (center_secQ_eq_bot h.quotient_quasisimple) hψ,
    card_dvd_card_centralizer hu hψ⟩

theorem inner_dvd_of_mulEquiv (h : ConfigRest X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {S : Type*} [Group S] (eS : X ⧸ Subgroup.center X ≃* S) :
    3 * Nat.card (secQ P) ∣ Nat.card S ∧
      ∃ x : S, orderOf x = 3 ∧ Nat.card (secQ P) ∣ Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨hord, h3, hC⟩ := h.inner_dvd hα hy
  set yb := QuotientGroup.mk' (Subgroup.center X) y
  refine ⟨Nat.card_congr eS.toEquiv ▸ h3, eS yb, by rw [MulEquiv.orderOf_eq]; exact hord, ?_⟩
  have hmap : (Subgroup.centralizer {yb}).map eS.toMonoidHom = Subgroup.centralizer {eS yb} := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : t * yb = yb * t := Subgroup.mem_centralizer_singleton_iff.mp ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      change eS t * eS yb = eS yb * eS t
      rw [← map_mul, ← map_mul, ht']
    · intro hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs
      refine ⟨eS.symm s, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
      apply eS.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hs]
  rw [← hmap, Subgroup.card_map_of_injective eS.injective]
  exact hC

end ConfigRest

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
