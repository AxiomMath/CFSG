module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38Comm
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_theta_of_two_pow {L : Subgroup G}
    (hθodd : Odd (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype))) {x : G}
    (hx : x ∈ (aschbacherSolvableCore 3 L).map L.subtype) {k : ℕ} (hxk : x ^ 2 ^ k = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card ((aschbacherSolvableCore 3 L).map L.subtype) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : (aschbacherSolvableCore 3 L).map L.subtype)
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype)) :=
    Nat.Coprime.pow_left k hθodd.coprime_two_right.symm
  have h3 : orderOf x ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem card_le_eight_of_isPGroup {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hθodd : Odd (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype)))
    (hM : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) :
    Nat.card P ≤ 8 := by
  classical
  set θ := aschbacherSolvableCore 3 L with hθ
  have hPL : P ≤ L := hPC.trans inf_le_left
  let ψ : P →* L ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hPL)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, hk⟩ := hP x
    have hx1 : (QuotientGroup.mk' θ) (Subgroup.inclusion hPL x) = 1 := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    have hxk : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := eq_one_of_mem_theta_of_two_pow hθodd ⟨_, hx1, rfl⟩ hxk
    exact Subtype.ext this
  have hψM : ψ.range ≤ barCentralizer (Subgroup.zpowers a) L := by
    rw [← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩]
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hPL x, Subgroup.mem_subgroupOf.mpr (hPC x.2), rfl⟩
  have hdvd : Nat.card P ∣ 216 := by
    rw [← hM, Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact Subgroup.card_dvd_of_le hψM
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  rw [hm] at hdvd ⊢
  by_contra hlt
  have h4 : 4 ≤ m := by
    by_contra h4
    push Not at h4
    exact hlt (by interval_cases m <;> norm_num)
  have h16 : 2 ^ 4 ∣ 2 ^ m := Nat.pow_dvd_pow 2 h4
  exact absurd (h16.trans hdvd) (by norm_num)

open CFSG.Goldschmidt.G310 in
theorem exists_B0_syl {L : Subgroup G} {a b c : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hcL : thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1)
    (hB0 : IsPGroup 3 (Subgroup.closure {b, c}))
    (hθodd : Odd (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype)))
    (T : Subgroup (L ⧸ aschbacherSolvableCore 3 L))
    (hTM : T ≤ barCentralizer (Subgroup.zpowers a) L) (hT8 : Nat.card T = 8)
    (hM : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216)
    (hTβ : ∀ x ∈ T, thetaQuotMulAut L (compAction L ⟨b, hbN⟩) x ∈ T)
    (hTc : T ≤ u38Comm T (thetaQuotMulAut L (compAction L ⟨b, hbN⟩))) :
    ∃ Q : Subgroup G, Q ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧ IsPGroup 2 Q ∧
      Nat.card Q = 8 ∧ Subgroup.closure {b, c} ≤ Subgroup.normalizer (Q : Set G) ∧
      ⁅Q, Subgroup.zpowers b⁆ = Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set q : L →* L ⧸ θ := QuotientGroup.mk' θ with hq
  set β := thetaQuotMulAut L (compAction L ⟨b, hbN⟩) with hβ
  set C : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G) with hC
  set M := barCentralizer (Subgroup.zpowers a) L with hMdef
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 3) (by rw [hT8]; norm_num)
  have hcommab : Commute a b := hab
  have hcommac : Commute a c := hac
  have hgC : ∀ g ∈ Subgroup.normalizer (L : Set G), Commute a g → ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hgN hag x hx
    obtain ⟨hxL, hxa⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
    have hxa' : Commute x a := hxa
    exact (((hag.symm.mul_left hxa').mul_left hag.symm.inv_left)).eq
  have hlift : ∀ w ∈ M, ∃ x : L, (x : G) ∈ C ∧ q x = w := by
    intro w hw
    rw [hMdef, ← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hβq : ∀ x : L, β (q x) = q (compAction L ⟨b, hbN⟩ x) := fun x =>
    Sec4.thetaQuotMulAut_mk (compAction L ⟨b, hbN⟩) x
  have hcq : ∀ x : L, q (compAction L ⟨c, hcN⟩ x) = q x := fun x => by
    have := Sec4.thetaQuotMulAut_mk (compAction L ⟨c, hcN⟩) x
    rw [hcL] at this
    exact this.symm
  set H : Subgroup G := ((T.comap q).map L.subtype) ⊓ C with hH
  have hHC : H ≤ C := inf_le_right
  have hHL : H ≤ L := hHC.trans inf_le_left
  have hHmem : ∀ x : L, (x : G) ∈ C → q x ∈ T → (x : G) ∈ H := fun x hxC hxT =>
    Subgroup.mem_inf.mpr ⟨⟨x, hxT, rfl⟩, hxC⟩
  have hHmem' : ∀ x ∈ H, ∃ l : L, (l : G) = x ∧ q l ∈ T ∧ x ∈ C := by
    intro x hx
    obtain ⟨⟨l, hl, hlx⟩, hxC⟩ := Subgroup.mem_inf.mp hx
    exact ⟨l, hlx, hl, hxC⟩
  have hconjb : ∀ x ∈ H, b * x * b⁻¹ ∈ H := by
    intro x hx
    obtain ⟨l, hlx, hlT, hxC⟩ := hHmem' x hx
    have hxC' : b * x * b⁻¹ ∈ C := hgC b hbN hcommab x hxC
    have hl' : ((compAction L ⟨b, hbN⟩ l : L) : G) = b * x * b⁻¹ := by rw [← hlx]; rfl
    have hT' : q (compAction L ⟨b, hbN⟩ l) ∈ T := by rw [← hβq]; exact hTβ _ hlT
    rw [← hl'] at hxC' ⊢
    exact hHmem _ hxC' hT'
  have hconjc : ∀ x ∈ H, c * x * c⁻¹ ∈ H := by
    intro x hx
    obtain ⟨l, hlx, hlT, hxC⟩ := hHmem' x hx
    have hxC' : c * x * c⁻¹ ∈ C := hgC c hcN hcommac x hxC
    have hl' : ((compAction L ⟨c, hcN⟩ l : L) : G) = c * x * c⁻¹ := by rw [← hlx]; rfl
    have hT' : q (compAction L ⟨c, hcN⟩ l) ∈ T := by rw [hcq]; exact hlT
    rw [← hl'] at hxC' ⊢
    exact hHmem _ hxC' hT'
  have hbH := HeringU38.mem_normalizer_of_conj_cube (H := H) hb3 hconjb
  have hcH := HeringU38.mem_normalizer_of_conj_cube (H := H) hc3 hconjc
  have hBH : Subgroup.closure {b, c} ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hbH, hcH]
  have hH3 : ¬ 3 ∣ Nat.card H := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 h3
    obtain ⟨l, hlx, hlT, -⟩ := hHmem' x x.2
    have hx3 : (x : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hl3 : l ^ 3 = 1 := Subtype.ext (by simpa [hlx] using hx3)
    have hql3 : (⟨q l, hlT⟩ : T) ^ 3 = 1 := Subtype.ext (by simpa [← map_pow, hl3])
    obtain ⟨k, hk⟩ := hT2 ⟨q l, hlT⟩
    have hq1 : (⟨q l, hlT⟩ : T) = 1 := by
      have h1 : orderOf (⟨q l, hlT⟩ : T) ∣ 3 := orderOf_dvd_of_pow_eq_one hql3
      have h2 : orderOf (⟨q l, hlT⟩ : T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h12 : orderOf (⟨q l, hlT⟩ : T) ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
      have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
      rw [hcop] at h12
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h12)
    have hqli : q l = 1 := congrArg Subtype.val hq1
    have hlθ : l ∈ θ := (QuotientGroup.eq_one_iff l).mp hqli
    have hl1 : l = 1 :=
      KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hlθ (j := 1) (by simpa using hl3)
    have : x = 1 := Subtype.ext (by rw [← hlx, hl1]; rfl)
    rw [this, orderOf_one] at hx
    omega
  obtain ⟨Q, hQfus, -, hBQ⟩ := exists_invariant_sylow_containing (r := 3) (q := 2)
    Nat.prime_three Nat.prime_two hB0 hH3 hBH bot_le IsPGroup.of_bot
    Subgroup.le_normalizer_of_normal
  obtain ⟨hQH, hQ2, -⟩ := id hQfus
  have hQC : Q ≤ C := hQH.trans hHC
  have hQL : Q ≤ L := hQC.trans inf_le_left
  have hQ8le : Nat.card Q ≤ 8 := card_le_eight_of_isPGroup haN ha3 hθodd hM hQ2 hQC
  let ψ : H →* L ⧸ θ := q.comp (Subgroup.inclusion hHL)
  have hψT : ψ.range = T := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, hlx, hlT, -⟩ := hHmem' x x.2
      have : (Subgroup.inclusion hHL x) = l := Subtype.ext hlx.symm
      show q (Subgroup.inclusion hHL x) ∈ T
      rw [this]
      exact hlT
    · intro hw
      obtain ⟨x, hxC, rfl⟩ := hlift w (hTM hw)
      exact ⟨⟨x, hHmem x hxC hw⟩, rfl⟩
  have h8H : 8 ∣ Nat.card H := by
    have := Subgroup.card_range_dvd ψ
    rwa [hψT, hT8] at this
  obtain ⟨Qs, hQs⟩ := exists_sylow_of_fusionIsSylowIn hQfus
  have hQcard : Nat.card Q = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hQs, Subgroup.card_map_of_injective H.subtype_injective]
    exact Sylow.card_eq_multiplicity Qs
  have hfac : 3 ≤ (Nat.card H).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using h8H)
  have hQ8 : Nat.card Q = 8 := by
    refine le_antisymm hQ8le ?_
    rw [hQcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Nat.card H).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  let ψQ : Q →* L ⧸ θ := q.comp (Subgroup.inclusion hQL)
  have hψQinj : Function.Injective ψQ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, hk⟩ := hQ2 x
    have hx1 : (QuotientGroup.mk' θ) (Subgroup.inclusion hQL x) = 1 := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    have hxk : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_mem_theta_of_two_pow hθodd ⟨_, hx1, rfl⟩ hxk)
  have hψQT : ψQ.range ≤ T := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hlx, hlT, -⟩ := hHmem' x (hQH x.2)
    have : Subgroup.inclusion hQL x = l := Subtype.ext hlx.symm
    show q (Subgroup.inclusion hQL x) ∈ T
    rw [this]
    exact hlT
  have hψQeq : ψQ.range = T := by
    refine Subgroup.eq_of_le_of_card_ge hψQT ?_
    rw [hT8, ← Nat.card_congr (MonoidHom.ofInjective hψQinj).toEquiv, hQ8]
  have hbQ : b ∈ Subgroup.normalizer (Q : Set G) := hBQ (Subgroup.subset_closure (by simp))
  refine ⟨Q, hQC, hQ2, hQ8, hBQ, le_antisymm ?_ ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [commutatorElement_def]
    have hbk : b ^ k ∈ Subgroup.normalizer (Q : Set G) := Subgroup.zpow_mem _ hbQ k
    have h1 : b ^ k * x⁻¹ * (b ^ k)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hbk _).mp (Subgroup.inv_mem _ hx)
    have : x * b ^ k * x⁻¹ * (b ^ k)⁻¹ = x * (b ^ k * x⁻¹ * (b ^ k)⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx h1
  · set NQ : Subgroup G := ⁅Q, Subgroup.zpowers b⁆ with hNQ
    have hNQQ : NQ ≤ Q := by
      rw [hNQ, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [commutatorElement_def]
      have hbk : b ^ k ∈ Subgroup.normalizer (Q : Set G) := Subgroup.zpow_mem _ hbQ k
      have h1 : b ^ k * x⁻¹ * (b ^ k)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hbk _).mp (Subgroup.inv_mem _ hx)
      have : x * b ^ k * x⁻¹ * (b ^ k)⁻¹ = x * (b ^ k * x⁻¹ * (b ^ k)⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx h1
    have hTN : T ≤ (NQ.subgroupOf Q).map ψQ := by
      refine hTc.trans ?_
      unfold u38Comm
      rw [Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [← hψQeq] at hw
      obtain ⟨x₀, rfl⟩ := hw
      let x₁ : Q := ⟨b * x₀ * b⁻¹, (Subgroup.mem_normalizer_iff.mp hbQ _).mp x₀.2⟩
      have hψx₁ : ψQ x₁ = β (ψQ x₀) := by
        show q (Subgroup.inclusion hQL x₁) = β (q (Subgroup.inclusion hQL x₀))
        rw [hβq]
        rfl
      refine ⟨x₀ * x₁⁻¹, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr ?_
        have : ((x₀ * x₁⁻¹ : Q) : G) = ⁅(x₀ : G), b⁆ := by
          show (x₀ : G) * (b * x₀ * b⁻¹)⁻¹ = _
          rw [commutatorElement_def]
          group
        rw [this]
        exact Subgroup.commutator_mem_commutator x₀.2 (Subgroup.mem_zpowers b)
      · rw [map_mul, map_inv, hψx₁]
    have hcardle : Nat.card T ≤ Nat.card (NQ.subgroupOf Q) := by
      calc Nat.card T ≤ Nat.card ((NQ.subgroupOf Q).map ψQ) := Subgroup.card_le_of_le hTN
        _ = Nat.card (NQ.subgroupOf Q) := Subgroup.card_map_of_injective hψQinj
    have htop : NQ.subgroupOf Q = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      refine le_antisymm (Subgroup.card_le_card_group _) ?_
      rw [hQ8]
      rwa [hT8] at hcardle
    exact (Subgroup.subgroupOf_eq_top.mp htop)

end CFSG.RankThree.PartTwo.Sec8
