module

public import CFSG.Quasithin.Background.E6TwentyTwo
public import CFSG.Quasithin.Background.E6TwentyFiveC
public import CFSG.Quasithin.Vol2.Ch4Sec3C57Use
public import CFSG.Quasithin.Vol2.Ch4Sec3Lem431
public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_ne_bot_of_isShort2 {B : Subgroup G} (hB : IsShort2 B) : pCoreOf 2 B ≠ ⊥ := by
  intro h
  have hU : blockU B = ⊥ := by
    rw [blockU, blockQ, h, Subgroup.commutator_bot_left]
  have hlt := hB.2.2.2.2.1
  rw [hU] at hlt
  exact absurd hlt (not_lt_bot)

theorem not_mem_centralizer_of_pow_three {B : Subgroup G} (hB : IsShort2 B) {x : G}
    (hxB : x ∈ B) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : x ∉ Subgroup.centralizer (B : Set G) := by
  intro hxC
  have hxO : x ∈ pCoreOf 2 B :=
    hB.2.1 ⟨hxB, Subgroup.centralizer_le (CFSG.LieType.BorelTits.pCoreOf_le 2 B) hxC⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B ⟨x, hxO⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have h1 := pow_gcd_eq_one.mpr ⟨hk', hx3⟩
  rw [hcop, pow_one] at h1
  exact hx1 h1

omit [Finite G] in
theorem three_dvd_card_of_type {B : Subgroup G}
    (ht : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 3 ∨ IsAltType B 5) :
    3 ∣ Nat.card B := by
  rcases ht with ⟨n, -, F, _, _, hF, α, hαs, -⟩ | ⟨α, hαs, -⟩ | ⟨α, hαs, -⟩
  · have h1 := Subgroup.card_range_dvd α
    rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hF]
      at h1
    refine dvd_trans (Dvd.dvd.mul_left ?_ _) h1
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 n
  · have h1 := Subgroup.card_range_dvd α
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top, hc] at h1
    exact h1
  · have h1 := Subgroup.card_range_dvd α
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top, hc] at h1
    exact dvd_trans (by norm_num) h1

theorem exists_pow_three_of_dvd {B : Subgroup G} (h3 : 3 ∣ Nat.card B) :
    ∃ x ∈ B, x ^ 3 = 1 ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 h3
  refine ⟨x, x.2, ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    simpa using congrArg Subtype.val h1
  · intro h1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    omega

theorem exists_ne_one_commute_of_normalized {p : ℕ} [Fact p.Prime] {T U : Subgroup G}
    (hT : IsPGroup p T) (hUT : U ≤ T) (hU : U ≠ ⊥)
    (hn : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ ∀ y ∈ T, y * z = z * y := by
  have hTnil : Group.IsNilpotent T := hT.isNilpotent
  have hUTn : (U.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr hn
  have hU' : U.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU')
  refine ⟨w, Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1,
    fun h1 => hw1 (Subtype.ext (Subtype.ext h1)), fun y hy => ?_⟩
  have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem exists_pow_three_commute {B : Subgroup G} {y : G} (hy3 : y ^ 3 = 1)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (h3 : 3 ∣ Nat.card B) :
    ∃ x ∈ B, x ^ 3 = 1 ∧ x ≠ 1 ∧ Commute x y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY3 : IsPGroup 3 (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨P, hPB, hP3, hP1, hPn⟩ :=
    exists_pSubgroup_le_normalized hY3 (Subgroup.zpowers_le.2 hyB) h3
  have hT3 : IsPGroup 3 ↥(Subgroup.zpowers y ⊔ P) := hY3.to_sup_of_normal_right' hP3 hPn
  obtain ⟨z, hzP, hz1, hzc⟩ := exists_ne_one_commute_of_normalized hT3 le_sup_right hP1
    (sup_le hPn Subgroup.le_normalizer)
  set P' := P ⊓ Subgroup.centralizer ({y} : Set G) with hP'def
  have hzP' : z ∈ P' := ⟨hzP, Subgroup.mem_centralizer_singleton_iff.2
    (hzc y (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))).symm⟩
  have hP'3 : IsPGroup 3 P' := hP3.to_le inf_le_left
  have hP'1 : Nat.card P' ≠ 1 := by
    intro h1
    have h2 := Subgroup.card_eq_one.mp h1
    rw [h2] at hzP'
    exact hz1 (Subgroup.mem_bot.1 hzP')
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P') 3
    (hP'3.card_eq_or_dvd.resolve_left hP'1)
  refine ⟨x, hPB x.2.1, ?_, ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    simpa using congrArg Subtype.val h1
  · intro h1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    omega
  · exact Subgroup.mem_centralizer_singleton_iff.1 x.2.2

theorem two_le_pRank_of_elems {p : ℕ} [hp : Fact p.Prime] {K C₁ : Subgroup G} {x₁ x₂ : G}
    (hx₁K : x₁ ∈ K) (hx₂K : x₂ ∈ K) (c12 : Commute x₁ x₂) (hp₁ : x₁ ^ p = 1)
    (hp₂ : x₂ ^ p = 1) (hx₁1 : x₁ ≠ 1) (h₁ : x₁ ∈ C₁) (h₂ : x₂ ∉ C₁) :
    2 ≤ CFSG.Open.pRank p K := by
  have hp1 : 1 < p := hp.out.one_lt
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : x₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact hx₁1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left x₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers x₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n)
  have hZ₁ : Subgroup.zpowers x₁ ≤ C₁ := Subgroup.zpowers_le.2 h₁
  have hx₂r : x₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact h₂ (ha ▸ hZ₁ (hr₁ a))
  have hc12 : ∀ a, Commute (F₁ a) x₂ := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ a)
    rw [← hk]
    exact c12.zpow_left k
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r hc12
  have hrange : F₂.range ≤ K := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    refine K.mul_mem ?_ (K.pow_mem hx₂K n)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ b)
    rw [← hk]
    exact K.zpow_mem hx₁K k
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₂ hpow₂ hcard₂ F₂ hF₂ hrange
  omega

omit [Finite G] in
theorem isBlock2_conjugate_of_normalizer {H B : Subgroup G} (hB : IsBlock2 H B) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : IsBlock2 H (CFSG.conjugate B g) := by
  have h1 := Setup.Campbell.isBlock2_map_conj hB g⁻¹
  have h2 : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg
  rw [h2] at h1
  exact h1

end Tools

section RankOne

variable {G : Type} [Group G]

theorem isRankOneSylow_of_lin2 {L : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hlin : IsLin2Type L n) : IsRankOneSylow (oTwoQuot ↥L) := by
  obtain ⟨F, _, _, hF, α, hαs, hker, -⟩ := hlin
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF'
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hLie : CFSG.Blueprint.LieModel (Matrix.SpecialLinearGroup (Fin 2) F) .PSL 2 2 n := by
    refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩, F, inferInstance,
      inferInstance, hF', CFSG.RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj⟩
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
  have hR : IsRankOneSylow (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds _ n hn hLie
  have e : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [hker])).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact hR.of_mulEquiv e.symm

theorem isRankOneSylow_of_alt5
    {L : Subgroup G} (h5 : IsAltType L 5) : IsRankOneSylow (oTwoQuot ↥L) := by
  obtain ⟨α, hαs, hker, -⟩ := h5
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨e₅⟩ := CFSG.Walter.Suzuki.nonempty_mulEquiv_psl24 (X := alternatingGroup (Fin 5)) h60
  have hR : IsRankOneSylow (alternatingGroup (Fin 5)) :=
    CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType (.linear 2 le_rfl e₅)
  have e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [hker])).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact hR.of_mulEquiv e.symm

variable [Finite G]

theorem isUniqueMaxOver_of_alt3 {B Q : Subgroup G} (h3 : IsAltType B 3) (hQ2 : IsPGroup 2 Q)
    (hQB : Q ≤ Subgroup.normalizer (B : Set G)) (hO₂B : pCoreOf 2 B ≤ Q) :
    CFSG.Quasithin.IsUniqueMaxOver (B ⊔ Q) Q Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα, hαk, -⟩ := id h3
  have hA3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hcardB : Nat.card B = Nat.card (pCoreOf 2 B) * 3 := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hα
    rw [hαk, hA3] at h1
    rw [← h1, pCoreOf, Subgroup.card_map_of_injective B.subtype_injective]
  have hBQ : B ⊓ Q = pCoreOf 2 B := by
    refine le_antisymm (fun x hx => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 B) hO₂B)
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hx.2⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : α ⟨x, hx.1⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hx.1⟩ : ↥B) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    have h3' : α ⟨x, hx.1⟩ = 1 := by
      have h4 : α ⟨x, hx.1⟩ ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥(alternatingGroup (Fin 3))) (x := α ⟨x, hx.1⟩)
        rwa [hA3] at this
      have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨h1, h4⟩
      rwa [hcop, pow_one] at this
    have hmem : (⟨x, hx.1⟩ : ↥B) ∈ CFSG.pCore 2 ↥B := by
      rw [← hαk, MonoidHom.mem_ker]
      exact h3'
    exact ⟨⟨x, hx.1⟩, by exact hmem, rfl⟩
  have hidx : Q.relIndex (B ⊔ Q) = 3 := by
    have h1 := Lin2.card_sup_mul_card_inf hQB
    rw [sup_comm, inf_comm, hBQ, hcardB] at h1
    have h2 := Subgroup.relIndex_mul_card Q (B ⊔ Q)
    rw [inf_of_le_left (le_sup_right : Q ≤ B ⊔ Q)] at h2
    have hpos : 0 < Nat.card (pCoreOf 2 B) := Nat.card_pos
    have hposQ : 0 < Nat.card Q := Nat.card_pos
    have h3 : Nat.card (B ⊔ Q : Subgroup G) = Nat.card Q * 3 := by
      have := h1
      nlinarith
    rw [h3] at h2
    exact Nat.eq_of_mul_eq_mul_right hposQ (h2.trans (mul_comm _ _))
  have hint : ∀ K : Subgroup G, Q ≤ K → K ≤ B ⊔ Q → K = Q ∨ K = B ⊔ Q := by
    intro K hQK hKBQ
    have h1 := Subgroup.relIndex_mul_relIndex Q K (B ⊔ Q) hQK hKBQ
    rw [hidx] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ h1) with h2 | h2
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hQK
    · right
      rw [h2] at h1
      have h3 : K.relIndex (B ⊔ Q) = 1 := by omega
      exact le_antisymm hKBQ (Subgroup.relIndex_eq_one.mp h3)
  have hQlt : Q < B ⊔ Q := by
    refine lt_of_le_of_ne le_sup_right fun h => ?_
    rw [← h, Subgroup.relIndex_self] at hidx
    omega
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hQlt, fun K hQK hK => ?_⟩, le_rfl⟩,
    fun N hN => ?_⟩
  · rcases hint K hQK.le hK with h | h
    · exact absurd h (ne_of_gt hQK)
    · exact h
  · rcases hint N hN.2 hN.1.1.le with h | h
    · exact h
    · exact absurd h (ne_of_lt hN.1.1)

end RankOne

section Unique

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isBlock2_of_pRank {H K B₁ B₂ : Subgroup G} (hH : CharTwo H) (hHK : H ≤ K)
    (hK : CFSG.Open.pRank 3 K ≤ 2) (hB₁ : IsBlock2 H B₁) (hB₂ : IsBlock2 H B₂)
    (h3₁ : 3 ∣ Nat.card B₁) (h3₂ : 3 ∣ Nat.card B₂)
    (hcase : CFSG.Open.pRank 3 H ≤ 1 ∨
      ∃ y ∈ K, y ∈ Subgroup.normalizer (H : Set G) ∧ y ^ 3 = 1 ∧ y ∉ H) :
    B₁ = B₂ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH2 : CFSG.Open.pRank 3 H ≤ 2 := (CFSG.SectionRank.pRank_mono (by norm_num) hHK).trans hK
  by_contra hne
  have hc12 : B₁ ≤ Subgroup.centralizer (B₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (distinctBlocksCommuteStatement H B₁ B₂ hH hB₁ hB₂ hne)
  obtain ⟨x₁, hx₁, hx₁3, hx₁1⟩ := exists_pow_three_of_dvd h3₁
  obtain ⟨x₂, hx₂, hx₂3, hx₂1⟩ := exists_pow_three_of_dvd h3₂
  rcases hcase with h1 | ⟨y, hyK, hyN, hy3, hyH⟩
  ·
    have := two_le_pRank_of_elems (p := 3) (C₁ := Subgroup.centralizer (B₂ : Set G))
      (hB₁.2.1 hx₁) (hB₂.2.1 hx₂) (Subgroup.mem_centralizer_iff.1 (hc12 hx₁) x₂ hx₂).symm
      hx₁3 hx₂3 hx₁1 (hc12 hx₁) (not_mem_centralizer_of_pow_three hB₂.1 hx₂ hx₂3 hx₂1)
    omega
  ·
    have horb : ∀ B : Subgroup G, IsBlock2 H B → 3 ∣ Nat.card B →
        y ∈ Subgroup.normalizer (B : Set G) := by
      intro B hB h3B
      by_contra hyB
      have hB1 : CFSG.conjugate B y ≠ B := fun he =>
        hyB (BenderBranch.conjugate_eq_iff_mem_normalizer.1 he)
      have hBy := isBlock2_conjugate_of_normalizer hB hyN
      have hByy := isBlock2_conjugate_of_normalizer hBy hyN
      have hB2 : CFSG.conjugate (CFSG.conjugate B y) y ≠ CFSG.conjugate B y := fun he =>
        hB1 (BenderBranch.conjugate_inj.1 he)
      have hB3 : CFSG.conjugate (CFSG.conjugate B y) y ≠ B := by
        intro he
        apply hB1
        have h1 : CFSG.conjugate (CFSG.conjugate (CFSG.conjugate B y) y) y =
            CFSG.conjugate B y := by rw [he]
        rw [BenderBranch.conjugate_conjugate, BenderBranch.conjugate_conjugate, ← pow_three, hy3,
          BenderBranch.conjugate_one] at h1
        exact h1.symm
      have c12 := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (distinctBlocksCommuteStatement H _ _ hH hB hBy hB1.symm)
      have c13 := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (distinctBlocksCommuteStatement H _ _ hH hB hByy hB3.symm)
      have c23 := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (distinctBlocksCommuteStatement H _ _ hH hBy hByy hB2.symm)
      obtain ⟨x, hx, hx3, hx1⟩ := exists_pow_three_of_dvd h3B
      set c := (MulAut.conj y⁻¹).toMonoidHom with hc
      have hcx : c x ∈ CFSG.conjugate B y := Subgroup.mem_map_of_mem _ hx
      have hccx : c (c x) ∈ CFSG.conjugate (CFSG.conjugate B y) y :=
        Subgroup.mem_map_of_mem _ hcx
      have hc3 : ∀ z : G, z ^ 3 = 1 → c z ^ 3 = 1 := fun z hz => by
        rw [← map_pow, hz, map_one]
      have hc1 : ∀ z : G, z ≠ 1 → c z ≠ 1 := fun z hz h => hz (by
        have := (MulAut.conj y⁻¹).injective (h.trans (map_one _).symm)
        exact this)
      have := three_le_pRank_of_commuting (p := 3) c12 c13 c23 hB.2.1 hBy.2.1 hByy.2.1 hx hcx
        hccx hx3 (hc3 x hx3) (hc3 _ (hc3 x hx3)) hx1
        (not_mem_centralizer_of_pow_three hBy.1 hcx (hc3 x hx3) (hc1 x hx1))
        (not_mem_centralizer_of_pow_three hByy.1 hccx (hc3 _ (hc3 x hx3))
          (hc1 _ (hc1 x hx1)))
      omega
    obtain ⟨z₁, hz₁, hz₁3, hz₁1, hz₁y⟩ := exists_pow_three_commute hy3 (horb B₁ hB₁ h3₁) h3₁
    obtain ⟨z₂, hz₂, hz₂3, hz₂1, hz₂y⟩ := exists_pow_three_commute hy3 (horb B₂ hB₂ h3₂) h3₂
    have := three_le_pRank_of_elems (p := 3) (C₁ := Subgroup.centralizer (B₂ : Set G)) (C₂ := H)
      (hHK (hB₁.2.1 hz₁)) (hHK (hB₂.2.1 hz₂)) hyK
      (Subgroup.mem_centralizer_iff.1 (hc12 hz₁) z₂ hz₂).symm hz₁y hz₂y hz₁3 hz₂3 hy3 hz₁1
      (hc12 hz₁) (not_mem_centralizer_of_pow_three hB₂.1 hz₂ hz₂3 hz₂1) (hB₁.2.1 hz₁)
      (hB₂.2.1 hz₂) hyH
    omega

end Unique

section Main

variable {G : Type} [Group G] [Finite G]

theorem as_E_6_14_of
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) : ASInputs.AS_E_6_14 := by
  intro G _ _ T M V W M₀ h hW1 hWV hres hH h3 hTM₀ hM₀Q hU hmax hidx2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  by_contra hWM
  have hWΓ : W ∈ gammaE64 V M := ⟨hWV, hW1, hWM, hres⟩
  set H := Subgroup.centralizer (W : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQ2 : IsPGroup 2 Q := h.isPGroup_Q
  have hW2 : IsPGroup 2 W := h.isPGroup_V.to_le hWV
  have hQsyl : IsSylowTwoOf Q H := e6_5_one h hWΓ
  have hcgs : cgsIn H Q ≤ H ⊓ M := (e6_5_two h hWΓ).1
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hH
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQsyl.1.trans h1)
  have hsq : IsSQTKIn H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G H Q (H ⊓ M) hsq hH hQsyl hcgs inf_le_left
  obtain ⟨i, hiM⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hWM
    intro x hx
    obtain ⟨m, hm', y, hy, rfl⟩ := hprod x hx
    refine M.mul_mem hm'.2 (Subgroup.list_prod_mem (K := M) fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hall j (hy j)
  set L := Lb i with hLdef
  have hLblock : IsBlock2 H L := (hLb i).1.1
  have htype := (hLb i).1.2
  have hJ : ⁅L, thompsonJ Q⁆ = L := (hLb i).2.2
  have hLH : L ≤ H := hLblock.2.1
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_type htype
  set K := Subgroup.normalizer (W : Set G) with hKdef
  have hK : CFSG.Open.pRank 3 K ≤ 2 :=
    (A1b.pRank_le_evenRank Nat.prime_three (by norm_num) ⟨W, hW1, hW2, rfl⟩).trans h.qtke.2.2
  have hHK : H ≤ K := Subgroup.centralizer_le_normalizer _
  have hKH : K ≤ Subgroup.normalizer (H : Set G) := by
    intro g hg
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, hHdef,
      BenderBranch.conjugate_centralizer, BenderBranch.conjugate_eq_iff_mem_normalizer.2 hg]
  have hcase : CFSG.Open.pRank 3 H ≤ 1 ∨
      ∃ y ∈ K, y ∈ Subgroup.normalizer (H : Set G) ∧ y ^ 3 = 1 ∧ y ∉ H := by
    rcases h3 with h3 | ⟨Y, hYN, hY3, hYC⟩
    · left
      rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) H,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact h3
    · right
      obtain ⟨⟨y, hyY⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (by rw [hY3])
      have hy3 : y ^ 3 = 1 := by
        have h1 := pow_orderOf_eq_one (⟨y, hyY⟩ : Y)
        rw [hy] at h1
        simpa using congrArg Subtype.val h1
      refine ⟨y, hYN hyY, hKH (hYN hyY), hy3, fun hyH => ?_⟩
      have h1 : y ∈ Y ⊓ H := ⟨hyY, hyH⟩
      rw [hYC] at h1
      have h2 : (⟨y, hyY⟩ : Y) = 1 := Subtype.ext (Subgroup.mem_bot.1 h1)
      rw [h2, orderOf_one] at hy
      omega
  have hKL : K ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hLg := isBlock2_conjugate_of_normalizer hLblock (hKH hg)
    have h3g : 3 ∣ Nat.card (CFSG.conjugate L g) := by
      rw [BenderBranch.card_conjugate]
      exact h3L
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.1
      (eq_of_isBlock2_of_pRank hH hHK hK hLblock hLg h3L h3g hcase).symm
  have hRN : Q ≤ Subgroup.normalizer (L : Set G) := hQsyl.1.trans (hHK.trans hKL)
  have hLB : IsBlock2 (L ⊔ Q) L :=
    ⟨hLblock.1, le_sup_left, ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hRN)).isSubnormal⟩
  have hsyl : IsSylowTwoOf Q (L ⊔ Q) := A4.isSylowTwoOf_mono hQsyl le_sup_right (sup_le hLH hQsyl.1)
  have hc : CharTwo (L ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hLblock.1.2.1 hQ2 hRN
  have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQsyl hLH hLblock.2.2
  have hO₂L : pCoreOf 2 L ≤ Q :=
    (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hLH hLblock.2.2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf hQsyl)
  have hum : ∃ N : Subgroup G, CFSG.Quasithin.IsUniqueMaxOver (L ⊔ Q) Q N := by
    rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
    · exact ⟨_, CFSG.Quasithin.H13.Ch4.isUniqueMaxOver_sup hRN
        (F1.rankOneAt_of_isRankOneSylow hSL (isRankOneSylow_of_lin2 hn hlin))⟩
    · exact ⟨Q, isUniqueMaxOver_of_alt3 h3 hQ2 hRN hO₂L⟩
    · exact ⟨_, CFSG.Quasithin.H13.Ch4.isUniqueMaxOver_sup hRN
        (F1.rankOneAt_of_isRankOneSylow hSL (isRankOneSylow_of_alt5 h5))⟩
  have hQM₀ : Q ≤ M₀ := inf_le_left.trans hTM₀
  have hC : C5.NoCommonNormal Q (L ⊔ Q) M₀ := by
    intro X hXQ hX1 hHX hMX
    have hX2 : IsPGroup 2 X := hQ2.to_le hXQ
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (⟨X, hX1, hX2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (X : Set G)))
    have hM'M : M' = M := hU.2 M' ⟨hM', hMX.trans hNM'⟩
    exact hiM ((le_sup_left.trans hHX).trans (hM'M ▸ hNM'))
  have hNL0 : M₀ ⊓ Subgroup.normalizer (L : Set G) ≠ M₀ := by
    intro heq
    have hM₀L : M₀ ≤ Subgroup.normalizer (L : Set G) := by
      rw [← heq]
      exact inf_le_right
    have hO := pCoreOf_ne_bot_of_isShort2 hLblock.1
    have hOp : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (⟨_, hO, hOp, rfl⟩ : IsTwoLocal (Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G)))
    have hNLO : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
    have hM'M : M' = M := hU.2 M' ⟨hM', (hM₀L.trans hNLO).trans hNM'⟩
    exact hiM ((Subgroup.le_normalizer.trans hNLO).trans (hM'M ▸ hNM'))
  have hle : M₀ ⊓ Subgroup.normalizer (W : Set G) ≤ M₀ ⊓ Subgroup.normalizer (L : Set G) :=
    inf_le_inf_left _ hKL
  have heqN : M₀ ⊓ Subgroup.normalizer (W : Set G) = M₀ ⊓ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    exact hNL0 (hmax.2 _ (lt_of_le_of_ne hle hne) inf_le_left)
  have hmaxL : IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (L : Set G)) := heqN ▸ hmax
  have h57 := CFSG.Quasithin.H13.Ch4.C57.relIndex_eq_two_of_block rfl hRN hLB
    (htype.imp (fun ⟨n, _, hn⟩ => ⟨n, hn⟩) id) hsyl hc hum hQM₀ hM₀Q hC hJ hmaxL
  rw [← heqN] at h57
  exact hidx2 h57

end Main

end E6

end CFSG.Quasithin
