module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmD
public import CFSG.Quasithin.EmptyFaithful.SBc5Three
public import CFSG.Quasithin.EmptyFaithful.T1515eC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Sec1211Ns

theorem exists_starImage_surj {G : Type} [Group G] [Finite G] {X L : Subgroup G} (hLX : L ≤ X)
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ρ : ↥(starImage 3 (L.subgroupOf X)) →* ↥L ⧸ CFSG.pCore 2 ↥L,
      Function.Surjective ρ ∧ ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hq
  have hN : ∀ l : ↥L, Subgroup.inclusion hLX l ∈ CFSG.pPrimeCore 3 ↥X → l ∈ CFSG.pCore 2 ↥L := by
    let N₀ : Subgroup ↥L := (CFSG.pPrimeCore 3 ↥X).comap (Subgroup.inclusion hLX)
    have hN₀ : N₀.Normal := Subgroup.Normal.comap inferInstance _
    have hM₀ : (N₀.map q).Normal := hN₀.map q (QuotientGroup.mk'_surjective _)
    intro l hl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map q) with hb | ht
    · have h1 : q l ∈ N₀.map q := Subgroup.mem_map_of_mem q hl
      rw [hb, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ CFSG.pCore 2 ↥L) 3 h3
      obtain ⟨m, hm, rfl⟩ := (ht ▸ Subgroup.mem_top z : z ∈ N₀.map q)
      have hm' : Subgroup.inclusion hLX m ∈ CFSG.pPrimeCore 3 ↥X := hm
      have h1 : orderOf (q m) ∣ orderOf m := orderOf_map_dvd q m
      have h2 : orderOf m = orderOf (Subgroup.inclusion hLX m) :=
        (orderOf_injective _ (Subgroup.inclusion_injective hLX) m).symm
      have h4 : orderOf (⟨Subgroup.inclusion hLX m, hm'⟩ : ↥(CFSG.pPrimeCore 3 ↥X)) ∣
          Nat.card ↥(CFSG.pPrimeCore 3 ↥X) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h4
      rw [hz] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
        (h1.trans (h2 ▸ h4))
  let π₁ : ↥(L.subgroupOf X) →* ↥(starImage 3 (L.subgroupOf X)) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)).subgroupMap (L.subgroupOf X)
  have hπ₁ : Function.Surjective π₁ := MonoidHom.subgroupMap_surjective _ _
  let e₀ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let φ : ↥(L.subgroupOf X) →* ↥L ⧸ CFSG.pCore 2 ↥L := q.comp e₀.toMonoidHom
  have hle : π₁.ker ≤ φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) (y : ↥X) = 1 := by
      have := congrArg Subtype.val hy
      simpa [π₁] using this
    have hyN : (y : ↥X) ∈ CFSG.pPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 h1
    have h2 : e₀ y ∈ CFSG.pCore 2 ↥L := hN (e₀ y) (by
      have e : Subgroup.inclusion hLX (e₀ y) = (y : ↥X) := Subtype.ext rfl
      rw [e]
      exact hyN)
    show q (e₀ y) = 1
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2
  let ρ : ↥(starImage 3 (L.subgroupOf X)) →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (MonoidHom.liftOfSurjective π₁ hπ₁) ⟨φ, hle⟩
  have hρ : ∀ y, ρ (π₁ y) = φ y := fun y => by
    simp [ρ]
  refine ⟨ρ, fun z => ?_, fun y hy h3y => ?_⟩
  · obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
    exact ⟨π₁ (e₀.symm l), by rw [hρ]; simp [φ, hq]⟩
  · obtain ⟨y', rfl⟩ := hπ₁ y
    rw [hρ] at hy
    have hx2 : e₀ y' ∈ CFSG.pCore 2 ↥L := by
      have hy' : q (e₀ y') = 1 := hy
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hx2⟩
    have hxa : y' ^ 2 ^ a = 1 := by
      apply e₀.injective
      rw [map_pow, map_one]
      exact congrArg Subtype.val ha
    have hpow : (π₁ y') ^ 2 ^ a = 1 := by rw [← map_pow, hxa, map_one]
    have h32 : 3 ∣ 2 ^ a := h3y.trans (orderOf_dvd_of_pow_eq_one hpow)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega

theorem not_a318Case2_of_surj' {Q X : Type} [Group Q] [Group X] [Finite X] {S : Subgroup Q}
    (hS : A318Exclusion X) (ρ : ↥S →* X) (hρ : Function.Surjective ρ) : ¬ A318Case2 S := by
  rintro ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩
  subst hq
  exact hS.noImage _ s r k hrp hk1 hPSL hmod ρ hρ

theorem not_a318Case3Group_of_surj' {Q X : Type} [Group Q] [Group X] [Finite X] [Finite Q]
    {S : Subgroup Q} (hS : A318Exclusion X) (ρ : ↥S →* X) (hρ : Function.Surjective ρ)
    (hker : ∀ y, ρ y = 1 → ¬ 3 ∣ orderOf y) : ¬ A318Case3Group ↥S := by
  intro h3
  obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3
  have hzc : ρ z ∈ Subgroup.center X := Subgroup.map_center_le_center hρ ⟨z, hzcen, rfl⟩
  rw [hS.center_eq_bot, Subgroup.mem_bot] at hzc
  exact hker z hzc (by rw [hz])

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem mem_cComp_normalizer (hyp : Hyp121 G T L V V₁ V₂ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    L ∈ cComp (Subgroup.normalizer (L : Set G)) := by
  obtain ⟨hne, hperf, -, hmin⟩ := cComp_of_isLocal hyp.maximal.1
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  refine ⟨hne, hperf, ?_, fun K hKL hKne hKperf hKsub => ?_⟩
  · exact IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer
      (IsSubnormal.refl _)
  · exact hmin K hKL hKne hKperf
      (A3.subnormal_of_le_of_le hKsub (hKL.le.trans le_sup_left) hLT)

theorem pCoreOf_normalizer_ne_bot (hyp : Hyp121 G T L V V₁ V₂ n) :
    pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
  obtain ⟨hN, -, -⟩ := hyp.reduced
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hyp.le).mp hN
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hyp.le hMV hV2
  intro hb
  rw [hb] at hle
  exact Sec121Thm.ne_bot_of_hyp121 hyp (le_bot_iff.mp hle)

theorem a318Exclusion_of_hyp121 (h34 : L34NotL42Fact1515e) (hyp : Hyp121 G T L V V₁ V₂ n) :
    A318Exclusion (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := hyp.iso
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hP : IsPSL n 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := SBc5.isPSL_two_of_statedSL hn3
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)))
  rcases hyp.rank with rfl | rfl
  · exact a318Exclusion_psl42 h34 hP
  · exact a318Exclusion_psl52 hP

end Sec1211Ns

theorem lem1211NormalA318_of (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h34 : L34NotL42Fact1515e) : Lem1211NormalA318 := by
  intro G _ _ T L V V₁ V₂ n hyp hTL x hx hx3
  have hS := Sec1211Ns.a318Exclusion_of_hyp121 h34 hyp
  have hH : SQTKGroup ↥(Subgroup.normalizer (L : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian
      (Sec1211Ns.pCoreOf_normalizer_ne_bot hyp)
  have hr : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [R3c.pRank_three_eq_pCore_quotient L]
    exact hS.rank
  obtain ⟨ρ, hρ, hker⟩ :=
    Sec1211Ns.exists_starImage_surj Subgroup.le_normalizer hS.simple hS.three_dvd_card
  have heq := SBc5.eq_oPrimeResidualOf_of_a318 hF h36 h38 hH
    (Sec1211Ns.mem_cComp_normalizer hyp hTL) (Sec121Thm.isQuasisimple_of_hyp121 hyp) hr
    (Sec1211Ns.not_a318Case2_of_surj' hS ρ hρ) (Sec1211Ns.not_a318Case3Group_of_surj' hS ρ hρ hker)
  rw [heq]
  exact Subgroup.subset_closure ⟨hx, hx3⟩

end CFSG.Quasithin.H13
