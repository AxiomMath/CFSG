module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Lev

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436 Vol2.KGNat
open scoped MatrixGroups commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}

theorem K₂_inf_pCoreOf_le' {K₂ KZ : Subgroup G} (hK₂ : K₂ ≤ KZ) :
    K₂ ⊓ pCoreOf 2 KZ ≤ pCoreOf 2 K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 KZ).to_le inf_le_right)
  intro k hk
  exact mem_normalizer_inf (Subgroup.le_normalizer hk) (le_normalizer_pCoreOf 2 KZ (hK₂ hk))

variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem mem_pCoreOf_of_commutator_mem {v : G} (hv : v ∈ K₂)
    (hc : ∀ k ∈ K₂, v * k * v⁻¹ * k⁻¹ ∈ pCoreOf 2 K₂) : v ∈ pCoreOf 2 K₂ := by
  have : CharP F 2 := s.charP
  have hz : s.levi ⟨v, hv⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := s.levi_surjective g
    have h1 : s.levi (⟨v, hv⟩ * k * ⟨v, hv⟩⁻¹ * k⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, s.ker_levi]
      exact (mem_pCoreOf_iff' _).mp (hc k k.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc s.levi k * s.levi ⟨v, hv⟩ =
          (s.levi ⟨v, hv⟩ * s.levi k * (s.levi ⟨v, hv⟩)⁻¹ * (s.levi k)⁻¹)⁻¹ *
            (s.levi ⟨v, hv⟩ * s.levi k) := by group
      _ = s.levi ⟨v, hv⟩ * s.levi k := by rw [h1, inv_one, one_mul]
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at hz
  have : (⟨v, hv⟩ : ↥K₂) ∈ s.levi.ker := hz
  rw [s.ker_levi] at this
  exact (mem_pCoreOf_iff' _).mpr this

theorem pRank_KZ_le_one (hF : A318Facts) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {KZ : Subgroup G} (hKZ : KZ ∈ cComp (Subgroup.centralizer (ZS : Set G)))
    (hK₂ : K₂ ≤ KZ) (hKZn : (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G))).Normal)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ m - 1) :
    CFSG.Open.pRank p KZ ≤ 1 ∨ (p = 3 ∧ A318Case2 (starImage 3 (KZ.subgroupOf
      (Subgroup.normalizer (ZS : Set G))))) := by
  classical
  set GZ := Subgroup.normalizer (ZS : Set G) with hGZ
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hr, hn2⟩ := hcon
  have hH : SQTKGroup ↥GZ := s.sqtkGroup_GZ
  have hSQ := SQTKHyp.of_sqtkGroup ↥GZ hH
  have hKZ' := cComp_normalizer hKZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp hKZ'
  have hLc := subgroupOf_mem_cComp hKZ'
  have hq := s.KZ_quasisimple h135 hR hC h36 h37 h38 h39 hKZ hK₂
  obtain ⟨e₀⟩ := L436.quotPCore_subgroupOf_mulEquiv hKZGZ
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hr' : 1 < CFSG.Open.pRank p (KZ.subgroupOf GZ) := by
    rw [L436.pRank_subgroupOf_eq_pRank hKZGZ hp]
    exact hr
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' hp hp2 hr'
  obtain ⟨y₁, hy₁Y, hyo⟩ := s.exists_elt_Y hpn
  have hy₁1 : y₁ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  have hyN : y₁ ∈ GZ := s.Y_le_normalizer_ZS hy₁Y
  have hyC : y₁ ∉ Subgroup.centralizer (ZS : Set G) := s.not_mem_centralizer_ZS hy₁Y hy₁1
  set y₁' : ↥GZ := ⟨y₁, hyN⟩ with hy'
  have hy'o : orderOf y₁' = p := by rw [← Subgroup.orderOf_coe]; exact hyo
  have hyKZ : y₁' ∉ KZ.subgroupOf GZ := fun h =>
    hyC (le_of_mem_cComp hKZ (Subgroup.mem_subgroupOf.mp h))
  rcases hconc with h1 | ⟨hp3, h2⟩ | ⟨hp3, -, h3⟩
  · apply hyKZ
    rw [h1]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [pow_one, hy'o]⟩
  · exact hn2 hp3 (hp3 ▸ h2)
  · subst hp3
    rcases h3 with h3a | h3b
    · apply hyKZ
      rw [h3a]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hy'o⟩
    · obtain ⟨sb, q, x, -, hxo, -, -, -, -, hcard, hconj⟩ := h3b
      set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
      set SK := starImage 3 (KZ.subgroupOf GZ) with hSK
      set ys := π y₁' with hys
      have hy3 : y₁ ^ 3 = 1 := by
        have := pow_orderOf_eq_one y₁
        rwa [hyo] at this
      have hyS : ys ∉ SK := fun h =>
        hyC (Setting436Sp4.mem_centralizer_of_mem_starImage (le_of_mem_cComp hKZ) hyN hyo h)
      have hys1 : ys ≠ 1 := fun h => hyS (h ▸ one_mem _)
      have hyso : orderOf ys = 3 := by
        have hy'3 : y₁' ^ 3 = 1 := by
          have := pow_orderOf_eq_one y₁'
          rwa [hy'o] at this
        have hd : orderOf ys ∣ 3 := orderOf_dvd_of_pow_eq_one (by
          rw [hys, ← map_pow, hy'3, map_one])
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hys1
        · exact h
      have hYc : Nat.card ↥(Subgroup.zpowers ys) = 3 := by rw [Nat.card_zpowers, hyso]
      have hYS : ¬ Subgroup.zpowers ys ≤ SK := fun h => hyS (h (Subgroup.mem_zpowers ys))
      obtain ⟨l, hlS, hYeq⟩ := hconj _ hYc hYS
      have hysmem : ys ∈ (Subgroup.zpowers x).map (MulAut.conj l).toMonoidHom :=
        hYeq ▸ Subgroup.mem_zpowers ys
      obtain ⟨z, hz, hzy⟩ := hysmem
      have hzy' : l * z * l⁻¹ = ys := hzy
      obtain ⟨v, hvK₂, hvy, hvm, hvl⟩ := s.exists_levi_lift hp hp2 hy₁Y hyo
        (⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, F))
      have hvl' : ((s.levi ⟨v, hvK₂⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
          !![1, 1; 0, 1] := by
        rw [hvl]
      have hrowv := SL3Pt.blk_row0 (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)
      have hvsq : v ^ 2 = 1 := s.sq_eq_one_of_unipotent h135 hR hC h37 h38 h39 hy₁Y hy₁1 hvK₂
        hvy (hvm ▸ hrowv.1) (hvm ▸ hrowv.2) hvl'
      have hvQ : v ∉ pCoreOf 2 K₂ := fun h => by
        have h1 : s.levi ⟨v, hvK₂⟩ = 1 := by
          rw [← MonoidHom.mem_ker, s.ker_levi]
          exact (mem_pCoreOf_iff' _).mp h
        have h2 := congrFun (congrFun (congrArg Subtype.val h1) 0) 1
        rw [hvl'] at h2
        simp at h2
      have hvKZ : v ∈ KZ := hK₂ hvK₂
      set v' : ↥GZ := ⟨v, hKZGZ hvKZ⟩ with hv'
      set vs := π v' with hvs
      have hvsS : vs ∈ SK := ⟨v', Subgroup.mem_subgroupOf.mpr hvKZ, rfl⟩
      have hvs2 : vs ^ 2 = 1 := by
        rw [hvs, ← map_pow]
        have : v' ^ 2 = 1 := Subtype.ext (by simpa using hvsq)
        rw [this, map_one]
      have hvsys : vs * ys = ys * vs := by
        rw [hvs, hys, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hvy.symm
      have hvs1 : vs ≠ 1 := by
        intro h1
        have hvO : v' ∈ CFSG.pPrimeCore 3 ↥GZ := (QuotientGroup.eq_one_iff _).mp h1
        set N := KZ ⊓ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype with hN
        have hNX : N ≤ KZ := inf_le_left
        have hON : (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype ≤
            Subgroup.normalizer (((CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype : Subgroup G) : Set G) :=
          Subgroup.le_normalizer
        have hGZO : GZ ≤ Subgroup.normalizer
            (((CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype : Subgroup G) : Set G) := by
          intro g hg
          rw [Subgroup.mem_normalizer_iff]
          intro w
          constructor
          · rintro ⟨w', hw', rfl⟩
            exact ⟨⟨g, hg⟩ * w' * ⟨g, hg⟩⁻¹,
              (CFSG.pPrimeCore_normal (p := 3) (G := ↥GZ)).conj_mem _ hw' _, rfl⟩
          · rintro ⟨w', hw', hw'e⟩
            refine ⟨⟨g, hg⟩⁻¹ * w' * ⟨g, hg⟩, ?_, ?_⟩
            · have := (CFSG.pPrimeCore_normal (p := 3) (G := ↥GZ)).conj_mem _ hw' ⟨g, hg⟩⁻¹
              simpa using this
            · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hw'e ⊢
              rw [hw'e]
              group
        have hXN : KZ ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
          mem_normalizer_inf (Subgroup.le_normalizer hk) (hGZO (hKZGZ hk))
        have hne : ¬ KZ ≤ N ⊔ pCoreOf 2 KZ := by
          intro hle
          have hO2 : pCoreOf 2 KZ ≤ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype := by
            intro w hw
            have hw' : (⟨w, (pCoreOf_le 2 KZ).trans hKZGZ hw⟩ : ↥GZ) ∈ CFSG.pPrimeCore 3 ↥GZ :=
              Setting436Sp4.pCoreOf_subgroupOf_le_pPrimeCore hKZGZ
                ((Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).1 hKZn) hw
            exact ⟨_, hw', rfl⟩
          have hsub : KZ ≤ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype :=
            hle.trans (sup_le inf_le_right hO2)
          obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₂) 3 (s.dvd_card_K₂ hpn)
          have haK : (a₀ : G) ∈ K₂ := a₀.2
          have hao : orderOf (a₀ : G) = 3 := by rw [Subgroup.orderOf_coe, ha₀]
          obtain ⟨a', ha', ha'e⟩ := hsub (hK₂ haK)
          have hdvd : 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥GZ) := by
            have h1 : orderOf a' = 3 := by
              rw [← hao, ← ha'e, Subgroup.coe_subtype, Subgroup.orderOf_coe]
            have h2 := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 ↥GZ) ha'
            rwa [h1] at h2
          have := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥GZ))
          exact absurd (Nat.Coprime.eq_one_of_dvd this hdvd) (by norm_num)
        have hvN : v ∈ N := ⟨hvKZ, ⟨v', hvO, rfl⟩⟩
        have hcomm := L436.commutator_mem_pCoreOf_of_quasisimple hq hNX hXN hne v hvN
        refine hvQ (s.mem_pCoreOf_of_commutator_mem hvK₂ fun k hk => ?_)
        have hvk : v * k * v⁻¹ * k⁻¹ ∈ K₂ :=
          mul_mem (mul_mem (mul_mem hvK₂ hk) (inv_mem hvK₂)) (inv_mem hk)
        exact K₂_inf_pCoreOf_le' hK₂ (Subgroup.mem_inf.mpr ⟨hvk, hcomm k (hK₂ hk)⟩)
      have hvso : orderOf vs = 2 := by
        have hd : orderOf vs ∣ 2 := orderOf_dvd_of_pow_eq_one hvs2
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hvs1
        · exact h
      set w := l⁻¹ * vs * l with hw
      have hwS : w ∈ SK := mul_mem (mul_mem (inv_mem hlS) hvsS) hlS
      have hwz : w * z = z * w := by
        have e : z = l⁻¹ * ys * l := by rw [← hzy']; group
        rw [hw, e]
        calc l⁻¹ * vs * l * (l⁻¹ * ys * l) = l⁻¹ * (vs * ys) * l := by group
          _ = l⁻¹ * (ys * vs) * l := by rw [hvsys]
          _ = l⁻¹ * ys * l * (l⁻¹ * vs * l) := by group
      have hz1 : z ≠ 1 := by
        intro h
        apply hys1
        rw [← hzy', h, mul_one, mul_inv_cancel]
      have hzx : Subgroup.zpowers z = Subgroup.zpowers x := by
        have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hz
        have hzo : orderOf z = 3 := by
          have hd : orderOf z ∣ 3 := by
            have := orderOf_dvd_of_mem_zpowers hz
            rwa [hxo] at this
          rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hz1
          · exact h
        exact Subgroup.eq_of_le_of_card_ge hle
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
      have hwx : w * x = x * w := by
        have hxz : x ∈ Subgroup.zpowers z := hzx ▸ Subgroup.mem_zpowers x
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
        exact (Commute.zpow_right hwz k)
      have hwo : orderOf w = 2 := by
        rw [hw, show l⁻¹ * vs * l = (MulAut.conj l⁻¹) vs by simp,
          MulEquiv.orderOf_eq]
        exact hvso
      have hwC : w ∈ SK ⊓ Subgroup.centralizer ({x} : Set _) :=
        ⟨hwS, Subgroup.mem_centralizer_singleton_iff.mpr hwx⟩
      have h2 : 2 ∣ Nat.card ↥(SK ⊓ Subgroup.centralizer ({x} : Set _)) := by
        have := Subgroup.orderOf_dvd_natCard _ hwC
        rwa [hwo] at this
      rw [hcard] at h2
      split_ifs at h2
      · have : Even (q * (q + 1)) := Nat.even_mul_succ_self q
        have e : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
        rw [e] at h2
        exact (Nat.not_even_iff_odd.mpr (Even.add_one this)) (even_iff_two_dvd.mpr h2)
      · have : Even (q * (q - 1)) := Nat.even_mul_pred_self q
        have e : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
          rcases Nat.eq_zero_or_pos q with h0 | hpos
          · subst h0; rfl
          · have : q ^ 2 - q = q * (q - 1) := by
              rw [Nat.mul_sub_one, sq]
            rw [this]
        rw [e] at h2
        exact (Nat.not_even_iff_odd.mpr (Even.add_one this)) (even_iff_two_dvd.mpr h2)

end Setting4311

end CFSG.Quasithin.H13.Ch4
