module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.C1PackS15212B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise
open CFSG.Quasithin.C1Pack12

namespace Der6D

variable {G : Type} [Group G] [Finite G] {T H : Subgroup G}

theorem inf_le_pCoreOf' (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* S152N.W3) {y : G}
    (hyK : y ∈ oTwoUpper H) (hyT : y ∈ T) : y ∈ pCoreOf 2 H := by
  have hyH : y ∈ H := oTwoUpper_le H hyK
  obtain ⟨k, hk⟩ := hT.2.1 ⟨y, hyT⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : (QuotientGroup.mk ⟨y, hyH⟩ : OTwoQuot H) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨y, hyH⟩ ^ 2 ^ k : ↥H) = 1 := Subtype.ext (by simpa using hk')
    rw [this]
    exact QuotientGroup.mk_one _
  have h3 : (QuotientGroup.mk ⟨y, hyH⟩ : OTwoQuot H) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff_mem_pCoreOf (⟨y, hyH⟩ ^ 3 : ↥H)).mpr (pow_three_mem_pCoreOf φ hyK)
  exact (mk_eq_one_iff_mem_pCoreOf ⟨y, hyH⟩).mp (eq_one_of_pow_two_pow_of_pow_three' h2 h3)

theorem xi_of_iso (hsyl : IsSylowTwoOf T H) (hTop : (pCoreOf 2 H) ≠ ⊥)
    (φ : OTwoQuot H ≃* S152N.W3) : IsXi T (oTwoUpper H) := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  have hsup : oTwoUpper H ⊔ T = H := oTwoUpper_sup_eq_of_sylow hsyl
  refine ⟨(C1Pack153.oTwoUpper_idem' H).symm, hsyl.1.trans (le_normalizer_oTwoUpper H), ?_, 3,
    Nat.prime_three, by norm_num, ?_, Or.inl ?_, ?_⟩
  · rw [hsup]
    exact hTop
  · intro x hx
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, pow_three_mem_pCoreOf φ hx⟩
  · rw [relIndex_pCoreOf_oTwoUpper φ]; norm_num
  · intro Y hY1 hY2 hYT
    have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Y := le_sup_right.trans hY1
    have hYH : Y ≤ H := hY2.trans hKH
    rcases S152N.eq_or_eq_of_le hsyl φ (le_sup_right : T ≤ Y ⊔ T)
      (sup_le hYH hsyl.1) with hN | hN
    · left
      refine le_antisymm (fun y hy => ?_) hY1
      have hyT : y ∈ T := hN ▸ (le_sup_left : Y ≤ Y ⊔ T) hy
      have hyQ : y ∈ pCoreOf 2 H := inf_le_pCoreOf' hsyl φ (hY2 hy) hyT
      exact Subgroup.mem_sup_right (hpK ▸ (⟨hY2 hy, hyQ⟩ : y ∈ oTwoUpper H ⊓ pCoreOf 2 H))
    · right
      refine le_antisymm hY2 (fun k hk => ?_)
      have hkH : k ∈ ((Y ⊔ T : Subgroup G) : Set G) := by
        rw [hN]
        exact hKH hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hYT] at hkH
      obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hkH
      have htK : t ∈ oTwoUpper H :=
        (oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem (hY2 hy)) hk |> fun h => by
          simpa using h
      have htQ : t ∈ pCoreOf 2 H := inf_le_pCoreOf' hsyl φ htK ht
      have htO : t ∈ pCoreOf 2 (oTwoUpper H) := hpK ▸ (⟨htK, htQ⟩ : t ∈ oTwoUpper H ⊓ pCoreOf 2 H)
      exact Y.mul_mem hy (hO2K htO)


theorem eq_of_normal_of_not_le_pCoreOf {L N : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) (hNL : N ≤ L)
    (hN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hNQ : ¬ N ≤ pCoreOf 2 L) : N = L := by
  classical
  have hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    have := hN l l.2 n (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  set π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥L, π x = 1 ↔ (x : G) ∈ pCoreOf 2 L := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  set ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    QuotientGroup.mk' _ with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := (QuotientGroup.eq_one_iff x).mp hx
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hsimple := hq.2.1
  have hNm : ((N.subgroupOf L).map π).Normal := Subgroup.Normal.map hNn π hπs
  have hNm2 : (((N.subgroupOf L).map π).map ρ).Normal := Subgroup.Normal.map hNm ρ hρs
  rcases hsimple.eq_bot_or_eq_top_of_normal (((N.subgroupOf L).map π).map ρ) with h | h
  · exfalso
    apply hNQ
    intro n hn
    have h1 : ρ (π ⟨n, hNL hn⟩) ∈ ((N.subgroupOf L).map π).map ρ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn))
    rw [h, Subgroup.mem_bot] at h1
    have h2 : π ⟨n, hNL hn⟩ = 1 := hρi (by rw [h1, map_one])
    exact (hker _).mp h2
  · have htop : (N.subgroupOf L).map π = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have h1 : ρ y ∈ ((N.subgroupOf L).map π).map ρ := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨z, hz, hzy⟩ := h1
      have : z = y := hρi hzy
      rwa [← this]
    refine C2Nine.eq_of_perfect_of_pow_mem hL hNL hNn fun x hx => ?_
    have h1 : π ⟨x, hx⟩ ∈ (N.subgroupOf L).map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := h1
    have hq1 : (n⁻¹ * ⟨x, hx⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      have : π (n⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hq1⟩
    refine ⟨k, ?_⟩
    have hq2 : (n⁻¹ * ⟨x, hx⟩ : ↥L) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxn : (⟨x, hx⟩ : ↥L) = n * (n⁻¹ * ⟨x, hx⟩) := by group
    have hmk : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ N.subgroupOf L) =
        QuotientGroup.mk (n⁻¹ * ⟨x, hx⟩) := by
      conv_lhs => rw [hxn]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have h3 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥L) ^ 2 ^ k) : ↥L ⧸ N.subgroupOf L) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, ← QuotientGroup.mk_pow, hq2, QuotientGroup.mk_one]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)


namespace W3Facts

open S152N S152N.W3

noncomputable local instance instFintype' : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEq' : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0' : DecidablePred (· ∈ N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem centralizer_N0_le : ∀ w : W3, (∀ n : W3, n ∈ N0 → w * n = n * w) → w ∈ N0 := by
  decide +kernel

theorem pow_four_of_pow_eight : ∀ w : W3, w ^ 8 = 1 → w ^ 4 = 1 := by
  decide +kernel

end W3Facts

noncomputable def piW {H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3) : ↥H →* S152N.W3 :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

omit [Finite G] in
theorem piW_eq_one_iff (φ : OTwoQuot H ≃* S152N.W3) {x : G} (hx : x ∈ H) :
    piW φ ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 H := by
  have h1 : piW φ ⟨x, hx⟩ = 1 ↔ (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : OTwoQuot H) = 1 :=
    φ.map_eq_one_iff
  rw [h1, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy

theorem not_autCyclic (hT : quasithinIsSylowTwo T) (hsyl : IsSylowTwoOf T H)
    (φ : OTwoQuot H ≃* S152N.W3) (hX : IsXi T (oTwoUpper H)) {P : Subgroup G}
    (hP : IsSylowIn 3 P (oTwoUpper H)) (hP9 : Nat.card P = 9) :
    ¬ EmptyFaithfulMultiple.AutCyclic T P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨c, hc, hcyc⟩
  have hTH : T ≤ H := hsyl.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hPK : P ≤ oTwoUpper H := hP.le
  have hPH : P ≤ H := hPK.trans hKH
  set ψ : ↥H →* S152N.W3 := piW φ with hψ
  have hψK : ∀ (x : G) (hx : x ∈ oTwoUpper H), ψ ⟨x, hKH hx⟩ ∈ S152N.W3.N0 := by
    intro x hx
    have hmem : (QuotientGroup.mk ⟨x, hKH hx⟩ : OTwoQuot H) ∈ imageOTwoQuot H (oTwoUpper H) :=
      mem_imageOTwoQuot_iff.mpr ⟨x, hKH hx, hx, rfl⟩
    rw [← map_imageOTwoQuot_oTwoUpper φ]
    exact Subgroup.mem_map_of_mem (φ : OTwoQuot H →* S152N.W3) hmem
  set ψP : ↥P →* S152N.W3 := ψ.comp (Subgroup.inclusion hPH) with hψP
  have hinj : Function.Injective ψP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((x : ↥P) : G) ∈ pCoreOf 2 H := (piW_eq_one_iff φ (hPH x.2)).mp hx
    have h2 : (x : G) ∈ P ⊓ pCoreOf 2 H := ⟨x.2, h1⟩
    have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 H) hP.isPGroup
      (pCoreOf_isPGroup 2 H)
    rw [hdis.eq_bot, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : ψP.range = S152N.W3.N0 := by
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_
    · obtain ⟨x, rfl⟩ := hy
      exact hψK x (hPK x.2)
    · rw [S152N.W3.card_N0]
      have : Nat.card ψP.range = Nat.card P :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
      rw [this, hP9]
  have hsurj : ∀ n ∈ S152N.W3.N0, ∃ x : G, ∃ hx : x ∈ P, ψ ⟨x, hPH hx⟩ = n := by
    intro n hn
    rw [← hrange] at hn
    obtain ⟨x, hx⟩ := hn
    exact ⟨x, x.2, hx⟩
  set b : S152N.W3 := ψ ⟨c, hTH hc.1⟩ with hb
  set D : Subgroup S152N.W3 := (T.subgroupOf H).map ψ with hD
  have hD2 : IsPGroup 2 D := IsPGroup.map (A4.isPGroup_subgroupOf_of_le hsyl.1 hsyl.2.1) ψ
  have hDmem : ∀ (t : G) (ht : t ∈ T), ψ ⟨t, hTH ht⟩ ∈ D := fun t ht =>
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ht)
  have hbD : b ∈ D := hDmem c hc.1
  have hDcard : Nat.card D = 8 := by
    have h1 := S152N.isSylowTwoOf_image hsyl φ
    have h2 := S152N.W3.index_eq_nine h1
    have hDD : ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        (φ : OTwoQuot H →* S152N.W3) = D := by
      rw [hD, Subgroup.map_map]
      rfl
    rw [hDD] at h2
    have h3 := D.index_mul_card
    rw [h2, S152N.W3.card_eq] at h3
    omega
  have hkey : ∀ (s : G) (hs : s ∈ T ⊓ Subgroup.normalizer (P : Set G)),
      ∃ k : ℕ, ψ ⟨s, hTH hs.1⟩ = b ^ k := by
    intro s hs
    obtain ⟨k, hk⟩ := hcyc s hs
    refine ⟨k, ?_⟩
    set a : S152N.W3 := ψ ⟨s, hTH hs.1⟩ with ha
    have haD : a ∈ D := hDmem s hs.1
    have hw : ∀ n ∈ S152N.W3.N0, (b ^ k)⁻¹ * a * n = n * ((b ^ k)⁻¹ * a) := by
      intro n hn
      obtain ⟨x, hxP, rfl⟩ := hsurj n hn
      have h1 : (⟨s, hTH hs.1⟩ : ↥H) * ⟨x, hPH hxP⟩ * (⟨s, hTH hs.1⟩ : ↥H)⁻¹ =
          (⟨c, hTH hc.1⟩ : ↥H) ^ k * ⟨x, hPH hxP⟩ * ((⟨c, hTH hc.1⟩ : ↥H) ^ k)⁻¹ :=
        Subtype.ext (hk x hxP)
      have h2 := congrArg ψ h1
      simp only [map_mul, map_inv, map_pow] at h2
      calc (b ^ k)⁻¹ * a * ψ ⟨x, hPH hxP⟩
          = (b ^ k)⁻¹ * (a * ψ ⟨x, hPH hxP⟩ * a⁻¹) * a := by group
        _ = (b ^ k)⁻¹ * (b ^ k * ψ ⟨x, hPH hxP⟩ * (b ^ k)⁻¹) * a := by rw [h2]
        _ = ψ ⟨x, hPH hxP⟩ * ((b ^ k)⁻¹ * a) := by group
    have hwN0 := W3Facts.centralizer_N0_le ((b ^ k)⁻¹ * a) hw
    have hw3 : ((b ^ k)⁻¹ * a) ^ 3 = 1 := S152N.W3.pow_three_of_mem_N0 _ hwN0
    have hwD : (b ^ k)⁻¹ * a ∈ D := D.mul_mem (D.inv_mem (D.pow_mem hbD k)) haD
    obtain ⟨j, hj⟩ := hD2 ⟨_, hwD⟩
    have hj' : ((b ^ k)⁻¹ * a) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hw1 := eq_one_of_pow_two_pow_of_pow_three' hj' hw3
    calc a = b ^ k * ((b ^ k)⁻¹ * a) := by group
      _ = b ^ k := by rw [hw1, mul_one]
  have hpX : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, relIndex_pCoreOf_oTwoUpper φ]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hTeq := hX.eq_pCoreOf_sup_normalizer hT (by norm_num : 3 ≠ 2) hpX hP
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  have hTN : T ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    inf_le_left.trans (hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)))
  have hall : ∀ (t : G) (ht : t ∈ T), ∃ k : ℕ, ψ ⟨t, hTH ht⟩ = b ^ k := by
    intro t ht
    have ht' : t ∈ pCoreOf 2 (oTwoUpper H) ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) := by
      rw [← hTeq]; exact ht
    obtain ⟨q, hq, s, hs, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hTN).1 ht'
    have hqH : q ∈ pCoreOf 2 H := (hpK ▸ hq : q ∈ oTwoUpper H ⊓ pCoreOf 2 H).2
    have hq1 : ψ ⟨q, hKH (hpK ▸ hq : q ∈ oTwoUpper H ⊓ pCoreOf 2 H).1⟩ = 1 :=
      (piW_eq_one_iff φ _).mpr hqH
    obtain ⟨k, hk⟩ := hkey s hs
    refine ⟨k, ?_⟩
    have : (⟨q * s, hTH ht⟩ : ↥H) = ⟨q, hKH (hpK ▸ hq : q ∈ oTwoUpper H ⊓ pCoreOf 2 H).1⟩ *
        ⟨s, hTH hs.1⟩ := rfl
    rw [this, map_mul, hq1, one_mul, hk]
  have hDle : D ≤ Subgroup.zpowers b := by
    intro y hy
    obtain ⟨⟨t, htH⟩, ht, rfl⟩ := hy
    obtain ⟨k, hk⟩ := hall t (Subgroup.mem_subgroupOf.mp ht)
    rw [hk]
    exact ⟨k, by simp⟩
  have h8 : 8 ≤ orderOf b := by
    have := Subgroup.card_le_of_le hDle
    rwa [hDcard, Nat.card_zpowers] at this
  have hdvd : orderOf b ∣ 8 := by
    have := Subgroup.orderOf_dvd_natCard D hbD
    rwa [hDcard] at this
  have hord : orderOf b = 8 := le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) h8
  have hb8 : b ^ 8 = 1 := by rw [← hord]; exact pow_orderOf_eq_one b
  have hb4 := W3Facts.pow_four_of_pow_eight b hb8
  have := orderOf_dvd_of_pow_eq_one hb4
  rw [hord] at this
  omega

end Der6D

end CFSG.Quasithin
