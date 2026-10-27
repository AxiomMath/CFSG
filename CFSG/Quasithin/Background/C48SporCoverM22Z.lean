module

public import CFSG.Quasithin.Background.C48SporCoverE8
public import CFSG.Quasithin.Background.C31SporL
public import CFSG.Quasithin.Vol2.KGFactC31M22
public import CFSG.Sporadic.Recognition.M22MultiplierCert

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_centralizes_of_m22
    {X : Type} [Group X] (e : X ≃* KGC31.M22.G₀) {N : Subgroup X}
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1) {y t : X}
    (hyN : y ∈ Subgroup.normalizer (N : Set X)) (hy7 : orderOf y = 7) (htN : t ∈ N)
    (hyt : y * t * y⁻¹ ≠ t) {c : X} (hc : ∀ n ∈ N, c * n = n * c) : c ∈ N := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hP, hPi⟩ := KGC31.M22.sylow_of_order KGC31.M22.orderOf_x7 (by norm_num)
  obtain ⟨g, hg⟩ := KGC31.exists_conj_mem_of_sylow hP hPi (y := e y) ⟨1, by
    rw [pow_one, ← hy7, ← orderOf_injective e.toMonoidHom e.injective y]
    exact pow_orderOf_eq_one _⟩
  set ψ : X →* KGC31.M22.G₀ := (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom with hψ
  have hψi : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp e.injective
  have hψa : ∀ a, ψ a = g⁻¹ * e a * g := fun a => by
    simp [hψ]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hyt
    group
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hN2 t htN) ht1
  have hU := KGC31.M22.orbSub_cases7 (y := ψ y) (t := ψ t) (by rw [hψa]; exact hg)
    (by rw [orderOf_injective ψ hψi]; exact ht2)
    (fun h => hyt (hψi (by rwa [map_mul, map_mul, map_inv])))
    (fun j _ => by
      have h1 := hNc t htN _ (conj_pow_mem hyN htN j)
      have h2 := congrArg ψ h1
      simp only [map_mul, map_pow, map_inv] at h2
      rw [inv_pow]
      exact h2)
  rw [← KGC31.orbSub_map] at hU
  have hcU : ψ c ∈ Subgroup.centralizer ((KGC31.orbSub y t).map ψ : Set KGC31.M22.G₀) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hc w (KGC31.orbSub_le hyN htN hw)]
  rw [hU] at hcU
  have h1 := KGC31.M22.cent_e8 hcU
  rw [← hU] at h1
  obtain ⟨w, hw, hwc⟩ := h1
  rw [← hψi hwc]
  exact KGC31.orbSub_le hyN htN hw

theorem eq_one_of_centralizes_of_m22
    {X : Type} [Group X]
    (e : X ≃* KGC31.M22.G₀) {B N : Subgroup X} (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set X)) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hN2 : ∀ a ∈ N, a * a = 1) (hN8 : Nat.card N = 8) {y t : X} (hyB : y ∈ B)
    (hy7 : orderOf y = 7) (htN : t ∈ N) (hyt : y * t * y⁻¹ ≠ t) {c : X}
    (hc : ∀ b ∈ B, c * b = b * c) : c = 1 := by
  have hcN := mem_of_centralizes_of_m22 e hNc hN2 (hBN hyB) hy7 htN hyt
    (fun n hn => hc n (hNB hn))
  exact eq_one_of_conj_eq hN8 (hy7 ▸ pow_orderOf_eq_one y) (hBN hyB) htN hyt hcN
    (by rw [← hc y hyB, mul_inv_cancel_right])

omit [Finite G] in
theorem isPGroup_center_of {K : Subgroup G} (hZ : IsPGroup 2 ↥(centerOf K)) :
    IsPGroup 2 ↥(Subgroup.center ↥K) := by
  rintro ⟨z, hz⟩
  have hzZ : (z : G) ∈ centerOf K := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)⟩
  obtain ⟨n, hn⟩ := hZ ⟨_, hzZ⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem mk_mem_of_mem_pCoreOf {K M₀ : Subgroup G} (hM₀K : M₀ ≤ K)
    {N₀ : Subgroup ↥(imageModCenter K M₀)} [N₀.Normal]
    (hq : C31Spor.QuasiNoTwo (↥(imageModCenter K M₀) ⧸ N₀)) {v : G} (hv : v ∈ pCoreOf 2 M₀)
    (hvK : v ∈ K) :
    QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩ ∈ N₀.map (imageModCenter K M₀).subtype := by
  set φ := (QuotientGroup.mk' N₀).comp (C31Spor.toImageModCenter hM₀K) with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N₀).comp (C31Spor.toImageModCenter_surjective hM₀K)
  have hPφ : (CFSG.Open.pCore 2 ↥M₀).map φ = ⊥ :=
    hq.2 _ ((CFSG.LieType.BorelTits.pCore_normal 2).map φ hφs)
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map φ)
  obtain ⟨y, hy, hyv⟩ := hv
  have h1 : φ y = 1 := by
    have : φ y ∈ (CFSG.Open.pCore 2 ↥M₀).map φ := Subgroup.mem_map_of_mem φ hy
    rwa [hPφ, Subgroup.mem_bot] at this
  rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  refine ⟨_, h1, ?_⟩
  show QuotientGroup.mk' _ (Subgroup.inclusion hM₀K y) = QuotientGroup.mk' _ ⟨v, hvK⟩
  congr 1
  exact Subtype.ext hyv

theorem exists_order_seven_moving {K M₀ V : Subgroup G} (hM₀K : M₀ ≤ K)
    (hVO₂ : V ≤ pCoreOf 2 M₀) (hVM : V ≤ M₀) (hVc : ⁅V, M₀⁆ = V) (hVne : V ≠ ⊥)
    {N₀ : Subgroup ↥(imageModCenter K M₀)} [N₀.Normal] (hN₀p : IsPGroup 2 ↥N₀)
    (hN₀c : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a) (hYs : IsSimpleGroup (↥(imageModCenter K M₀) ⧸ N₀))
    (hq : C31Spor.QuasiNoTwo (↥(imageModCenter K M₀) ⧸ N₀))
    (h7 : 7 ∣ Nat.card (↥(imageModCenter K M₀) ⧸ N₀)) :
    ∃ y : ↥(imageModCenter K M₀), orderOf y = 7 ∧ ∃ t ∈ N₀, y * t * y⁻¹ ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  have hdvd : 7 ∣ Nat.card ↥(imageModCenter K M₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀]
    exact Dvd.dvd.mul_right h7 _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
  set C₀ := Subgroup.centralizer (N₀ : Set ↥(imageModCenter K M₀)) with hC₀
  have hyC : y ∈ C₀ := Subgroup.mem_centralizer_iff.mpr fun n hn => by
    calc n * y = y * n * y⁻¹ * y := by rw [hcon y hy7 n hn]
      _ = y * n := by group
  have : (C₀.map (QuotientGroup.mk' N₀)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N₀)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C₀.map (QuotientGroup.mk' N₀)) with hb | ht'
  ·
    have h1 : QuotientGroup.mk' N₀ y = 1 := by
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N₀) hyC
      rwa [hb, Subgroup.mem_bot] at this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := hN₀p ⟨y, h1⟩
    have h2 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hy7] at h3
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : (7 : ℕ).Prime).dvd_of_dvd_pow h3)
    omega
  ·
    have hcen : ∀ g : ↥(imageModCenter K M₀), ∀ n ∈ N₀, g * n = n * g := by
      intro g n hn
      obtain ⟨c, hc, hcg⟩ : QuotientGroup.mk' N₀ g ∈ C₀.map (QuotientGroup.mk' N₀) := by
        rw [ht']
        trivial
      have hk : c⁻¹ * g ∈ N₀ := QuotientGroup.eq.mp hcg
      have hg : g = c * (c⁻¹ * g) := by group
      rw [hg, mul_assoc, hN₀c _ hk n hn, ← mul_assoc,
        (Subgroup.mem_centralizer_iff.mp hc n hn).symm, mul_assoc]
    apply hVne
    have hVZ : V ≤ centerOf K := by
      rw [← hVc, Subgroup.commutator_le]
      intro v hv m hm
      have hvK : v ∈ K := hM₀K (hVM hv)
      have hmK : m ∈ K := hM₀K hm
      obtain ⟨n, hn, hnv⟩ := mk_mem_of_mem_pCoreOf hM₀K hq (hVO₂ hv) hvK
      have hmMb : QuotientGroup.mk' (Subgroup.center ↥K) ⟨m, hmK⟩ ∈ imageModCenter K M₀ :=
        Subgroup.mem_map_of_mem _ (show (⟨m, hmK⟩ : ↥K) ∈ M₀.subgroupOf K from hm)
      have h1 : QuotientGroup.mk' (Subgroup.center ↥K) ⁅(⟨v, hvK⟩ : ↥K), ⟨m, hmK⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        have h2 := hcen ⟨_, hmMb⟩ n hn
        have h3 := congrArg Subtype.val h2
        simp only [Subgroup.coe_mul] at h3
        rw [show ((imageModCenter K M₀).subtype n) = (n : ↥K ⧸ _) from rfl] at hnv
        rw [← hnv]
        exact h3.symm
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      refine ⟨K.mul_mem (K.mul_mem (K.mul_mem hvK hmK) (K.inv_mem hvK)) (K.inv_mem hmK),
        Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨k, hk⟩)
    rw [eq_bot_iff, ← hVc, Subgroup.commutator_le]
    intro v hv m hm
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hVZ hv).2 m (hM₀K hm)).symm

omit [Finite G] in
theorem mem_normalizer_of_centerOf {K X : Subgroup G} (hXK : X ≤ K) {z : G}
    (hz : z ∈ centerOf K) : z ∈ Subgroup.normalizer (X : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hXK hz.2)

omit [Finite G] in
theorem conj_mem_centerOf {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {z : G} (hz : z ∈ centerOf K) : g * z * g⁻¹ ∈ centerOf K := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1,
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ K := (Subgroup.mem_normalizer_iff''.mp hg k).mp hk
  have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * k := by group

theorem centerOf_le_of_hyp {H R M L V K : Subgroup G} (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (hM₀K : conjClosure L M ≤ K)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) (hZ : IsPGroup 2 ↥(centerOf K)) :
    centerOf K ≤ R := by
  set M₀ := conjClosure L M with hM₀
  have hcomm : ∀ z ∈ centerOf K, ∀ k ∈ K, k * z = z * k := fun z hz k hk =>
    Subgroup.mem_centralizer_iff.mp hz.2 k hk
  have hZM : centerOf K ≤ M := fun z hz =>
    h.V_norm ⟨hK.1 hz.1, mem_normalizer_of_centerOf (h.V_le.trans hM₀K) hz⟩
  have hO₂ : pCoreOf 2 M₀ ≤ M₀ := Subgroup.map_subtype_le _
  have hZC : centerOf K ≤ centralizerSection M M₀ (pCoreOf 2 M₀) := fun z hz =>
    ⟨hZM hz, mem_normalizer_of_centerOf hM₀K hz, mem_normalizer_of_centerOf (hO₂.trans hM₀K) hz,
      fun m hm => by
        rw [hcomm z hz m (hM₀K hm), mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _⟩
  have hZn : ((centerOf K).subgroupOf (centralizerSection M M₀ (pCoreOf 2 M₀))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZC]
    intro g hg
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := hMK hg.1
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨conj_mem_centerOf hgK, fun hz => ?_⟩
    have := conj_mem_centerOf (Subgroup.inv_mem _ hgK) hz
    simpa [mul_assoc] using this
  exact (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hZC hZn hZ).trans
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.sylow)

theorem e8_mul_self (w : Multiplicative (Fin 3 → ZMod 2)) : w * w = 1 := by
  revert w
  decide

theorem card_center_le_two_of_m22
    (H R M L V K : Subgroup G) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hc : C31Conclusion H R M L V K) (h3 : C31Case3 H R M L V K) (hpsl : IsPSL 3 2 1 (ModO2 L)) :
    Nat.card (Subgroup.center ↥K) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLM₀, -, hM₀K, hMK, hZ, -⟩ := hc
  set M₀ := conjClosure L M with hM₀
  rw [hLM₀] at hpsl
  have hcard168 : Nat.card (ModO2 M₀) = 168 := GoldS146R.card_of_isPSL_three_two hpsl
  obtain ⟨hs, hext | hext | hext⟩ := h3
  · exfalso
    obtain ⟨Y, _, hY, hd⟩ :=
      C48Spor.card_modO2_dvd_of_isExt hM₀K hZ (fun h => C48Spor.isPGroup_of_isE2 h) hext
    rw [C48Spor.card_of_isPSL_two_two_two hY, hcard168] at hd
    norm_num at hd
  · exfalso
    obtain ⟨Y, _, hY, hd⟩ :=
      C48Spor.card_modO2_dvd_of_isExt hM₀K hZ (fun h => C48Spor.isPGroup_of_isE2 h) hext
    rw [C48Spor.card_of_isAlt_six hY, hcard168] at hd
    norm_num at hd
  obtain ⟨e⟩ := hs
  let e' : ↥K ⧸ Subgroup.center ↥K ≃* KGC31.M22.G₀ := e
  have hKperf : commutator ↥K = ⊤ := hK.2.2.1
  have hKs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  obtain ⟨hcyc, hdvd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate
      (Group.isPerfect_def.mpr hKperf) e'
  obtain ⟨a, ha⟩ := (isPGroup_center_of hZ).exists_card_eq
  by_contra hgt
  push Not at hgt
  have ha2 : a = 2 := by
    rw [ha] at hdvd hgt
    have ha3 : a < 3 := by
      by_contra h3
      push Not at h3
      have := (pow_dvd_pow 2 h3).trans hdvd
      norm_num at this
    interval_cases a <;> first | rfl | (norm_num at hgt)
  set Mb := imageModCenter K M₀ with hMb
  obtain ⟨N₀, hN₀, ⟨eN⟩, hY⟩ := hext
  have hYs : IsSimpleGroup (↥Mb ⧸ N₀) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hY).2
  have hcardY : Nat.card (↥Mb ⧸ N₀) = 168 := GoldS146R.card_of_isPSL_three_two hY
  have hq : C31Spor.QuasiNoTwo (↥Mb ⧸ N₀) := C31Spor.quasiNoTwo_L32 hY
  have hYZ : Subgroup.center (↥Mb ⧸ N₀) = ⊥ :=
    center_eq_bot_of_not_prime hYs (by rw [hcardY]; norm_num)
  have hN₀8 : Nat.card ↥N₀ = 8 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hN₀2 : ∀ n ∈ N₀, n * n = 1 := by
    intro n hn
    have h1 : eN ⟨n, hn⟩ * eN ⟨n, hn⟩ = 1 := e8_mul_self _
    rw [← map_mul, MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hN₀c : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    intro a ha b hb
    have h1 : eN ⟨a, ha⟩ * eN ⟨b, hb⟩ = eN ⟨b, hb⟩ * eN ⟨a, ha⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (eN.injective h1)
  have hN₀p : IsPGroup 2 ↥N₀ := fun n =>
    ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hN₀2 _ n.2)⟩
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using h.V_elem.2 x x.2)⟩
  have hVO₂ : V ≤ pCoreOf 2 M₀ :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V M₀ h.V_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.V_le).mpr
        (C48Spor.M0_le_normalizer_V h)) hV2
  obtain ⟨y₀, hy₀7, t₀, ht₀, hyt₀⟩ := exists_order_seven_moving hM₀K hVO₂ h.V_le h.V_comm h.V_ne
    hN₀p hN₀c hYs hq (by rw [hcardY]; norm_num)
  set N : Subgroup (↥K ⧸ Subgroup.center ↥K) := N₀.map Mb.subtype with hN
  have hNB : N ≤ Mb := Subgroup.map_subtype_le N₀
  have hBN : Mb ≤ Subgroup.normalizer (N : Set (↥K ⧸ Subgroup.center ↥K)) := by
    have h1 := Subgroup.le_normalizer_map (H := N₀) Mb.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hN₀, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
  have hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hN₀c a ha b hb)
  have hN2 : ∀ a ∈ N, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hN₀2 a ha)
  have hN8 : Nat.card N = 8 := by
    rw [← Nat.card_congr (N₀.equivMapOfInjective Mb.subtype Mb.subtype_injective).toEquiv,
      hN₀8]
  have hCN : ∀ c ∈ Mb, (∀ n ∈ N, c * n = n * c) → c ∈ N := by
    intro c hc hcn
    have h1 := mem_of_commute_of_simple hYs hN₀c ht₀ hyt₀ (c := ⟨c, hc⟩) fun n hn =>
      Subtype.ext (hcn _ ⟨n, hn, rfl⟩)
    exact ⟨_, h1, rfl⟩
  have hZN : ∀ u ∈ Mb, (∀ b ∈ Mb, (u * b)⁻¹ * (b * u) ∈ N) → u ∈ N := by
    intro u hu hub
    have h1 := mem_of_central_of_simple hYZ (u := ⟨u, hu⟩) fun b => by
      obtain ⟨n, hn, hnb⟩ := hub b b.2
      have h2 : n = (⟨u, hu⟩ * b)⁻¹ * (b * ⟨u, hu⟩) := Subtype.ext hnb
      rw [← h2]
      exact hn
    exact ⟨_, h1, rfl⟩
  set y : ↥K ⧸ Subgroup.center ↥K := (y₀ : ↥K ⧸ Subgroup.center ↥K) with hy
  set t : ↥K ⧸ Subgroup.center ↥K := (t₀ : ↥K ⧸ Subgroup.center ↥K) with ht
  have hyB : y ∈ Mb := y₀.2
  have hy7 : orderOf y = 7 := by rw [hy, Subgroup.orderOf_coe]; exact hy₀7
  have htN : t ∈ N := ⟨t₀, ht₀, rfl⟩
  have hyt : y * t * y⁻¹ ≠ t := fun h1 => hyt₀ (Subtype.ext h1)
  have hcen1 : ∀ c : ↥K ⧸ Subgroup.center ↥K, (∀ b ∈ Mb, c * b = b * c) → c = 1 := fun c hc =>
    eq_one_of_centralizes_of_m22 e' hNB hBN hNc hN2 hN8 hyB hy7 htN hyt hc
  have hXZ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    have hw' : e' w ∈ Subgroup.center KGC31.M22.G₀ := Subgroup.mem_center_iff.mpr fun g => by
      obtain ⟨g', rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw g']
    rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot] at hw'
    rw [Subgroup.mem_bot]
    exact e'.injective (hw'.trans (map_one e').symm)
  have hXA : Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) ≤
      2 * Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Schreier.m22_mulAut_card
  have hsq : ∀ x ∈ R, x * x ∈ Subgroup.centralizer (K : Set G) := by
    intro x hxR
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := hMK (h.le_M hxR)
    obtain ⟨-, -, -, hxC⟩ := h.sylow.1 hxR
    set σ := barConj x hxK with hσdef
    have hσ : ∀ b ∈ Mb, σ b * b⁻¹ ∈ N := by
      rintro _ ⟨k, hk, rfl⟩
      have hkM : (k : G) ∈ M₀ := hk
      have hmem : x * k * x⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 M₀ := by
        have h1 := (pCoreOf 2 M₀).inv_mem (hxC k hkM)
        have h2 : ((k : G) * x * (k : G)⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * (k : G)⁻¹ := by group
        rwa [h2] at h1
      have hK' : x * k * x⁻¹ * (k : G)⁻¹ ∈ K :=
        K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxK k).mp k.2) (K.inv_mem k.2)
      have h1 := mk_mem_of_mem_pCoreOf hM₀K hq hmem hK'
      have heq : σ (QuotientGroup.mk' (Subgroup.center ↥K) k) *
          (QuotientGroup.mk' (Subgroup.center ↥K) k)⁻¹ =
          QuotientGroup.mk' (Subgroup.center ↥K) ⟨x * k * x⁻¹ * (k : G)⁻¹, hK'⟩ := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hσdef, barConj_mk,
          ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [heq]
      exact h1
    have hσ2 := sq_eq_of_section hBN hNB hNc hN2 hN8 hCN hZN hyB (hy7 ▸ pow_orderOf_eq_one y)
      htN hyt σ hσ
    obtain ⟨c, hc⟩ := exists_conj_eq_mul_self hXZ hXA σ
    have hc1 : c = 1 := hcen1 c fun b hb => by
      have h1 := congrArg (fun φ : MulAut (↥K ⧸ Subgroup.center ↥K) => φ b) hc
      simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
      rw [hσ2 b hb] at h1
      calc c * b = c * b * c⁻¹ * c := by group
        _ = b * c := by rw [← h1]
    rw [hc1, map_one] at hc
    exact mul_self_mem_centralizer hKperf hxK hc
  have hZR : centerOf K ≤ R := centerOf_le_of_hyp h hK hM₀K hMK hZ
  obtain ⟨z₀, hz₀⟩ := IsCyclic.exists_generator (α := ↥(Subgroup.center ↥K))
  have hz₀o : orderOf z₀ = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz₀, ha, ha2]
    norm_num
  set z : G := ((z₀ : ↥K) : G) with hz
  have hzZ : z ∈ centerOf K := ⟨(z₀ : ↥K).2, Subgroup.mem_centralizer_iff.mpr fun k hk =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨k, hk⟩)⟩
  have hzz : z * z ≠ 1 := by
    intro h1
    have h2 : z₀ ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [sq]
      exact h1
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  set C₀ : Subgroup ↥R := Subgroup.closure (Set.range fun r : ↥R => r * r) with hC₀
  set C : Subgroup G := C₀.map R.subtype with hC
  have hCR : C ≤ R := Subgroup.map_subtype_le C₀
  have hCne : C ≠ ⊥ := by
    intro hb
    apply hzz
    have h1 : z * z ∈ C :=
      ⟨⟨z, hZR hzZ⟩ * ⟨z, hZR hzZ⟩, Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
    rwa [hb, Subgroup.mem_bot] at h1
  have hchar : (C.subgroupOf R).Characteristic := by
    have h1 : C.subgroupOf R = C₀ :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective C₀
    rw [h1, Subgroup.characteristic_iff_map_le]
    intro φ
    rw [hC₀, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨φ r, by simp⟩
  have hCK : C ≤ Subgroup.centralizer (K : Set G) := by
    rw [hC, Subgroup.map_le_iff_le_comap, hC₀, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact hsq r r.2
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.mp hCK).trans (Subgroup.centralizer_le_normalizer _)
  have hKM : K ≤ M := by
    refine le_trans ?_ h.cgs
    have hle : H ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn H R := by
      unfold cgsIn
      exact le_iSup₂_of_le C hCR (le_iSup₂_of_le hCne hchar le_rfl)
    exact (le_inf hK.1 hKC).trans hle
  have hKM₀ : K ≤ Subgroup.normalizer (M₀ : Set G) := hKM.trans (le_normalizer_conjClosure L M)
  have hn : (M₀.subgroupOf K).Normal :=
    ⟨fun n hn k => (Subgroup.mem_normalizer_iff.mp (hKM₀ k.2) n).mp hn⟩
  have hMbn : Mb.Normal := Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hMbc : Nat.card ↥Mb = 1344 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀, hcardY, hN₀8]
  have hXc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 443520 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Mb with hb | ht'
  · rw [hb, Subgroup.card_bot] at hMbc
    norm_num at hMbc
  · rw [ht', Subgroup.card_top, hXc] at hMbc
    norm_num at hMbc

end CFSG.Quasithin.C48Cover
