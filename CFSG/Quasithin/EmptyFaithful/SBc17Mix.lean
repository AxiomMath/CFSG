module

public import CFSG.Quasithin.EmptyFaithful.SBc17Diag
public import CFSG.Quasithin.EmptyFaithful.SBc17FixG2
public import CFSG.Quasithin.EmptyFaithful.SBc13JM5Quasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem not_mem_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) {a : G} (ha : orderOf a = 5) :
    a ∉ P := by
  intro haP
  obtain ⟨k, hk⟩ := hP ⟨a, haP⟩
  have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [ha] at hd
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd
  omega

omit [Finite G] in
theorem exists_five_not_mem_of_not_le {K L : Subgroup G}
    (hgen : K ≤ Subgroup.closure {x | x ∈ K ∧ orderOf x = 5}) (h : ¬ K ≤ L) :
    ∃ k ∈ K, orderOf k = 5 ∧ k ∉ L := by
  by_contra hcon
  push Not at hcon
  exact h (hgen.trans ((Subgroup.closure_le _).mpr fun x hx => hcon x hx.1 hx.2))

theorem exists_commuting_five (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) {z : G} (hzK : z ∈ oTwoUpper H₁)
    (hz5 : orderOf z = 5) :
    ∃ k ∈ oTwoUpper H₂, orderOf k = 5 ∧ z * k = k * z ∧
      Subgroup.zpowers z ⊓ Subgroup.zpowers k = ⊥ := by
  have hp : p.Prime := hred.prime
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hset := hdec.setup14615_of_C1 S hred hCz
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hK₁K : oTwoUpper H₁ ≤ oTwoUpper H := hKX ▸ le_sup_left
  have hK₂K : oTwoUpper H₂ ≤ oTwoUpper H := hKX ▸ le_sup_right
  have hKN₂ : oTwoUpper H ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := by
    have := kz_le_g2_14615 hdec hset
    rw [hCz] at this
    exact this
  set K := oTwoUpper H with hK
  set O := pCoreOf 2 K with hO
  set W := oTwoUpper H₂ ⊓ O with hW
  obtain ⟨z₂, hz₂K, hz₂5'⟩ := hdec.swap.exists_order_p_P14 hp hred.odd
  have hz₂5 : orderOf z₂ = 5 := by rw [hz₂5', hp5]
  have hzKK : z ∈ K := hK₁K hzK
  have hz₂KK : z₂ ∈ K := hK₂K hz₂K
  have hzN : z ∈ Subgroup.normalizer (W : Set G) :=
    SBc14.mem_normalizer_inf (hKN₂ hzKK)
      (normalizer_le_normalizer_pCoreOf 2 K (Subgroup.le_normalizer hzKK))
  have hy : ∀ e ∈ Subgroup.zpowers z, ∃ w ∈ W, e * z₂ * e⁻¹ = z₂ * w := by
    intro e he
    have heK₁ : e ∈ oTwoUpper H₁ := (Subgroup.zpowers_le.mpr hzK) he
    have heK : e ∈ K := hK₁K heK₁
    have h1 : e * z₂ * e⁻¹ ∈ oTwoUpper H₂ := (Subgroup.mem_normalizer_iff.mp (hKN₂ heK) z₂).mp hz₂K
    have hcQ : ⁅e, z₂⁆ ∈ pCoreOf 2 H :=
      hdec.comm (Subgroup.commutator_mem_commutator (oTwoUpper_le H₁ heK₁) (oTwoUpper_le H₂ hz₂K))
    refine ⟨z₂⁻¹ * (e * z₂ * e⁻¹), ⟨(oTwoUpper H₂).mul_mem ((oTwoUpper H₂).inv_mem hz₂K) h1, ?_⟩, by group⟩
    refine (SBc16.mem_pCoreOf_oTwoUpper_iff H).mpr
      ⟨K.mul_mem (K.inv_mem hz₂KK) (K.mul_mem (K.mul_mem heK hz₂KK) (K.inv_mem heK)), ?_⟩
    have hz₂H : z₂ ∈ H := (hdec.le₂.trans hdec.le) (oTwoUpper_le H₂ hz₂K)
    have e1 : z₂⁻¹ * (e * z₂ * e⁻¹) = z₂⁻¹ * ⁅e, z₂⁆ * z₂ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    have hn := le_normalizer_pCoreOf 2 H (H.inv_mem hz₂H)
    have := (Subgroup.mem_normalizer_iff.mp hn ⁅e, z₂⁆).mp hcQ
    simpa [mul_assoc] using this
  have hE : IsPGroup 5 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz5]; norm_num)
  have hW2 : IsPGroup 2 W := (pCoreOf_isPGroup 2 K).to_le inf_le_right
  obtain ⟨w, hwW, hfix⟩ := exists_fixed_mem_coset hE hW2 (Subgroup.zpowers_le.mpr hzN) hy
  set x := z₂ * w with hx
  have hxK₂ : x ∈ oTwoUpper H₂ := (oTwoUpper H₂).mul_mem hz₂K hwW.1
  have hxc : z * x = x * z := by
    have := hfix z (Subgroup.mem_zpowers z)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 K
  have hxO : x ∉ O := by
    intro hxO
    exact not_mem_of_isPGroup_two hO2 hz₂5 (by
      have : z₂ = x * w⁻¹ := by rw [hx]; group
      rw [this]
      exact O.mul_mem hxO (O.inv_mem hwW.2))
  have hx5 : x ^ 5 ∈ O := by
    have hxKK : x ∈ K := hK₂K hxK₂
    have h1 : (QuotientGroup.mk (⟨x, hxKK⟩ : ↥K) : OTwoQuot K) = QuotientGroup.mk ⟨z₂, hz₂KK⟩ := by
      rw [QuotientGroup.eq, SBc16.mem_pCore_iff_coe]
      show (x⁻¹ * z₂) ∈ pCoreOf 2 K
      have : x⁻¹ * z₂ = w⁻¹ := by rw [hx]; group
      rw [this]
      exact O.inv_mem hwW.2
    have hz₂pow : z₂ ^ 5 = 1 := by
      have := pow_orderOf_eq_one z₂
      rwa [hz₂5] at this
    have h2 : (QuotientGroup.mk (⟨x, hxKK⟩ : ↥K) : OTwoQuot K) ^ 5 = 1 := by
      rw [h1, ← QuotientGroup.mk_pow]
      have : (⟨z₂, hz₂KK⟩ : ↥K) ^ 5 = 1 := Subtype.ext (by simpa using hz₂pow)
      rw [this, QuotientGroup.mk_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, SBc16.mem_pCore_iff_coe] at h2
    exact h2
  obtain ⟨n, hn5, hnO⟩ := exists_five_part hO2 hx5 hxO
  refine ⟨x ^ n, (oTwoUpper H₂).pow_mem hxK₂ n, hn5, (Commute.pow_right (hxc : z * x = x * z) n), ?_⟩
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  have hgH₁ : g ∈ H₁ := oTwoUpper_le H₁ ((Subgroup.zpowers_le.mpr hzK) hg1)
  have hgH₂ : g ∈ H₂ := oTwoUpper_le H₂ ((Subgroup.zpowers_le.mpr ((oTwoUpper H₂).pow_mem hxK₂ n)) hg2)
  have hgQ : g ∈ pCoreOf 2 H := by
    rw [← hdec.inf]
    exact ⟨hgH₁, hgH₂⟩
  have hg5 : g ^ 5 = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz5, pow_orderOf_eq_one,
      one_zpow]
  by_contra hne
  have hg1' : g ≠ 1 := hne
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg1'
  exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 H) hord hgQ

theorem oTwoUpper_le_of_diag (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) {J : Subgroup G}
    (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    (hJn : g2_14615 (oTwoUpper H₂) ≤ Subgroup.normalizer (J : Set G)) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ oTwoUpper H₁) (hk₂ : k₂ ∈ oTwoUpper H₂) (hk₁5 : orderOf k₁ = 5) {l : ℕ}
    (ha : k₁ * k₂ ^ l ∈ J) : oTwoUpper H₁ ≤ J := by
  have hKG := mcOf_le_normalizer_oTwoUpper hCz
  obtain ⟨σ, τ, hσA, -, hσ₂, hσ₁, -, -⟩ := exists_sigma_tau S hp5 hred hdec hKG
  obtain ⟨⟨hX₁, hO₁, hP₁⟩, ⟨hX₂, hO₂, hP₂⟩⟩ := lines_data hdec
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hK₁K : oTwoUpper H₁ ≤ oTwoUpper H := hKX ▸ le_sup_left
  have hK₂K : oTwoUpper H₂ ≤ oTwoUpper H := hKX ▸ le_sup_right
  obtain ⟨⟨s, hs⟩, rfl⟩ := hσA
  set K := oTwoUpper H with hK
  set O := pCoreOf 2 K with hO
  have hsN : s ∈ Subgroup.normalizer (K : Set G) := hKG hs
  have hmapV₂ : (imageOTwoQuot K (oTwoUpper H₂)).map (psiHom hKG ⟨s, hs⟩).toMonoidHom =
      imageOTwoQuot K (oTwoUpper H₂) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have := hσ₂ u hu
      simpa [this] using hu
    · intro hv
      exact ⟨v, hv, hσ₂ v hv⟩
  have hsK₂ : s ∈ Subgroup.normalizer (oTwoUpper H₂ : Set G) :=
    (map_actHom_eq_iff hX₂ hO₂ hP₂ hsN).mp hmapV₂
  have hsJ : s ∈ Subgroup.normalizer (J : Set G) := hJn hsK₂
  set N₀ := J ⊓ K with hN₀
  have hsN₀ : conjSub s N₀ = N₀ :=
    conjSub_eq_of_mem_normalizer (SBc14.mem_normalizer_inf hsJ hsN)
  set D := imageOTwoQuot K N₀ with hD
  have hDσ : D.map (SBc16.actHom K ⟨s, hsN⟩).toMonoidHom = D := by
    rw [hD, SBc16.map_actHom_imageOTwoQuot K hsN inf_le_right, hsN₀]
  have hk₁KK : k₁ ∈ K := hK₁K hk₁
  have hk₂KK : k₂ ∈ K := hK₂K hk₂
  have haK : k₁ * k₂ ^ l ∈ K := K.mul_mem hk₁KK (K.pow_mem hk₂KK l)
  have haD : (QuotientGroup.mk ⟨k₁ * k₂ ^ l, haK⟩ : OTwoQuot K) ∈ D :=
    mem_imageOTwoQuot_iff.mpr ⟨_, haK, ⟨ha, haK⟩, rfl⟩
  set u₁ : OTwoQuot K := QuotientGroup.mk ⟨k₁, hk₁KK⟩ with hu₁
  set u₂ : OTwoQuot K := QuotientGroup.mk ⟨k₂, hk₂KK⟩ with hu₂
  have hu₁V : u₁ ∈ imageOTwoQuot K (oTwoUpper H₁) := mem_imageOTwoQuot_iff.mpr ⟨k₁, hk₁KK, hk₁, rfl⟩
  have hu₂V : u₂ ∈ imageOTwoQuot K (oTwoUpper H₂) := mem_imageOTwoQuot_iff.mpr ⟨k₂, hk₂KK, hk₂, rfl⟩
  have hcomm := SBc16.mul_comm_OTwoQuot_K S hp5 hred hdec
  have hamk : (QuotientGroup.mk ⟨k₁ * k₂ ^ l, haK⟩ : OTwoQuot K) = u₁ * u₂ ^ l := by
    rw [hu₁, hu₂, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
    rfl
  have hσa : (SBc16.actHom K ⟨s, hsN⟩) (u₁ * u₂ ^ l) ∈ D := by
    rw [← hamk, ← hDσ]
    exact Subgroup.mem_map_of_mem _ haD
  have hσ₁u : (SBc16.actHom K ⟨s, hsN⟩) u₁ = u₁⁻¹ := hσ₁ u₁ hu₁V
  have hσ₂u : (SBc16.actHom K ⟨s, hsN⟩) u₂ = u₂ := hσ₂ u₂ hu₂V
  rw [map_mul, map_pow, hσ₁u, hσ₂u] at hσa
  have hdiff : u₁ ^ 2 ∈ D := by
    have h1 : (u₁ * u₂ ^ l) * (u₁⁻¹ * u₂ ^ l)⁻¹ ∈ D := D.mul_mem (hamk ▸ haD) (D.inv_mem hσa)
    have e : (u₁ * u₂ ^ l) * (u₁⁻¹ * u₂ ^ l)⁻¹ = u₁ ^ 2 := by
      have hc : ∀ a b : OTwoQuot K, a * b = b * a := hcomm
      calc (u₁ * u₂ ^ l) * (u₁⁻¹ * u₂ ^ l)⁻¹ = u₁ * u₂ ^ l * ((u₂ ^ l)⁻¹ * u₁) := by
            rw [mul_inv_rev, inv_inv]
        _ = u₁ * (u₂ ^ l * (u₂ ^ l)⁻¹) * u₁ := by group
        _ = u₁ ^ 2 := by rw [mul_inv_cancel, mul_one, pow_two]
    rwa [e] at h1
  have hV₁card : Nat.card (imageOTwoQuot K (oTwoUpper H₁)) = 5 := by
    have := SBc16.card_imageOTwoQuot_K hred hdec
    rwa [hp5] at this
  have hu₁5 : u₁ ^ 5 = 1 := by
    have := pow_card_eq_one' (G := imageOTwoQuot K (oTwoUpper H₁)) (x := ⟨u₁, hu₁V⟩)
    rw [hV₁card] at this
    exact congrArg Subtype.val this
  have hu₁D : u₁ ∈ D := by
    have : u₁ = (u₁ ^ 2) ^ 3 := by
      calc u₁ = u₁ ^ 6 * (u₁ ^ 5)⁻¹ := by group
        _ = (u₁ ^ 2) ^ 3 := by rw [hu₁5]; group
    rw [this]
    exact D.pow_mem hdiff 3
  have hu₁ne : u₁ ≠ 1 := by
    intro h1
    rw [hu₁, QuotientGroup.eq_one_iff, SBc16.mem_pCore_iff_coe] at h1
    exact not_mem_of_isPGroup_two (pCoreOf_isPGroup 2 K) hk₁5 h1
  have hV₁D : imageOTwoQuot K (oTwoUpper H₁) ≤ D := by
    have hle : imageOTwoQuot K (oTwoUpper H₁) ⊓ D ≤ imageOTwoQuot K (oTwoUpper H₁) := inf_le_left
    have hne : imageOTwoQuot K (oTwoUpper H₁) ⊓ D ≠ ⊥ := by
      intro hbot
      have : u₁ ∈ imageOTwoQuot K (oTwoUpper H₁) ⊓ D := ⟨hu₁V, hu₁D⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu₁ne this
    have hcard : Nat.card ↥(imageOTwoQuot K (oTwoUpper H₁) ⊓ D) ∣ 5 := by
      rw [← hV₁card]
      exact Subgroup.card_dvd_of_le hle
    have h5 : Nat.card ↥(imageOTwoQuot K (oTwoUpper H₁) ⊓ D) = 5 := by
      rcases (Nat.dvd_prime (by norm_num)).mp hcard with h1 | h5
      · exact absurd (Subgroup.card_eq_one.mp h1) hne
      · exact h5
    have heq : imageOTwoQuot K (oTwoUpper H₁) ⊓ D = imageOTwoQuot K (oTwoUpper H₁) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h5, hV₁card])
    exact heq ▸ inf_le_right
  have hK₁sup : oTwoUpper H₁ ≤ N₀ ⊔ O := by
    intro g hg
    have hgK : g ∈ K := hK₁K hg
    have hgV : (QuotientGroup.mk ⟨g, hgK⟩ : OTwoQuot K) ∈ imageOTwoQuot K (oTwoUpper H₁) :=
      mem_imageOTwoQuot_iff.mpr ⟨g, hgK, hg, rfl⟩
    obtain ⟨x, hxK, hxN, hxg⟩ := mem_imageOTwoQuot_iff.mp (hV₁D hgV)
    have h1 : (⟨x, hxK⟩ : ↥K)⁻¹ * ⟨g, hgK⟩ ∈ CFSG.Open.pCore 2 ↥K := QuotientGroup.eq.mp hxg
    have h2 : x⁻¹ * g ∈ O := (SBc16.mem_pCore_iff_coe K _).mp h1
    have e : g = x * (x⁻¹ * g) := by group
    rw [e]
    exact (N₀ ⊔ O).mul_mem (Subgroup.mem_sup_left hxN) (Subgroup.mem_sup_right h2)
  have hON : O ≤ Subgroup.normalizer (N₀ : Set G) := fun o ho =>
    SBc14.mem_normalizer_inf (hKJ (pCoreOf_le 2 K ho))
      (Subgroup.le_normalizer (pCoreOf_le 2 K ho))
  have hup : oTwoUpper (N₀ ⊔ O) ≤ N₀ :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hON))
      (pCoreOf_isPGroup 2 K) le_sup_right le_rfl
  calc oTwoUpper H₁ = oTwoUpper (oTwoUpper H₁) := (oTwoUpper_idem_P H₁).symm
    _ ≤ oTwoUpper (N₀ ⊔ O) := oTwoUpper_mono hK₁sup
    _ ≤ N₀ := hup
    _ ≤ J := inf_le_left

theorem oTwoUpper_le_of_innerSub (h36 : A36ForSQTK) (S : Setting146 G T M) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hCz : conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H) {J : Subgroup G}
    (hX : SQTKGroup ↥(g2_14615 (oTwoUpper H₂))) (hJc : J ∈ cComp (g2_14615 (oTwoUpper H₂)))
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hK₂N : oTwoUpper H₂ ≤ Subgroup.normalizer (J : Set G))
    (hK₂c : ⁅J, oTwoUpper H₂⁆ ≤ pCoreOf 2 J) (hKJ : oTwoUpper H ≤ Subgroup.normalizer (J : Set G))
    (hJn : g2_14615 (oTwoUpper H₂) ≤ Subgroup.normalizer (J : Set G))
    (hin : oTwoUpper H₁ ⊔ oTwoUpper H₂ ≤ innerSub J)
    (hnc : ¬ ⁅J, oTwoUpper H₁⁆ ≤ pCoreOf 2 J) : oTwoUpper H₁ ≤ J := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hset := hdec.setup14615_of_C1 S hred hCz
  have hKX : oTwoUpper H = oTwoUpper H₁ ⊔ oTwoUpper H₂ := hdec.oTwoUpper_eq S hred
  have hKG₂ : oTwoUpper H ≤ g2_14615 (oTwoUpper H₂) := by
    have := kz_le_g2_14615 hdec hset
    rwa [hCz] at this
  have hK₁K : oTwoUpper H₁ ≤ oTwoUpper H := hKX ▸ le_sup_left
  have hgen₁ : oTwoUpper H₁ ≤ Subgroup.closure {x | x ∈ oTwoUpper H₁ ∧ orderOf x = 5} :=
    hdec.oTwoUpper_le_closure_five hp5 le_rfl
  have hK₁nc : ¬ oTwoUpper H₁ ≤ cMod J := by
    intro h
    apply hnc
    refine Subgroup.commutator_le.mpr fun x hx c hc => ?_
    exact ((mem_cMod.mp (h hc)).2 x hx)
  obtain ⟨k₁, hk₁K, hk₁5, hk₁nc'⟩ := exists_five_not_mem_of_not_le hgen₁ hK₁nc
  obtain ⟨k₂, hk₂K, hk₂5, hcomm, hind⟩ := exists_commuting_five S hp5 hred hdec hCz hk₁K hk₁5
  have hk₂c : k₂ ∈ cMod J :=
    mem_cMod.mpr ⟨hK₂N hk₂K, fun x hx => hK₂c (Subgroup.commutator_mem_commutator hx hk₂K)⟩
  have hk₁in : k₁ ∈ innerSub J := hin (Subgroup.mem_sup_left hk₁K)
  have h5Z : ∀ z ∈ J, z ∈ cMod J → orderOf z ≠ 5 := fun z hzJ hzc hz5 =>
    SBc13.not_mem_of_commutes hX (h36 _ (SQTKHyp.of_sqtkGroup _ hX)) hJc hJq hz5
      (fun x hx => (mem_cMod.mp hzc).2 x hx) hzJ
  have hX2 : CFSG.Open.pRank 5 (g2_14615 (oTwoUpper H₂)) ≤ 2 := by
    have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥(g2_14615 (oTwoUpper H₂))) ≤ 2 :=
      hX.1 5 (by norm_num) (by norm_num)
    rwa [pRank_top_subtype] at h2
  obtain ⟨l, hl⟩ := exists_diag_mem hX2 (le_of_mem_cComp hJc) (hKG₂ (hK₁K hk₁K))
    (hKG₂ (hKX ▸ (le_sup_right : oTwoUpper H₂ ≤ oTwoUpper H₁ ⊔ oTwoUpper H₂) hk₂K)) hk₁5 hk₂5
    hcomm hind hk₂c hk₁in hk₁nc' h5Z
  exact oTwoUpper_le_of_diag S hp5 hred hdec hCz hKJ hJn hk₁K hk₂K hk₁5 hl

end SBc17

end CFSG.Quasithin
