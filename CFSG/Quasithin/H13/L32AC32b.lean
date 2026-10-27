module

public import CFSG.Quasithin.H13.L32AC32a
public import CFSG.Quasithin.H13.L32AC33h
public import CFSG.Quasithin.H13.L32AC51a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem not_nine_dvd_card_L (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) : ¬ 9 ∣ Nat.card ↥L := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 L).exists_card_eq
  rw [S14.card_L, ha]
  intro h
  have h1 : 9 ∣ 168 :=
    (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h
  norm_num at h1

theorem isSylowIn_szS1_of (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) :
    IsSylowIn 2 (szS1 T H K) (modO2Image H K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact F6.isSylowIn_inf_of_isSubnormal (modO2Image_mem_cComp hK).2.2.1
    (isSylowIn_modO2Image (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow
      (Setting147.TH' S)))

theorem false_of_l32_core (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hA37 : A37ForSQTK) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G)) {t₀ : G}
    (ht₀T : t₀ ∈ T) (ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G))
    (h2 : (conjSubgroupsBy H K).ncard = 2) (hP : IsPSL 3 2 1 (cStar K)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have ht₀H : t₀ ∈ H := Setting147.TH' S ht₀T
  have ht₀2 : t₀ * t₀ ∈ Subgroup.normalizer (K : Set G) := by
    rcases mem_normalizer_or_of_ncard h2 ht₀H ht₀N _ (mul_mem ht₀H ht₀H) with h | h
    · exact h
    · exact absurd (by simpa using h) ht₀N
  obtain ⟨φ⟩ := modO2_mulEquiv hK
  obtain ⟨e₁⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, ht₀H⟩ with htb
  set Kb := modO2Image H K with hKb
  set Kb' := Kb.map (MulAut.conj tb : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) with hKb'
  let E₀ : ↥Kb ≃* A6.SL3.S := φ.symm.trans ((cStarEquiv K).symm.trans e₁)
  let E : ↥Kb ≃* GL32 := E₀.trans (slEquivGL 3)
  let E' : ↥Kb' ≃* GL32 := ((MulAut.conj tb).subgroupMap Kb).symm.trans E
  have hZ := G58.center_eq_bot_of_gl32 E
  have hZ' := G58.center_eq_bot_of_gl32 E'
  have h3 : 3 ∣ Nat.card ↥Kb := by rw [G58.card_of_gl32 E]; norm_num
  have h3' : 3 ∣ Nat.card ↥Kb' := by rw [G58.card_of_gl32 E']; norm_num
  have hKb'e : Kb' = modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :=
    (modO2Image_map_conj hKH ⟨t₀, ht₀H⟩).symm
  have hcomm : ∀ a ∈ Kb, ∀ b ∈ Kb', a * b = b * a := fun a ha b hb =>
    commute_of_conj hA37 S hK ht₀H ht₀N ha (hKb'e ▸ hb)
  have hKK : ∀ z ∈ Kb, z ∈ Kb' → z = 1 := fun z hz hz' =>
    eq_one_of_mem_of_commute hZ hz fun n hn => (hcomm n hn z hz').symm
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := by rw [← hl1]; exact hxL
  have hxH : x ∈ H := Setting147.l1H' S hx
  have hxO : x ∉ pCoreOf 2 (l1 T L V) := by
    intro h
    rw [← hl1] at h
    have hxt := S14.pCoreOf_L1_le h
    have hle : V ≤ fsuV1 T V := fun v hv =>
      hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  set xb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ with hxb
  have hxb1 : xb ≠ 1 := by
    intro h
    apply hxO
    refine pCoreOf_inf_le_of_le (Setting147.l1H' S) ⟨?_, hx⟩
    rw [hxb, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf] at h
    exact h
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hx3)
  have hxK : xb ∈ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    mk_mem_normalizer (y := ⟨x, hxH⟩) hKH (hyN x hx hx3)
  have hTl1 := Setting147.T_le_N_l1 S h1332
  have hx' : t₀⁻¹ * x * t₀ ∈ l1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTl1 (inv_mem ht₀T)) x).mp hx
    simpa using this
  have hx'3 : (t₀⁻¹ * x * t₀) ^ 3 = 1 := by
    rw [show (t₀⁻¹ * x * t₀) ^ 3 = t₀⁻¹ * x ^ 3 * t₀ by rw [pow_three, pow_three]; group, hx3]
    group
  have hxK' : xb ∈ Subgroup.normalizer (Kb' : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine mem_normalizer_map_conj ?_
    have e : tb⁻¹ * xb * tb = QuotientGroup.mk' (CFSG.pCore 2 ↥H)
        ⟨t₀⁻¹ * x * t₀, Setting147.l1H' S hx'⟩ := by
      rw [htb, hxb, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact mk_mem_normalizer hKH (hyN _ hx' hx'3)
  obtain ⟨k₁, hk₁K, hk₁3, hk₁⟩ := exists_inner_of_gl32 E hxK hxb3
  obtain ⟨k₂, hk₂K, hk₂3, hk₂⟩ := exists_inner_of_gl32 E' hxK' hxb3
  have hxk₁ : xb * k₁ = k₁ * xb := by
    have h1 := hk₁ k₁ hk₁K
    rw [mul_inv_cancel_right] at h1
    calc xb * k₁ = xb * k₁ * xb⁻¹ * xb := by group
      _ = k₁ * xb := by rw [h1]
  have hxk₂ : xb * k₂ = k₂ * xb := by
    have h1 := hk₂ k₂ hk₂K
    rw [mul_inv_cancel_right] at h1
    calc xb * k₂ = xb * k₂ * xb⁻¹ * xb := by group
      _ = k₂ * xb := by rw [h1]
  have hk₁k₂ : k₁ * k₂ = k₂ * k₁ := hcomm k₁ hk₁K k₂ hk₂K
  have hy : xb * k₁⁻¹ * k₂⁻¹ = 1 := by
    refine eq_one_of_centralizes_two (pRank_three_star_le_two S) hcomm hZ hZ' h3 h3'
      (fun n hn => ?_) (fun n hn => ?_) ?_
    · have h1 : k₂⁻¹ * n = n * k₂⁻¹ := (hcomm n hn _ (inv_mem hk₂K)).symm
      have h2 := hk₁ _ (mul_mem (mul_mem (inv_mem hk₁K) hn) hk₁K)
      calc xb * k₁⁻¹ * k₂⁻¹ * n = xb * k₁⁻¹ * (k₂⁻¹ * n) := by group
        _ = xb * k₁⁻¹ * (n * k₂⁻¹) := by rw [h1]
        _ = xb * (k₁⁻¹ * n * k₁) * xb⁻¹ * (xb * k₁⁻¹ * k₂⁻¹) := by group
        _ = k₁ * (k₁⁻¹ * n * k₁) * k₁⁻¹ * (xb * k₁⁻¹ * k₂⁻¹) := by rw [h2]
        _ = n * (xb * k₁⁻¹ * k₂⁻¹) := by group
    · have hm : k₂⁻¹ * n * k₂ ∈ Kb' := mul_mem (mul_mem (inv_mem hk₂K) hn) hk₂K
      have h1 : k₁⁻¹ * (k₂⁻¹ * n * k₂) = (k₂⁻¹ * n * k₂) * k₁⁻¹ :=
        hcomm _ (inv_mem hk₁K) _ hm
      have h2 := hk₂ _ hm
      calc xb * k₁⁻¹ * k₂⁻¹ * n = xb * (k₁⁻¹ * (k₂⁻¹ * n * k₂)) * k₂⁻¹ := by group
        _ = xb * ((k₂⁻¹ * n * k₂) * k₁⁻¹) * k₂⁻¹ := by rw [h1]
        _ = xb * (k₂⁻¹ * n * k₂) * xb⁻¹ * (xb * k₁⁻¹ * k₂⁻¹) := by group
        _ = k₂ * (k₂⁻¹ * n * k₂) * k₂⁻¹ * (xb * k₁⁻¹ * k₂⁻¹) := by rw [h2]
        _ = n * (xb * k₁⁻¹ * k₂⁻¹) := by group
    · have c1 : Commute xb k₁⁻¹ := Commute.inv_right hxk₁
      have c2 : Commute xb k₂⁻¹ := Commute.inv_right hxk₂
      have c3 : Commute k₁⁻¹ k₂⁻¹ := Commute.inv_inv hk₁k₂
      rw [(c2.mul_left c3).mul_pow, c1.mul_pow, hxb3, inv_pow, inv_pow, hk₁3, hk₂3]
      group
  have hxk : xb = k₁ * k₂ := by
    calc xb = xb * k₁⁻¹ * k₂⁻¹ * (k₂ * k₁) := by group
      _ = k₂ * k₁ := by rw [hy, one_mul]
      _ = k₁ * k₂ := hk₁k₂.symm
  have hLN : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful).2.1.1
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hxbL : xb ∈ modO2Image H L := mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hl1L hx, rfl⟩
  have hzH : t₀ * x * t₀⁻¹ ∈ H := mul_mem (mul_mem ht₀H hxH) (inv_mem ht₀H)
  have hze : tb * xb * tb⁻¹ = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀ * x * t₀⁻¹, hzH⟩ := by
    rw [htb, hxb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hzL : tb * xb * tb⁻¹ ∈ modO2Image H L := by
    rw [hze]
    exact mem_modO2Image'.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp (hLN ht₀T) x).mp (hl1L hx),
      rfl⟩
  have hz3 : (tb * xb * tb⁻¹) ^ 3 = 1 := by
    rw [show tb * xb * tb⁻¹ = MulAut.conj tb xb from rfl, ← map_pow, hxb3, map_one]
  have hz1 : tb * xb * tb⁻¹ ≠ 1 := fun h => hxb1 (by
    have := congrArg (fun z => tb⁻¹ * z * tb) h
    simpa [mul_assoc] using this)
  have h9 : ¬ 9 ∣ Nat.card ↥(modO2Image H L) := fun h =>
    not_nine_dvd_card_L h1222 h1332 h1334 S (h.trans card_modO2Image_dvd_card)
  by_cases hk₁1 : k₁ = 1
  ·
    rw [hk₁1, one_mul] at hxk
    have hxKb' : xb ∈ Kb' := hxk ▸ hk₂K
    have hxnK : xb ∉ Kb := fun h => hxb1 (hKK xb h hxKb')
    have htt : tb * tb ∈ Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      have := mk_mem_normalizer (y := ⟨t₀, ht₀H⟩ * ⟨t₀, ht₀H⟩) hKH ht₀2
      rwa [map_mul] at this
    have hzK : tb * xb * tb⁻¹ ∈ Kb := by
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hxKb'
      have e : tb * xb * tb⁻¹ = (tb * tb) * m * (tb * tb)⁻¹ := by
        rw [← hme]
        simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp htt m).mp hm
    exact h9 (nine_dvd_card hxbL hxK hxb3 hxnK hzL hzK hz3 hz1)
  by_cases hk₂1 : k₂ = 1
  ·
    rw [hk₂1, mul_one] at hxk
    have hxKb : xb ∈ Kb := hxk ▸ hk₁K
    have hxnK' : xb ∉ Kb' := fun h => hxb1 (hKK xb hxKb h)
    have hzK' : tb * xb * tb⁻¹ ∈ Kb' :=
      Subgroup.mem_map.mpr ⟨xb, hxKb, by simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]⟩
    exact h9 (nine_dvd_card hxbL hxK' hxb3 hxnK' hzL hzK' hz3 hz1)
  have hxnK : xb ∉ Kb := by
    intro h
    apply hk₂1
    refine eq_one_of_mem_of_commute hZ' hk₂K fun n hn => ?_
    have h1 := hk₂ n hn
    have h3 : xb * n * xb⁻¹ = n := by rw [hcomm xb h n hn, mul_inv_cancel_right]
    rw [h3] at h1
    calc k₂ * n = k₂ * n * k₂⁻¹ * k₂ := by group
      _ = n * k₂ := by rw [← h1]
  have hS₁ := isSylowIn_szS1_of S hK
  have hS2 : IsPGroup 2 ↥((szS1 T H K).subgroupOf Kb) :=
    hS₁.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS₁.le).symm
  have hk₁3' : (⟨k₁, hk₁K⟩ : ↥Kb) ^ 3 = 1 := Subtype.ext (by simpa using hk₁3)
  have hk₁1' : (⟨k₁, hk₁K⟩ : ↥Kb) ≠ 1 := fun h => hk₁1 (congrArg Subtype.val h)
  obtain ⟨σ, hσ, hσ3, hσ1⟩ := exists_comm_three_of_sylow E₀ hS2 hS₁.not_dvd_relIndex hk₁3' hk₁1'
  have hc : xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ =
      (((⟨k₁, hk₁K⟩ : ↥Kb) * σ * (⟨k₁, hk₁K⟩ : ↥Kb)⁻¹ * σ⁻¹ : ↥Kb) :
        ↥H ⧸ CFSG.pCore 2 ↥H) := by
    rw [hk₁ σ σ.2]
    rfl
  have hcK : xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ ∈ Kb := by
    rw [hc]
    exact SetLike.coe_mem _
  have hc3 : (xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹) ^ 3 = 1 := by
    rw [hc, ← Subgroup.coe_pow, hσ3, OneMemClass.coe_one]
  have hc1 : xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ ≠ 1 := by
    rw [hc]
    exact fun h => hσ1 (Subtype.ext h)
  have hcL : xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ ∈
      modO2Image H L := by
    obtain ⟨r, hrT, hre⟩ := mem_modO2Image'.mp (Subgroup.mem_subgroupOf.mp hσ).1
    have hrL : (r : G) * x⁻¹ * (r : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hLN hrT) _).mp (inv_mem (hl1L hx))
    have hcm : x * r * x⁻¹ * (r : G)⁻¹ ∈ L := by
      have e : x * r * x⁻¹ * (r : G)⁻¹ = x * ((r : G) * x⁻¹ * (r : G)⁻¹) := by group
      rw [e]
      exact mul_mem (hl1L hx) hrL
    have hcH : x * r * x⁻¹ * (r : G)⁻¹ ∈ H :=
      mul_mem (mul_mem (mul_mem hxH r.2) (inv_mem hxH)) (inv_mem r.2)
    have e : xb * (σ : ↥H ⧸ CFSG.pCore 2 ↥H) * xb⁻¹ * (σ : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hcH⟩ := by
      rw [← hre, hxb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact mem_modO2Image'.mpr ⟨_, hcm, rfl⟩
  exact h9 (nine_dvd_card hxbL hxK hxb3 hxnK hcL hcK hc3 hc1)

theorem false_of_l32 (h30 : Lemma14_7_30) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hT : ¬ T ≤ Subgroup.normalizer (K : Set G))
    (hP : IsPSL 3 2 1 (cStar K)) : False := by
  obtain ⟨-, -, S₀, -⟩ := h30 G T L V H S K hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun s hs k hk =>
    H.mul_mem (H.mul_mem (hTH hs) (hKH hk)) (H.inv_mem (hTH hs))
  have hKH₀ : K ≤ conjClosure K T ⊔ (l1 T L V ⊔ T) := (le_conjClosure K T).trans le_sup_left
  have hK₀ : K ∈ cComp (conjClosure K T ⊔ (l1 T L V ⊔ T)) :=
    mem_cComp_of_le_of_le hK hKH₀ (sup_le hK₀H S.hz.1.1)
  have h121 := lemma_1_2_1_three S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian hA37 hA38
    S₀.hz.1.2 hK₀
  have hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G) :=
    fun y hy hy3 =>
      mem_normalizer_of_cube hKH₀ (h121.imp_right fun h => h.1) (Setting147.l1H' S₀ hy) hy3
  obtain ⟨t₀, ht₀T, ht₀N⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra h
    push Not at h
    exact hT h
  have h2 : (conjSubgroupsBy (conjClosure K T ⊔ (l1 T L V ⊔ T)) K).ncard = 2 := by
    rcases h121 with hn | ⟨h2, -⟩
    · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH₀).mp hn
        (Setting147.TH' S₀ ht₀T)) ht₀N
    · exact h2
  exact false_of_l32_core h1222 h1332 h1334 hA37 S₀ hK₀ hyN ht₀T ht₀N h2 hP

end CFSG.Quasithin.H13.L32A.C
