module

public import CFSG.Quasithin.H13.L32A705b
public import CFSG.Quasithin.H13.L32ASk6

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

theorem modO2Image_oTwoUpper_le {H X : Subgroup G} (hXH : oTwoUpper X ≤ H) :
    modO2Image H (oTwoUpper X) ≤ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : oTwoUpper X ≤ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    refine ⟨⟨x, hXH (Subgroup.subset_closure hx)⟩,
      mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact hx.2
  have h2 : (oTwoUpper (⊤ : Subgroup ↥H)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      oTwoUpper ⊤ := by
    rw [← oTwoUpper_map]
    exact oTwoUpper_mono le_top
  intro y hy
  obtain ⟨h, hh, rfl⟩ := mem_modO2Image'.mp hy
  obtain ⟨h', hh', he⟩ := h1 hh
  rw [show h = h' from Subtype.ext he.symm]
  exact h2 ⟨h', hh', rfl⟩

omit [Finite G] in
theorem normal_oTwoUpper_top {K : Type*} [Group K] : (oTwoUpper (⊤ : Subgroup K)).Normal :=
  ⟨fun _ hn _ => conj_mem_oTwoUpper (Subgroup.mem_normalizer_iff.mpr fun _ => by simp) hn⟩

omit [Finite G] in
theorem eq_of_le_isCyclic {K : Type*} [Group K] [Finite K] {P A B : Subgroup K}
    [IsCyclic ↥P] (hA : A ≤ P) (hB : B ≤ P) (h : Nat.card A = Nat.card B) : A = B := by
  have h' : A.subgroupOf P = B.subgroupOf P := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
    exact h
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h'
  exact h'

omit [Finite G] in
theorem normal_of_le_isCyclic {K : Type*} [Group K] [Finite K] {P A : Subgroup K}
    [IsCyclic ↥P] (hP : P.Normal) (hA : A ≤ P) : A.Normal := by
  refine ⟨fun a ha g => ?_⟩
  have hc : A.map (MulAut.conj g).toMonoidHom ≤ P := by
    rintro _ ⟨b, hb, rfl⟩
    exact hP.conj_mem b (hA hb) g
  have he : A.map (MulAut.conj g).toMonoidHom = A :=
    eq_of_le_isCyclic hc hA
      (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
  rw [← he]
  exact ⟨a, ha, rfl⟩

omit [Finite G] in
theorem comm_of_fix_three {K : Type*} [Group K] {P : Subgroup K}
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP3 : IsPGroup 3 P) {t : K}
    (hconj : ∀ z ∈ P, t * z * t⁻¹ ∈ P) {m : ℕ} (ht : t ^ 2 ^ m = 1)
    (hfix : ∀ y ∈ P, y ^ 3 = 1 → t * y * t⁻¹ = y) {x : K} (hx : x ∈ P) :
    t * x * t⁻¹ = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ n : ℕ, t * x ^ n * t⁻¹ * (x ^ n)⁻¹ = (t * x * t⁻¹ * x⁻¹) ^ n := by
    intro n
    have hc : Commute (t * x * t⁻¹) x⁻¹ := hPab _ (hconj x hx) _ (inv_mem hx)
    rw [hc.mul_pow, conj_pow, inv_pow]
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, t * x * t⁻¹ * x⁻¹ = y := ⟨_, rfl⟩
  have hyP : y ∈ P := by
    rw [← hy]
    exact mul_mem (hconj x hx) (inv_mem hx)
  have hy1 : y ≠ 1 := fun h => hne (mul_inv_eq_one.mp (hy.trans h))
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP3 ⟨y, hyP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by simpa using hk))
  obtain ⟨x', hx'⟩ : ∃ x', x ^ 3 ^ (k - 1) = x' := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y ^ 3 ^ (k - 1) = y' := ⟨_, rfl⟩
  have hy'e : t * x' * t⁻¹ * x'⁻¹ = y' := by
    rw [← hx', ← hy', hpow, hy]
  have hy'3 : y' ^ 3 = 1 := by
    rw [← hy', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), ← hk,
      pow_orderOf_eq_one]
  have hy'1 : y' ≠ 1 := by
    intro h
    rw [← hy'] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hk] at hd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hd
    omega
  have hy'P : y' ∈ P := by
    rw [← hy']
    exact pow_mem hyP _
  have hty : t * y' * t⁻¹ = y' := hfix y' hy'P hy'3
  have htx : t * x' * t⁻¹ = y' * x' := by
    rw [← hy'e]
    group
  have hn : ∀ n : ℕ, t ^ n * x' * (t ^ n)⁻¹ = y' ^ n * x' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc t ^ (n + 1) * x' * (t ^ (n + 1))⁻¹ = t * (t ^ n * x' * (t ^ n)⁻¹) * t⁻¹ := by group
        _ = t * (y' ^ n * x') * t⁻¹ := by rw [ih]
        _ = (t * y' * t⁻¹) ^ n * (t * x' * t⁻¹) := by rw [conj_pow]; group
        _ = y' ^ (n + 1) * x' := by rw [hty, htx]; group
  have h2 : y' ^ 2 ^ m = 1 := by
    have h := hn (2 ^ m)
    rw [ht, one_mul, inv_one, mul_one] at h
    calc y' ^ 2 ^ m = y' ^ 2 ^ m * x' * x'⁻¹ := by group
      _ = 1 := by rw [← h, mul_inv_cancel]
  have hd3 : orderOf y' ∣ 3 := orderOf_dvd_of_pow_eq_one hy'3
  have hd2 : orderOf y' ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (orderOf y') (2 ^ m) :=
    Nat.Coprime.coprime_dvd_left hd3 (Nat.Coprime.pow_right m (by norm_num))
  exact hy'1 (orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd2))

omit [Finite G] in
theorem mem_O2H_of_commute {H : Subgroup G} (a b : ↥H)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 ↥H) b * QuotientGroup.mk' (CFSG.pCore 2 ↥H) a =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) a * QuotientGroup.mk' (CFSG.pCore 2 ↥H) b) :
    (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H := by
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hab
  have e : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ =
      ((b : G) * a) * ((((b * a)⁻¹ * (a * b) : ↥H) : G)) * ((b : G) * a)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (mul_mem b.2 a.2)) _).mp hab

namespace Setting147

variable {T L V H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem l1_star_normal (S : Setting147 G T L V H)
    (hC : IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    (modO2Image H (l1 T L V)).Normal := by
  have := hC
  exact normal_of_le_isCyclic normal_oTwoUpper_top (modO2Image_oTwoUpper_le (Setting147.l1H' S))

theorem mem_l1_star_of_cube (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hC : IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    {y : ↥H ⧸ CFSG.pCore 2 ↥H} (hy : y ∈ oTwoUpper ⊤) (hy3 : y ^ 3 = 1) :
    y ∈ modO2Image H (l1 T L V) := by
  have := hC
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hy3) with h | h
  · rw [orderOf_eq_one_iff.mp h]
    exact one_mem _
  · have he : Subgroup.zpowers y = modO2Image H (l1 T L V) :=
      eq_of_le_isCyclic (Subgroup.zpowers_le.mpr hy)
        (modO2Image_oTwoUpper_le (Setting147.l1H' S))
        (by rw [Nat.card_zpowers, h, Setting147.card_l1_star S h1222 h1332 h1334 hHL])
    rw [← he]
    exact Subgroup.mem_zpowers y

theorem R1_le_O2H (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (hC : IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    (h3 : IsPGroup 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    pCoreOf 2 (l1 T L V ⊔ T) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hC
  have hHL := Setting147.H_le_N_l1 S h1332 (Setting147.l1_star_normal S hC)
  have hR := Setting147.R1_star_eq S h1222 h1332 h1334 hHL
  have hTH := Setting147.TH' S
  have hRT := Setting147.R1_le_T S
  have hcent : ∀ r : ↥H, (r : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) →
      ∀ p ∈ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)),
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) r * p * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ =
          p := by
    intro r hr p hp
    have hrs : QuotientGroup.mk' (CFSG.pCore 2 ↥H) r ∈
        modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) := mem_modO2Image'.mpr ⟨r, hr, rfl⟩
    rw [hR] at hrs
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨r, hRT hr⟩
    have hk' : (r : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hkH : r ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    refine comm_of_fix_three (fun a ha b hb => congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) ⟨b, hb⟩)) h3
      (fun z hz => normal_oTwoUpper_top.conj_mem z hz _) (m := k)
      (by rw [← map_pow, hkH, map_one]) (fun y hy hy3 => ?_) hp
    have hyl := Setting147.mem_l1_star_of_cube S h1222 h1332 h1334 hHL hC hy hy3
    have hc := Subgroup.mem_centralizer_iff.mp hrs.2 y hyl
    rw [← hc]
    group
  have hON : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hkH : k ∈ H := oTwoUpper_le H hk
    have hrH : r ∈ H := hTH (hRT hr)
    have hkP : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ ∈ oTwoUpper ⊤ :=
      modO2Image_oTwoUpper_le (X := H) (oTwoUpper_le H) (mem_modO2Image'.mpr ⟨⟨k, hkH⟩, hk, rfl⟩)
    have h1 := hcent ⟨r, hrH⟩ hr _ hkP
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ := by
      calc QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩)⁻¹ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ := by group
        _ = _ := by rw [h1]
    have h3 := mem_O2H_of_commute ⟨k, hkH⟩ ⟨r, hrH⟩ h2
    rw [show k * r * k⁻¹ = (k * r * k⁻¹ * r⁻¹) * r by group]
    exact mul_mem (Setting147.O2H_le_R1 S h3) hr
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := fun t ht =>
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right ht)
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := by
    rw [← F112W.sup_oTwoUpper_eq_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH)]
    exact sup_le hTN hON
  exact le_pCoreOf_of_le_normalizer 2 (hRT.trans hTH) hHN (pCoreOf_isPGroup 2 _)

theorem Uγ_le_O2H (hF : HypF98 T V L (fsuV1 T V) V H) (s : F8Setup T V L H γ γ' g)
    (hR : pCoreOf 2 (l1 T L V ⊔ T) ≤ pCoreOf 2 H) : F8.Uγ V H (g : G) ≤ pCoreOf 2 H := by
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨c, hcH, hc⟩ := S1549C.exists_alpha hF s
  intro w hw
  have h0 : c * w * c⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
    hl1eq ▸ hc (Quasithin.mul_mem_conjSub hw)
  have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hcH)) _).mp
    (hR h0)
  rw [show c⁻¹ * (c * w * c⁻¹) * c⁻¹⁻¹ = w by group] at h2
  exact h2

theorem false_of_Uγ_le (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) (s : F8Setup T V L H γ γ' g)
    (hU : F8.Uγ V H (g : G) ≤ pCoreOf 2 H) : False := by
  refine not_le_of_gt (Dγ_lt_Uγ S hF h1222 h1332 h1334 hHL s) fun w hw => ?_
  obtain ⟨-, hN, hc⟩ := mem_centralizerMod.mp (hF.pCoreOf_eq_centralizerMod.le (hU hw))
  exact mem_centralizerMod.mpr ⟨hw, hN, hc⟩

end Setting147

theorem lemma14_7_8_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : Lemma14_7_8 := by
  rintro G _ _ T L V H S ⟨hC, h3⟩
  have hF : HypF98 T V L (fsuV1 T V) V H :=
    Setting147.hypF98 S (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  exact Setting147.false_of_Uγ_le S hF h1222 h1332 h1334
    (Setting147.H_le_N_l1 S h1332 (Setting147.l1_star_normal S hC)) s
    (Setting147.Uγ_le_O2H hF s (Setting147.R1_le_O2H S h1222 h1332 h1334 hC h3))

end CFSG.Quasithin.H13.L32A
