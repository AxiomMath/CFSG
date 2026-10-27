module

public import CFSG.Quasithin.H13.L32AC41f
public import CFSG.Quasithin.H13.L32AC43a
public import CFSG.Quasithin.H13.L32A727b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem eq_zpowers_of_card_three {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : Nat.card A = 3) {x : X} (hx : x ∈ A) (hx1 : x ≠ 1) : A = Subgroup.zpowers x := by
  have hle : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.mpr hx
  have hdvd : orderOf x ∣ 3 := by
    rw [← hA, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have ho : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, ho, hA]

theorem mul_comm_of_card_three {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : Nat.card A = 3) {a b : X} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  rw [eq_zpowers_of_card_three hA ha ha1] at hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_one_add, ← zpow_add_one, add_comm]

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure Hyp42 (T L V H K : Subgroup G) : Prop where
  S : Setting147 G T L V H
  hK : K ∈ cComp H
  hq : CFSG.IsQuasisimple (cStar K)
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHeq : H = K ⊔ (l1 T L V ⊔ T)
  hl1K : ¬ l1 T L V ≤ K
  hc : modO2Image H (l1 T L V) ≤
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))

namespace Hyp42

variable {K : Subgroup G} (C : Hyp42 T L V H K)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem hTH : T ≤ H := Setting147.TH' C.S

theorem hl1H : l1 T L V ≤ H := Setting147.l1H' C.S

theorem kbNormal : (modO2Image H K).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer C.hKH).mpr C.hKn).map _
    (QuotientGroup.mk'_surjective _)

theorem comm_mem {y : G} (hy : y ∈ l1 T L V) {k : G} (hk : k ∈ K) :
    y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have hyH := C.hl1H hy
  have hkH := C.hKH hk
  have h1 := Subgroup.mem_centralizer_iff.mp (C.hc (mem_modO2Image'.mpr ⟨⟨y, hyH⟩, hy, rfl⟩))
    _ (mem_modO2Image'.mpr ⟨⟨k, hkH⟩, hk, rfl⟩)
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      ((⟨y, hyH⟩ : ↥H) * ⟨k, hkH⟩ * (⟨y, hyH⟩ : ↥H)⁻¹ * (⟨k, hkH⟩ : ↥H)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  exact (mk_pCore_eq_one_iff _).mp h2

theorem lbNormal (h1332 : Stmt13_3_2) : (modO2Image H (l1 T L V)).Normal := by
  have hcm : ∀ y ∈ l1 T L V, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    fun y hy k hk => C.comm_mem hy hk
  have hS := C.S
  have hKn := C.hKn
  have hHeq := C.hHeq
  subst hHeq
  exact l1_star_normal h1332 hS (le_sup_right.trans hKn) hcm

theorem hHL (h1332 : Stmt13_3_2) : H ≤ Subgroup.normalizer (l1 T L V : Set G) :=
  Setting147.H_le_N_l1 C.S h1332 (C.lbNormal h1332)

theorem card_lb (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Nat.card ↥(modO2Image H (l1 T L V)) = 3 :=
  Setting147.card_l1_star C.S h1222 h1332 h1334 (C.hHL h1332)

theorem lb_inf_kb (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    modO2Image H (l1 T L V) ⊓ modO2Image H K = ⊥ := by
  have hcard := C.card_lb h1222 h1332 h1334
  have hdvd : Nat.card ↥(modO2Image H (l1 T L V) ⊓ modO2Image H K) ∣ 3 :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · refine absurd (l1_le_of_star_le C.S C.hK C.hKn ?_) C.hl1K
    have := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : modO2Image H (l1 T L V) ⊓ modO2Image H K ≤ _) (h3.trans hcard.symm).ge
    rw [← this]
    exact inf_le_right

theorem oddCore_eq (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V) := by
  have hcard := C.card_lb h1222 h1332 h1334
  rcases h28 G T L V H C.S with h | h
  · have hle : modO2Image H (l1 T L V) ≤ CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) :=
      le_sSup ⟨C.lbNormal h1332, by rw [hcard]; decide⟩
    rw [h, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hcard
    omega
  · exact h

theorem center_eq_bot (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    Subgroup.center ↥(modO2Image H K) = ⊥ := by
  set Kb := modO2Image H K with hKb
  have hKbN : Kb.Normal := C.kbNormal
  obtain ⟨-, hodd, -⟩ := kst_props C.hK C.hq hLie
  set Z : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (Subgroup.center ↥Kb).map Kb.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨z', hz', rfl⟩ := hz
    refine ⟨⟨g * z' * g⁻¹, hKbN.conj_mem _ z'.2 g⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    have hy : g⁻¹ * (y : ↥H ⧸ CFSG.pCore 2 ↥H) * g ∈ Kb := by
      simpa using hKbN.conj_mem _ y.2 g⁻¹
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h1 ⊢
    calc (y : ↥H ⧸ CFSG.pCore 2 ↥H) * (g * z' * g⁻¹) = g * (g⁻¹ * y * g * z') * g⁻¹ := by group
      _ = g * (z' * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * z' * g⁻¹ * y := by group
  have hZodd : Odd (Nat.card Z) := by
    rwa [hZ, Subgroup.card_map_of_injective Kb.subtype_injective]
  have hZL : Z ≤ modO2Image H (l1 T L V) :=
    (C.oddCore_eq h28 h1222 h1332 h1334) ▸ le_sSup ⟨hZn, hZodd⟩
  have hZK : Z ≤ Kb := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hZ1 : Z = ⊥ := by
    have := le_inf hZL hZK
    rwa [C.lb_inf_kb h1222 h1332 h1334, le_bot_iff] at this
  rw [eq_bot_iff]
  intro z hz
  have : (z : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Z := ⟨z, hz, rfl⟩
  rw [hZ1, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem cent_inf_kb (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ modO2Image H K = ⊥ := by
  have hZ := C.center_eq_bot h28 h1222 h1332 h1334 hLie
  rw [eq_bot_iff]
  rintro z ⟨hzC, hzK⟩
  have hz : (⟨z, hzK⟩ : ↥(modO2Image H K)) ∈ Subgroup.center ↥(modO2Image H K) :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC y y.2)
  rw [hZ, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz)

theorem pRank_kb (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h34 : Lemma14_7_34) : CFSG.pRank 3 ↥(modO2Image H K) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  set Lb := modO2Image H (l1 T L V) with hLb
  have hcard := C.card_lb h1222 h1332 h1334
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine le_antisymm ?_ ?_
  · obtain ⟨E, -, hE, hEc⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup ↥Kb)
    have hsq : SQTKGroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
      S153D.sqtkGroup_quot_pCore (sqtkGroup_of_setting C.S)
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 :=
      hsq.1 3 Nat.prime_three (by norm_num)
    have hcomm : ∀ (e : ↥E) (l : ↥Lb), Commute ((Kb.subtype.comp E.subtype) e) (Lb.subtype l) :=
      fun e l => Subgroup.mem_centralizer_iff.mp (C.hc l.2) _ (e : ↥Kb).2
    set f := MonoidHom.noncommCoprod (Kb.subtype.comp E.subtype) Lb.subtype hcomm with hf
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      rintro ⟨e, l⟩ h
      have h1 : ((e : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) * (l : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := h
      have he : ((e : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Lb ⊓ Kb := by
        refine ⟨?_, (e : ↥Kb).2⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Lb.inv_mem l.2
      rw [C.lb_inf_kb h1222 h1332 h1334, Subgroup.mem_bot] at he
      have he' : e = 1 := Subtype.ext (Subtype.ext he)
      subst he'
      have hl : l = 1 := Subtype.ext (by simpa using h1)
      rw [hl]
      rfl
    have := hE.1
    have hAc : ∀ a b : ↥E × ↥Lb, a * b = b * a := by
      rintro ⟨e, l⟩ ⟨e', l'⟩
      exact Prod.ext (mul_comm' e e') (Subtype.ext (mul_comm_of_card_three hcard l.2 l'.2))
    have hApow : ∀ a : ↥E × ↥Lb, a ^ 3 = 1 := by
      rintro ⟨e, l⟩
      refine Prod.ext (Subtype.ext (hE.2 _ e.2)) (Subtype.ext ?_)
      have hd : orderOf l ∣ 3 := hcard ▸ orderOf_dvd_natCard l
      have := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
      simpa using this
    have hAcard : Nat.card (↥E × ↥Lb) =
        3 ^ (CFSG.Open.pRank 3 (⊤ : Subgroup ↥Kb) + 1) := by
      rw [Nat.card_prod, hEc, hcard, pow_succ]
    have := CFSG.SectionRank.le_pRank_of_injective (by norm_num) hAc hApow hAcard f hfinj le_top
    omega
  · obtain ⟨E, hEK, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
    have h1 : 1 ≤ CFSG.Open.pRank 3 K := by
      rcases h34 G T L V H C.S K C.hK with h | h <;> omega
    obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hb : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
      rw [hb, Subgroup.card_bot] at hEc
      have : 3 ≤ 3 ^ CFSG.Open.pRank 3 K := Nat.le_self_pow (by omega) 3
      omega
    have he3 : e ^ 3 = 1 := hE.2 e heE
    have heK := hEK heE
    have heH := C.hKH heK
    set y := QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨e, heH⟩ : ↥H) with hy
    have hyK : y ∈ Kb := mem_modO2Image'.mpr ⟨⟨e, heH⟩, heK, rfl⟩
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← map_pow]
      have : (⟨e, heH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using he3)
      rw [this, map_one]
    have hy1 : y ≠ 1 := by
      intro h
      have heO : e ∈ pCoreOf 2 H := (mk_pCore_eq_one_iff _).mp h
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨e, heO⟩
      have hk' : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      exact he1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one he3)))
    set y' : ↥Kb := ⟨y, hyK⟩ with hy'
    have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top
      (E := Subgroup.zpowers y') ⟨inferInstance, fun x hx => ?_⟩ ?_
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy'3, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hy'3 hy'1, pow_one]

theorem exists_tC (hN1 : LieSylowOver3) (hN4 : LieBorelTwoInner) (h29 : Thm14_7_29)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h34 : Lemma14_7_34)
    {n : ℕ} (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    ∃ x ∈ modO2Image H (l1 T L V),
      ∃ t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)),
        x ^ 3 = 1 ∧ x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨mx, hmxL, ms, hmsLT, hx3, hx1, ⟨ks, hks⟩, hsx, -, hsB, -⟩ :=
    exists_inv_pair_borel hN1 h29 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie C.hl1K
  have hKbN : (modO2Image H K).Normal := C.kbNormal
  obtain ⟨hqX, hoddX, hLieX⟩ := kst_props C.hK C.hq hLie
  have hS := isSylowIn_szS1_of C.S C.hK
  have hN1' := l1T_le_normalizer_szS1' hN1 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie
  set α : MulAut ↥(modO2Image H K) := MulAut.conjNormal ms with hα
  have hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1 := ⟨ks, by rw [hα, ← map_pow, hks, map_one]⟩
  obtain ⟨s, -, hαs⟩ := hN4 _ n hn hqX hoddX hLieX (C.pRank_kb h1222 h1332 h1334 h34)
    _ (isSylowTwoOf_subgroupOf hS) α hα2 (map_conjNormal_szS1 (hN1' hmsLT))
    (conjNormal_mul_inv_mem C.S C.hK hsB)
  have key : ∀ y : ↥(modO2Image H K),
      ms * (y : ↥H ⧸ CFSG.pCore 2 ↥H) * ms⁻¹ =
        (s : ↥H ⧸ CFSG.pCore 2 ↥H) * y * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut ↥(modO2Image H K) =>
      ((φ y : ↥(modO2Image H K)) : ↥H ⧸ CFSG.pCore 2 ↥H)) hαs
    simpa [hα, MulAut.conjNormal_apply, Subgroup.coe_inv] using this
  refine ⟨mx, hmxL, ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹, ?_, hx3, hx1, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * y * s ∈ modO2Image H K := by
      simpa using hKbN.conj_mem y hy (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹
    have h1 := key ⟨_, hy'⟩
    have h2 : ms * ((s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * y * s) * ms⁻¹ = y := by
      rw [h1]
      group
    calc y * (ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹) =
        ms * ((s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * y * s) * ms⁻¹ *
          (ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹) := by rw [h2]
      _ = ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * y := by group
  · have hsc : (s : ↥H ⧸ CFSG.pCore 2 ↥H) * mx = mx * s :=
      Subgroup.mem_centralizer_iff.mp (C.hc hmxL) _ s.2
    calc ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * mx * (ms * (s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹)⁻¹ =
        ms * ((s : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * (mx * s)) * ms⁻¹ := by group
      _ = ms * mx * ms⁻¹ := by rw [← hsc]; group
      _ = mx⁻¹ := hsx

theorem cent_inf_cent (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓
      Subgroup.centralizer (modO2Image H (l1 T L V) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) =
      modO2Image H (l1 T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  set Lb := modO2Image H (l1 T L V) with hLb
  set Tb := modO2Image H T with hTb
  set N := Subgroup.centralizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓
    Subgroup.centralizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hN
  have hKbN : Kb.Normal := C.kbNormal
  have hLbN : Lb.Normal := C.lbNormal h1332
  have hcard := C.card_lb h1222 h1332 h1334
  have hLN : Lb ≤ N := le_inf C.hc fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    mul_comm_of_card_three hcard hb ha
  have hNK : N ⊓ Kb = ⊥ := by
    rw [eq_bot_iff, ← C.cent_inf_kb h28 h1222 h1332 h1334 hLie]
    exact inf_le_inf_right _ inf_le_left
  have h2 : ∀ x ∈ N, ∃ e : ℕ, x ^ 2 ^ e ∈ Lb := by
    intro x hxN
    have htop : (Kb ⊔ Lb) ⊔ Tb = ⊤ := by
      rw [sup_assoc, hKb, hLb, hTb, ← R727.modO2Image_sup C.hl1H C.hTH,
        ← R727.modO2Image_sup C.hKH (sup_le C.hl1H C.hTH), ← C.hHeq, R727.modO2Image_self]
    have hM : (Kb ⊔ Lb).Normal := Subgroup.sup_normal _ _
    obtain ⟨m, hm, t, ht, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (fun g _ => (Subgroup.normalizer_eq_top_iff.mpr hM).symm ▸ Subgroup.mem_top g)).mp
      (htop ▸ Subgroup.mem_top x)
    have hT2 : IsPGroup 2 ↥Tb := R727.isPGroup_modO2Image C.S.hyp.fsu.sylow.1
    obtain ⟨e, he⟩ := hT2 ⟨t, ht⟩
    have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    refine ⟨e, ?_⟩
    have hmem : (m * t) ^ 2 ^ e ∈ Kb ⊔ Lb := by
      have hm1 : QuotientGroup.mk' (Kb ⊔ Lb) m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      have h1 : QuotientGroup.mk' (Kb ⊔ Lb) ((m * t) ^ 2 ^ e) = 1 := by
        rw [map_pow, map_mul, hm1, one_mul, ← map_pow, he', map_one]
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk, l, hl, hkl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (fun g _ => (Subgroup.normalizer_eq_top_iff.mpr hKbN).symm ▸ Subgroup.mem_top g)).mp hmem
    have hkN : k ∈ N := by
      have h1 : k = (m * t) ^ 2 ^ e * l⁻¹ := by rw [hkl, mul_inv_cancel_right]
      rw [h1]
      exact mul_mem (pow_mem hxN _) (inv_mem (hLN hl))
    have hk1 : k ∈ N ⊓ Kb := ⟨hkN, hk⟩
    rw [hNK, Subgroup.mem_bot] at hk1
    rw [hkl, hk1, one_mul]
    exact hl
  have hNn : N.Normal := Subgroup.normal_inf_normal _ _
  set Lb' := Lb.subgroupOf N with hLb'
  have hLb'n : Lb'.Normal := hLbN.subgroupOf N
  have hLb'c : Nat.card Lb' = 3 := by
    rw [hLb', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv, hcard]
  have hp : IsPGroup 2 (↥N ⧸ Lb') := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 x x.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using he)
  obtain ⟨b, hb⟩ := hp.exists_card_eq
  have hidx : Lb'.index = 2 ^ b := hb
  have hcop : Nat.Coprime (Nat.card Lb') Lb'.index := by
    rw [hLb'c, hidx]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨P, hP⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hPc : Nat.card P = 2 ^ b := by
    have h1 := hP.card_mul_card
    have h3 := Lb'.card_mul_index
    rw [hidx] at h3
    have h4 : 0 < Nat.card Lb' := by rw [hLb'c]; norm_num
    exact Nat.eq_of_mul_eq_mul_left h4 (h1.trans h3.symm)
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hPc
  have hcentral : ∀ l ∈ Lb', ∀ y : ↥N, l * y = y * l := by
    intro l hl y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2.2 _ (Subgroup.mem_subgroupOf.mp hl))
  have hPn : P.Normal := by
    refine ⟨fun p hp g => ?_⟩
    obtain ⟨l, hl, p', hp', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (fun g _ => (Subgroup.normalizer_eq_top_iff.mpr hLb'n).symm ▸ Subgroup.mem_top g)).mp
      (hP.sup_eq_top ▸ Subgroup.mem_top g)
    have e : l * p' * p * (l * p')⁻¹ = p' * p * p'⁻¹ := by
      calc l * p' * p * (l * p')⁻¹ = l * (p' * p * p'⁻¹) * l⁻¹ := by group
        _ = p' * p * p'⁻¹ * l * l⁻¹ := by rw [hcentral l hl]
        _ = p' * p * p'⁻¹ := by group
    rw [e]
    exact P.mul_mem (P.mul_mem hp' hp) (P.inv_mem hp')
  have hP'O : P.map N.subtype ≤ pCoreOf 2 N := by
    refine le_pCoreOf 2 (Subgroup.map_subtype_le P) ?_ (hP2.map _)
    show ((P.map N.subtype).comap N.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact hPn
  have hO : pCoreOf 2 N ≤ CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) := by
    have hnorm : (pCoreOf 2 N).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      exact normalizer_le_normalizer_pCoreOf 2 N
        ((Subgroup.normalizer_eq_top_iff.mpr hNn).symm ▸ Subgroup.mem_top g)
    exact le_sSup ⟨hnorm, pCoreOf_isPGroup 2 N⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hO
  have hP1 : P = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp
      (le_bot_iff.mp (hP'O.trans hO))
  have hLtop : Lb' = ⊤ := by
    have := hP.sup_eq_top
    rwa [hP1, sup_bot_eq] at this
  refine le_antisymm (fun x hx => ?_) hLN
  have : (⟨x, hx⟩ : ↥N) ∈ Lb' := hLtop ▸ Subgroup.mem_top _
  exact this

theorem mem_cent_cases (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x t : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) (hx1 : x ≠ 1)
    (ht : t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (htx : t * x * t⁻¹ = x⁻¹) {r : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hr : r ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    ∃ i : ℕ, r = x ^ i ∨ r = t * x ^ i := by
  classical
  have hcard := C.card_lb h1222 h1332 h1334
  have hLbN : (modO2Image H (l1 T L V)).Normal := C.lbNormal h1332
  have hLz := eq_zpowers_of_card_three hcard hx hx1
  have hN := C.cent_inf_cent h28 h1222 h1332 h1334 hLie
  have hx3 : x ^ 3 = 1 := by
    have hd : orderOf x ∣ 3 := by
      rw [← hcard, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hnat : ∀ y ∈ modO2Image H (l1 T L V), ∃ i : ℕ, i < 3 ∧ y = x ^ i := by
    intro y hy
    rw [hLz, mem_zpowers_iff_mem_range_orderOf, hox] at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  have hpow : ∀ y ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)),
      y * x = x * y → ∃ i : ℕ, y = x ^ i := by
    intro y hy hyx
    have hyL : y ∈ modO2Image H (l1 T L V) := by
      rw [← hN]
      refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      rw [hLz] at hl
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
      exact ((Commute.zpow_left (show Commute x y from hyx.symm) k)).eq
    obtain ⟨i, -, hi⟩ := hnat y hyL
    exact ⟨i, hi⟩
  obtain ⟨j, hj, hjx⟩ := hnat _ (hLbN.conj_mem x hx r)
  interval_cases j
  · exfalso
    apply hx1
    rw [pow_zero] at hjx
    calc x = r⁻¹ * (r * x * r⁻¹) * r := by group
      _ = 1 := by rw [hjx]; group
  · obtain ⟨i, hi⟩ := hpow r hr (by
      rw [pow_one] at hjx
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [hjx])
    exact ⟨i, Or.inl hi⟩
  · have htr : t⁻¹ * r ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      mul_mem (inv_mem ht) hr
    have hx2 : x ^ 2 = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx3]
    obtain ⟨i, hi⟩ := hpow _ htr (by
      rw [hx2] at hjx
      have e1 : x = t⁻¹ * x⁻¹ * t := by
        calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
          _ = t⁻¹ * x⁻¹ * t := by rw [htx]
      calc t⁻¹ * r * x = t⁻¹ * (r * x * r⁻¹) * r := by group
        _ = t⁻¹ * x⁻¹ * t * (t⁻¹ * r) := by rw [hjx]; group
        _ = x * (t⁻¹ * r) := by rw [← e1])
    exact ⟨i, Or.inr (by rw [← hi]; group)⟩

end Hyp42

end CFSG.Quasithin.H13.L32A.C
