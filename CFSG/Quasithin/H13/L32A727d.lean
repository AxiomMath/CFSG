module

public import CFSG.Quasithin.H13.L32A727c
public import CFSG.Quasithin.EmptyFaithful.SzN16TwoRed

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem cube_centralizes {X : Type*} [Group X] {W : Subgroup X} [Finite W] {y : X}
    (hyW : y ∈ Subgroup.normalizer (W : Set X)) (hW : Nat.card W ≤ 8) (hy : y ^ 9 = 1)
    {w : X} (hw : w ∈ W) : y ^ 3 * w * (y ^ 3)⁻¹ = w := by
  have hpow : ∀ n : ℕ, y ^ n * w * (y ^ n)⁻¹ ∈ W := fun n =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyW n) w).mp hw
  let f : Fin 9 → ↥W := fun i => ⟨y ^ (i : ℕ) * w * (y ^ (i : ℕ))⁻¹, hpow i⟩
  classical
  have : Fintype ↥W := Fintype.ofFinite _
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hC : ∀ a b : Fin 9, a < b → f a = f b → y ^ ((b : ℕ) - a) ∈
      Subgroup.centralizer ({w} : Set X) := by
    intro a b hab he
    have he' : y ^ (a : ℕ) * w * (y ^ (a : ℕ))⁻¹ = y ^ (b : ℕ) * w * (y ^ (b : ℕ))⁻¹ :=
      congrArg Subtype.val he
    have hb : y ^ (b : ℕ) = y ^ (a : ℕ) * y ^ ((b : ℕ) - a) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hab)]
    rw [hb] at he'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : w = y ^ ((b : ℕ) - a) * w * (y ^ ((b : ℕ) - a))⁻¹ := by
      have := congrArg (fun z => (y ^ (a : ℕ))⁻¹ * z * y ^ (a : ℕ)) he'
      simpa [mul_assoc] using this
    have hcomm : w * y ^ ((b : ℕ) - a) = y ^ ((b : ℕ) - a) * w :=
      calc w * y ^ ((b : ℕ) - a) = y ^ ((b : ℕ) - a) * w * (y ^ ((b : ℕ) - a))⁻¹ *
            y ^ ((b : ℕ) - a) := by rw [← h2]
        _ = y ^ ((b : ℕ) - a) * w := by group
    exact hcomm.symm
  obtain ⟨a, b, hab, hd⟩ : ∃ a b : Fin 9, a < b ∧ y ^ ((b : ℕ) - a) ∈
      Subgroup.centralizer ({w} : Set X) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hC i j h hfij⟩
    · exact ⟨j, i, h, hC j i h hfij.symm⟩
  set d := (b : ℕ) - a with hd'
  have hd1 : 1 ≤ d := by omega
  have hd8 : d ≤ 8 := by omega
  have hy3 : y ^ 3 ∈ Subgroup.centralizer ({w} : Set X) := by
    by_cases h3 : 3 ∣ d
    · obtain ⟨e, he⟩ := h3
      have he12 : e = 1 ∨ e = 2 := by omega
      rcases he12 with rfl | rfl
      · simpa [he] using hd
      · have h6 : y ^ 6 ∈ Subgroup.centralizer ({w} : Set X) := by simpa [he] using hd
        have e3 : y ^ 3 = (y ^ 6) ^ 2 := by
          rw [← pow_mul, show 6 * 2 = 9 + 3 by norm_num, pow_add, hy, one_mul]
        rw [e3]
        exact Subgroup.pow_mem _ h6 2
    · have hcop : Nat.Coprime d 9 := by
        have : Nat.Coprime d 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3 |>.symm
        simpa using Nat.Coprime.pow_right 2 this
      have hcop' : Nat.Coprime d (orderOf y) :=
        Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy) hcop
      have hyC : y ∈ Subgroup.centralizer ({w} : Set X) :=
        (Subgroup.zpowers_le.mpr hd) (A4.mem_zpowers_pow_of_coprime hcop')
      exact Subgroup.pow_mem _ hyC 3
  rw [Subgroup.mem_centralizer_singleton_iff] at hy3
  rw [hy3]
  group

theorem false_of_A (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h79 : Lemma14_7_9) (h78 : Lemma14_7_8)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hexp : ∀ x ∈ K, x ^ 3 = 1) (hKP : K ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hcent : ∀ x ∈ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H), (∀ y ∈ K, x * y = y * x) →
      orderOf x = 3 → x ∈ K)
    (hKne : K ≠ ⊥) (hKM : pre H K ≤ Subgroup.normalizer (L : Set G))
    (hne : CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) ≠ modO2Image H (l1 T L V)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) with hP
  set L1s := modO2Image H (l1 T L V) with hL1s
  have hP3 : IsPGroup 3 ↥P := CFSG.pCore_isPGroup
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hLM := l1T_le_M S.hyp h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  obtain ⟨hYY, hYH, hHY, hY3⟩ := hyp79 hKn hexp
  have hKY := modO2Image_oTwoUpper_pre hK
  have hYM : oTwoUpper (pre H K) ≤ Subgroup.normalizer (L : Set G) :=
    (oTwoUpper_le _).trans hKM
  have hlt : pCoreOf 2 (oTwoUpper (pre H K)) <
      oTwoUpper (pre H K) ⊓ Subgroup.normalizer (L : Set G) := by
    rw [inf_eq_left.mpr hYM]
    refine lt_of_le_of_ne (pCoreOf_le 2 _) fun h => hKne ?_
    have h2 : IsPGroup 2 ↥K := by
      rw [← hKY]
      exact isPGroup_modO2Image (h ▸ pCoreOf_isPGroup 2 _)
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) K K h2 hK)
  obtain ⟨-, h⟩ := h79 G T L V H S _ 3 Nat.prime_three hYY hYH hHY hY3 hlt
  have hYl : oTwoUpper (pre H K) = l1 T L V := by
    rcases h with h | ⟨-, -, -, -, h⟩
    · exact h
    · rw [h, inf_eq_left.mpr hYM, hYY]
  have hKL : K = L1s := by rw [← hKY, hYl]
  have hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    Setting147.H_le_N_l1 S h1332 (show L1s.Normal from hKL ▸ hKn)
  have hL3 : Nat.card ↥L1s = 3 := Setting147.card_l1_star S h1222 h1332 h1334 hHL
  have hKZ : ∀ x ∈ P, ∀ k ∈ K, x * k = k * x := by
    have : Group.IsNilpotent ↥P := hP3.isNilpotent
    have : (K.subgroupOf P).Normal := hKn.subgroupOf P
    have hKP' : K.subgroupOf P ≠ ⊥ := fun h =>
      hKne ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hKP)
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hKP')
    have hzK : ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hz1' : ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) ≠ 1 := fun h =>
      hz1 (Subtype.ext (Subtype.ext h))
    have hKz : K = Subgroup.zpowers ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
      have hcK : Nat.card ↥K = 3 := by rw [hKL]; exact hL3
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzK) ?_).symm
      rw [hcK, Nat.card_zpowers]
      have hd : orderOf ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) ∣ 3 :=
        hcK ▸ Subgroup.orderOf_dvd_natCard K hzK
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1'
      · exact h1.ge
    intro x hx k hk
    rw [hKz] at hk
    obtain ⟨n, rfl⟩ := hk
    have hc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2 ⟨x, hx⟩
    have hc' : x * ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) = ((z : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) * x :=
      congrArg Subtype.val hc
    exact (Commute.zpow_right hc' n).eq
  have hK3 : ∀ x ∈ P, x ^ 3 = 1 → x ∈ K := by
    intro x hx hx3
    by_cases hx1 : x = 1
    · rw [hx1]
      exact K.one_mem
    have hord : orderOf x = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h1
    exact hcent x hx (fun k hk => hKZ x hx k hk) hord
  have hPc : IsCyclic ↥P := by
    by_contra hnc
    have : Fact (IsPGroup 3 ↥P) := ⟨hP3⟩
    obtain ⟨E, -, hE9, hEab⟩ := CFSG.lemma_4_5_a (R := ↥P) (p := 3) (by norm_num) hnc
    have := hEab
    have hEK : E.map P.subtype ≤ K := by
      rintro _ ⟨e, he, rfl⟩
      have he3 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) e he
      exact hK3 _ e.2 (by simpa using congrArg Subtype.val he3)
    have h1 := Subgroup.card_le_of_le hEK
    rw [Subgroup.card_map_of_injective P.subtype_injective, hE9, hKL, hL3] at h1
    norm_num at h1
  have hPM : pre H P ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hPM
    set H0 := pre H P ⊔ T with hH0
    have hH0H : H0 ≤ H := sup_le (pre_le P) hTH
    have hl1P : l1 T L V ≤ pre H P := le_pre_of_le hl1H (show L1s ≤ P from hKL ▸ hKP)
    have hLT0 : l1 T L V ⊔ T ≤ H0 := sup_le (hl1P.trans le_sup_left) le_sup_right
    have S0 := setting_of_le S h1332 h1334 hLT0 hH0H fun h => hPM (le_sup_left.trans h)
    apply h78 G T L V H0 S0
    set P' := modO2Image H0 (pre H P) with hP'
    have hQ0 : pCoreOf 2 H ≤ pCoreOf 2 H0 :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_pre P).trans le_sup_left)
        (hH0H.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    have hP'3 : IsPGroup 3 ↥P' := by
      rintro ⟨z, hz⟩
      obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hz
      obtain ⟨k, hk⟩ := pow_mem_of_isPGroup hP3 ha
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : a ^ 3 ^ k ∈ CFSG.pCore 2 ↥H0 := by
        rw [← mem_pCoreOf_iff]
        simpa using hQ0 hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr h1
    obtain ⟨c, hc⟩ := hPc
    obtain ⟨xc, hxc⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) (c : ↥H ⧸ _)
    have hxcP : (xc : G) ∈ pre H P := (mem_pre xc).mpr (by rw [hxc]; exact c.2)
    have hP'c : P' ≤ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥H0)
        ⟨xc, le_sup_left (a := pre H P) hxcP⟩) := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hz
      have haH : (a : G) ∈ H := hH0H a.2
      obtain ⟨n, hn⟩ := hc ⟨_, (mem_pre (H := H) (K := P) ⟨(a : G), haH⟩).mp ha⟩
      have hn' : (c : ↥H ⧸ _) ^ n = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨a, haH⟩ :=
        congrArg Subtype.val hn
      rw [← hxc, ← map_zpow] at hn'
      have hq : (xc ^ n)⁻¹ * ⟨a, haH⟩ ∈ CFSG.pCore 2 ↥H := by
        rw [← QuotientGroup.eq]
        exact hn'
      rw [← mem_pCoreOf_iff] at hq
      have hq0 : ((⟨xc, le_sup_left (a := pre H P) hxcP⟩ : ↥H0) ^ n)⁻¹ * a ∈
          CFSG.pCore 2 ↥H0 := by
        rw [← mem_pCoreOf_iff]
        simpa using hQ0 hq
      refine ⟨n, ?_⟩
      show QuotientGroup.mk' (CFSG.pCore 2 ↥H0) _ ^ n = _
      rw [← map_zpow]
      exact QuotientGroup.eq.mpr hq0
    have hTop : (⊤ : Subgroup (↥H0 ⧸ CFSG.pCore 2 ↥H0)) ≤ P' ⊔ modO2Image H0 T := by
      exact (modO2Image_self (H := H0)).symm.le.trans
        (modO2Image_sup (H := H0) le_sup_left le_sup_right).le
    have hT2 : IsPGroup 2 ↥(modO2Image H0 T) := isPGroup_modO2Image S.hyp.fsu.sylow.1
    have hTP' : modO2Image H0 T ≤ Subgroup.normalizer (P' : Set (↥H0 ⧸ CFSG.pCore 2 ↥H0)) :=
      modO2Image_le_normalizer' (hTH.trans (le_normalizer_pre CFSG.pCore_normal))
    have hO : oTwoUpper (⊤ : Subgroup (↥H0 ⧸ CFSG.pCore 2 ↥H0)) ≤ P' :=
      oTwoUpper_le_of_pow_mem fun x hx =>
        exists_pow_mem_of_mem_sup_two hT2 hTP' (hTop hx)
    exact ⟨Subgroup.isCyclic_of_le (hO.trans hP'c), hP'3.to_le hO⟩
  obtain ⟨c, hcP⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
  obtain ⟨n, hn⟩ := hP3.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt2
    apply hne
    refine (Subgroup.eq_of_le_of_card_ge (hKL ▸ hKP) ?_).symm
    rw [hn, hL3]
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  have hdvd : 3 ^ (n - 2) ∣ orderOf c := by
    rw [hcP, hn]
    exact Nat.pow_dvd_pow 3 (by omega)
  have hg9 : orderOf (c ^ 3 ^ (n - 2)) = 9 := by
    have hne0 : 3 ^ (n - 2) ≠ 0 := by positivity
    rw [orderOf_pow_of_dvd hne0 hdvd, hcP, hn, Nat.pow_div (by omega) (by norm_num),
      show n - (n - 2) = 2 by omega]
  set g : ↥H ⧸ CFSG.pCore 2 ↥H := ((c ^ 3 ^ (n - 2) : ↥P) : ↥H ⧸ CFSG.pCore 2 ↥H) with hg
  have hgP : g ∈ P := (c ^ 3 ^ (n - 2)).2
  have hgo : orderOf g = 9 := by rw [hg, Subgroup.orderOf_coe, hg9]
  have hg3K : g ^ 3 ∈ K :=
    hK3 _ (P.pow_mem hgP 3) (by rw [← pow_mul, show 3 * 3 = orderOf g by rw [hgo]]
                                exact pow_orderOf_eq_one g)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) g
  have hxP : (x : G) ∈ pre H P := (mem_pre x).mpr (by rw [hx]; exact hgP)
  have hx9 : x ^ 9 ∈ CFSG.pCore 2 ↥H := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (x ^ 9) = 1 := by
      rw [map_pow, hx, ← hgo, pow_orderOf_eq_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [← mem_pCoreOf_iff] at hx9
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hx9⟩
  have hj' : ((x : G) ^ 9) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  set y : ↥H := x ^ 2 ^ j with hy
  have hy9 : (y : G) ^ 9 = 1 := by
    rw [hy, Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hj']
  have hyo : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) y) = 9 := by
    have hcop : (orderOf g).Coprime (2 ^ j) := by
      rw [hgo]
      exact Nat.Coprime.pow_right j (by norm_num)
    rw [hy, map_pow, hx, Nat.Coprime.orderOf_pow hcop, hgo]
  have hy3K : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (y ^ 3) ∈ L1s := by
    rw [← hKL, hy, ← pow_mul, mul_comm, pow_mul, map_pow, map_pow, hx]
    exact K.pow_mem hg3K _
  have hy3o : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) (y ^ 3)) = 3 := by
    rw [map_pow, orderOf_pow_of_dvd (by norm_num) (by rw [hyo]; norm_num), hyo]
  have hyM : (y : G) ∈ Subgroup.normalizer (L : Set G) := hPM (Subgroup.pow_mem _ hxP _)
  have hVc : conjClosure (fsuV1 T V) L = V :=
    (h1334 G T L V S.hyp.hyp.h13 (S.hyp.hyp1223 (stmt13_3_2_two_of h1332)).irrPlus).2.1
  have hyV : (y : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [← hVc]
    exact SzN16.mem_normalizer_conjClosure hyM (S.hz.2.1 y.2)
  have hcube : ∀ v ∈ V, (y : G) ^ 3 * v * ((y : G) ^ 3)⁻¹ = v := fun v hv =>
    cube_centralizes hyV (by rw [hMod.2.1]) hy9 hv
  obtain ⟨l, hl, hle⟩ := mem_modO2Image'.mp hy3K
  have hq : l⁻¹ * y ^ 3 ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp hle
  rw [← mem_pCoreOf_iff] at hq
  set q : G := ((l⁻¹ * y ^ 3 : ↥H) : G) with hqdef
  have hqV : q ∈ Subgroup.normalizer (V : Set G) :=
    hMod.2.2.1 (Subgroup.mem_sup_right (pCoreOf_le_of_le S.hyp hTH hq))
  have hqv : ∀ v ∈ V, q⁻¹ * v * q⁻¹⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (inv_mem hqV) v).mp hv
  have hlq : (l : G) = (y : G) ^ 3 * q⁻¹ := by
    rw [hqdef]
    simp
  have hlv : ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = q⁻¹ * v * q⁻¹⁻¹ := by
    intro v hv
    have := hcube _ (hqv v hv)
    rw [hlq]
    calc (y : G) ^ 3 * q⁻¹ * v * ((y : G) ^ 3 * q⁻¹)⁻¹ =
        (y : G) ^ 3 * (q⁻¹ * v * q⁻¹⁻¹) * ((y : G) ^ 3)⁻¹ := by group
      _ = q⁻¹ * v * q⁻¹⁻¹ := this
  have hpowl : ∀ k : ℕ, ∀ v ∈ V, (l : G) ^ k * v * ((l : G) ^ k)⁻¹ =
      (q⁻¹) ^ k * v * ((q⁻¹) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro v _; simp
    | succ k ih =>
      intro v hv
      have h1 := ih _ (hqv v hv)
      calc (l : G) ^ (k + 1) * v * ((l : G) ^ (k + 1))⁻¹ =
          (l : G) ^ k * ((l : G) * v * (l : G)⁻¹) * ((l : G) ^ k)⁻¹ := by group
        _ = (l : G) ^ k * (q⁻¹ * v * q⁻¹⁻¹) * ((l : G) ^ k)⁻¹ := by rw [hlv v hv]
        _ = (q⁻¹) ^ k * (q⁻¹ * v * q⁻¹⁻¹) * ((q⁻¹) ^ k)⁻¹ := h1
        _ = (q⁻¹) ^ (k + 1) * v * ((q⁻¹) ^ (k + 1))⁻¹ := by group
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨q, hq⟩
  have hm' : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hl'V : ∀ v ∈ V, (l : G) ^ 2 ^ m * v * ((l : G) ^ 2 ^ m)⁻¹ * v⁻¹ ∈ fsuV1 T V := by
    intro v hv
    rw [hpowl _ v hv, inv_pow, hm', inv_one, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hl'L : (l : G) ^ 2 ^ m ∈ l1 T L V := Subgroup.pow_mem _ hl _
  have hl'O : (l : G) ^ 2 ^ m ∉ pCoreOf 2 (l1 T L V) := by
    intro h
    have h1 : ((l ^ 2 ^ m : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [← Setting147.inf_O2H S hHL] at h
      simpa using h.1
    rw [mem_pCoreOf_iff, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow,
      hle] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hy3o] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  have hVV1 : V ≤ fsuV1 T V := fun v hv =>
    Setting147.mem_V1_of_fix S h1222 h1332 h1334 hHL hl'L hl'O (le_conjClosure V H hv)
      (hl'V v hv)
  have h1 := Subgroup.card_le_of_le hVV1
  rw [hMod.2.1, hMod.2.2.2.1] at h1
  norm_num at h1

end CFSG.Quasithin.H13.L32A.R727
