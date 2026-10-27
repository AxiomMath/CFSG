module

public import CFSG.Quasithin.H13.L32AC32h
public import CFSG.Quasithin.H13.L32AC32g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem mk_comm_pow {t : G} (htH : t ∈ H) (w : ↥H) {m : ℕ}
    (hw : (t * w * t⁻¹ * (w : G)⁻¹) ^ 2 ^ m = 1) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) w *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) w)⁻¹) ^ 2 ^ m = 1 := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow]
  convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
  exact Subtype.ext (by simpa using hw)

namespace CtxL2

variable {K : Subgroup G} {t₀ : G} {n : ℕ} (C : CtxL2 T L V H K t₀ n)
include C

theorem n_le_two_of_swap (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting G T L V V₂) {t : G} (htT : t ∈ T) (htL : t ∈ L)
    (htN : t ∉ Subgroup.normalizer (K : Set G)) : n ≤ 2 := by
  have hS1 := C.mk_l1_mem_normalizer_szS1 hA37 h1222 h1332 h1334
  obtain ⟨h', hh'N, hh'o⟩ := exists_orderOf_normalizer_sylow C.isPSL_kb
    (isSylowTwoOf_subgroupOf C.isSylowIn_szS1)
  have hhK : (h' : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ modO2Image H K := h'.2
  have hhS : (h' : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
    have hsQ : (⟨s, hs.2⟩ : ↥(modO2Image H K)) ∈ (szS1 T H K).subgroupOf (modO2Image H K) := hs
    exact (Subgroup.mem_normalizer_iff.mp hh'N _).mp hsQ
  have hho : orderOf (h' : ↥H ⧸ CFSG.pCore 2 ↥H) = 2 ^ n - 1 := by
    rw [Subgroup.orderOf_coe, hh'o]
  obtain ⟨hh, -, hhe⟩ := mem_modO2Image'.mp hhK
  have hhL : (hh : G) ∈ Subgroup.normalizer (L : Set G) :=
    C.mem_normalizer_L hA37 h29 h1222 h1332 h1334 hS1
      (by rw [hhe]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨hhS, hhK⟩))
  have hhX := C.mem_nX h1332 h1334 hh.2 hhL
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  have hw : (hh : G) ^ 6 ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have e : (⟨(hh : G) ^ 6, pow_mem hhX 6⟩ : ↥(L32NSet14.nX T V)) = ⟨(hh : G), hhX⟩ ^ 6 := rfl
    refine (hψ ⟨(hh : G) ^ 6, pow_mem hhX 6⟩).mp ?_
    rw [e, map_pow]
    exact L32NSet14.sl2_pow_six _
  obtain ⟨m, hm⟩ := comm_pow_two S14 htL (S14.T_le_X htT) (pow_mem hhL 6) hw
  have htH : t ∈ H := C.hTH htT
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ with htb
  set h : ↥H ⧸ CFSG.pCore 2 ↥H := (h' : ↥H ⧸ CFSG.pCore 2 ↥H) with hhdef
  have hcb : (tb * h ^ 6 * tb⁻¹ * (h ^ 6)⁻¹) ^ 2 ^ m = 1 := by
    have := mk_comm_pow htH (hh ^ 6) (by simpa using hm)
    rwa [map_pow, hhe] at this
  have hbK' : tb * h ^ 6 * tb⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
    have hr := (C.two t htH).resolve_left htN
    have hrH : t₀⁻¹ * t ∈ H := mul_mem (inv_mem C.ht₀H) htH
    have hrb := mk_mem_normalizer (y := ⟨t₀⁻¹ * t, hrH⟩) C.hKH hr
    have h1 := (Subgroup.mem_normalizer_iff.mp hrb _).mp (pow_mem hhK 6)
    rw [← C.kb'_eq]
    refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
    have e : tb = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * t, hrH⟩ := by
      rw [htb, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [e]
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  have hab : ((h ^ 6)⁻¹ * (tb * h ^ 6 * tb⁻¹)) ^ 2 ^ m = 1 := by
    rw [C.commute_kb hA37 (inv_mem (pow_mem hhK 6)) hbK']
    exact hcb
  have ha := pow_eq_one_of_mul (fun a ha b hb => C.commute_kb hA37 ha hb)
    (fun z hz hz' => C.eq_one_of_mem_kb_kt hA37 hz hz') (inv_mem (pow_mem hhK 6)) hbK' hab
  have h6 : h ^ (6 * 2 ^ m) = 1 := by
    rw [inv_pow, inv_eq_one, ← pow_mul] at ha
    exact ha
  have hdvd : 2 ^ n - 1 ∣ 6 * 2 ^ m := hho ▸ orderOf_dvd_of_pow_eq_one h6
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by have := C.hn; omega⟩)
      odd_one
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  have h6' : 2 ^ n - 1 ∣ 6 := hcop.dvd_of_dvd_mul_right hdvd
  have hle := Nat.le_of_dvd (by norm_num) h6'
  by_contra hn
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem false_of_not_swap (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting G T L V V₂) {x : G} (hx : x ∈ l1 T L V) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {t : G} (htT : t ∈ T)
    (htL : t ∈ L) (htn : t ∉ L32NSet14.trivSub V (fsuV1 T V))
    (htN : t ∈ Subgroup.normalizer (K : Set G)) : False := by
  have hS1 := C.mk_l1_mem_normalizer_szS1 hA37 h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have htH : t ∈ H := C.hTH htT
  obtain ⟨k₁, hk₁K, k₂, hk₂K, he, hk₁3, hk₂3, hk₁, hk₂⟩ := C.decomp hA37 hx hx3
  obtain ⟨hk₁1, hk₂1⟩ := C.k_ne_one hA37 h1222 h1332 h1334 hx hx3 hfpf hk₁K hk₂K he
  have hk₁B := C.k₁_mem_szB1 h1222 h1332 h1334 hx hx3 hk₁K hk₁
  have hk₂B := C.k₂_mem_szB2 h1222 h1332 h1334 hx hx3 hk₂K hk₂
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ with htb
  set t₀b := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ with ht₀b
  have hBS : ∀ b ∈ szB1 T H K, ∀ m : ℕ, b ^ 2 ^ m = 1 → b ∈ szS1 T H K :=
    fun b hb m hbm => mem_of_pow_two C.isSylowIn_szS1 hb.2 hb.1 hbm
  have hS₁p : IsPGroup 2 ↥(szS1 T H K) := C.isSylowIn_szS1.isPGroup
  have hS₂p : IsPGroup 2 ↥((szS1 T H K).map (MulAut.conj t₀b : _ →* (↥H ⧸ CFSG.pCore 2 ↥H))) :=
    hS₁p.map _
  have htK : tb ∈ Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    mk_mem_normalizer C.hKH htN
  have htK' : tb ∈ Subgroup.normalizer
      (modO2Image H (K.map (MulAut.conj t₀ : G →* G)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    mk_mem_normalizer C.hKtH (C.mem_normalizer_kt htH htN)
  have htB1 : tb ∈ Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    C.mk_T_mem_normalizer_szB1 htT htN
  have htB2 : tb ∈ Subgroup.normalizer (((szB1 T H K).map
      (MulAut.conj t₀b : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup _) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine mem_normalizer_map_conj ?_
    have hrH : t₀⁻¹ * t * t₀ ∈ H := mul_mem (mul_mem (inv_mem C.ht₀H) htH) C.ht₀H
    have hrT : t₀⁻¹ * t * t₀ ∈ T := mul_mem (mul_mem (inv_mem C.ht₀) htT) C.ht₀
    have hrN : t₀⁻¹ * t * t₀ ∈ Subgroup.normalizer (K : Set G) := by
      rcases C.two _ hrH with h | h
      · exact h
      · exfalso
        apply C.ht₀N
        have := mul_mem (inv_mem htN) (mul_mem C.sq_mem h)
        rwa [show t⁻¹ * (t₀ * t₀ * (t₀⁻¹ * (t₀⁻¹ * t * t₀))) = t₀ by group] at this
    have e : t₀b⁻¹ * tb * t₀b = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀⁻¹ * t * t₀, hrH⟩ := by
      rw [ht₀b, htb, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact C.mk_T_mem_normalizer_szB1 hrT hrN
  have hxL : x ∈ L₁Of L (fsuV1 T V) := by rw [hl1]; exact hx
  obtain ⟨m₀, hm₀⟩ := comm_x_pow_two S14 hxL hx3 hfpf htT htn
  have hκ : (tb * (k₁ * k₂) * tb⁻¹ * (k₁ * k₂)) ^ 2 ^ m₀ = 1 := by
    rw [← he, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hm₀)
  have hk₂t : tb * k₂ * tb⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :=
    (Subgroup.mem_normalizer_iff.mp htK' k₂).mp hk₂K
  have hk₁t : tb * k₁ * tb⁻¹ ∈ modO2Image H K := (Subgroup.mem_normalizer_iff.mp htK k₁).mp hk₁K
  rw [conj_mul_split (C.commute_kb hA37 hk₁K hk₂t).symm] at hκ
  have ha'₁ := pow_eq_one_of_mul (fun a ha b hb => C.commute_kb hA37 ha hb)
    (fun z hz hz' => C.eq_one_of_mem_kb_kt hA37 hz hz') (mul_mem hk₁t hk₁K)
    (mul_mem hk₂t hk₂K) hκ
  have ha'₂ := pow_eq_one_of_mul (fun a ha b hb => (C.commute_kb hA37 hb ha).symm)
    (fun z hz hz' => C.eq_one_of_mem_kb_kt hA37 hz' hz) (mul_mem hk₂t hk₂K)
    (mul_mem hk₁t hk₁K) (by rwa [(C.commute_kb hA37 (mul_mem hk₁t hk₁K) (mul_mem hk₂t hk₂K))]
      at hκ)
  have hS₁a' : tb * k₁ * tb⁻¹ * k₁ ∈ szS1 T H K :=
    hBS _ (mul_mem ((Subgroup.mem_normalizer_iff.mp htB1 k₁).mp hk₁B) hk₁B) m₀ ha'₁
  have hS₂a' : tb * k₂ * tb⁻¹ * k₂ ∈
      (szS1 T H K).map (MulAut.conj t₀b : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    mem_map_conj_of_pow_two hBS (mul_mem ((Subgroup.mem_normalizer_iff.mp htB2 k₂).mp hk₂B)
      hk₂B) ha'₂
  obtain ⟨q₁, -, hq₁e⟩ := mem_modO2Image'.mp hk₁K
  obtain ⟨q₂, -, hq₂e⟩ := mem_modO2Image'.mp hk₂K
  have hq₁L : (q₁ : G) ∈ Subgroup.normalizer (L : Set G) :=
    C.mem_normalizer_L hA37 h29 h1222 h1332 h1334 hS1
      (by rw [hq₁e]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hk₁B))
  have hq₂L : (q₂ : G) ∈ Subgroup.normalizer (L : Set G) :=
    C.mem_normalizer_L hA37 h29 h1222 h1332 h1334 hS1
      (by rw [hq₂e]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hk₂B))
  have hq₁X := C.mem_nX h1332 h1334 q₁.2 hq₁L
  have hq₂X := C.mem_nX h1332 h1334 q₂.2 hq₂L
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  have hQ := pCoreOf_le_trivSub C.S S14
  have hcube : ∀ (q : ↥H) (hqX : (q : G) ∈ L32NSet14.nX T V) (k : ↥H ⧸ CFSG.pCore 2 ↥H),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) q = k → k ^ 3 = 1 → ψ ⟨q, hqX⟩ ^ 3 = 1 := by
    intro q hqX k hqk hk3
    rw [← map_pow]
    have h1 : (q : G) ^ 3 ∈ pCoreOf 2 H := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (q ^ 3) = 1 := by rw [map_pow, hqk, hk3]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
        Subgroup.mem_subgroupOf] at h2
      simpa using h2
    have h2 : (⟨q, hqX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = ⟨(q : G) ^ 3, pow_mem hqX 3⟩ := rfl
    rw [h2]
    exact (hψ _).mpr (hQ h1)
  have hψ1 := hcube q₁ hq₁X k₁ hq₁e hk₁3
  have hψ2 := hcube q₂ hq₂X k₂ hq₂e hk₂3
  have hcase₁ : ∀ j : ℕ, ψ ⟨q₁, hq₁X⟩ * ψ ⟨q₂, hq₂X⟩ ^ j = 1 → False := by
    intro j hj
    have hwX : (q₁ : G) * (q₂ : G) ^ j ∈ L32NSet14.nX T V := mul_mem hq₁X (pow_mem hq₂X j)
    have hw : (q₁ : G) * (q₂ : G) ^ j ∈ L32NSet14.trivSub V (fsuV1 T V) := by
      have e : (⟨(q₁ : G) * (q₂ : G) ^ j, hwX⟩ : ↥(L32NSet14.nX T V)) =
          ⟨q₁, hq₁X⟩ * ⟨q₂, hq₂X⟩ ^ j := rfl
      refine (hψ ⟨(q₁ : G) * (q₂ : G) ^ j, hwX⟩).mp ?_
      rw [e, map_mul, map_pow]
      exact hj
    obtain ⟨m, hm⟩ := comm_pow_two S14 htL (S14.T_le_X htT) (mul_mem hq₁L (pow_mem hq₂L j)) hw
    have hc := mk_comm_pow htH (q₁ * q₂ ^ j) (by simpa using hm)
    rw [map_mul, map_pow, hq₁e, hq₂e] at hc
    have hk₂j : k₂ ^ j ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := pow_mem hk₂K j
    have hB : tb * k₂ ^ j * tb⁻¹ * (k₂ ^ j)⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp htK' _).mp hk₂j) (inv_mem hk₂j)
    rw [comm_mul_split (C.commute_kb hA37 (inv_mem hk₁K) hB).symm] at hc
    have ha₁ := pow_eq_one_of_mul (fun a ha b hb => C.commute_kb hA37 ha hb)
      (fun z hz hz' => C.eq_one_of_mem_kb_kt hA37 hz hz') (mul_mem hk₁t (inv_mem hk₁K)) hB hc
    have hS₁a : tb * k₁ * tb⁻¹ * k₁⁻¹ ∈ szS1 T H K :=
      hBS _ (mul_mem ((Subgroup.mem_normalizer_iff.mp htB1 k₁).mp hk₁B) (inv_mem hk₁B)) m ha₁
    exact hk₁1 (eq_one_of_conj_mul hS₁p hk₁3 hS₁a hS₁a')
  rcases sl2_cube_cases _ _ hψ1 hψ2 with h | h | h | h
  · exact hcase₁ 0 (by rw [pow_zero, mul_one]; exact h)
  · exact hcase₁ 1 (by rw [pow_one]; exact h)
  · exact hcase₁ 2 h
  ·
    have hw : (q₂ : G) ∈ L32NSet14.trivSub V (fsuV1 T V) := (hψ ⟨q₂, hq₂X⟩).mp h
    obtain ⟨m, hm⟩ := comm_pow_two S14 htL (S14.T_le_X htT) hq₂L hw
    have hc := mk_comm_pow htH q₂ hm
    rw [hq₂e] at hc
    have hS₂a : tb * k₂ * tb⁻¹ * k₂⁻¹ ∈
        (szS1 T H K).map (MulAut.conj t₀b : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      mem_map_conj_of_pow_two hBS (mul_mem ((Subgroup.mem_normalizer_iff.mp htB2 k₂).mp hk₂B)
        (inv_mem hk₂B)) hc
    exact hk₂1 (eq_one_of_conj_mul hS₂p hk₂3 hS₂a hS₂a')

theorem n_eq_two (hA37 : A37ForSQTK) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : n = 2 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := by rw [← hl1]; exact hxL
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv C.S.hyp h1332 S14
  by_cases htN : t ∈ Subgroup.normalizer (K : Set G)
  · exact (C.false_of_not_swap hA37 h29 h1222 h1332 h1334 S14 hx hx3 hfpf htT htL htn
      htN).elim
  · have := C.n_le_two_of_swap hA37 h29 h1222 h1332 h1334 S14 htT htL htN
    have := C.hn
    omega

end CtxL2

end CFSG.Quasithin.H13.L32A.C
