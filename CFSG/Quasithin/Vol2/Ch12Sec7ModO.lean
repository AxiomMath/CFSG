module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModN
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_le' (K : Subgroup G) : oTwoUpper K ≤ K :=
  (Subgroup.closure_le K).2 fun _ hx => hx.1

theorem autOn_oTwoUpper {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    autOn (oTwoUpper K) V = oTwoUpper (autOn K V) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨x, hx, hxO, rfl⟩ := mem_autOn'.1 ha
    have key : ∀ x (hxO : x ∈ oTwoUpper K) (hx : x ∈ Subgroup.normalizer (V : Set G)),
        conjAct V ⟨x, hx⟩ ∈ oTwoUpper (autOn K V) := by
      intro x hxO
      induction hxO using Subgroup.closure_induction with
      | mem x hxS =>
        intro hx
        refine Subgroup.subset_closure ⟨conjAct_mem_autOn hxS.1 hx, ?_⟩
        have hd := orderOf_map_dvd (conjAct V) ⟨x, hx⟩
        rw [Subgroup.orderOf_mk] at hd
        exact Odd.of_dvd_nat hxS.2 hd
      | one =>
        intro hx
        have e : conjAct V ⟨1, hx⟩ = 1 := map_one (conjAct V)
        rw [e]
        exact Subgroup.one_mem _
      | mul x y hx' hy' ihx ihy =>
        intro hxy
        have hxN := hK (oTwoUpper_le' K hx')
        have hyN := hK (oTwoUpper_le' K hy')
        rw [conjAct_mul' hxN hyN]
        exact Subgroup.mul_mem _ (ihx hxN) (ihy hyN)
      | inv x hx' ihx =>
        intro hxi
        have hxN := hK (oTwoUpper_le' K hx')
        have e : conjAct V ⟨x⁻¹, hxi⟩ = (conjAct V ⟨x, hxN⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [e]
        exact Subgroup.inv_mem _ (ihx hxN)
    exact key x hxO hx
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro a ⟨ha, hodd⟩
    obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn'.1 ha
    have hn0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
    obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    set y := x ^ (2 ^ j) with hy
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hx _
    have hyodd : Odd (orderOf y) := by
      have : y ^ m = 1 := by
        rw [hy, ← pow_mul, ← hn, pow_orderOf_eq_one]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one this)
    have hyO : y ∈ oTwoUpper K := Subgroup.subset_closure ⟨K.pow_mem hxK _, hyodd⟩
    have hcop : (2 ^ j).Coprime (orderOf (conjAct V ⟨x, hx⟩)) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
    obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
    have hconj : conjAct V ⟨y ^ e, Subgroup.pow_mem _ hyN e⟩ =
        (conjAct V ⟨x, hx⟩ ^ (2 ^ j)) ^ e := by
      rw [← map_pow, ← map_pow]
      rfl
    rw [← he, ← hconj]
    exact conjAct_mem_autOn ((oTwoUpper K).pow_mem hyO e) _

omit [Finite G] in
theorem oTwoUpper_idem (K : Subgroup G) : oTwoUpper (oTwoUpper K) = oTwoUpper K := by
  apply le_antisymm (oTwoUpper_le' _)
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxK, hodd⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hxK, hodd⟩, hodd⟩

omit [Finite G] in
theorem oTwoUpper_mono {K K' : Subgroup G} (h : K ≤ K') : oTwoUpper K ≤ oTwoUpper K' :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem Mc.app_sV {A : Mc} (hA : A.Valid) {c : ℕ} (hc : c < 4) {v : ℕ} (hv : v < 64) :
    A.app (sV c v) = sV c (A.app v) := by
  apply decV_injective (Mc.app_lt A hA) (sV_lt_64 _ hc _ (Mc.app_lt A hA))
  rw [← Mc.toMat_mulVec A hA, decV_sV hc hv, decV_sV hc (Mc.app_lt A hA), Matrix.mulVec_smul,
    Mc.toMat_mulVec A hA]

theorem zs6_app : ∀ z ∈ zs6, ∃ c < 4, ∀ v < 64, z.app v = sV c v := by decide

theorem zs6_comm : ∀ z ∈ zs6, ∀ B ∈ gm6, z.comp B = B.comp z := by
  intro z hz B hB
  obtain ⟨c, hc, hzc⟩ := zs6_app z hz
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  have hall := cert_gmList_mem
  have hAv := (hall A hA).1
  apply B6.ext_app
  intro v hv
  rw [B6.app_comp, B6.app_comp, hzc _ (B6.app_lt (toB6_valid hAv) v), hzc v hv,
    toB6_app A hv, toB6_app A (sV_lt_64 _ hc _ hv), Mc.app_sV hAv hc hv]

theorem zsm_inGm : ∀ Z ∈ zsm, Z.Valid ∧ inGm Z = true := by decide

theorem zs6_sub_gm6 : ∀ z ∈ zs6, z ∈ gm6 := by
  intro z hz
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hz
  exact gm6_of_gmList (zsm_inGm Z hZ)

theorem zs6_pow3 : ∀ z ∈ zs6, z.pow 3 = B6.id := by decide

section Setting

variable {T L : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem mem_oTwoZIn (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {x : G} :
    x ∈ oTwoZIn L ↔ x ∈ L ∧ ∀ m ∈ L, x⁻¹ * m⁻¹ * x * m ∈ Subgroup.centralizer (V : Set G) := by
  have hP : ∀ y : ↥L, y ∈ CFSG.pCore 2 ↥L ↔ (y : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro y
    have e := inf_centralizer_eq_of_1222 h1222 h
    constructor
    · intro hy
      have : (y : G) ∈ pCoreOf 2 L := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
      rw [← e] at this
      exact this.2
    · intro hy
      have : (y : G) ∈ pCoreOf 2 L := by
        rw [← e]
        exact ⟨y.2, hy⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 this
      rw [← Subtype.ext hzy]
      exact hz
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.2, fun m hm => ?_⟩
    have hc := Subgroup.mem_center_iff.1 hl (QuotientGroup.mk' _ ⟨m, hm⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc
    have := (hP _).1 hc
    simpa [mul_assoc] using this
  · rintro ⟨hxL, hx⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxL⟩, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply (hP _).2
    simpa [mul_assoc] using hx m hm

omit [Finite G] [IsMulCommutative ↥V] in
theorem commute_conjAct_iff {x m : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x, hx⟩ * conjAct V ⟨m, hm⟩ = conjAct V ⟨m, hm⟩ * conjAct V ⟨x, hx⟩ ↔
      x⁻¹ * m⁻¹ * x * m ∈ Subgroup.centralizer (V : Set G) := by
  have hN : x⁻¹ * m⁻¹ * x * m ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
      (Subgroup.inv_mem _ hm)) hx) hm
  rw [← conjAct_eq_one' hN]
  have e : conjAct V ⟨x⁻¹ * m⁻¹ * x * m, hN⟩ =
      (conjAct V ⟨x, hx⟩)⁻¹ * (conjAct V ⟨m, hm⟩)⁻¹ * conjAct V ⟨x, hx⟩ * conjAct V ⟨m, hm⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e]
  generalize conjAct V ⟨x, hx⟩ = p
  generalize conjAct V ⟨m, hm⟩ = q
  constructor
  · intro hc
    rw [mul_assoc (p⁻¹ * q⁻¹), hc]
    group
  · intro hc
    calc p * q = q * p * (p⁻¹ * q⁻¹ * p * q) := by group
      _ = q * p := by rw [hc, mul_one]

omit [IsMulCommutative ↥V] in
theorem mem_autOn_oTwoZIn (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {a : MulAut ↥V} :
    a ∈ autOn (oTwoZIn L) V ↔ a ∈ autOn L V ∧ ∀ b ∈ autOn L V, a * b = b * a := by
  have hLV := L_le_normalizer h
  constructor
  · intro ha
    obtain ⟨x, hx, hxZ, rfl⟩ := mem_autOn'.1 ha
    obtain ⟨hxL, hxc⟩ := (mem_oTwoZIn h1222 h).1 hxZ
    refine ⟨conjAct_mem_autOn hxL hx, fun b hb => ?_⟩
    obtain ⟨m, hm, hmL, rfl⟩ := mem_autOn'.1 hb
    exact (commute_conjAct_iff hx hm).2 (hxc m hmL)
  · rintro ⟨ha, hc⟩
    obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ha
    refine conjAct_mem_autOn ((mem_oTwoZIn h1222 h).2 ⟨hxL, fun m hm => ?_⟩) hx
    exact (commute_conjAct_iff hx (hLV hm)).1 (hc _ (conjAct_mem_autOn hm (hLV hm)))

theorem mem_autOn_XOf
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (a : MulAut ↥V) : a ∈ autOn (XOf L) V ↔ C.cB a ∈ zs6 := by
  have hZ : ∀ b, b ∈ autOn (oTwoZIn L) V ↔ C.cB b ∈ zs6 := by
    intro b
    rw [mem_autOn_oTwoZIn h1222 h]
    constructor
    · rintro ⟨hb, hc⟩
      refine cert_center _ ((hC.1 b).1 hb) fun D hD => ?_
      obtain ⟨d, rfl⟩ := hC.2 D hD
      rw [← C.cB_mul, ← C.cB_mul, hc d ((hC.1 d).2 hD)]
    · intro hb
      refine ⟨(hC.1 b).2 (zs6_sub_gm6 _ hb), fun d hd => ?_⟩
      apply C.cB_injective
      rw [C.cB_mul, C.cB_mul, zs6_comm _ hb _ ((hC.1 d).1 hd)]
  rw [XOf, autOn_oTwoUpper (K := oTwoZIn L)
    (fun x hx => L_le_normalizer h ((mem_oTwoZIn h1222 h).1 hx).1)]
  constructor
  · intro ha
    have : a ∈ autOn (oTwoZIn L) V := oTwoUpper_le' _ ha
    exact (hZ a).1 this
  · intro ha
    refine Subgroup.subset_closure ⟨(hZ a).2 ha, ?_⟩
    have h3 : a ^ 3 = 1 := (C.pow_eq_one_iff a 3).2 (zs6_pow3 _ ha)
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem l1m_facts : ∀ A ∈ l1m, A.Valid ∧ inGm A = true ∧ fixP1 A.toB6 = true := by decide

theorem id_mem_l1 : B6.id ∈ l1 := by decide

theorem l1_closed : ∀ x ∈ l1, ∀ y ∈ l1, x.comp y ∈ l1 := by decide

theorem l1_nodup : l1.Nodup := by decide

theorem l1_gen : ∀ g ∈ l1, ∃ a ∈ l1, ∃ b ∈ l1, a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧
    g = a.comp b := by decide

theorem l2m_facts : ∀ A ∈ l2m, A.Valid ∧ inGm A = true ∧ onQuot A.toB6 = true := by decide

theorem id_mem_l2 : B6.id ∈ l2 := by decide

theorem l2_closed : ∀ x ∈ l2, ∀ y ∈ l2, x.comp y ∈ l2 := by decide

theorem l2_nodup : l2.Nodup := by decide

theorem l2_gen : ∀ g ∈ l2, ∃ a ∈ l2, ∃ b ∈ l2, a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧
    g = a.comp b := by decide

theorem fixP1_iff (B : B6) : fixP1 B = true ↔ ∀ c ∈ p1c, B.app c = c := by
  simp [fixP1, List.all_eq_true]

theorem onQuot_iff (B : B6) :
    onQuot B = true ↔ presv l2c B = true ∧ ∀ c < 64, c ^^^ B.app c ∈ l2c := by
  simp [onQuot, List.all_eq_true]

theorem odd_dvd_fifteen {n : ℕ} (hn : Odd n) (h : n ∣ 60) : n ∣ 15 := by
  have hc : Nat.Coprime n 4 := by
    have : Nat.Coprime n 2 := Nat.coprime_two_right.2 hn
    simpa using this.pow_right 2
  exact hc.dvd_of_dvd_mul_left (by simpa using h)

theorem pow15_of_odd {W : Type} [CommGroup W] (C : Coding W)
    {a : MulAut W} (ha : C.cB a ∈ gm6) (hodd : Odd (orderOf a)) : (C.cB a).pow 15 = B6.id := by
  rw [← C.pow_eq_one_iff]
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (gm6_pow60 _ ha)
  exact orderOf_dvd_iff_pow_eq_one.1 (odd_dvd_fifteen hodd (orderOf_dvd_of_pow_eq_one h60))

theorem odd_of_pow3 {W : Type} [CommGroup W] (C : Coding W) {a : MulAut W}
    (h : (C.cB a).pow 3 = B6.id) : Odd (orderOf a) := by
  have h3 : a ^ 3 = 1 := (C.pow_eq_one_iff a 3).2 h
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem mem_autOn_CV1 (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : Std C T L) (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.centralizer (V1 T L V : Set G)) V ↔
      C.cB a ∈ gm6 ∧ fixP1 (C.cB a) = true := by
  have hV1 := V1_eq h hC
  rw [fixP1_iff]
  constructor
  · intro ha
    obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn'.1 ha
    refine ⟨(hC.1.1 _).1 (conjAct_mem_autOn hxK.1 hx), fun c hc => ?_⟩
    have hv : (C.dc c : G) ∈ V1 T L V := by
      rw [hV1, C.mem_subG, C.cd_dc c (p1c_lt c hc)]
      exact hc
    have hcomm := Subgroup.mem_centralizer_iff.1 hxK.2 _ hv
    have := (commute_iff_code C hx (C.dc c)).1 hcomm.symm
    rwa [C.cd_dc c (p1c_lt c hc)] at this
  · rintro ⟨hgm, hfix⟩
    obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hgm)
    refine conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨hxL, Subgroup.mem_centralizer_iff.2 ?_⟩) hx
    intro w hw
    have hwV : w ∈ V := (show V1 T L V ≤ V from inf_le_left) hw
    rw [hV1] at hw
    have hcw := (C.mem_subG ⟨w, hwV⟩).1 hw
    exact ((commute_iff_code C hx ⟨w, hwV⟩).2 (hfix _ hcw)).symm

theorem mem_autOn_CV2
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) (a : MulAut ↥V) :
    a ∈ autOn (centralizerMod (V2 T L V) L V) V ↔ C.cB a ∈ gm6 ∧ onQuot (C.cB a) = true := by
  have hV2 := V2_eq h hC
  have hLV := L_le_normalizer h
  rw [onQuot_iff, presv_iff]
  have hcomm : ∀ {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (u : ↥V),
      ∃ hm : x * u * x⁻¹ * u⁻¹ ∈ V, C.cd ⟨_, hm⟩ =
        C.cd u ^^^ (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd u) := by
    intro x hx u
    have hm : x * u * x⁻¹ * u⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.1 hx u).1 u.2) (V.inv_mem u.2)
    refine ⟨hm, ?_⟩
    have e : (⟨x * u * x⁻¹ * u⁻¹, hm⟩ : ↥V) = conjAct V ⟨x, hx⟩ u * u⁻¹ := by
      apply Subtype.ext
      show x * u * x⁻¹ * u⁻¹ = ((conjAct V ⟨x, hx⟩ u * u⁻¹ : ↥V) : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_val]
    rw [e, C.cd_mul, C.cd_inv, C.cd_apply, Nat.xor_comm]
  constructor
  · intro ha
    obtain ⟨x, hx, ⟨hxL, hxN, hxc⟩, rfl⟩ := mem_autOn'.1 ha
    refine ⟨(hC.1.1 _).1 (conjAct_mem_autOn hxL hx), fun c hc => ?_, fun c hc => ?_⟩
    · have hv : (C.dc c : G) ∈ V2 T L V := by
        rw [hV2, C.mem_subG, C.cd_dc c (l2c_lt c hc)]
        exact hc
      have hv' := (Subgroup.mem_normalizer_iff.1 hxN _).1 hv
      rw [hV2] at hv'
      have := (C.mem_subG ⟨_, (Subgroup.mem_normalizer_iff.1 hx _).1 (C.dc c).2⟩).1 hv'
      rwa [cd_conj, C.cd_dc c (l2c_lt c hc)] at this
    · obtain ⟨hm, e⟩ := hcomm hx (C.dc c)
      have hv := hxc _ (C.dc c).2
      rw [hV2] at hv
      have := (C.mem_subG ⟨_, hm⟩).1 hv
      rwa [e, C.cd_dc c hc] at this
  · rintro ⟨hgm, hpres, hq⟩
    obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hgm)
    refine conjAct_mem_autOn (show x ∈ centralizerMod (V2 T L V) L V from
      ⟨hxL, ?_, fun u hu => ?_⟩) hx
    · rw [hV2]
      apply normalizer_of_maps
      intro w hw
      obtain ⟨hwV, hwl⟩ := hw
      have hm := (Subgroup.mem_normalizer_iff.1 hx w).1 hwV
      have e : C.cd ⟨x * w * x⁻¹, hm⟩ = (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd ⟨w, hwV⟩) :=
        cd_conj C hx ⟨w, hwV⟩
      exact ⟨hm, by rw [e]; exact hpres _ hwl⟩
    · obtain ⟨hm, e⟩ := hcomm hx ⟨u, hu⟩
      rw [hV2]
      refine ⟨hm, ?_⟩
      have e' : C.cd ⟨x * u * x⁻¹ * u⁻¹, hm⟩ =
          C.cd ⟨u, hu⟩ ^^^ (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd ⟨u, hu⟩) := e
      rw [e']
      exact hq _ (C.cd_lt _)

theorem mem_autOn_L1
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) (a : MulAut ↥V) :
    a ∈ autOn (L1 T L V) V ↔ C.cB a ∈ l1 := by
  rw [L1, autOn_oTwoUpper (inf_le_left.trans (L_le_normalizer h))]
  constructor
  · intro ha
    have hle : oTwoUpper (autOn (L ⊓ Subgroup.centralizer (V1 T L V : Set G)) V) ≤
        C.subOf l1 id_mem_l1 l1_closed := by
      rw [oTwoUpper, Subgroup.closure_le]
      rintro b ⟨hb, hodd⟩
      obtain ⟨hgm, hfix⟩ := (mem_autOn_CV1 h hC b).1 hb
      exact cert_odd1 _ hgm hfix (pow15_of_odd C hgm hodd)
    exact hle ha
  · intro ha
    obtain ⟨u, hu, v, hv, hu3, hv3, he⟩ := l1_gen _ ha
    obtain ⟨b, rfl⟩ := hC.1.2 _ (List.mem_map.1 hu |>.elim fun A ⟨hA, hAe⟩ =>
      hAe ▸ gm6_of_gmList ⟨(l1m_facts A hA).1, (l1m_facts A hA).2.1⟩)
    obtain ⟨d, rfl⟩ := hC.1.2 _ (List.mem_map.1 hv |>.elim fun A ⟨hA, hAe⟩ =>
      hAe ▸ gm6_of_gmList ⟨(l1m_facts A hA).1, (l1m_facts A hA).2.1⟩)
    have hmem : ∀ e : MulAut ↥V, C.cB e ∈ l1 →
        e ∈ autOn (L ⊓ Subgroup.centralizer (V1 T L V : Set G)) V := by
      intro e he'
      obtain ⟨A, hA, hAe⟩ := List.mem_map.1 he'
      refine (mem_autOn_CV1 h hC e).2 ⟨?_, ?_⟩
      · rw [← hAe]
        exact gm6_of_gmList ⟨(l1m_facts A hA).1, (l1m_facts A hA).2.1⟩
      · rw [← hAe]
        exact (l1m_facts A hA).2.2
    have hab : a = b * d := C.cB_injective (by rw [C.cB_mul, ← he])
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hmem b hu, odd_of_pow3 C hu3⟩)
      (Subgroup.subset_closure ⟨hmem d hv, odd_of_pow3 C hv3⟩)

theorem mem_autOn_L2
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) (a : MulAut ↥V) :
    a ∈ autOn (L2 T L V) V ↔ C.cB a ∈ l2 := by
  have hK : centralizerMod (V2 T L V) L V ≤ Subgroup.normalizer (V : Set G) :=
    fun x hx => L_le_normalizer h hx.1
  rw [L2, autOn_oTwoUpper hK]
  constructor
  · intro ha
    have hle : oTwoUpper (autOn (centralizerMod (V2 T L V) L V) V) ≤
        C.subOf l2 id_mem_l2 l2_closed := by
      rw [oTwoUpper, Subgroup.closure_le]
      rintro b ⟨hb, hodd⟩
      obtain ⟨hgm, hq⟩ := (mem_autOn_CV2 h hC b).1 hb
      exact cert_odd2 _ hgm hq (pow15_of_odd C hgm hodd)
    exact hle ha
  · intro ha
    obtain ⟨u, hu, v, hv, hu3, hv3, he⟩ := l2_gen _ ha
    obtain ⟨b, rfl⟩ := hC.1.2 _ (List.mem_map.1 hu |>.elim fun A ⟨hA, hAe⟩ =>
      hAe ▸ gm6_of_gmList ⟨(l2m_facts A hA).1, (l2m_facts A hA).2.1⟩)
    obtain ⟨d, rfl⟩ := hC.1.2 _ (List.mem_map.1 hv |>.elim fun A ⟨hA, hAe⟩ =>
      hAe ▸ gm6_of_gmList ⟨(l2m_facts A hA).1, (l2m_facts A hA).2.1⟩)
    have hmem : ∀ e : MulAut ↥V, C.cB e ∈ l2 →
        e ∈ autOn (centralizerMod (V2 T L V) L V) V := by
      intro e he'
      obtain ⟨A, hA, hAe⟩ := List.mem_map.1 he'
      refine (mem_autOn_CV2 h hC e).2 ⟨?_, ?_⟩
      · rw [← hAe]
        exact gm6_of_gmList ⟨(l2m_facts A hA).1, (l2m_facts A hA).2.1⟩
      · rw [← hAe]
        exact (l2m_facts A hA).2.2
    have hab : a = b * d := C.cB_injective (by rw [C.cB_mul, ← he])
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hmem b hu, odd_of_pow3 C hu3⟩)
      (Subgroup.subset_closure ⟨hmem d hv, odd_of_pow3 C hv3⟩)

end Setting

end CFSG.Quasithin.H13.S127.Mod

end
