module

public import CFSG.Quasithin.H13.L32AC32d
public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.Quasithin.EmptyFaithful.S151S4F
public import CFSG.Quasithin.EmptyFaithful.S146zMListCl
public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.H13.L32AC32b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure CtxS (T L V H K : Subgroup G) (t₀ : G) : Prop where
  S : Setting147 G T L V H
  hK : K ∈ cComp H
  ht₀ : t₀ ∈ T
  ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G)
  two : ∀ h ∈ H, h ∈ Subgroup.normalizer (K : Set G) ∨ t₀⁻¹ * h ∈ Subgroup.normalizer (K : Set G)
  hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G)

structure CtxL2 (T L V H K : Subgroup G) (t₀ : G) (n : ℕ) : Prop extends CtxS T L V H K t₀ where
  hn : 2 ≤ n
  hP : IsPSL 2 2 n (cStar K)

namespace CtxS

variable {K : Subgroup G} {t₀ : G} (C : CtxS T L V H K t₀)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem hTH : T ≤ H := Setting147.TH' C.S

theorem ht₀H : t₀ ∈ H := C.hTH C.ht₀

theorem hKtH : K.map (MulAut.conj t₀ : G →* G) ≤ H := by
  rintro _ ⟨k, hk, rfl⟩
  exact mul_mem (mul_mem C.ht₀H (C.hKH hk)) (inv_mem C.ht₀H)

theorem sq_mem : t₀ * t₀ ∈ Subgroup.normalizer (K : Set G) := by
  rcases C.two _ (mul_mem C.ht₀H C.ht₀H) with h | h
  · exact h
  · exact absurd (by simpa using h) C.ht₀N

theorem mem_normalizer_kt {h : G} (hH : h ∈ H) (hN : h ∈ Subgroup.normalizer (K : Set G)) :
    h ∈ Subgroup.normalizer ((K.map (MulAut.conj t₀ : G →* G) : Subgroup G) : Set G) := by
  refine mem_normalizer_map_conj ?_
  rcases C.two _ (mul_mem hH C.ht₀H) with h1 | h1
  · exact absurd (by simpa using mul_mem (inv_mem hN) h1) C.ht₀N
  · simpa [mul_assoc] using h1

theorem kb'_eq : (modO2Image H K).map
    (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩) :
      _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) = modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :=
  (modO2Image_map_conj C.hKH ⟨t₀, C.ht₀H⟩).symm

theorem commute_kb (hA37 : A37ForSQTK) {a b : ↥H ⧸ CFSG.pCore 2 ↥H} (ha : a ∈ modO2Image H K)
    (hb : b ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G))) : a * b = b * a :=
  commute_of_conj hA37 C.S C.hK C.ht₀H C.ht₀N ha hb

theorem conj_l1 (h1332 : Stmt13_3_2) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    t₀⁻¹ * y * t₀ ∈ l1 T L V ∧ (t₀⁻¹ * y * t₀) ^ 3 = 1 := by
  have hTl1 := Setting147.T_le_N_l1 C.S h1332
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hTl1 (inv_mem C.ht₀)) y).mp hy
    simpa using this
  · rw [show (t₀⁻¹ * y * t₀) ^ 3 = t₀⁻¹ * y ^ 3 * t₀ by rw [pow_three, pow_three]; group, hy3]
    group

theorem mk_mem_normalizers {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        Subgroup.normalizer (modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :
          Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  ⟨mk_mem_normalizer (y := ⟨y, _⟩) C.hKH (C.hyN y hy hy3),
    mk_mem_normalizer (y := ⟨y, _⟩) C.hKtH
      (C.mem_normalizer_kt (Setting147.l1H' C.S hy) (C.hyN y hy hy3))⟩

theorem pCoreOf_le_normalizer : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := by
  intro q hq
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  refine mem_normalizer_of_mk (h := ⟨q, hqH⟩) C.hK ?_
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨q, hqH⟩ : ↥H) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf]
    exact hq
  rw [h1]
  exact one_mem _

theorem pCoreOf_le_normalizer_conjClosure :
    pCoreOf 2 H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  intro q hq
  refine mem_normalizer_of_conj_mem_fin fun a ha => ?_
  have hle : conjClosure K T ≤ (conjClosure K T).comap (MulAut.conj q : G →* G) := by
    refine conjClosure_le fun s hs k hk => ?_
    rw [Subgroup.mem_comap]
    have hsH := C.hTH hs
    have hq' : s⁻¹ * q * s ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hsH)) q).mp hq
      simpa using this
    have hk' := (Subgroup.mem_normalizer_iff.mp (C.pCoreOf_le_normalizer hq') k).mp hk
    have h1 := mem_conjClosure hs hk'
    have e : s * (s⁻¹ * q * s * k * (s⁻¹ * q * s)⁻¹) * s⁻¹ = q * (s * k * s⁻¹) * q⁻¹ := by group
    rw [e] at h1
    simpa using h1
  have := hle ha
  rw [Subgroup.mem_comap] at this
  simpa using this

theorem mk_ne_one (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {x : G}
    (hx : x ∈ l1 T L V) (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, Setting147.l1H' C.S hx⟩ ≠ 1 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hxO : x ∉ pCoreOf 2 (l1 T L V) := by
    intro h
    rw [← hl1] at h
    have hxt := S14.pCoreOf_L1_le h
    have hle : V ≤ fsuV1 T V := fun v hv =>
      hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  intro h
  apply hxO
  refine pCoreOf_inf_le_of_le (Setting147.l1H' C.S) ⟨?_, hx⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
    Subgroup.mem_subgroupOf] at h
  exact h

end CtxS

namespace CtxL2

variable {K : Subgroup G} {t₀ : G} {n : ℕ} (C : CtxL2 T L V H K t₀ n)
include C

theorem nonempty_equiv : Nonempty (cStar K ≃* ↥(modO2Image H K)) := by
  obtain ⟨φ⟩ := modO2_mulEquiv C.hK
  exact ⟨(cStarEquiv K).trans φ⟩

theorem isSimpleGroup_kb : IsSimpleGroup ↥(modO2Image H K) := by
  obtain ⟨e⟩ := C.nonempty_equiv
  have := SBc6.isSimpleGroup_of_psl (by have := C.hn; omega) C.hP
  exact e.symm.isSimpleGroup

theorem center_kb : Subgroup.center ↥(modO2Image H K) = ⊥ := by
  obtain ⟨e⟩ := C.nonempty_equiv
  have hZ := S151S4.center_eq_bot_of_isPSL2 C.hP
  rw [eq_bot_iff]
  intro z hz
  have h1 : e.symm z ∈ Subgroup.center (cStar K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hz (e g)]
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg e h1

theorem three_dvd_kb : 3 ∣ Nat.card ↥(modO2Image H K) := by
  obtain ⟨e⟩ := C.nonempty_equiv
  rw [← Nat.card_congr e.toEquiv]
  exact three_dvd_card_psl_model C.hP

noncomputable def equivKt : ↥(modO2Image H K) ≃*
    ↥(modO2Image H (K.map (MulAut.conj t₀ : G →* G))) :=
  ((MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩)).subgroupMap _).trans
    (MulEquiv.subgroupCongr C.kb'_eq)

theorem center_kt : Subgroup.center ↥(modO2Image H (K.map (MulAut.conj t₀ : G →* G))) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : C.equivKt.symm z ∈ Subgroup.center ↥(modO2Image H K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply C.equivKt.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
      Subgroup.mem_center_iff.mp hz (C.equivKt g)]
  rw [C.center_kb, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg C.equivKt h1

theorem three_dvd_kt : 3 ∣ Nat.card ↥(modO2Image H (K.map (MulAut.conj t₀ : G →* G))) := by
  rw [← Nat.card_congr C.equivKt.toEquiv]
  exact C.three_dvd_kb

theorem eq_one_of_mem_kb_kt (hA37 : A37ForSQTK) {z : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hz : z ∈ modO2Image H K) (hz' : z ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G))) :
    z = 1 :=
  eq_one_of_mem_of_commute C.center_kb hz fun _ hm => (C.commute_kb hA37 hm hz').symm

theorem decomp (hA37 : A37ForSQTK) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    ∃ k₁ ∈ modO2Image H K, ∃ k₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ = k₁ * k₂ ∧
      k₁ ^ 3 = 1 ∧ k₂ ^ 3 = 1 ∧
      (∀ m ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ *
        m * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ =
          k₁ * m * k₁⁻¹) ∧
      (∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ * m *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩)⁻¹ =
            k₂ * m * k₂⁻¹) := by
  have hm := pRank_three_star_le_two C.S
  obtain ⟨hyK, hyK'⟩ := C.mk_mem_normalizers hy hy3
  have hyb3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩) ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hy3)
  have hc : ∀ a ∈ modO2Image H K, ∀ b ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
      a * b = b * a := fun a ha b hb => C.commute_kb hA37 ha hb
  have hc' : ∀ a ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)), ∀ b ∈ modO2Image H K,
      a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  obtain ⟨k₁, hk₁K, hk₁⟩ := inner_of_pRank hm hc C.center_kb C.center_kt C.three_dvd_kb
    C.three_dvd_kt hyK hyK' hyb3
  obtain ⟨k₂, hk₂K, hk₂⟩ := inner_of_pRank hm hc' C.center_kt C.center_kb C.three_dvd_kt
    C.three_dvd_kb hyK' hyK hyb3
  exact ⟨k₁, hk₁K, k₂, hk₂K, eq_mul_of_inner hm hc C.center_kb C.center_kt C.three_dvd_kb
    C.three_dvd_kt hyb3 hk₁K hk₂K hk₁ hk₂, pow_three_of_inner C.center_kb hyb3 hk₁K hk₁,
    pow_three_of_inner C.center_kt hyb3 hk₂K hk₂, hk₁, hk₂⟩

theorem l1_le (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : l1 T L V ≤ conjClosure K T := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 C.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 C.S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure C.ht₀ hk
  have hle : l1 T L V ≤ conjClosure K T ⊔ pCoreOf 2 H := by
    rw [← hl1]
    refine l1_le_of_cube S14 fun y hyL hy3 => ?_
    have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
    obtain ⟨k₁, hk₁K, k₂, hk₂K, he, -⟩ := C.decomp hA37 hy hy3
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
        modO2Image H (conjClosure K T) := by
      have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image H A ≤ modO2Image H B :=
        fun h => Subgroup.map_mono fun _ hz => h hz
      rw [he]
      exact mul_mem (hmono (le_conjClosure K T) hk₁K) (hmono hKt hk₂K)
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmem
    have hq : (a : G)⁻¹ * y ∈ pCoreOf 2 H := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hae
      simpa using hae
    have e : y = (a : G) * ((a : G)⁻¹ * y) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq)
  have h2 := C58.oTwoUpper_le_of_le_sup hle (pCoreOf_isPGroup 2 H)
    C.pCoreOf_le_normalizer_conjClosure
  rwa [A4.oTwoUpper_oTwoUpper] at h2

theorem k_ne_one (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {x : G} (hx : x ∈ l1 T L V) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    {k₁ k₂ : ↥H ⧸ CFSG.pCore 2 ↥H} (hk₁K : k₁ ∈ modO2Image H K)
    (hk₂K : k₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)))
    (he : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, Setting147.l1H' C.S hx⟩ = k₁ * k₂) :
    k₁ ≠ 1 ∧ k₂ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxH : x ∈ H := Setting147.l1H' C.S hx
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀, C.ht₀H⟩ with htb
  set xb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ with hxb
  have hxb1 : xb ≠ 1 := C.mk_ne_one h1222 h1332 h1334 hx hfpf
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hx3)
  obtain ⟨hxK, hxK'⟩ := C.mk_mem_normalizers hx hx3
  have hLN : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L C.S.hyp.hyp.h13 L C.S.hyp.hyp.h13.faithful).2.1.1
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hxbL : xb ∈ modO2Image H L := mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hl1L hx, rfl⟩
  have hzH : t₀ * x * t₀⁻¹ ∈ H := mul_mem (mul_mem C.ht₀H hxH) (inv_mem C.ht₀H)
  have hze : tb * xb * tb⁻¹ = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀ * x * t₀⁻¹, hzH⟩ := by
    rw [htb, hxb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hzL : tb * xb * tb⁻¹ ∈ modO2Image H L := by
    rw [hze]
    exact mem_modO2Image'.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp (hLN C.ht₀) x).mp (hl1L hx),
      rfl⟩
  have hz3 : (tb * xb * tb⁻¹) ^ 3 = 1 := by
    rw [show tb * xb * tb⁻¹ = MulAut.conj tb xb from rfl, ← map_pow, hxb3, map_one]
  have hz1 : tb * xb * tb⁻¹ ≠ 1 := fun h => hxb1 (by
    have := congrArg (fun z => tb⁻¹ * z * tb) h
    simpa [mul_assoc] using this)
  have h9 : ¬ 9 ∣ Nat.card ↥(modO2Image H L) := fun h =>
    not_nine_dvd_card_L h1222 h1332 h1334 C.S (h.trans card_modO2Image_dvd_card)
  have htt : tb * tb ∈ Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have := mk_mem_normalizer (y := ⟨t₀, C.ht₀H⟩ * ⟨t₀, C.ht₀H⟩) C.hKH C.sq_mem
    rwa [map_mul] at this
  refine ⟨fun hk₁1 => ?_, fun hk₂1 => ?_⟩
  ·
    rw [hk₁1, one_mul] at he
    have hxKb' : xb ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := he ▸ hk₂K
    have hxnK : xb ∉ modO2Image H K := fun h => hxb1 (C.eq_one_of_mem_kb_kt hA37 h hxKb')
    have hzK : tb * xb * tb⁻¹ ∈ modO2Image H K := by
      rw [← C.kb'_eq] at hxKb'
      obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hxKb'
      have e : tb * xb * tb⁻¹ = (tb * tb) * m * (tb * tb)⁻¹ := by
        rw [← hme, htb]
        simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp htt m).mp hm
    exact h9 (nine_dvd_card hxbL hxK hxb3 hxnK hzL hzK hz3 hz1)
  ·
    rw [hk₂1, mul_one] at he
    have hxKb : xb ∈ modO2Image H K := he ▸ hk₁K
    have hxnK' : xb ∉ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := fun h =>
      hxb1 (C.eq_one_of_mem_kb_kt hA37 hxKb h)
    have hzK' : tb * xb * tb⁻¹ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
      rw [← C.kb'_eq]
      exact Subgroup.mem_map.mpr ⟨xb, hxKb, by
        rw [htb]
        simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]⟩
    exact h9 (nine_dvd_card hxbL hxK' hxb3 hxnK' hzL hzK' hz3 hz1)

end CtxL2

end CFSG.Quasithin.H13.L32A.C
