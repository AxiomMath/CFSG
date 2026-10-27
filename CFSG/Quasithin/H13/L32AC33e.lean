module

public import CFSG.Quasithin.H13.L32AC36g
public import CFSG.Quasithin.H13.L32AC47g
public import CFSG.Quasithin.H13.L32A770k
public import CFSG.Quasithin.H13.L32AC33b
public import CFSG.Quasithin.H13.L32AC33c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

@[expose] def szS1 (T H K : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  modO2Image H T ⊓ modO2Image H K

@[expose] def szB1 (T H K : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ modO2Image H K

structure CtxB (T L V H K : Subgroup G) (t₀ : G) : Prop where
  S : Setting147 G T L V H
  hK : K ∈ cComp H
  ht₀ : t₀ ∈ T
  ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G)
  two : ∀ h ∈ H, h ∈ Subgroup.normalizer (K : Set G) ∨ t₀⁻¹ * h ∈ Subgroup.normalizer (K : Set G)
  hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G)
  triv : ∀ r ∈ T, r ∈ Subgroup.normalizer (K : Set G) → r ∈ L32NSet14.trivSub V (fsuV1 T V)

theorem comm_mem_pCoreOf_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) {r : G} (hrT : r ∈ T)
    (hr : r ∈ L32NSet14.trivSub V (fsuV1 T V)) {y : G} (hy : y ∈ l1 T L V) :
    r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, -, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hyL : y ∈ L₁Of L (fsuV1 T V) := by rw [hl1]; exact hy
  have hkL : r * y * r⁻¹ * y⁻¹ ∈ L₁Of L (fsuV1 T V) :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (S14.T_Lp hrT) y).mp hyL) (inv_mem hyL)
  have hyX := S14.L1_le_X hyL
  have hkt : r * y * r⁻¹ * y⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have h1 := L32NSet14.conj_mem_trivSub hyX.1 hyX.2 (inv_mem hr)
    have e : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem hr h1
  have := mem_pCoreOf_of_triv S14 hxL hfpf hkL hkt
  rwa [hl1] at this

theorem mk_mem_T_of_coprime (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) {l : ↥H} (hl : (l : G) ∈ l1 T L V)
    (hcop : Nat.Coprime 3 (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) l ∈ modO2Image H T := by
  have h3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  have hPT : pCoreOf 2 (l1 T L V) ≤ T := fun z hz => ((l1_inf_T h1222 h1332 h1334 S).ge hz).2
  by_cases hO : (l : G) ∈ pCoreOf 2 (l1 T L V)
  · exact mem_modO2Image'.mpr ⟨l, hPT hO, rfl⟩
  exfalso
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (l ^ orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  generalize orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l) = m at hcop h1
  have hm : (l : G) ^ m ∈ pCoreOf 2 H := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hmL : (l : G) ^ m ∈ pCoreOf 2 (l1 T L V) :=
    pCoreOf_inf_le_of_le (Setting147.l1H' S) ⟨hm, pow_mem hl _⟩
  have : ((pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)
  have hu1 : (QuotientGroup.mk ⟨l, hl⟩ : ↥(l1 T L V) ⧸
      (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)) ≠ 1 := fun h =>
    hO (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
      (N := (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)) ⟨l, hl⟩).mp h))
  have hum : (QuotientGroup.mk ⟨l, hl⟩ : ↥(l1 T L V) ⧸
      (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hmL
  have hcard : Nat.card (↥(l1 T L V) ⧸ (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact h3
  have hou : orderOf (QuotientGroup.mk ⟨l, hl⟩ : ↥(l1 T L V) ⧸
      (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V)) = 3 := by
    have h1 := orderOf_dvd_natCard (QuotientGroup.mk ⟨l, hl⟩ : ↥(l1 T L V) ⧸
      (pCoreOf 2 (l1 T L V)).subgroupOf (l1 T L V))
    rw [hcard] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have h3m := orderOf_dvd_of_pow_eq_one hum
  rw [hou] at h3m
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3m

theorem commute_of_conj (hA37 : A37ForSQTK) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) {t : G} (htH : t ∈ H) (htN : t ∉ Subgroup.normalizer (K : Set G))
    {a c : ↥H ⧸ CFSG.pCore 2 ↥H} (ha : a ∈ modO2Image H K)
    (hc : c ∈ modO2Image H (K.map (MulAut.conj t : G →* G))) : a * c = c * a := by
  have h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H) :=
    hA37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
      S.hyp.fsu.nonabelian S.hz.1.2)
  have hK' : K.map (MulAut.conj t : G →* G) ∈ cComp H := by
    have := cComp_map_mulEquiv (MulAut.conj t) hK
    rwa [MulEquiv.toMonoidHom_eq_coe,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htH)] at this
  have hne : K ≠ K.map (MulAut.conj t : G →* G) := fun h =>
    htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm := commutator_le_pCoreOf_of_ne h37 hK hK' hne
  obtain ⟨k, hk, rfl⟩ := mem_modO2Image'.mp ha
  obtain ⟨k', hk', rfl⟩ := mem_modO2Image'.mp hc
  have h1 := hcomm (Subgroup.commutator_mem_commutator hk hk')
  rw [commutatorElement_def] at h1
  exact Setting147.mk_commute_of_mem k k' h1

theorem mem_normalizer_szB1 {K : Subgroup G} {g : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hgS : g ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (hgK : g ∈ Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    g ∈ Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  refine mem_normalizer_of_conj_mem_fin fun b hb => ⟨?_, ?_⟩
  · refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
    have h1 : g⁻¹ * s * g ∈ szS1 T H K := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgS) s).mp hs
      simpa using this
    have h2 := (Subgroup.mem_normalizer_iff.mp hb.1 _).mp h1
    have h3 := (Subgroup.mem_normalizer_iff.mp hgS _).mp h2
    have e : g * (b * (g⁻¹ * s * g) * b⁻¹) * g⁻¹ = g * b * g⁻¹ * s * (g * b * g⁻¹)⁻¹ := by group
    rwa [e] at h3
  · exact (Subgroup.mem_normalizer_iff.mp hgK b).mp hb.2

theorem mem_normalizer_map_conj {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {c g : Y}
    (h : c⁻¹ * g * c ∈ Subgroup.normalizer (A : Set Y)) :
    g ∈ Subgroup.normalizer ((A.map (MulAut.conj c : Y →* Y) : Subgroup Y) : Set Y) := by
  refine mem_normalizer_of_conj_mem_fin fun a ha => ?_
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  refine Subgroup.mem_map.mpr ⟨(c⁻¹ * g * c) * a' * (c⁻¹ * g * c)⁻¹,
    (Subgroup.mem_normalizer_iff.mp h a').mp ha', ?_⟩
  simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
  group

namespace CtxB

variable {K : Subgroup G} {t₀ : G} (C : CtxB T L V H K t₀)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem hTH : T ≤ H := Setting147.TH' C.S

theorem mk_T_mem_normalizer_szB1 {r : ↥H} (hrT : (r : G) ∈ T)
    (hrN : (r : G) ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) r ∈
      Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hK := mk_mem_normalizer C.hKH hrN
  have hT := mk_mem_normalizer C.hTH (Subgroup.le_normalizer hrT)
  exact mem_normalizer_szB1 (Subgroup.inf_normalizer_le_normalizer_inf ⟨hT, hK⟩) hK

theorem mk_l1_mem_normalizer_szS1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have hyH : y ∈ H := Setting147.l1H' C.S hy
  have hPT : pCoreOf 2 (l1 T L V) ≤ T := fun z hz =>
    ((l1_inf_T h1222 h1332 h1334 C.S).ge hz).2
  have hyK := mk_mem_normalizer (y := ⟨y, hyH⟩) C.hKH (C.hyN y hy hy3)
  have key : ∀ s ∈ szS1 T H K, s * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * s⁻¹ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ ∈ szS1 T H K := by
    intro s hs
    obtain ⟨r, hrT, rfl⟩ := mem_modO2Image'.mp hs.1
    have hrN : (r : G) ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_mk C.hK (Subgroup.le_normalizer hs.2)
    have hc := comm_mem_pCoreOf_l1 h1222 h1332 h1334 C.S hrT (C.triv _ hrT hrN) hy
    have hcH : (r : G) * y * (r : G)⁻¹ * y⁻¹ ∈ H :=
      mul_mem (mul_mem (mul_mem r.2 hyH) (inv_mem r.2)) (inv_mem hyH)
    have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) r *
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hcH⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    refine ⟨?_, ?_⟩
    · rw [e]
      exact mem_modO2Image'.mpr ⟨_, hPT hc, rfl⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp hyK _).mp (inv_mem hs.2)
      have e' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) r *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ =
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) r * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹) := by group
      rw [e']
      exact mul_mem hs.2 h1
  refine mem_normalizer_of_conj_mem_fin fun s hs => ?_
  have h1 := key s⁻¹ (inv_mem hs)
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * s *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹ =
        s * (s⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ * s⁻¹⁻¹ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩)⁻¹) := by group
  rw [e]
  exact mul_mem hs h1

theorem mk_l1_mem_normalizer_szB1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, Setting147.l1H' C.S hy⟩ ∈
      Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  mem_normalizer_szB1 (C.mk_l1_mem_normalizer_szS1 h1222 h1332 h1334 hy hy3)
    (mk_mem_normalizer (y := ⟨y, Setting147.l1H' C.S hy⟩) C.hKH (C.hyN y hy hy3))

end CtxB

end CFSG.Quasithin.H13.L32A.C
