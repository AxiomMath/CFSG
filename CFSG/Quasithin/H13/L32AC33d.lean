module

public import CFSG.Quasithin.H13.L32AC33c
public import CFSG.Quasithin.H13.L32A708a
public import CFSG.Quasithin.H13.L32A770k
public import CFSG.Quasithin.H13.L32AC33b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem comm_of_conj_eq {Y : Type} [Group Y] {a b : Y} (h : a * b * a⁻¹ = b) : b * a = a * b :=
  calc b * a = a * b * a⁻¹ * a := by rw [h]
    _ = a * b := by group

theorem comm_of_cube (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hKH : K ≤ H)
    (hc : ∀ y ∈ l1 T L V, y ^ 3 = 1 → ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∀ y ∈ l1 T L V, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hC : L₁Of L (fsuV1 T V) ≤
      ((Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype := by
    refine l1_le_of_cube S14 fun y hyL hy3 => ?_
    have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
    refine Subgroup.mem_map.mpr ⟨⟨y, hl1H hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image'.mp hn
    exact (Setting147.mk_commute_of_mem ⟨y, hl1H hy⟩ k (hc y hy hy3 k hk)).symm
  intro y hy k hk
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp (hC (by rw [hl1]; exact hy))
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hy'
  exact mem_O2H_of_commute y' ⟨k, hKH hk⟩ (hy' _ (mem_modO2Image'.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩))

theorem comm_of_inv (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    {e : ℕ} (hSz : IsSz e (cStar K)) {r : G} (hrT : r ∈ T)
    (hrN : r ∈ Subgroup.normalizer (K : Set G)) (hrn : r ∉ L32NSet14.trivSub V (fsuV1 T V))
    {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    {k : G} (hk : k ∈ K) : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨x, hxL, -, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hyH : y ∈ H := Setting147.l1H' S hy
  have hrH : r ∈ H := Setting147.TH' S hrT
  have hyL : y ∈ L₁Of L (fsuV1 T V) := by rw [hl1]; exact hy
  obtain ⟨φ⟩ := modO2_mulEquiv hK
  have hKsz : IsSz e ↥(modO2Image H K) := isSz_congr ((cStarEquiv K).trans φ) hSz
  have ho := inv_mem_pCoreOf S14 hxL hfpf hrT hrn hyL hy3
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))) ⟨_, ho⟩
  have hj' : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩)⁻¹ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩) ^ 2 ^ j = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using congrArg Subtype.val hj)
  have hy3' : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩) ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) using 2
    exact Subtype.ext (by simpa using hy3)
  have hc := centralizes_sz_of_inv' (N := modO2Image H K) hKsz
    (mk_mem_normalizer hKH hyN) (mk_mem_normalizer hKH hrN) hy3' hj'
    (mem_modO2Image'.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩)
  exact mem_O2H_of_commute ⟨y, hyH⟩ ⟨k, hKH hk⟩ (comm_of_conj_eq hc)

theorem comm_conjClosure (h1332 : Stmt13_3_2) (S : Setting147 G T L V H) {K : Subgroup G}
    (hKH : K ≤ H) (hc : ∀ y ∈ l1 T L V, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∀ y ∈ l1 T L V, ∀ x ∈ conjClosure K T, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  have hTH : T ≤ H := Setting147.TH' S
  have hTl1 := Setting147.T_le_N_l1 S h1332
  intro y hy
  have hyH : y ∈ H := Setting147.l1H' S hy
  have hD : conjClosure K T ≤ ((Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩} : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype := by
    refine conjClosure_le fun s hs k hk => ?_
    have hsH := hTH hs
    have hz : s * k * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hsH (hKH hk)) (H.inv_mem hsH)
    refine Subgroup.mem_map.mpr ⟨⟨s * k * s⁻¹, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hy' : s⁻¹ * y * s ∈ l1 T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (hTl1 (T.inv_mem hs)) y).mp hy
      simpa using this
    have h2 : s * (s⁻¹ * y * s * k * (s⁻¹ * y * s)⁻¹ * k⁻¹) * s⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hsH) _).mp (hc _ hy' k hk)
    have e : s * (s⁻¹ * y * s * k * (s⁻¹ * y * s)⁻¹ * k⁻¹) * s⁻¹ =
        y * (s * k * s⁻¹) * y⁻¹ * (s * k * s⁻¹)⁻¹ := by group
    rw [e] at h2
    exact (Setting147.mk_commute_of_mem ⟨y, hyH⟩ ⟨_, hz⟩ h2).symm
  intro x hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp (hD hx)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hx'
  exact mem_O2H_of_commute ⟨y, hyH⟩ x' hx'

theorem l1T_le_normalizer_conjClosure (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G)) :
    l1 T L V ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  have hTl1 := Setting147.T_le_N_l1 S h1332
  refine sup_le ?_ (le_normalizer_conjClosure K T)
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [← hl1]
  refine l1_le_of_cube S14 fun y hyL hy3 => ?_
  have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
  have hle : conjClosure K T ≤ (conjClosure K T).comap (MulAut.conj y : G →* G) := by
    refine conjClosure_le fun s hs k hk => ?_
    rw [Subgroup.mem_comap]
    have hy' : s⁻¹ * y * s ∈ l1 T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (hTl1 (T.inv_mem hs)) y).mp hy
      simpa using this
    have hy'3 : (s⁻¹ * y * s) ^ 3 = 1 := by
      rw [show (s⁻¹ * y * s) ^ 3 = s⁻¹ * y ^ 3 * s by rw [pow_three, pow_three]; group, hy3]
      group
    have hk' := (Subgroup.mem_normalizer_iff.mp (hyN _ hy' hy'3) k).mp hk
    have h1 := mem_conjClosure hs hk'
    have e : s * (s⁻¹ * y * s * k * (s⁻¹ * y * s)⁻¹) * s⁻¹ = y * (s * k * s⁻¹) * y⁻¹ := by group
    rw [e] at h1
    simpa using h1
  refine mem_normalizer_of_conj_mem_fin fun a ha => ?_
  have := hle ha
  rw [Subgroup.mem_comap] at this
  simpa using this

end CFSG.Quasithin.H13.L32A.C
