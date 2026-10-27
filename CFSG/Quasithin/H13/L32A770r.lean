module

public import CFSG.Quasithin.H13.L32A770n
public import CFSG.Quasithin.H13.L32A770o
public import CFSG.Quasithin.H13.L32A770p
public import CFSG.Quasithin.H13.L32A770q
public import CFSG.Quasithin.H13.GoldEdgeS3

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_inf_le_four_of_caseTwo {D : Type} [Group D] [Finite D] {H₁ H₂ : Subgroup D}
    (hT : IsGoldschmidtTriple H₁ H₂) (h : F6.IsF618CaseTwo D) : Nat.card ↥(H₁ ⊓ H₂) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.isPGroup_inf.exists_card_eq
  have hdvd : Nat.card ↥(H₁ ⊓ H₂) ∣ Nat.card D := Subgroup.card_subgroup_dvd_card _
  obtain ⟨m, hm, hD⟩ : ∃ m : ℕ, Odd m ∧ Nat.card D = 4 * m := by
    rcases h with he | ⟨φ, hφ, hN⟩
    · obtain ⟨e⟩ := he
      refine ⟨9, by decide, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
      rfl
    · refine ⟨27, by decide, ?_⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hN.2.1,
        Nat.card_prod]
      simp
  rw [hD, hk] at hdvd
  have h4 : 2 ^ k ∣ 4 :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h4

theorem card_map_inf_eq {I G₁ G₂ : Subgroup G} (htriple : F6.IsGoldschmidtTripleIn I G₁ G₂) :
    Nat.card ↥((G₁.subgroupOf I ⊓ G₂.subgroupOf I).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) = (pCoreOf 2 I).relIndex (G₁ ⊓ G₂) := by
  have hG₁I : G₁ ≤ I := htriple.1 ▸ le_sup_left
  have hinf : CFSG.pPrimeCore 3 ↥I ⊓ (G₁.subgroupOf I ⊓ G₂.subgroupOf I) =
      CFSG.Open.pCore 2 ↥I := by
    have h1 := F6.inf_pPrimeCore_eq_pCore_left htriple.subgroupOf
    have h2 := F6.inf_pPrimeCore_eq_pCore_right htriple.subgroupOf
    calc CFSG.pPrimeCore 3 ↥I ⊓ (G₁.subgroupOf I ⊓ G₂.subgroupOf I) =
        (G₁.subgroupOf I ⊓ CFSG.pPrimeCore 3 ↥I) ⊓ (G₂.subgroupOf I ⊓ CFSG.pPrimeCore 3 ↥I) := by
          ext x
          simp only [Subgroup.mem_inf]
          tauto
      _ = CFSG.Open.pCore 2 ↥I := by rw [h1, h2, inf_idem]
  have e1 : CFSG.Open.pCore 2 ↥I = (pCoreOf 2 I).subgroupOf I := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [← Subtype.ext hyx]
  have e2 : G₁.subgroupOf I ⊓ G₂.subgroupOf I = (G₁ ⊓ G₂).subgroupOf I := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [F6.card_map_mk, ← Subgroup.inf_relIndex_right, hinf, e1, e2,
    Subgroup.relIndex_subgroupOf (inf_le_left.trans hG₁I)]

theorem exists_l1_comm (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧ ∀ w ∈ V ⊔ u0 T V, w ∉ u0 T V →
      w⁻¹ * (x * w * x⁻¹) ∈ V ∧ w⁻¹ * (x * w * x⁻¹) ∉ fsuV1 T V := by
  obtain ⟨x, hxL1, hx3, hfpf⟩ := exists_l1_fpf h hMod h1222 h1332 h1334
  refine ⟨x, hxL1, hx3, fun w hw hwU0 => ?_⟩
  have hxK : x ∈ kz T V := l1_le_kz h hMod hxL1
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hVU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  obtain ⟨hUc, -⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN] at hw
  obtain ⟨v, hv, u, hu, hvu⟩ := hw
  have hvu' : v * u = w := hvu
  have hvV1 : v ∉ fsuV1 T V := fun h' => hwU0 (by
    rw [← hvu']
    exact mul_mem (fsuV1_le_u0 h hMod h') hu)
  have hc : u⁻¹ * x * u * x⁻¹ ∈ fsuV1 T V := by
    simpa using (inv_mem hu).2.2 x hxK
  have hxvV : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have e : w⁻¹ * (x * w * x⁻¹) = (v⁻¹ * (x * v * x⁻¹)) * (u⁻¹ * x * u * x⁻¹) := by
    rw [← hvu']
    calc (v * u)⁻¹ * (x * (v * u) * x⁻¹) = u⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * (x * u * x⁻¹) := by
          group
      _ = (v⁻¹ * (x * v * x⁻¹)) * u⁻¹ * (x * u * x⁻¹) := by
          rw [hUc u⁻¹ (inv_mem (hU0U hu)) _ (mul_mem (inv_mem (hVU hv)) (hVU hxvV))]
      _ = (v⁻¹ * (x * v * x⁻¹)) * (u⁻¹ * x * u * x⁻¹) := by group
  have hdV : v⁻¹ * (x * v * x⁻¹) ∈ V := mul_mem (inv_mem hv) hxvV
  have hdV1 : v⁻¹ * (x * v * x⁻¹) ∉ fsuV1 T V := by
    intro hd
    apply hvV1
    refine hfpf v hv ?_
    have hv1 := hF.H_normalizes_V₁ (hUH (hVU hv))
    have := (Subgroup.mem_normalizer_iff.mp hv1 _).mp hd
    rwa [show v * (v⁻¹ * (x * v * x⁻¹)) * v⁻¹ = x * v * x⁻¹ * v⁻¹ by group] at this
  rw [e]
  refine ⟨mul_mem hdV (hF.V₁_le_Vp hc), fun hm => hdV1 ?_⟩
  rw [show v⁻¹ * (x * v * x⁻¹) = (v⁻¹ * (x * v * x⁻¹)) * (u⁻¹ * x * u * x⁻¹) *
    (u⁻¹ * x * u * x⁻¹)⁻¹ by group]
  exact mul_mem hm (inv_mem hc)

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem exists_cycle (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {z zα : G} (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V)) (hzα1 : zα ≠ 1) :
    ∃ y ∈ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G),
      y * z * y⁻¹ = zα ∧ y * zα * y⁻¹ = z * zα := by
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hcom : z * zα = zα * z := hUc z hzU zα (hZU hzα)
  obtain ⟨q, hqQ, hqzα⟩ := N.exists_q h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 hz0 hz1
    hzα hzα1
  obtain ⟨a, haQ, haz⟩ := N.exists_a h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1
    hzα hzα1
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hqQ
  have hqz : q * z * q⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hqH z hz0
    rw [← this, mul_inv_cancel_right]
  have haα : a * zα * a⁻¹ = zα := by
    have haG : a ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) haQ
    rw [← conjSub_centralizer] at haG
    have := Subgroup.mem_centralizer_iff.mp haG zα hzα
    rw [← this, mul_inv_cancel_right]
  have hzE : z ∈ E := Subgroup.mem_sup_left hz0
  have hzαE : zα ∈ E := Subgroup.mem_sup_right hzα
  have hzzαE : z * zα ∈ E := mul_mem hzE hzαE
  have hqX : q ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_E (g := g) (k := k) hF hz0
    hz1 hzα hzα1 (by rw [hqz]; exact hzE) (by rw [hqzα]; exact hzzαE)
  have haX : a ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_E (g := g) (k := k) hF hz0
    hz1 hzα hzα1 (by rw [haz, ← hcom]; exact hzzαE) (by rw [haα]; exact hzαE)
  have hqc : q * z = z * q := by
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [hqz]
  have hqz' : q⁻¹ * z * q = z := by rw [mul_assoc, ← hqc]; group
  have hqα' : q⁻¹ * zα * q = z * zα := by
    calc q⁻¹ * zα * q = q⁻¹ * (z * (z * zα)) * q := by
          rw [show z * (z * zα) = zα by rw [← mul_assoc, hzz, one_mul]]
      _ = q⁻¹ * (z * (q * zα * q⁻¹)) * q := by rw [hqzα]
      _ = (q⁻¹ * z * q) * zα := by group
      _ = z * zα := by rw [hqz']
  refine ⟨q⁻¹ * a, mul_mem (inv_mem hqX) haX, ?_, ?_⟩
  · calc (q⁻¹ * a) * z * (q⁻¹ * a)⁻¹ = q⁻¹ * (a * z * a⁻¹) * q := by group
      _ = q⁻¹ * (zα * z) * q := by rw [haz]
      _ = (q⁻¹ * zα * q) * (q⁻¹ * z * q) := by group
      _ = z * zα * z := by rw [hqα', hqz']
      _ = zα := by rw [mul_assoc, ← hcom, ← mul_assoc, hzz, one_mul]
  · calc (q⁻¹ * a) * zα * (q⁻¹ * a)⁻¹ = q⁻¹ * (a * zα * a⁻¹) * q := by group
      _ = z * zα := by rw [haα, hqα']

theorem zα_not_mem_V (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8) {z zα : G}
    (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V))
    (hzα1 : zα ≠ 1) (hne : zα ≠ z) : zα ∉ V := by
  intro hzαV
  have hFV := N.inf_V_eq h hMod h63 hF h1222 h1332 h1334 h64 h69 h2 h8
  have hzαF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2 hzα
  have hm : zα ∈ fsuV1 T V := by
    rw [← hFV]
    exact Subgroup.mem_inf.mpr ⟨hzαF, hzαV⟩
  rcases eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1 zα hm with e | e
  · exact hzα1 e
  · exact hne e

theorem not_le_normalizer_T (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ¬ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (T : Set G) := by
  intro hle
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  obtain ⟨y, hyX, hyz, -⟩ :=
    N.exists_cycle h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1 hzα hzα1
  obtain ⟨q, hqQ, hqzα⟩ := N.exists_q h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 hz0 hz1
    hzα hzα1
  have hqT : q ∈ T := pCoreOf_le_of_le h hF.T_le_H hqQ
  have hq' : y⁻¹ * q * y ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (hle (inv_mem hyX)) q).mp hqT
    simpa using this
  have e := Subgroup.mem_centralizer_iff.mp (hF.T_le_H hq') z hz0
  have h1 : q * zα * q⁻¹ = zα := by
    calc q * zα * q⁻¹ = y * ((y⁻¹ * q * y) * z * (y⁻¹ * q * y)⁻¹) * y⁻¹ := by
          rw [← hyz]; group
      _ = y * z * y⁻¹ := by rw [← e]; group
      _ = zα := hyz
  apply hz1
  calc z = z * zα * zα⁻¹ := by group
    _ = q * zα * q⁻¹ * zα⁻¹ := by rw [hqzα]
    _ = 1 := by rw [h1]; group

theorem triple (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) :
    F6.IsGoldschmidtTripleIn ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ Subgroup.normalizer
        ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G))
      (L₁Of L (fsuV1 T V) ⊔ T) (Subgroup.normalizer
        ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) ∧
    (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.normalizer
        ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  set X := Subgroup.normalizer (E : Set G) with hX
  set A := L₁Of L (fsuV1 T V) ⊔ T with hA
  have hNHE := N.normalizer_inf_eq h hMod h63 hF h1222 h1332 h1334 h68 h2 hTE
  have hAX : A ⊓ X = T := le_antisymm
    (by rw [← hNHE]; exact inf_le_inf_right X hF.L₁T_le_H) (le_inf le_sup_right hTE)
  have hT2 : IsPGroup 2 ↥T := h.fsu.sylow.1
  have hTA := relIndex_T_L1T h hMod h63 hF h1222 h1332 h1334
  have hTX := N.relIndex_T_X h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hTE
  have hAn : ¬ A ≤ Subgroup.normalizer (T : Set G) := by
    intro hle
    have hTR : T ≤ pCoreOf 2 A := le_pCoreOf_of_le_normalizer 2 le_sup_right hle hT2
    have h2' := S14.index2_eq
    rw [Subgroup.relIndex_eq_one.mpr hTR] at h2'
    omega
  have hXn := N.not_le_normalizer_T h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2
  refine ⟨⟨rfl, nonempty_quotient_perm_three le_sup_right hT2 hTA hAn,
    nonempty_quotient_perm_three hTE hT2 hTX hXn, ?_⟩, hAX⟩
  rw [hAX]
  exact isSylowTwoOf_of_le h (le_sup_right.trans le_sup_left)

theorem false_of_card_eight (hedge : GoldschmidtEdgeBoundS3)
    (hF618 : F6.TheoremF618Cat) (hBig : A5.FactF618Big) (h1434 : Lemma1434One)
    (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8) {s : G}
    (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V)) (hsQ : s ∉ pCoreOf 2 (hz T V))
    (hsT : ∀ t ∈ T, t * s * t⁻¹ * s⁻¹ ∈ pCoreOf 2 (hz T V)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTE := N.T_le_normalizer_E h hMod h63 hF h1222 h1332 h1334 h13314 h64 h69 h2 h8 hsW hsQ
    hsT
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  set X := Subgroup.normalizer (E : Set G) with hX
  set A := L₁Of L (fsuV1 T V) ⊔ T with hA
  set I := A ⊔ X with hI
  obtain ⟨htriple, hAX⟩ := N.triple h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hTE
  have hAI : A ≤ I := le_sup_left
  have hXI : X ≤ I := le_sup_right
  have hTI : T ≤ I := le_sup_right.trans hAI
  have hQI : pCoreOf 2 I ≠ ⊥ := by
    intro hb
    have hpc : Open.pCore 2 ↥I = ⊥ := by
      unfold pCoreOf at hb
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hb
    have hbd := card_inf_le_of_goldschmidtEdgeBoundS3 hedge ⟨htriple.subgroupOf, hpc⟩
    have hT : Nat.card ↥(A.subgroupOf I ⊓ X.subgroupOf I) = Nat.card T := by
      have e : A.subgroupOf I ⊓ X.subgroupOf I = (A ⊓ X).subgroupOf I := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      rw [e, hAX]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTI).toEquiv
    have hle : Nat.card ↥T ≤ 2 ^ 7 := hT ▸ hbd
    have := N.card_T_ge h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 h8
    omega
  have hQIT : pCoreOf 2 I ≤ T := pCoreOf_le_of_le h hTI
  have hQIN : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := le_normalizer_pCoreOf 2 I
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hQIZ : pCoreOf 2 I ≤
      Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) :=
    N.comm_zα_of_normal h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hTE hQIT
      ((N.Qα_le_normalizer_E h hMod h63 hF h1222 h1332 h1334 h69 h2).trans (hXI.trans hQIN))
  have hzαVU : zα ∈ V ⊔ u0 T V := by
    rw [← N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ]
    exact Subgroup.mem_sup_left (N.zα_le h hMod h63 hF h1222 h1332 h1334 h2 hzα)
  have hzαu := N.gen_not_mem_u0 h hF h68 hzα hzα1
  have hQIV : pCoreOf 2 I ≤ Subgroup.centralizer (V : Set G) :=
    le_centralizer_V h hMod hF h1222 h1332 h1334 (hQIT.trans hF.T_le_H) (hAI.trans hQIN) hzαVU
      hzαu fun p hp => (Subgroup.mem_centralizer_iff.mp (hQIZ hp) zα hzα).symm
  have hsmall : (pCoreOf 2 I).relIndex T ≤ 8 → False := by
    intro h8'
    have heq := eq_cT_of_le h hMod hF h1222 h1332 h1334 (le_inf hQIT hQIV) h8'
    refine N.false_of_normal h hMod h63 hF h1222 h1332 h1334 h13314 h64 h68 h69 h2 h8 hTE hQI
      hQIT ?_ (hXI.trans hQIN)
    rw [heq]
    exact le_normalizer_cT hF
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hne : zα ≠ z := fun e => hzαu (e ▸ hzu)
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hzαzα : zα * zα = 1 := by rw [← sq]; exact hUe zα (hZU hzα)
  have hcom : z * zα = zα * z := hUc z hzU zα (hZU hzα)
  obtain ⟨y, hyX, hyz, hyzα⟩ :=
    N.exists_cycle h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1 hzα hzα1
  have hZ : ∀ K : Subgroup G, K ≤ I → I ≤ Subgroup.normalizer (K : Set G) →
      ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ → IsPGroup 2 ↥K := by
    intro K _ hIK hb
    have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp hz0).2
    have hc : ∀ c ∈ K, c * z = z * c := by
      intro c hc
      have hm := Subgroup.commutator_mem_commutator hzZ hc
      rw [hb, Subgroup.mem_bot, commutatorElement_def] at hm
      calc c * z = (z * c * z⁻¹ * c⁻¹)⁻¹ * (z * c) := by group
        _ = z * c := by rw [hm, inv_one, one_mul]
    have hKH : K ≤ hz T V := by
      intro c hcK
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rcases eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1 v hv with e | e
      · rw [e, one_mul, mul_one]
      · rw [e]
        exact (hc c hcK).symm
    have hKZα : K ≤ Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) := by
      intro c hcK
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1 w hw with e | e
      · rw [e, one_mul, mul_one]
      · rw [e]
        have hc' : y⁻¹ * c * y ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (hIK (inv_mem (hXI hyX))) c).mp hcK
          simpa using this
        have e' := hc _ hc'
        calc zα * c = (y * z * y⁻¹) * c := by rw [hyz]
          _ = y * (z * (y⁻¹ * c * y)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * c * y) * z) * y⁻¹ := by rw [← e']
          _ = c * (y * z * y⁻¹) := by group
          _ = c * zα := by rw [hyz]
    exact (N.isPGroup_cE h hMod h63 hF h1222 h1332 h1334 h68 h2).to_le (le_inf hKH hKZα)
  have hfin : CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) ∧
      (∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) ≠
        60 * 2 ^ b) →
      IsGoldschmidtAmalgam ((A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((X.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) → False := by
    rintro ⟨hq, h60⟩ hAm
    have h21 := three_mul_card_eq_of_quasisimple h1434 h.hyp h.fsu.qtke h.fsu.sylow htriple hAX
      hQI hZ hq h60 hAm
    have hidx : A.relIndex I = 7 := by
      have hm := Subgroup.relIndex_mul_card A I
      rw [inf_of_le_left hAI] at hm
      have hpos : 0 < Nat.card ↥A := Nat.card_pos
      have e1 : (3 * A.relIndex I) * Nat.card ↥A = 21 * Nat.card ↥A := by
        rw [mul_assoc, hm, h21]
      have := Nat.eq_of_mul_eq_mul_right hpos e1
      omega
    obtain ⟨x, hxL1, hx3, hxw⟩ := exists_l1_comm h hMod hF h1222 h1332 h1334
    obtain ⟨hdV, hdV1⟩ := hxw zα hzαVU hzαu
    have hxH : x ∈ hz T V := hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
    have hxz : x * z * x⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hxH z hz0, mul_inv_cancel_right]
    have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
      hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
    have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
    have hzαV := N.zα_not_mem_V h hMod h63 hF h1222 h1332 h1334 h64 h69 h2 h8 hz0 hz1 hzα hzα1
      hne
    have hz7 : {w : G | ∃ g ∈ I, g * z * g⁻¹ = w}.ncard ≤ 7 := by
      have := ncard_conj_le (I := I) (H := A) (z := z) fun a ha => by
        rw [← Subgroup.mem_centralizer_iff.mp (hF.L₁T_le_H ha) z hz0, mul_inv_cancel_right]
      rwa [hidx] at this
    exact false_of_ncard_le_seven (hAI (Subgroup.mem_sup_left hxL1)) (hXI hyX) hx3 hxz hyz hyzα
      hz1 hzz hzαzα hcom hzV hzαV hxV hdV (fun e => hdV1 (e ▸ one_mem _))
      (fun e => hdV1 (e ▸ hz0)) hz7
  rcases htriple.goldschmidt_mod_pPrimeCore with ⟨hinf, hAm, -⟩ | ⟨h1, -, -, -, -⟩
  · have := h.fsu.simple
    have hSQ : CFSG.SectionRank.IsSQTKCat ↥I :=
      (qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1 _ hQI
    have hconc := hF618 _ _ _ hAm.toIsGoldschmidtTriple
      ⟨↥I, inferInstance, inferInstance, hSQ, ⟨MulEquiv.refl _⟩⟩
    have hcardT := card_map_inf_eq htriple
    rw [← hinf, hAX] at hcardT
    have hsmall' : Nat.card ↥((A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (X.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ≤ 8 → False :=
      fun h' => hsmall (hcardT ▸ h')
    have hAm' : IsGoldschmidtAmalgam
        ((X.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) :=
      { hAm.toIsGoldschmidtTriple.symm with pCore_eq_bot := hAm.pCore_eq_bot }
    rcases hconc with hc | hc
    · rcases hc with h1c | h2c | h3c | hbc
      · obtain ⟨⟨e⟩, -⟩ := h1c
        exact hsmall' (by rw [Nat.card_congr e.toEquiv]; simp)
      · exact hsmall' ((card_inf_le_four_of_caseTwo hAm.toIsGoldschmidtTriple h2c).trans
          (by norm_num))
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := h3c
        exact hsmall' (by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
      · exact hfin (hBig _ _ _ hAm hbc) hAm
    · rcases hc with h1c | h2c | h3c | hbc
      · obtain ⟨⟨e⟩, -⟩ := h1c
        exact hsmall' (by rw [inf_comm, Nat.card_congr e.toEquiv]; simp)
      · exact hsmall' ((card_inf_le_four_of_caseTwo hAm.toIsGoldschmidtTriple h2c).trans
          (by norm_num))
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := h3c
        exact hsmall' (by rw [inf_comm, Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
      · exact hfin (hBig _ _ _ hAm' hbc) hAm
  ·
    have hRQ : pCoreOf 2 A = pCoreOf 2 I := by
      rw [← L14331.map_pCoreOf_subgroupOf' hAI, h1]
      rfl
    have h13322 := stmt13_3_2_two_of h1332
    obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
    have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
    have S14 := h.set14 h1222 h1332 h1334 hV2
    have hPN : A ≤ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V)) : Set G) :=
      sup_le (le_normalizer_pCoreOf 2 _) (S14.T_Lp.trans (normalizer_le_normalizer_pCoreOf 2 _))
    have hPR : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ pCoreOf 2 A :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) hPN
        (pCoreOf_isPGroup 2 _)
    have h4 := four_le_relIndex_pCoreOf h hMod hF h1222 h1332 h1334
    rw [Subgroup.relIndex_eq_one.mpr (hPR.trans (hRQ ▸ hQIV))] at h4
    omega

end Not1471

end CFSG.Quasithin.H13.L32A
