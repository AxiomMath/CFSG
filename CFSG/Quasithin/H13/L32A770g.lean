module

public import CFSG.Quasithin.H13.L32A770b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.RuType
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_comm_not_mem_v1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ x ∈ L₁Of L (fsuV1 T V), ∃ v ∈ V, v * x * v⁻¹ * x⁻¹ ∉ fsuV1 T V := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, -⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  refine ⟨x, Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩, a,
    haV', fun hm => hbV ?_⟩
  have e : a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹)⁻¹ := by group
  rw [e, hxa] at hm
  have := mul_mem (inv_mem (hV2.1 hm)) ha
  simpa using this

theorem centralizer_le_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) {u : G} (hu : u ∈ fsuU T V)
    (hc : ∀ q ∈ pCoreOf 2 (hz T V), q * u = u * q) : u ∈ u0 T V := by
  by_contra huU0
  have h13322 := stmt13_3_2_two_of h1332
  have hV1U0 := fsuV1_le_u0 h hMod
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  set C := fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hC
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hHC : hz T V ≤ Subgroup.normalizer (C : Set G) := by
    intro k hk
    rw [← conjSub_eq_self_iff, hC, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr (hz_le_normalizer_U h hMod hk),
      conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hk)]
  have hHU0 : hz T V ≤ Subgroup.normalizer (u0 T V : Set G) := hz_le_normalizer_u0 h hMod
  have huC : u ∈ C := ⟨hu, Subgroup.mem_centralizer_iff.mpr fun q hq => hc q hq⟩
  have hV1C : fsuV1 T V ≤ C := le_inf (hV1U0.trans hU0U) fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun q hq => (Subgroup.mem_centralizer_iff.mp
      (pCoreOf_le 2 _ hq) z hz).symm
  have hsup : C ⊔ u0 T V = fsuU T V := by
    refine eq_fsuU_of_lt h hMod h63 le_sup_right (sup_le inf_le_left hU0U) ?_ fun e => ?_
    · intro k hk
      rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hHC (hKH hk)),
        conjSub_eq_self_iff.mpr (hHU0 (hKH hk))]
    · exact huU0 (e ▸ Subgroup.mem_sup_left huC)
  have hcomm : ∀ x ∈ kz T V, ∀ w ∈ fsuU T V, w * x * w⁻¹ * x⁻¹ ∈ C := by
    intro x hx w hw
    have hxH := hKH hx
    have hCN : C ≤ Subgroup.normalizer (u0 T V : Set G) :=
      (inf_le_left.trans hUH).trans hHU0
    rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hw
    obtain ⟨c, hcC, u₀, hu₀, rfl⟩ := hw
    rw [← comm_mul_comm h hMod hxH (Subgroup.mem_inf.mp hcC).1 (hU0U hu₀)]
    refine mul_mem ?_ (hV1C (hu₀.2.2 x hx))
    have : x * c⁻¹ * x⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hHC hxH) _).mp (inv_mem hcC)
    rw [show c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) by group]
    exact mul_mem hcC this
  obtain ⟨x, hxL1, v, hv, hvx⟩ := exists_comm_not_mem_v1 h hMod h1222 h1332 h1334
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hmV : v * x * v⁻¹ * x⁻¹ ∈ V := by
    rw [show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
    exact mul_mem hv ((Subgroup.mem_normalizer_iff.mp hxV _).mp (inv_mem hv))
  have hm := hcomm x (l1_le_kz h hMod hxL1) v (le_conjClosure V _ hv)
  have hCVN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer ((C ⊓ V : Subgroup G) : Set G) := by
    intro l hl
    rw [← conjSub_eq_self_iff, conjSub_inf, conjSub_eq_self_iff.mpr (hHC (hF.L₁T_le_H hl)),
      conjSub_eq_self_iff.mpr (hF.L₁T_normalizes_Vp hl)]
  have hCV : C ⊓ V = V := by
    rcases hF.irred (C ⊓ V) (le_inf hV1C hF.V₁_le_Vp) inf_le_right hCVN with e | e
    · have hmCV : v * x * v⁻¹ * x⁻¹ ∈ C ⊓ V := ⟨hm, hmV⟩
      rw [e] at hmCV
      exact absurd hmCV hvx
    · exact e
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have h41 := lemma14_7_4_one h h13322 hMod h13314 hV2
  rw [show A6.g1 T V = hz T V from normalizer_eq_centralizer_of_card_eq_two hF.card_V₁] at h41
  have hb : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw q hq
    have hwC : w ∈ C := (hCV.symm ▸ hV2.2.1 hw : w ∈ C ⊓ V).1
    rw [Subgroup.mem_bot, commutatorElement_def,
      ← Subgroup.mem_centralizer_iff.mp hwC.2 q hq, mul_inv_cancel_right, mul_inv_cancel]
  rw [h41] at hb
  have := hF.card_V₁
  rw [hb, Subgroup.card_bot] at this
  omega

theorem isPGroup_centralizer_of_not_mem_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) {a : G} (haU : a ∈ fsuU T V) (hau0 : a ∉ u0 T V) :
    IsPGroup 2 ↥(hz T V ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, π, β, -, hπk, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hβa : Multiplicative.toAdd (β ⟨a, haU⟩) ≠ 0 := fun h0 => hau0 (by
    have h1 : β ⟨a, haU⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0, toAdd_one]
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf] at h1
    exact h1)
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    fun {q} hq hqd => ?_)
  by_contra hq2
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hyo : orderOf (y : G) = q := by rw [Subgroup.orderOf_coe, hy]
  have hyodd : Odd (orderOf (y : G)) := by
    rw [hyo]
    exact hq.odd_of_ne_two hq2
  have hyK : (y : G) ∈ kz T V := mem_oTwoUpper_of_odd (Subgroup.mem_inf.mp y.2).1 hyodd
  have hya : (y : G) * a * (y : G)⁻¹ = a := by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2 a rfl
    rw [← this, mul_inv_cancel_right]
  have hfix : ((π ⟨y, hyK⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
      (Multiplicative.toAdd (β ⟨a, haU⟩)) = Multiplicative.toAdd (β ⟨a, haU⟩) := by
    have h1 := hβe ⟨y, hyK⟩ ⟨a, haU⟩ ⟨a, haU⟩ hya.symm
    have := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at this
    exact this.symm
  have h2 := sl24_sq_of_fix _ _ hβa hfix
  have hq' : π ⟨y, hyK⟩ ^ q = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyK⟩ : ↥(kz T V)) ^ q = 1 :=
      Subtype.ext (by simpa [← hyo] using pow_orderOf_eq_one (y : G))
    rw [e, map_one]
  have hπ1 : π ⟨y, hyK⟩ = 1 := by
    have hord := Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hq')
    exact orderOf_eq_one_iff.mp hord
  have hyO : (y : G) ∈ pCoreOf 2 (kz T V) := by
    have : (⟨y, hyK⟩ : ↥(kz T V)) ∈ π.ker := hπ1
    rw [hπk, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (kz T V)) ⟨_, hyO⟩
  have hk' : (y : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hqd2 : q ∣ 2 ^ k := hyo ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqd2))

theorem comm_mem_of_R1_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {r u : G} (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hu : u ∈ u0 T V) : r * u * r⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨hR1KQ, -⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKN : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    hKH.trans (le_normalizer_pCoreOf 2 _)
  have hr' := hR1KQ hr
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at hr'
  obtain ⟨k, hk, q, hq, rfl⟩ := hr'
  have hUu : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
  have h1 : q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := comm_mem_of_pCoreOf h hMod hF hq hUu
  have h2 : u * k * u⁻¹ * k⁻¹ ∈ fsuV1 T V := hu.2.2 k hk
  have h2' : k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    have := inv_mem h2
    rwa [show (u * k * u⁻¹ * k⁻¹)⁻¹ = k * u * k⁻¹ * u⁻¹ by group] at this
  have hc : k * (q * u * q⁻¹ * u⁻¹) * k⁻¹ = q * u * q⁻¹ * u⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp (hKH hk) _ h1
    rw [← this, mul_inv_cancel_right]
  rw [show k * q * u * (k * q)⁻¹ * u⁻¹ =
    (k * (q * u * q⁻¹ * u⁻¹) * k⁻¹) * (k * u * k⁻¹ * u⁻¹) by group, hc]
  exact mul_mem h1 h2'

theorem comm_mem_of_R1_sup (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {r w : G} (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hw : w ∈ V ⊔ u0 T V) : r * w * r⁻¹ * w⁻¹ ∈ fsuV1 T V := by
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    ((le_conjClosure V _).trans hUH).trans (hz_le_normalizer_u0 h hMod)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN] at hw
  obtain ⟨v, hv, u, hu, rfl⟩ := hw
  have hrH : r ∈ hz T V := (pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H hr
  have h1 := comm_mem_of_R1 hF hr hv
  have h2 := comm_mem_of_R1_u0 h hMod h63 hF h1222 h1332 h1334 hr hu
  have hc : v * (r * u * r⁻¹ * u⁻¹) * v⁻¹ = r * u * r⁻¹ * u⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp (hUH (le_conjClosure V _ hv)) _ h2
    rw [← this, mul_inv_cancel_right]
  rw [show r * (v * u) * r⁻¹ * (v * u)⁻¹ =
    (r * v * r⁻¹ * v⁻¹) * (v * (r * u * r⁻¹ * u⁻¹) * v⁻¹) by group, hc]
  exact mul_mem h1 h2

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem zα_le_U (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    conjSub ((k : G) * g) (fsuV1 T V) ≤ fsuU T V := by
  refine (N.zα_le h hMod h63 hF h1222 h1332 h1334 h2).trans ?_
  rw [Subgroup.commutator_le]
  intro u hu w hw
  have hwH : w ∈ hz T V := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H) (this hw)
  have hwu : w * u⁻¹ * w⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_U h hMod hwH) _).mp (inv_mem hu)
  rw [commutatorElement_def, show u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) by group]
  exact mul_mem hu hwu

theorem commutator_zα_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ⁅conjSub ((k : G) * g) (fsuV1 T V), pCoreOf 2 (hz T V)⁆ = fsuV1 T V := by
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hle : ⁅conjSub ((k : G) * g) (fsuV1 T V), pCoreOf 2 (hz T V)⁆ ≤ fsuV1 T V := by
    rw [Subgroup.commutator_le]
    intro w hw q hq
    have := inv_mem (comm_mem_of_pCoreOf h hMod hF hq (hZU hw))
    rwa [show (q * w * q⁻¹ * w⁻¹)⁻¹ = ⁅w, q⁆ by rw [commutatorElement_def]; group] at this
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hF.card_V₁ hle with hb | he
  · exfalso
    apply N.zα_not_le_u0 hF h68 h
    intro w hw
    refine centralizer_le_u0 h hMod h63 hF h1222 h1332 h1334 h13314 (hZU hw) fun q hq => ?_
    have h1 : ⁅w, q⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← hb]
      exact Subgroup.commutator_mem_commutator hw hq
    rw [commutatorElement_def] at h1
    calc q * w = (w * q * w⁻¹ * q⁻¹)⁻¹ * (w * q) := by group
      _ = w * q := by rw [h1, inv_one, one_mul]
  · exact he

theorem le_normalizer_E (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤
      Subgroup.normalizer ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) :
        Set G) := by
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hZVU : conjSub ((k : G) * g) (fsuV1 T V) ≤ V ⊔ u0 T V := by
    rw [← N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ]
    exact (N.zα_le h hMod h63 hF h1222 h1332 h1334 h2).trans le_sup_left
  intro r hr
  have hrH : r ∈ hz T V := (pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H hr
  rw [← conjSub_eq_self_iff]
  refine conjSub_eq_of_le ?_
  rw [conjSub_sup, conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ hrH)]
  refine sup_le le_sup_left ?_
  rintro _ ⟨w, hw, rfl⟩
  have h1 := comm_mem_of_R1_sup h hMod h63 hF h1222 h1332 h1334 hr (hZVU hw)
  show r * w * r⁻¹ ∈ _
  rw [show r * w * r⁻¹ = (r * w * r⁻¹ * w⁻¹) * w by group]
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hw)

theorem isPGroup_cE (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    IsPGroup 2 ↥(hz T V ⊓ Subgroup.centralizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G)) := by
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  obtain ⟨a, haZ, haU0⟩ : ∃ a ∈ conjSub ((k : G) * g) (fsuV1 T V), a ∉ u0 T V := by
    by_contra hc
    push Not at hc
    exact N.zα_not_le_u0 hF h68 h hc
  refine (isPGroup_centralizer_of_not_mem_u0 h hMod h63 (hZU haZ) haU0).to_le ?_
  refine inf_le_inf_left _ (Subgroup.centralizer_le ?_)
  rintro _ rfl
  exact haZ

end Not1471

end CFSG.Quasithin.H13.L32A
