module

public import CFSG.Quasithin.H13.L32A715m
public import CFSG.Quasithin.H13.L32A718a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Lines

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_of_chain {L X₀ X K : Subgroup Γ} (hK : Nat.card K = 27) (hL : Nat.card L = 3)
    (h1 : L < X₀) (h2 : X₀ < X) (h3 : X ≤ K) : X = K := by
  have d1 := Subgroup.card_dvd_of_le h1.le
  have d2 := Subgroup.card_dvd_of_le h2.le
  have d3 := Subgroup.card_dvd_of_le h3
  have l1 := Subgroup.card_lt_of_lt h1
  have l2 := Subgroup.card_lt_of_lt h2
  rw [hL] at d1 l1
  rw [hK] at d3
  refine Subgroup.eq_of_le_of_card_ge h3 ?_
  rw [hK]
  have d3' : Nat.card X ∣ 3 ^ 3 := by norm_num [d3]
  obtain ⟨i, hi, hXi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 d3'
  have d2' : Nat.card X₀ ∣ 3 ^ i := hXi ▸ d2
  obtain ⟨j, hj, hX₀j⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 d2'
  rw [hXi] at l2 ⊢
  rw [hX₀j] at l1 l2
  interval_cases i <;> interval_cases j <;> revert l1 l2 <;> norm_num

theorem le_closure_pair {K L : Subgroup Γ} (hK : Nat.card K = 27) (hL : Nat.card L = 3)
    (hLK : L ≤ K) {g h : Γ} (hg : g ∈ K) (hgL : g ∉ L) (hh : h ∈ K)
    (hhL : h ∉ Subgroup.zpowers g ⊔ L) : K ≤ Subgroup.closure {g, h} ⊔ L := by
  have h1 : L < Subgroup.zpowers g ⊔ L :=
    lt_of_le_of_ne le_sup_right fun e => hgL (e ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  have hle : Subgroup.zpowers g ⊔ L ≤ Subgroup.closure {g, h} ⊔ L :=
    sup_le_sup_right ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Set.mem_insert g _))) L
  have h2 : Subgroup.zpowers g ⊔ L < Subgroup.closure {g, h} ⊔ L :=
    lt_of_le_of_ne hle fun e => hhL (e ▸ Subgroup.mem_sup_left
      (Subgroup.subset_closure (Set.mem_insert_of_mem g rfl)))
  have h3 : Subgroup.closure {g, h} ⊔ L ≤ K := by
    refine sup_le ((Subgroup.closure_le K).mpr ?_) hLK
    rintro x (rfl | rfl)
    · exact hg
    · exact hh
  exact (eq_of_chain hK hL h1 h2 h3).ge

omit [Finite Γ] in
theorem conj_not_mem_sup {K L : Subgroup Γ} [L.Normal] {y g : Γ} (hg : g ∈ K) (hgL : g ∉ L)
    (hg3 : g ^ 3 = 1) (hyL : ∀ l ∈ L, y * l * y⁻¹ = l) (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l)
    (hinv : y ^ 2 * g * (y ^ 2)⁻¹ * g ∈ L) : y * g * y⁻¹ ∉ Subgroup.zpowers g ⊔ L := by
  intro hmem
  obtain ⟨x, hx, l, hl, hxl⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hcomm : Commute (g ^ i) l := (hLK l hl _ (K.zpow_mem hg i)).symm
  have e1 : y * g ^ i * y⁻¹ = (g ^ i * l) ^ i := by rw [hxl, conj_zpow]
  have e2 : (g ^ i * l) ^ i = g ^ (i * i) * l ^ i := by rw [hcomm.mul_zpow, ← zpow_mul]
  have e3 : y ^ 2 * g * (y ^ 2)⁻¹ = g ^ (i * i) * l ^ i * l := by
    calc y ^ 2 * g * (y ^ 2)⁻¹ = y * (y * g * y⁻¹) * y⁻¹ := by rw [sq]; group
      _ = y * (g ^ i * l) * y⁻¹ := by rw [hxl]
      _ = (y * g ^ i * y⁻¹) * (y * l * y⁻¹) := by group
      _ = g ^ (i * i) * l ^ i * l := by rw [e1, e2, hyL l hl]
  rw [e3] at hinv
  have hlil : l ^ i * l ∈ L := L.mul_mem (L.zpow_mem hl i) hl
  have h4 : g ^ (i * i + 1) ∈ L := by
    have hc2 : (l ^ i * l) * g = g * (l ^ i * l) := hLK _ hlil g hg
    have e4 : g ^ (i * i + 1) = (g ^ (i * i) * l ^ i * l * g) * (l ^ i * l)⁻¹ := by
      rw [zpow_add_one]
      calc g ^ (i * i) * g = g ^ (i * i) * (g * (l ^ i * l)) * (l ^ i * l)⁻¹ := by group
        _ = g ^ (i * i) * ((l ^ i * l) * g) * (l ^ i * l)⁻¹ := by rw [hc2]
        _ = (g ^ (i * i) * l ^ i * l * g) * (l ^ i * l)⁻¹ := by group
    rw [e4]
    exact L.mul_mem hinv (L.inv_mem hlil)
  have h5 : g ^ (i * i + 1) = g ^ ((i * i + 1) % (3 : ℕ)) := zpow_eq_zpow_emod' _ hg3
  obtain ⟨q, r, hr, hqr⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ i = 3 * q + r :=
    ⟨i / 3, i % 3, by omega, by omega⟩
  have h6 : (i * i + 1) % 3 = 1 ∨ (i * i + 1) % 3 = 2 := by
    have e5 : i * i + 1 = (r * r + 1) + 3 * (3 * q * q + 2 * q * r) := by rw [hqr]; ring
    rw [e5, Int.add_mul_emod_self_left]
    rcases hr with rfl | rfl | rfl <;> norm_num
  push_cast at h5
  rcases h6 with h | h
  · rw [h5, h, zpow_one] at h4
    exact hgL h4
  · rw [h5, h] at h4
    apply hgL
    have e6 : g = (g ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul]
      have : g ^ ((2 : ℤ) * 2) = g ^ (((2 : ℤ) * 2) % (3 : ℕ)) := zpow_eq_zpow_emod' _ hg3
      rw [this]
      norm_num
    rw [e6]
    exact L.zpow_mem h4 2

end Lines

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem card_kdot : Nat.card ↥(modO2Image (hz T V) (oTwoUpper H)) = 27 :=
  E.isPOnePlusTwo_kdot.2.1

theorem card_l1dot : Nat.card ↥(modO2Image (hz T V) (l1 T L V)) = 3 :=
  (E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal).2.2.1

theorem pow_three_of_mem_kdot {x : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hx : x ∈ modO2Image (hz T V) (oTwoUpper H)) : x ^ 3 = 1 := by
  have := E.isPOnePlusTwo_kdot.2.2 ⟨x, hx⟩
  simpa using congrArg Subtype.val this

theorem l1dot_le_kdot : modO2Image (hz T V) (l1 T L V) ≤ modO2Image (hz T V) (oTwoUpper H) :=
  modO2Image_mono (lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three).1

theorem comm_of_mem_l1dot : ∀ l ∈ modO2Image (hz T V) (l1 T L V),
    ∀ x ∈ modO2Image (hz T V) (oTwoUpper H), l * x = x * l := by
  intro l hl x hx
  rw [← E.exists_y.1] at hl
  obtain ⟨z, hz, rfl⟩ := hl
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩).symm

theorem kdot_le_closure_pair {g h : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hg : g ∈ modO2Image (hz T V) (oTwoUpper H)) (hgL : g ∉ modO2Image (hz T V) (l1 T L V))
    (hh : h ∈ modO2Image (hz T V) (oTwoUpper H))
    (hhL : h ∉ Subgroup.zpowers g ⊔ modO2Image (hz T V) (l1 T L V)) :
    modO2Image (hz T V) (oTwoUpper H) ≤
      Subgroup.closure {g, h} ⊔ modO2Image (hz T V) (l1 T L V) :=
  le_closure_pair E.card_kdot E.card_l1dot E.l1dot_le_kdot hg hgL hh hhL

theorem kdot_le_closure_conj {y : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hyC : y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))))
    (hinv : ∀ x ∈ modO2Image (hz T V) (oTwoUpper H),
      y ^ 2 * x * (y ^ 2)⁻¹ * x ∈ modO2Image (hz T V) (l1 T L V))
    {g : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)}
    (hg : g ∈ modO2Image (hz T V) (oTwoUpper H)) (hgL : g ∉ modO2Image (hz T V) (l1 T L V)) :
    modO2Image (hz T V) (oTwoUpper H) ≤
      Subgroup.closure {g, y * g * y⁻¹} ⊔ modO2Image (hz T V) (l1 T L V) := by
  have := E.l1dot_normal
  have := E.kdot_normal
  refine E.kdot_le_closure_pair hg hgL (this.conj_mem g hg y) ?_
  refine conj_not_mem_sup hg hgL (E.pow_three_of_mem_kdot hg) (fun l hl => ?_)
    E.comm_of_mem_l1dot (hinv g hg)
  have h1 := Subgroup.mem_centralizer_iff.mp hyC l hl
  rw [← h1]
  group

end Ctx7153


section Conj

variable {G : Type} [Group G]

theorem conjSub_centralizer (m : G) (S : Subgroup G) :
    Quasithin.conjSub m (Subgroup.centralizer (S : Set G)) =
      Subgroup.centralizer (Quasithin.conjSub m S : Set G) := by
  ext x
  rw [Quasithin.mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have hs' : m⁻¹ * s * m ∈ S := Quasithin.mem_conjSub.mp hs
    have h1 := h _ hs'
    calc s * x = m * ((m⁻¹ * s * m) * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * x * m) * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1]
      _ = x * s := by group
  · intro h s hs
    have hs' : m * s * m⁻¹ ∈ Quasithin.conjSub m S := by
      rw [Quasithin.mem_conjSub]
      simpa [mul_assoc] using hs
    have h1 := h _ hs'
    calc s * (m⁻¹ * x * m) = m⁻¹ * ((m * s * m⁻¹) * x) * m := by group
      _ = m⁻¹ * (x * (m * s * m⁻¹)) * m := by rw [h1]
      _ = m⁻¹ * x * m * s := by group

end Conj

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem centralizer_le_qh :
    hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤ pCoreOf 2 (hz T V) := by
  intro x hx
  have h1 : C1Pack.rhoH hF.toHypF91 ⟨x, hx.1⟩ = 1 := by
    ext w
    obtain ⟨u, hu, rfl⟩ := exists_clsU hF.toHypF91 w
    rw [MulAut.one_apply, rhoH_clsU_eq_iff]
    have h2 : u * x = x * u := Subgroup.mem_centralizer_iff.mp hx.2 u (E.fsuU_eq ▸ hu)
    have e : x * u * x⁻¹ * u⁻¹ = 1 := by rw [← h2]; group
    rw [e]
    exact one_mem _
  exact (C1Pack.rhoH_eq_one_iff hF.toHypF91 ⟨x, hx.1⟩).mp h1

theorem u_le_p : fsuU T V ≤ pCoreOf 2 (oTwoUpper (hz T V)) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hueq := E.u_eq hF
  subst hH
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hUL : fsuU T V ≤ l1 T L V := by
    rw [← hueq, Subgroup.commutator_le]
    intro u hu l hl
    have hlU : l * u⁻¹ * l⁻¹ ∈ fsuU T V := by
      have := (Subgroup.mem_normalizer_iff.mp
        (hz_le_normalizer_U E.S.hyp hMod ((oTwoUpper_le _) (hL1K hl))) u⁻¹).mp (inv_mem hu)
      exact this
    have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
    have huH : u ∈ hz T V := pCoreOf_le 2 _ (hF.toHypF91.conjClosure_Vp_le_pCoreOf huU)
    have huL : u ∈ Subgroup.normalizer (l1 T L V : Set G) := E.hz_le_normalizer_l1 huH
    have h1 : u * l * u⁻¹ ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp huL l).mp hl
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hl)
  rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
  refine le_inf (hUL.trans hL1K) ?_
  rw [E.fsuU_eq]
  exact hF.toHypF91.conjClosure_Vp_le_pCoreOf

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem normalizer_ualpha : hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤
    Subgroup.normalizer (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) : Set G) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  rw [hl₀U]
  intro x hx
  have hxz : x ∈ Quasithin.conjSub l₀ (hz T V) := by
    rw [Quasithin.mem_conjSub]
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hv' : l₀ * v * l₀⁻¹ ∈ fsuU T V := by
      have h1 : l₀ * v * l₀⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp ((le_sup_left.trans hLTV) hl₀) v).mp
          (Subgroup.mem_inf.mp hv).1
      rw [E.fsuU_eq]
      exact le_conjClosure V _ h1
    have h2 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * (l₀⁻¹ * x * l₀) = l₀⁻¹ * ((l₀ * v * l₀⁻¹) * x) * l₀ := by group
      _ = l₀⁻¹ * (x * (l₀ * v * l₀⁻¹)) * l₀ := by rw [h2]
      _ = l₀⁻¹ * x * l₀ * v := by group
  exact conjSub_le_normalizer (hz_le_normalizer_U E.S.hyp hMod) l₀ hxz

theorem ualpha_le_hz : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ hz T V :=
  (E.ualpha_le_q hF N).trans ((pCoreOf_le_of_le E.S.hyp le_sup_right).trans E.t_le_hz)

theorem comm_mem_ealpha : ∀ x ∈ hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G),
    ∀ u ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)),
      x⁻¹ * (u * x * u⁻¹) ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hN := E.normalizer_ualpha hF N
  have hAhz := E.ualpha_le_hz hF N
  intro x hx u hu
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : x⁻¹ * u * x ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) := by
      have := (Subgroup.mem_normalizer_iff.mp (hN (inv_mem hx)) u).mp hu
      simpa using this
    have e : x⁻¹ * (u * x * u⁻¹) = (x⁻¹ * u * x) * u⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hu)
  · refine mul_mem (inv_mem hx.2) (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    have huU : u⁻¹ * w * u ∈ fsuU T V := by
      have := (Subgroup.mem_normalizer_iff.mp
        (hz_le_normalizer_U E.S.hyp hMod (inv_mem (hAhz hu))) w).mp hw
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hx.2 _ huU
    calc w * (u * x * u⁻¹) = u * ((u⁻¹ * w * u) * x) * u⁻¹ := by group
      _ = u * (x * (u⁻¹ * w * u)) * u⁻¹ := by rw [h2]
      _ = u * x * u⁻¹ * w := by group

theorem ealpha_eq_conj : ∃ m ∈ L, Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
    Subgroup.centralizer (fsuU T V : Set G) =
      Quasithin.conjSub m ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  have hne : Quasithin.conjSub 1 (fsuU T V) ≠ Quasithin.conjSub l₀ (fsuU T V) := by
    rw [Quasithin.conjSub_one, ← hl₀U]
    exact (E.ualpha_ne hF N).symm
  obtain ⟨m, hm, h1, h2⟩ := lemma14_7_12_one E.setting_hz hF h13322 hMod (one_mem L) hl₀ hl₀
    (one_mem L) hne hne.symm
  rw [mul_one] at h1
  rw [Quasithin.conjSub_one, Quasithin.conjSub_mul, ← hl₀U] at h2
  refine ⟨m, hm, ?_⟩
  rw [← E.centralizer_ualpha_eq hF N, Quasithin.conjSub_inf, conjSub_centralizer, h1, h2, hl₀U]

theorem ealpha_le_r : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
    Subgroup.centralizer (fsuU T V : Set G) ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L := by
  obtain ⟨m, hm, he⟩ := E.ealpha_eq_conj hF N
  rw [he]
  rintro _ ⟨e, he, rfl⟩
  exact mem_conjClosure hm he

theorem relIndex_v_ealpha : V ≤ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
    Subgroup.centralizer (fsuU T V : Set G) ∧
      V.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G)) = 4 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  obtain ⟨m, hm, he⟩ := E.ealpha_eq_conj hF N
  obtain ⟨hVE4, -⟩ := E.relIndex_ve_eu hF N
  have hVE := E.v_le_e hF N
  have hcardE : Nat.card ↥⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ = 32 := by
    have h4 := Subgroup.relIndex_mul_card V ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆
    rw [inf_eq_left.mpr hVE, hV8, hVE4] at h4
    omega
  have hcard : Nat.card ↥(Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
      Subgroup.centralizer (fsuU T V : Set G)) = 32 := by
    rw [he, Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj m).injective, hcardE]
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  have hVU : V ≤ fsuU T V := by
    rw [E.fsuU_eq]
    exact le_conjClosure V _
  have hVα : V ≤ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) := by
    rw [hl₀U]
    intro v hv
    rw [Quasithin.mem_conjSub]
    have h1 := (Subgroup.mem_normalizer_iff.mp ((le_sup_left.trans hLTV) (inv_mem hl₀)) v).mp hv
    rw [inv_inv] at h1
    exact hVU h1
  have hVC : V ≤ Subgroup.centralizer (fsuU T V : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => fsuU_comm E.S.hyp hu (hVU hv)
  refine ⟨le_inf hVα hVC, ?_⟩
  have h4 := Subgroup.relIndex_mul_card V (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
    Subgroup.centralizer (fsuU T V : Set G))
  rw [inf_eq_left.mpr (le_inf hVα hVC), hV8, hcard] at h4
  omega

end Ctx7153

end CFSG.Quasithin.H13.L32A
