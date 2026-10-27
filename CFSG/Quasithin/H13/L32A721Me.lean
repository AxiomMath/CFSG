module

public import CFSG.Quasithin.H13.L32A720c
public import CFSG.Quasithin.H13.L32A721Ma
public import CFSG.Quasithin.H13.L32A721Mb

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Iota

variable {G : Type} [Group G] [Finite G] {T V : Subgroup G}

@[expose] noncomputable def iotaK (hle : hz T V ≤ mK T V)
    (hO : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (mK T V)) :
    (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) →* (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) :=
  QuotientGroup.map _ _ (Subgroup.inclusion hle) fun x hx => by
    rw [Subgroup.mem_comap]
    exact C2Six.mem_pCore_two_iff.mpr (hO (C2Six.mem_pCore_two_iff.mp hx))

omit [Finite G] in
theorem iotaK_mk (hle : hz T V ≤ mK T V) (hO : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (mK T V))
    (h : ↥(hz T V)) :
    iotaK hle hO (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) h) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) (Subgroup.inclusion hle h) := rfl

omit [Finite G] in
theorem iotaK_injective (hle : hz T V ≤ mK T V) (hO : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (mK T V))
    (hO' : pCoreOf 2 (mK T V) ≤ pCoreOf 2 (hz T V)) : Function.Injective (iotaK hle hO) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [MonoidHom.mem_ker, iotaK_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    C2Six.mem_pCore_two_iff] at hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    C2Six.mem_pCore_two_iff]
  exact hO' hx

omit [Finite G] in
theorem map_iotaK (hle : hz T V ≤ mK T V) (hO : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (mK T V))
    {X : Subgroup G} (hX : X ≤ hz T V) :
    (modO2Image (hz T V) X).map (iotaK hle hO) = modO2Image (mK T V) X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_modO2Image_iff.mp hx
    exact mem_modO2Image_iff.mpr ⟨Subgroup.inclusion hle h, hh, rfl⟩
  · intro hy
    obtain ⟨g, hg, rfl⟩ := mem_modO2Image_iff.mp hy
    refine ⟨QuotientGroup.mk' _ ⟨g, hX hg⟩, mem_modO2Image_iff.mpr ⟨⟨g, hX hg⟩, hg, rfl⟩, ?_⟩
    rw [iotaK_mk]
    rfl

omit [Finite G] in
theorem mem_map_iotaK (hle : hz T V ≤ mK T V) (hO : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (mK T V))
    {X : Subgroup G} (hX : X ≤ hz T V) {y : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hy : y ∈ modO2Image (mK T V) X) :
    ∃ x ∈ modO2Image (hz T V) X, iotaK hle hO x = y := by
  rw [← map_iotaK hle hO hX] at hy
  exact hy

end Iota

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

theorem iota_injective (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) :
    Function.Injective (iotaK E.hz_le_mK hO.ge) :=
  iotaK_injective E.hz_le_mK hO.ge hO.le

theorem center_kbar_eq (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) :
    (Subgroup.center ↥(modO2Image (mK T V) (kz T V))).map
      (modO2Image (mK T V) (kz T V)).subtype = modO2Image (mK T V) (l1 T L V) := by
  have hX := E.isPOnePlusTwo_kbar
  have hL1hz := E.l1_le_hz
  have hKhz : kz T V ≤ hz T V := oTwoUpper_le _
  have hle : modO2Image (mK T V) (l1 T L V) ≤ (Subgroup.center ↥(modO2Image (mK T V)
      (kz T V))).map (modO2Image (mK T V) (kz T V)).subtype := by
    intro x hx
    have hxK : x ∈ modO2Image (mK T V) (kz T V) := modO2Image_mono E.l1_le_kz_ctx hx
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, rfl⟩
    obtain ⟨x', hx', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge hL1hz hx
    obtain ⟨k', hk', hk'e⟩ := mem_map_iotaK E.hz_le_mK hO.ge hKhz k.2
    simp only [Subgroup.coe_mul]
    rw [← hk'e, ← map_mul, ← map_mul, E.comm_of_mem_l1dot x' hx' k' hk']
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Heis.card_center hX,
    ← map_iotaK E.hz_le_mK hO.ge hL1hz, Subgroup.card_map_of_injective (E.iota_injective hO),
    E.card_l1dot]

theorem r1bar_eq (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) :
    modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)) = modO2Image (mK T V) T ⊓
      Subgroup.centralizer (modO2Image (mK T V) (l1 T L V) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hRhz : pCoreOf 2 (l1 T L V ⊔ T) ≤ hz T V := E.r1_le_hz
  have hinj := E.iota_injective hO
  apply le_antisymm
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge hRhz hr
    rw [hR1C] at hr'
    obtain ⟨hr'T, hr'C⟩ := Subgroup.mem_inf.mp hr'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← map_iotaK E.hz_le_mK hO.ge E.t_le_hz]
      exact ⟨r', hr'T, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨l', hl', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge E.l1_le_hz hl
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hr'C l' hl']
  · intro r hr
    obtain ⟨hrT, hrC⟩ := Subgroup.mem_inf.mp hr
    obtain ⟨r', hr', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge E.t_le_hz hrT
    rw [← map_iotaK E.hz_le_mK hO.ge hRhz, hR1C]
    refine ⟨r', Subgroup.mem_inf.mpr ⟨hr', ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hrC _
      (by rw [← map_iotaK E.hz_le_mK hO.ge E.l1_le_hz]; exact ⟨l, hl, rfl⟩)

theorem exists_upsilon (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V)) :
    ∃ υ ∈ modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)), υ ^ 2 ≠ 1 ∧ υ ^ 4 = 1 ∧
      (∀ r ∈ modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)), r ^ 2 = 1 → r ≠ 1 → r = υ ^ 2) ∧
      (∀ x ∈ modO2Image (mK T V) (kz T V),
        υ ^ 2 * x * (υ ^ 2)⁻¹ * x ∈ modO2Image (mK T V) (l1 T L V)) := by
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  obtain ⟨-, y, hyT, hyC, hy2, hy4, huniq, hinv⟩ := E.exists_y
  have hRhz : pCoreOf 2 (l1 T L V ⊔ T) ≤ hz T V := E.r1_le_hz
  have hKhz : kz T V ≤ hz T V := oTwoUpper_le _
  have hinj := E.iota_injective hO
  have hyR : y ∈ modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)) := by
    rw [hR1C]; exact Subgroup.mem_inf.mpr ⟨hyT, hyC⟩
  refine ⟨iotaK E.hz_le_mK hO.ge y,
    by rw [← map_iotaK E.hz_le_mK hO.ge hRhz]; exact ⟨y, hyR, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ne_eq, ← map_one (iotaK E.hz_le_mK hO.ge)]
    exact fun h => hy2 (hinj h)
  · rw [← map_pow, hy4, map_one]
  · intro r hr hr2 hr1
    obtain ⟨r', hr', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge hRhz hr
    rw [hR1C] at hr'
    obtain ⟨hr'T, hr'C⟩ := Subgroup.mem_inf.mp hr'
    have hr'2 : r' ^ 2 = 1 := hinj (by rw [map_pow, hr2, map_one])
    have hr'1 : r' ≠ 1 := fun h => hr1 (by rw [h, map_one])
    rw [huniq r' hr'T hr'C hr'2 hr'1, map_pow]
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := mem_map_iotaK E.hz_le_mK hO.ge hKhz hx
    rw [← map_iotaK E.hz_le_mK hO.ge E.l1_le_hz]
    refine ⟨_, hinv x' hx', ?_⟩
    simp only [map_mul, map_inv, map_pow]

theorem isCyclic_centralizer_kbar (hP : IsPGroup 3 ↥(Subgroup.centralizer
    ((modO2Image (mK T V) (kz T V) : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
      Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))))) :
    IsCyclic ↥(Subgroup.centralizer ((modO2Image (mK T V) (kz T V) :
      Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := E.isPOnePlusTwo_kbar
  set X := modO2Image (mK T V) (kz T V) with hXdef
  set C := Subgroup.centralizer (X : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) with hC
  have hZ : ∀ c : ↥C, c ^ 3 = 1 → (c : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) ∈
      (Subgroup.center ↥X).map X.subtype := fun c hc =>
    mem_center_of_pow_three E.pRank_gamma_le hX c.2 (by simpa using congrArg Subtype.val hc)
  by_contra hnc
  have : Fact (IsPGroup 3 ↥C) := ⟨hP⟩
  obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hpow : ∀ s : ↥S, (s : ↥C) ^ 3 = 1 := by
    intro s
    have h1 : s ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSel.exponent_dvd_p s
    simpa using congrArg (fun t : ↥S => (t : ↥C)) h1
  let f : ↥S → ↥((Subgroup.center ↥X).map X.subtype) := fun s =>
    ⟨((s : ↥C) : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)), hZ _ (hpow s)⟩
  have hf : Function.Injective f := by
    intro s t hst
    have := congrArg Subtype.val hst
    exact Subtype.ext (Subtype.ext this)
  have hle := Nat.card_le_card_of_injective f hf
  rw [hS9, Subgroup.card_map_of_injective X.subtype_injective, Heis.card_center hX] at hle
  norm_num at hle

theorem comm_r1bar_centralizer (hO : pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V))
    (hP : IsPGroup 3 ↥(Subgroup.centralizer
      ((modO2Image (mK T V) (kz T V) : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))))
    {r : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hr : r ∈ modO2Image (mK T V) (pCoreOf 2 (l1 T L V ⊔ T)))
    {c : ↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)}
    (hc : c ∈ Subgroup.centralizer ((modO2Image (mK T V) (kz T V) :
      Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))) :
    r * c * r⁻¹ = c := by
  have hX := E.isPOnePlusTwo_kbar
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  set X := modO2Image (mK T V) (kz T V) with hXdef
  set C := Subgroup.centralizer (X : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) with hC
  have hcyc := E.isCyclic_centralizer_kbar hP
  have hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hrC : r ∈ Subgroup.centralizer (modO2Image (mK T V) (l1 T L V) :
      Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    rw [E.r1bar_eq hO] at hr
    exact hr.2
  have hrN : r ∈ Subgroup.normalizer (C : Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    refine mem_normalizer_of_conj_mem_721 fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : r⁻¹ * x * r⁻¹⁻¹ ∈ X := (inferInstance : X.Normal).conj_mem x hx r⁻¹
    have e := Subgroup.mem_centralizer_iff.mp hy _ hx'
    calc x * (r * y * r⁻¹) = r * ((r⁻¹ * x * r⁻¹⁻¹) * y) * r⁻¹ := by group
      _ = r * (y * (r⁻¹ * x * r⁻¹⁻¹)) * r⁻¹ := by rw [e]
      _ = r * y * r⁻¹ * x := by group
  have hRhz : pCoreOf 2 (l1 T L V ⊔ T) ≤ hz T V := E.r1_le_hz
  obtain ⟨r', hr', rfl⟩ := mem_modO2Image_iff.mp hr
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (l1 T L V ⊔ T)) ⟨r', hr'⟩
  have hk' : (QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) r') ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : r' ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  refine conj_eq_of_coprime hCc hP hrN (m := 2 ^ k) (Nat.Coprime.pow_right _ (by norm_num))
    (fun y _ => by rw [hk', one_mul, inv_one, mul_one]) (fun y hy hy3 => ?_) hc
  have hyZ := mem_center_of_pow_three E.pRank_gamma_le hX hy hy3
  rw [E.center_kbar_eq hO] at hyZ
  rw [← Subgroup.mem_centralizer_iff.mp hrC y hyZ, mul_inv_cancel_right]

end Ctx7153

end CFSG.Quasithin.H13.L32A
