module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeAmb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem seven_eight_core_lift_coe_mul {H : Subgroup G} {Q : Type} [Group Q]
    (φ : ↥H →* Q) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    φ ⟨a * b, H.mul_mem ha hb⟩ = φ ⟨a, ha⟩ * φ ⟨b, hb⟩ := by
  rw [show (⟨a * b, H.mul_mem ha hb⟩ : ↥H) = ⟨a, ha⟩ * ⟨b, hb⟩ from Subtype.ext rfl,
    map_mul]

private theorem seven_eight_core_lift_coe_inv {H : Subgroup G} {Q : Type} [Group Q]
    (φ : ↥H →* Q) {a : G} (ha : a ∈ H) :
    φ ⟨a⁻¹, H.inv_mem ha⟩ = (φ ⟨a, ha⟩)⁻¹ := by
  rw [show (⟨a⁻¹, H.inv_mem ha⟩ : ↥H) = ⟨a, ha⟩⁻¹ from Subtype.ext rfl, map_inv]

private theorem seven_eight_core_lift_coe_pow {H : Subgroup G} {Q : Type} [Group Q]
    (φ : ↥H →* Q) {a : G} (ha : a ∈ H) (n : ℕ) :
    φ ⟨a ^ n, H.pow_mem ha n⟩ = (φ ⟨a, ha⟩) ^ n := by
  rw [show (⟨a ^ n, H.pow_mem ha n⟩ : ↥H) = ⟨a, ha⟩ ^ n from Subtype.ext rfl, map_pow]

theorem Hyp73.exists_isHallCompl_le_kSub {V H E J : Subgroup G} (h : Hyp73 V H E J)
    {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {Xb : Subgroup Q}
    (hXK : Xb ≤ barSub H φ (kSub V H E)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ x ∈ Xb, x ^ p = 1) :
    ∃ Y : Subgroup G, IsHallCompl V H E J (barPre H φ Xb) Y ∧ Y ≤ kSub V H E := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  have hHnormK : H ≤ Subgroup.normalizer (kSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hKH (kSub_subgroupOf_normal h.le h.normal h.omega_le)
  have hJ'KH : kSub V H E ⊓ J ≤ H := inf_le_left.trans hKH
  have hHnormJ' : H ≤ Subgroup.normalizer ((kSub V H E ⊓ J : Subgroup G) : Set G) := by
    intro x hx
    have hJx : x ∈ Subgroup.normalizer (J : Set G) := hHnormJ hx
    have hKx : x ∈ Subgroup.normalizer (kSub V H E : Set G) := hHnormK hx
    rw [Subgroup.mem_normalizer_iff] at hJx hKx ⊢
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨(hKx y).mp h.1, (hJx y).mp h.2⟩,
      fun h => ⟨(hKx y).mpr h.1, (hJx y).mpr h.2⟩⟩
  haveI hJ'n : ((kSub V H E ⊓ J).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ'KH).2 hHnormJ'
  have hJ'X' : kSub V H E ⊓ J ≤ barPre H φ Xb ⊓ kSub V H E :=
    le_inf (inf_le_right.trans (le_barPre hJH hφ Xb)) inf_le_left
  have hX'H : barPre H φ Xb ⊓ kSub V H E ≤ H :=
    inf_le_left.trans (barPre_le H φ Xb)
  have hX'normJ' : barPre H φ Xb ⊓ kSub V H E ≤
      Subgroup.normalizer ((kSub V H E ⊓ J : Subgroup G) : Set G) :=
    hX'H.trans hHnormJ'
  haveI hJ'X'n : ((kSub V H E ⊓ J).subgroupOf (barPre H φ Xb ⊓ kSub V H E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ'X').2 hX'normJ'
  have hexp' : ∀ y ∈ barPre H φ Xb ⊓ kSub V H E, y ^ p ∈ kSub V H E ⊓ J := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyX, hyK⟩ := hy
    have hyH : y ∈ H := barPre_le H φ Xb hyX
    have hyXb : φ ⟨y, hyH⟩ ∈ Xb := (mem_barPre.mp hyX).2
    refine ⟨(kSub V H E).pow_mem hyK p, ?_⟩
    have h1 : φ ⟨y ^ p, H.pow_mem hyH p⟩ = 1 := by
      rw [seven_eight_core_lift_coe_pow φ hyH p, hexp _ hyXb]
    exact (hφ.ker_iff ⟨y ^ p, H.pow_mem hyH p⟩).mp h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg := isPGroup_quotient_of_exp (J := kSub V H E ⊓ J)
    (Y := barPre H φ Xb ⊓ kSub V H E) hexp'
  have h76 : Hyp76 V H E (kSub V H E ⊓ J) ⊥ (barPre H φ Xb ⊓ kSub V H E) := by
    refine ⟨h.elemAbelian, h.ti, h.abelian, h.le, h.normal, h.omega_le,
      inf_le_right.trans h.pcore_le, hJ'n, ?_, ?_, hX'H, bot_le, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_inf (iSup₂_le fun U hU => inf_le_left.trans (le_kSub hU)) h.iSub_le
    · exact le_inf (inf_le_right.trans (le_barPre hJH hφ Xb)) inf_le_left
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
      have h1 : (kSub V H E ⊓ J).relIndex (barPre H φ Xb ⊓ kSub V H E) =
          Nat.card (↥(barPre H φ Xb ⊓ kSub V H E) ⧸
            (kSub V H E ⊓ J).subgroupOf (barPre H φ Xb ⊓ kSub V H E)) :=
        Subgroup.index_eq_card _
      rw [h1, hn]
      exact (hp.odd_of_ne_two hp2).pow
    · exact hpg.isNilpotent
    · intro a ha _
      rw [Subgroup.mem_bot] at ha
      rw [ha]
      exact (kSub V H E ⊓ J).one_mem
    · exact le_antisymm bot_le (iSup₂_le fun U _ => iSup_le fun h => h)
    · exact IsPGroup.of_bot
  obtain ⟨Y, hY⟩ := h76.exists_hallCompl
  have hYK : Y ≤ kSub V H E := hY.le_X.trans inf_le_right
  refine ⟨Y, ⟨hY.iSub_le, hY.le_X.trans inf_le_left, ?_, ?_⟩, hYK⟩
  · rw [show Y ⊓ J = Y ⊓ (kSub V H E ⊓ J) from by
      rw [← inf_assoc, inf_eq_left.mpr hYK], hY.inf_J]
  · refine le_antisymm (sup_le (hY.le_X.trans inf_le_left) (le_barPre hJH hφ Xb)) ?_
    intro g hg
    have hgH : g ∈ H := barPre_le H φ Xb hg
    have hgXb : φ ⟨g, hgH⟩ ∈ Xb := (mem_barPre.mp hg).2
    obtain ⟨k, hkK, hkφ⟩ := mem_barSub.mp (hXK hgXb)
    have hjH : (k : G)⁻¹ * g ∈ H := H.mul_mem (H.inv_mem k.2) hgH
    have hjφ : φ ⟨(k : G)⁻¹ * g, hjH⟩ = 1 := by
      rw [seven_eight_core_lift_coe_mul φ (H.inv_mem k.2) hgH,
        seven_eight_core_lift_coe_inv φ k.2, hkφ]
      simp
    have hjJ : (k : G)⁻¹ * g ∈ J := (hφ.ker_iff ⟨_, hjH⟩).mp hjφ
    have hkX : (k : G) ∈ barPre H φ Xb :=
      mem_barPre.mpr ⟨k.2, by rw [hkφ]; exact hgXb⟩
    have hkX' : (k : G) ∈ barPre H φ Xb ⊓ kSub V H E := ⟨hkX, hkK⟩
    have hle : Y ⊔ (kSub V H E ⊓ J) ≤ Y ⊔ J :=
      sup_le le_sup_left (inf_le_right.trans le_sup_right)
    have hkYJ : (k : G) ∈ Y ⊔ J := hle (hY.sup_J ▸ hkX')
    have hg_eq : g = (k : G) * ((k : G)⁻¹ * g) := by group
    rw [hg_eq]
    exact (Y ⊔ J).mul_mem hkYJ (Subgroup.mem_sup_right hjJ)

theorem IsHallCompl.relIndex_inf_barPre {V H E J Y : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    {Xb : Subgroup Q} (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {Ab : Subgroup Q}
    (hAb : Ab ≤ Xb) : (iSub V H E).relIndex (Y ⊓ barPre H φ Ab) = Nat.card Ab := by
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH hJn
  have hAbX : barPre H φ Ab ≤ barPre H φ Xb := by
    intro a ha
    obtain ⟨haH, hab⟩ := mem_barPre.mp ha
    exact mem_barPre.mpr ⟨haH, hAb hab⟩
  have hJAb : J ≤ barPre H φ Ab := le_barPre hJH hφ Ab
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) :=
    hY.le_X.trans ((barPre_le H φ Xb).trans hHnormJ)
  have hBJsup : Y ⊓ barPre H φ Ab ⊔ J = barPre H φ Ab := by
    refine le_antisymm (sup_le inf_le_right hJAb) ?_
    intro a ha
    have haX : a ∈ Y ⊔ J := by
      rw [hY.sup_J]
      exact hAbX ha
    have ha' : a ∈ (↑Y : Set G) * (↑J : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y J hYN]
      exact haX
    rw [Set.mem_mul] at ha'
    obtain ⟨y, hyY, j, hjJ, hyj⟩ := ha'
    have hybar : y ∈ barPre H φ Ab := by
      have hy_eq : y = a * j⁻¹ := by rw [← hyj]; group
      rw [hy_eq]
      exact (barPre H φ Ab).mul_mem ha ((barPre H φ Ab).inv_mem (hJAb hjJ))
    have ha_eq : a = y * j := hyj.symm
    rw [ha_eq]
    exact (Y ⊓ barPre H φ Ab ⊔ J).mul_mem (Subgroup.mem_sup_left ⟨hyY, hybar⟩)
      (Subgroup.mem_sup_right hjJ)
  have hIJ : iSub V H E ≤ J := hY.inf_J ▸ inf_le_right
  have hIbar : iSub V H E ≤ barPre H φ Ab := hIJ.trans hJAb
  have hBJ : Y ⊓ barPre H φ Ab ⊓ J = iSub V H E := by
    rw [show Y ⊓ barPre H φ Ab ⊓ J = (Y ⊓ J) ⊓ barPre H φ Ab from by
      rw [inf_assoc, inf_comm (barPre H φ Ab) J, ← inf_assoc],
      hY.inf_J, inf_eq_left.mpr hIbar]
  calc (iSub V H E).relIndex (Y ⊓ barPre H φ Ab)
      = (Y ⊓ barPre H φ Ab ⊓ J).relIndex (Y ⊓ barPre H φ Ab) := by rw [hBJ]
    _ = J.relIndex (Y ⊓ barPre H φ Ab) := Subgroup.inf_relIndex_left _ _
    _ = J.relIndex (Y ⊓ barPre H φ Ab ⊔ J) :=
        (relIndex_sup_right_of_le_normalizer (K := Y ⊓ barPre H φ Ab) (N := J)
          (inf_le_left.trans hYN)).symm
    _ = J.relIndex (barPre H φ Ab) := by rw [hBJsup]
    _ = Nat.card Ab := relIndex_barPre hJH hφ Ab

theorem IsHallCompl.exists_mem_eq {V H E J Y : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    {Xb : Subgroup Q} (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {q : Q} (hq : q ∈ Xb) :
    ∃ y ∈ Y, ∃ hy : y ∈ H, φ ⟨y, hy⟩ = q := by
  obtain ⟨k, hk⟩ := hφ.surjective q
  have hkX : (k : G) ∈ barPre H φ Xb :=
    mem_barPre.mpr ⟨k.2, by rw [hk]; exact hq⟩
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH hJn
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) :=
    hY.le_X.trans ((barPre_le H φ Xb).trans hHnormJ)
  have hkYJ : (k : G) ∈ Y ⊔ J := by rw [hY.sup_J]; exact hkX
  have hk' : (k : G) ∈ (↑Y : Set G) * (↑J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y J hYN]
    exact hkYJ
  rw [Set.mem_mul] at hk'
  obtain ⟨y, hyY, j, hjJ, hyj⟩ := hk'
  have hjH : j ∈ H := hJH hjJ
  have hyH : y ∈ H := by
    have hy_eq : y = (k : G) * j⁻¹ := by rw [← hyj]; group
    rw [hy_eq]
    exact H.mul_mem k.2 (H.inv_mem hjH)
  refine ⟨y, hyY, hyH, ?_⟩
  have hy_eq : (⟨y, hyH⟩ : ↥H) = k * ⟨j, hjH⟩⁻¹ := by
    apply Subtype.ext
    show y = (k : G) * j⁻¹
    rw [← hyj]
    group
  rw [hy_eq, map_mul, map_inv]
  have hj1 : φ ⟨j, hjH⟩ = 1 := (hφ.ker_iff ⟨j, hjH⟩).mpr hjJ
  rw [hj1, inv_one, mul_one]
  exact hk

theorem IsHallCompl.barSub_inf_barPre {V H E J Y : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    {Xb : Subgroup Q} (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {Ab : Subgroup Q}
    (hAb : Ab ≤ Xb) : barSub H φ (Y ⊓ barPre H φ Ab) = Ab := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hx
    rw [Subgroup.mem_inf] at hk
    obtain ⟨hkh, hkAb⟩ := mem_barPre.mp hk.2
    rwa [show (⟨(k : G), hkh⟩ : ↥H) = k from Subtype.ext rfl] at hkAb
  · intro q hq
    obtain ⟨y, hyY, hyH, hyφ⟩ := hY.exists_mem_eq hφ hJH hJn (hAb hq)
    have hybar : y ∈ barPre H φ Ab :=
      mem_barPre.mpr ⟨hyH, by rw [hyφ]; exact hq⟩
    exact mem_barSub.mpr ⟨⟨y, hyH⟩, ⟨hyY, hybar⟩, hyφ⟩

theorem IsHallCompl.inf_barPre_le {V H E J Y : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {Xb : Subgroup Q}
    (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {T : Subgroup G} (hIT : iSub V H E ≤ T)
    (hTY : T ≤ Y) {Ab : Subgroup Q} (hAb : Ab ≤ barSub H φ T) : Y ⊓ barPre H φ Ab ≤ T := by
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyY, hybar⟩ := hy
  have hyH : y ∈ H := (mem_barPre.mp hybar).1
  have hyAb : φ ⟨y, hyH⟩ ∈ Ab := (mem_barPre.mp hybar).2
  obtain ⟨t, htT, htφ⟩ := mem_barSub.mp (hAb hyAb)
  have htyH : (t : G)⁻¹ * y ∈ H := H.mul_mem (H.inv_mem t.2) hyH
  have htyφ : φ ⟨(t : G)⁻¹ * y, htyH⟩ = 1 := by
    rw [seven_eight_core_lift_coe_mul φ (H.inv_mem t.2) hyH,
      seven_eight_core_lift_coe_inv φ t.2, htφ]
    simp
  have htyJ : (t : G)⁻¹ * y ∈ J := (hφ.ker_iff ⟨_, htyH⟩).mp htyφ
  have htyY : (t : G)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hTY htT)) hyY
  have htyI : (t : G)⁻¹ * y ∈ iSub V H E := by
    rw [← hY.inf_J]
    exact ⟨htyY, htyJ⟩
  have htyT : (t : G)⁻¹ * y ∈ T := hIT htyI
  have hy_eq : y = (t : G) * ((t : G)⁻¹ * y) := by group
  rw [hy_eq]
  exact T.mul_mem htT htyT

theorem IsHallCompl.commutator_zpowers_le_barSub {V H E J Y : Subgroup G} {Q : Type}
    [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) {Xb : Subgroup Q}
    (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {w : G} (hw : w ∈ H) :
    ⁅Xb, Subgroup.zpowers (φ ⟨w, hw⟩)⁆ ≤ barSub H φ ⁅Y, Subgroup.zpowers w⁆ := by
  rw [Subgroup.commutator_le]
  intro q hq r hr
  obtain ⟨y, hyY, hyH, hyφ⟩ := hY.exists_mem_eq hφ hJH hJn hq
  rw [Subgroup.mem_zpowers_iff] at hr
  obtain ⟨n, rfl⟩ := hr
  rw [← hyφ]
  have hcomm : ⁅φ ⟨y, hyH⟩, (φ ⟨w, hw⟩) ^ n⁆ =
      φ ⁅(⟨y, hyH⟩ : ↥H), (⟨w, hw⟩ : ↥H) ^ n⁆ := by
    rw [← map_zpow φ (⟨w, hw⟩ : ↥H) n,
      ← map_commutatorElement φ ⟨y, hyH⟩ ((⟨w, hw⟩ : ↥H) ^ n)]
  rw [hcomm]
  refine mem_barSub.mpr ⟨⁅(⟨y, hyH⟩ : ↥H), (⟨w, hw⟩ : ↥H) ^ n⁆, ?_, rfl⟩
  have hcoe : ((⁅(⟨y, hyH⟩ : ↥H), (⟨w, hw⟩ : ↥H) ^ n⁆ : ↥H) : G) = ⁅y, w ^ n⁆ := by
    change H.subtype ⁅(⟨y, hyH⟩ : ↥H), (⟨w, hw⟩ : ↥H) ^ n⁆ = ⁅y, w ^ n⁆
    rw [map_commutatorElement H.subtype, map_zpow]
    rfl
  rw [hcoe]
  exact Subgroup.commutator_mem_commutator hyY (Subgroup.zpow_mem_zpowers w n)

theorem barSub_map_conj {H : Subgroup G} {Q : Type} [Group Q] (φ : ↥H →* Q) (A : Subgroup G)
    (k : ↥H) :
    barSub H φ (A.map (MulAut.conj (k : G)).toMonoidHom) =
      (barSub H φ A).map (MulAut.conj (φ k)).toMonoidHom := by
  ext x
  rw [mem_barSub, Subgroup.mem_map]
  constructor
  · rintro ⟨h', hh', rfl⟩
    rw [Subgroup.mem_map] at hh'
    obtain ⟨a, ha, hak⟩ := hh'
    change MulAut.conj (k : G) a = (h' : G) at hak
    rw [MulAut.conj_apply] at hak
    have haH : a ∈ H := by
      have : a = (k : G)⁻¹ * (h' : G) * (k : G) := by rw [← hak]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem k.2) h'.2) k.2
    refine ⟨φ ⟨a, haH⟩, mem_barSub.mpr ⟨⟨a, haH⟩, ha, rfl⟩, ?_⟩
    change MulAut.conj (φ k) (φ ⟨a, haH⟩) = φ h'
    rw [MulAut.conj_apply]
    have ha_eq : (⟨a, haH⟩ : ↥H) = k⁻¹ * h' * k := by
      apply Subtype.ext
      show a = (k : G)⁻¹ * (h' : G) * (k : G)
      rw [← hak]
      group
    rw [ha_eq, map_mul, map_mul, map_inv]
    group
  · rintro ⟨b, hb, hbx⟩
    rw [mem_barSub] at hb
    obtain ⟨a, haA, haφ⟩ := hb
    refine ⟨⟨k * a * k⁻¹, H.mul_mem (H.mul_mem k.2 a.2) (H.inv_mem k.2)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨(a : G), haA, rfl⟩
    · change φ ⟨k * (a : G) * (k : G)⁻¹,
          H.mul_mem (H.mul_mem k.2 a.2) (H.inv_mem k.2)⟩ = x
      rw [← hbx, ← haφ]
      change φ ⟨k * (a : G) * (k : G)⁻¹,
          H.mul_mem (H.mul_mem k.2 a.2) (H.inv_mem k.2)⟩ = MulAut.conj (φ k) (φ a)
      rw [MulAut.conj_apply]
      rw [seven_eight_core_lift_coe_mul φ (H.mul_mem k.2 a.2) (H.inv_mem k.2),
        seven_eight_core_lift_coe_mul φ k.2 a.2, seven_eight_core_lift_coe_inv φ k.2]

end CFSG.LocalAnalysis.WeakClosure81
