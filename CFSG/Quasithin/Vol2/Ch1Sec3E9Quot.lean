module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Group
public import CFSG.Quasithin.Vol2.Ch1Sec3Solvable
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

omit [Finite G] in
theorem mem_pCoreOf_iff {x : G} (hx : x ∈ H) :
    x ∈ pCoreOf 2 H ↔ (⟨x, hx⟩ : H) ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem mem_sup_of_mem_modO2Image {Y : Subgroup G} {x : G} (hx : x ∈ H)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩ ∈ modO2Image H Y) :
    x ∈ Y ⊔ pCoreOf 2 H := by
  obtain ⟨y, hy, hyx⟩ := h
  have hker : y⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact hyx
  have h1 : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
    rw [mem_pCoreOf_iff (H.mul_mem (H.inv_mem y.2) hx)]
    exact hker
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hy h1

theorem pCoreOf_le_normalizer_of_mem_cComp {L : Subgroup G} (hL : L ∈ cComp H) :
    pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have h := (cComp_commutator_perfectCore hL (pCoreOf_le 2 H) (isSolvable_pCoreOf_two H)
    (hLH.trans (le_normalizer_pCoreOf 2 H))).1
  exact Subgroup.le_normalizer_iff_commutator_le_left.mpr h

theorem mem_of_mem_modO2Image {Y : Subgroup G} (hO : pCoreOf 2 H ≤ Subgroup.normalizer (Y : Set G))
    {x : G} (hx : x ∈ H) (hx3 : x ^ 3 = 1)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩ ∈ modO2Image H Y) : x ∈ Y :=
  mem_of_mem_sup_of_pow_three_eq_one (pCoreOf_isPGroup 2 H) hO (mem_sup_of_mem_modO2Image hx h) hx3

theorem inf_pCoreOf_eq_bot {Y : Subgroup G} (hexp : ∀ a ∈ Y, a ^ 3 = 1) :
    Y ⊓ pCoreOf 2 H = ⊥ := by
  have hY : IsPGroup 3 Y := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y (pCoreOf 2 H) hY
    (pCoreOf_isPGroup 2 H)).eq_bot

omit [Finite G] in
theorem eq_of_mk_eq {Y : Subgroup G} (hY : Y ⊓ pCoreOf 2 H = ⊥) {a b : G} (ha : a ∈ Y)
    (hb : b ∈ Y) (haH : a ∈ H) (hbH : b ∈ H)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨a, haH⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨b, hbH⟩) : a = b := by
  have hker : (⟨a, haH⟩ : H)⁻¹ * ⟨b, hbH⟩ ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp h
  have h1 : a⁻¹ * b ∈ pCoreOf 2 H := by
    rw [mem_pCoreOf_iff (H.mul_mem (H.inv_mem haH) hbH)]
    exact hker
  have h2 : a⁻¹ * b ∈ Y ⊓ pCoreOf 2 H := ⟨Y.mul_mem (Y.inv_mem ha) hb, h1⟩
  rw [hY, Subgroup.mem_bot] at h2
  calc a = a * (a⁻¹ * b) := by rw [h2, mul_one]
    _ = b := by group

omit [Finite G] in
theorem card_modO2Image {Y : Subgroup G} (hYH : Y ≤ H) (hY : Y ⊓ pCoreOf 2 H = ⊥) :
    Nat.card (modO2Image H Y) = Nat.card Y := by
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hinf : Y.subgroupOf H ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', eq_bot_iff]
    rintro ⟨x, hxH⟩ ⟨hxY, hxO⟩
    have h1 : x ∈ Y ⊓ pCoreOf 2 H := ⟨hxY, (mem_pCoreOf_iff hxH).mpr hxO⟩
    rw [hY, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  rw [modO2Image, Ch1Sec3.card_map_of_inf_ker_eq_bot hinf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv

omit [Finite G] in
theorem mk_mem_modO2Image {Y : Subgroup G} {x : G} (hxY : x ∈ Y) (hxH : x ∈ H) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈ modO2Image H Y :=
  ⟨⟨x, hxH⟩, hxY, rfl⟩

omit [Finite G] in
theorem modO2Image_mono {Y Z : Subgroup G} (h : Y ≤ Z) : modO2Image H Y ≤ modO2Image H Z :=
  Subgroup.map_mono fun _ hx => h hx

end CFSG.Quasithin.P134
