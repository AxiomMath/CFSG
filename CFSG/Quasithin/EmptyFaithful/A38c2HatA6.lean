module

public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.EmptyFaithful.S153F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem hatA6ProperThreePart_holds : HatA6ProperThreePart := by
  intro G _ _ L S₀ X hL hS hS₀X hXL hXne h27
  have hQcard := card_quotPCore_of_isHatA6Block hL
  obtain ⟨-, ⟨hqs, hZ3, -⟩, -, -⟩ := hL
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let X' : Subgroup ↥L := X.subgroupOf L
  have hNle : CFSG.pCore 2 ↥L ≤ X' := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := by
      refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
      assumption
    exact hS₀X (hS.pCoreOf_le hx')
  let H : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := X'.map π
  have hHne : H ≠ ⊤ := by
    intro htop
    apply hXne
    have : X' = ⊤ := by
      rw [eq_top_iff]
      intro l _
      have hl : π l ∈ H := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hxl⟩ := hl
      have h1 : x⁻¹ * l ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hxl
      have e : l = x * (x⁻¹ * l) := by group
      rw [e]
      exact X'.mul_mem hx (hNle h1)
    exact le_antisymm hXL (Subgroup.subgroupOf_eq_top.mp this)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hKer : Nat.card (π.comp X'.subtype).ker = Nat.card (CFSG.pCore 2 ↥L) := by
    have : (π.comp X'.subtype).ker = (CFSG.pCore 2 ↥L).subgroupOf X' := by
      ext x
      simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  have hRange : (π.comp X'.subtype).range = H := by
    ext y
    simp only [MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_map, H]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hXcard : Nat.card X = 2 ^ k * Nat.card H := by
    have h1 := Subgroup.card_ker_mul_card_range (π.comp X'.subtype)
    rw [hKer, hRange, hk] at h1
    have h2 : Nat.card X' = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv
    rw [← h2]
    exact h1.symm
  have hLcard : Nat.card ↥L = 1080 * 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
    rw [hQcard, hk] at h1
    exact h1
  have h8 : 8 ∣ Nat.card H := by
    have hidx : Odd (S₀.subgroupOf L).index := Nat.odd_iff.mpr (by
      have := hS.2.2
      omega)
    have hS0 : Nat.card S₀ * (S₀.subgroupOf L).index = Nat.card ↥L := by
      have h1 := (S₀.subgroupOf L).card_mul_index
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv] at h1
    have hd : 2 ^ (k + 3) ∣ Nat.card S₀ * (S₀.subgroupOf L).index := by
      rw [hS0, hLcard, pow_add]
      exact ⟨135, by ring⟩
    have hcop : Nat.Coprime (2 ^ (k + 3)) (S₀.subgroupOf L).index :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hidx)
    have h2 : 2 ^ (k + 3) ∣ Nat.card S₀ := hcop.dvd_of_dvd_mul_right hd
    have h3 : 2 ^ (k + 3) ∣ Nat.card X := h2.trans (Subgroup.card_dvd_of_le hS₀X)
    rw [hXcard, pow_add] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h3
  have h27H : 27 ∣ Nat.card H := by
    rw [hXcard] at h27
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 27 2)).dvd_of_dvd_mul_left h27
  have h216 : 216 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 27) h8 h27H
  have hHdvd : Nat.card H ∣ 1080 := hQcard ▸ Subgroup.card_subgroup_dvd_card H
  have hH216 : Nat.card H = 216 := by
    obtain ⟨m, hm⟩ := h216
    rw [hm] at hHdvd
    have hm5 : m ≤ 5 := by
      have := Nat.le_of_dvd (by norm_num) hHdvd
      omega
    interval_cases m
    · exact absurd hHdvd (by decide)
    · omega
    · exact absurd hHdvd (by decide)
    · exact absurd hHdvd (by decide)
    · exact absurd hHdvd (by decide)
    · exact absurd (Subgroup.eq_top_of_card_eq H (by rw [hm, hQcard])) hHne
  have hidx5 : H.index = 5 := by
    have := H.card_mul_index
    rw [hH216, hQcard] at this
    omega
  have hdvd := H.index_normalCore_dvd_factorial_index
  rw [hidx5] at hdvd
  have hcore : H.normalCore ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (H.normalCore_normal) with h | h
    · exact absurd (eq_top_iff.mpr (h ▸ H.normalCore_le)) hHne
    · exact h
  have hc3 : Nat.card H.normalCore ≤ 3 := by
    have := Subgroup.card_dvd_of_le hcore
    rw [hZ3] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hi : H.normalCore.index ≤ 120 := Nat.le_of_dvd (by norm_num) (by simpa [Nat.factorial] using hdvd)
  have hmul := H.normalCore.card_mul_index
  rw [hQcard] at hmul
  have := Nat.mul_le_mul hc3 hi
  omega

end CFSG.Quasithin
