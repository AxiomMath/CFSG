module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordSpecK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

private theorem movModel_action {T₀ H : Subgroup P10} {TL : List (List ℕ)} {D : KData} {m : MovW}
    (hH : Desc H D.K.lit) (hT : Desc T₀ TL) (huK : D.K.lit.contains m.u = true)
    (huT : TL.contains m.u = true) (hact : actB D.y m.u m.a m.b = true)
    {y : P10} (hyc : code y = D.y) :
    ∃ u ∈ H ⊓ T₀, u ∈ normalizer (zpowers y : Set P10) ∧ u * y * u⁻¹ ≠ y := by
  obtain ⟨u, huH, huc⟩ := hH.surj m.u (List.contains_iff_mem.mp huK)
  obtain ⟨t, htT, htc⟩ := hT.surj m.u (List.contains_iff_mem.mp huT)
  have hut : u = t := code_injective (huc.trans htc.symm)
  have hact' := hact
  simp only [actB, Bool.and_eq_true, beq_iff_eq] at hact'
  obtain ⟨⟨huy0, hyu0⟩, hya⟩ := hact'
  have huy : u * y = y ^ m.a * u := by
    have h := huy0
    rw [← huc, ← hyc, cpow_eq_code] at h
    exact code_mul_eq_iff.mp h
  have hyu : y * u = u * y ^ m.b := by
    have h := hyu0
    rw [← huc, ← hyc, cpow_eq_code] at h
    exact code_mul_eq_iff.mp h
  have hya' : y ^ m.a ≠ y := by
    have h := hya
    rw [← hyc, cpow_eq_code, bne_iff_ne] at h
    exact fun hh => h (by rw [hh])
  have hconj1 : u * y * u⁻¹ = y ^ m.a := by
    rw [huy]
    group
  have hconj2 : u⁻¹ * y * u = y ^ m.b := by
    calc u⁻¹ * y * u = u⁻¹ * (y * u) := by group
      _ = u⁻¹ * (u * y ^ m.b) := by rw [hyu]
      _ = y ^ m.b := by group
  have hnormu : u ∈ normalizer (zpowers y : Set P10) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨n, rfl⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨(m.a : ℤ) * n, ?_⟩
      rw [zpow_mul, zpow_natCast, ← hconj1, conj_zpow]
    · rintro ⟨n, hn⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨(m.b : ℤ) * n, ?_⟩
      have hx' : x = u⁻¹ * y ^ n * u := by
        calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
          _ = u⁻¹ * y ^ n * u := by rw [← hn]
      rw [hx', zpow_mul, zpow_natCast, ← hconj2]
      simpa only [inv_inv] using conj_zpow (a := u⁻¹) (b := y) (i := n)
  exact ⟨u, ⟨huH, by rw [hut]; exact htT⟩, hnormu, by rw [hconj1]; exact hya'⟩

private theorem movModel_of_check {L₀ T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {D : KData} (hD : D.check TL = true)
    (hgens : ∀ c ∈ D.K.gc, ∃ x ∈ (L₀ : Set P10), code x = c)
    {E : Subgroup P10} {L : List (List ℕ)} (hE : Desc E L) {m : MovW}
    (hm : movCheck TL D L m = true) :
    ∃ (H N : Subgroup P10) (y : P10), H ≤ L₀ ∧ Desc H D.K.lit ∧ Desc N D.N2.lit ∧
      N ≤ pCoreOf 2 H ∧ code y = D.y ∧ Coord.MovModel L₀ T₀ E H (zpowers y) D.p := by
  obtain ⟨hnormE, huK, huT, hact, hthree⟩ := by
    simpa only [movCheck, Bool.and_eq_true, and_assoc] using hm
  obtain ⟨H, hHle, hH, ⟨N, hN, hNle⟩, htwo⟩ := kdata_spec hT hT2 hD hgens
  have hyK : D.K.lit.contains D.y = true := by
    have h1 := hD
    simp only [KData.check, Bool.and_eq_true, and_assoc] at h1
    exact h1.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨y, -, hyc⟩ := hH.surj D.y (List.contains_iff_mem.mp hyK)
  obtain ⟨u, huHT, hnormu, hya'⟩ := movModel_action hH hT huK huT hact hyc
  refine ⟨H, N, y, hHle, hH, hN, hNle, hyc, ?_⟩
  refine ⟨hHle, ?_, (htwo y hyc).1, (htwo y hyc).2,
    ⟨u, ⟨huHT, hnormu⟩, y, Subgroup.mem_zpowers y, hya'⟩, ?_⟩
  · intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact normB_spec hE hH hnormE he hh
    · intro hh
      have h2 := normB_spec hE hH hnormE (inv_mem he) hh
      convert h2 using 1
      group
  · rw [← hyc] at hthree
    exact three_spec hT hthree

private theorem all_comm_of_le_centralizer {E Es₀ : Subgroup P10} {L Est : List (List ℕ)}
    (hE : Desc E L) (hEst : Desc Es₀ Est) (hEc : E ≤ centralizer (Es₀ : Set P10)) :
    (L.all fun x => Est.all (ccomm x)) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro e he
  obtain ⟨x', hx'E, rfl⟩ := hE.surj x hx
  obtain ⟨e', he'E, rfl⟩ := hEst.surj e he
  exact ccomm_iff.mpr (Subgroup.mem_centralizer_iff.mp (hEc hx'E) e' he'E).symm

private theorem star_core {Es₀ H N : Subgroup P10} {Est : List (List ℕ)} {D : KData}
    (hEst : Desc Es₀ Est) (hN : Desc N D.N2.lit) (hNle : N ≤ pCoreOf 2 H)
    {y : P10} (hyc : code y = D.y) (hcard : Nat.card (zpowers y) = 3)
    (hstarall : (Est.all fun e => cinvol e && (List.range 3).all fun j =>
      D.N2.lit.contains
        (cmul (cmul (cmul e (cpow D.y j)) e) (cpow D.y (3 - j)))) = true) :
    ∀ e ∈ Es₀, ∀ x ∈ zpowers y, e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  intro e he x hx
  have hest : code e ∈ Est := (hEst.mem e).mp he
  have hest' := (List.all_eq_true.mp hstarall) (code e) hest
  simp only [Bool.and_eq_true] at hest'
  have heinvol : e * e = 1 := cinvol_iff.mp hest'.1
  have horder : orderOf y = 3 := by rw [← Nat.card_zpowers, hcard]
  rw [mem_zpowers_iff_mem_range_orderOf, horder] at hx
  obtain ⟨j, hj, hxj⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hj
  have hxinv : x⁻¹ = y ^ (3 - j) := by
    have hmul : y ^ j * y ^ (3 - j) = 1 := by
      have hj' : j + (3 - j) = 3 := by omega
      rw [← pow_add, hj', ← horder, pow_orderOf_eq_one]
    rw [← hxj]
    exact inv_eq_of_mul_eq_one_right hmul
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right heinvol
  have hcx : code x = cpow D.y j := by
    rw [← hxj, code_pow, hyc]
  have hcxinv : code x⁻¹ = cpow D.y (3 - j) := by
    rw [hxinv, code_pow, hyc]
  have hceinv : code e⁻¹ = code e := by
    rw [heinv]
  have hcode : code (e * x * e⁻¹ * x⁻¹) =
      cmul (cmul (cmul (code e) (cpow D.y j)) (code e)) (cpow D.y (3 - j)) := by
    simp only [code_mul, hcx, hcxinv, hceinv]
  have hmemN2 : cmul (cmul (cmul (code e) (cpow D.y j)) (code e)) (cpow D.y (3 - j)) ∈
      D.N2.lit :=
    List.contains_iff_mem.mp ((List.all_eq_true.mp hest'.2) j (List.mem_range.mpr hj))
  exact hNle ((hN.mem _).mpr (hcode.symm ▸ hmemN2))

theorem mov_spec {L₀ T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {Hs : List KData} (hHs : ∀ D ∈ Hs, D.check TL = true)
    (hHg : ∀ D ∈ Hs, ∀ c ∈ D.K.gc, ∃ x ∈ (L₀ : Set P10), code x = c)
    {El : List (List (List ℕ))} {ms : List MovW} (h : movAll TL Hs El ms = true)
    {E : Subgroup P10} {L : List (List ℕ)} (hL : L ∈ El) (hE : Desc E L) :
    ∃ (H Xh : Subgroup P10) (p : ℕ), Coord.MovModel L₀ T₀ E H Xh p := by
  obtain ⟨hlen, hall⟩ := by
    simpa only [movAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] using h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have hms : i < ms.length := hlen ▸ hi
  let m : MovW := ms[i]
  have hzip : (El[i], m) ∈ El.zip ms := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, hlen, min_self]
      exact hms
    · rw [List.getElem_zip]
  have hpass := hall (El[i], m) hzip
  let D : KData := Hs.getD m.k KData.dflt
  have hDmem : D ∈ Hs := getD_mem_of_lt KData.dflt hpass.1
  have hmc : movCheck TL D (El[i]) m = true := hpass.2
  obtain ⟨H, -, y, -, -, -, -, -, hmodel⟩ :=
    movModel_of_check hT hT2 (hHs D hDmem) (hHg D hDmem) hE hmc
  exact ⟨H, zpowers y, D.p, hmodel⟩

theorem star_spec {L₀ T₀ Es₀ : Subgroup P10} {TL Est : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) (hEst : Desc Es₀ Est) {Hs : List KData}
    (hHs : ∀ D ∈ Hs, D.check TL = true)
    (hHg : ∀ D ∈ Hs, ∀ c ∈ D.K.gc, ∃ x ∈ (L₀ : Set P10), code x = c)
    {El : List (List (List ℕ))} {ms : List MovW} (h : starAll TL Hs Est El ms = true)
    {E : Subgroup P10} {L : List (List ℕ)} (hL : L ∈ El) (hE : Desc E L)
    (hEc : E ≤ centralizer (Es₀ : Set P10)) :
    ∃ H Xh : Subgroup P10, Coord.MovModel L₀ T₀ E H Xh 3 ∧ Es₀ ≤ normalizer (H : Set P10) ∧
      ∀ e ∈ Es₀, ∀ x ∈ Xh, e * x * e⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨hlen, hall⟩ := by
    simpa only [starAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
      using h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have hcommL := all_comm_of_le_centralizer hE hEst hEc
  have hms : i < ms.length := hlen ▸ hi
  let m : MovW := ms[i]
  have hzip : (El[i], m) ∈ El.zip ms := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, hlen, min_self]
      exact hms
    · rw [List.getElem_zip]
  have hpass := hall (El[i], m) hzip
  have hpass' : (decide (m.k < Hs.length) &&
      starCheck TL (Hs.getD m.k KData.dflt) Est (El[i]) m) = true := by
    have h1 := hpass
    simp only [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · rw [hcommL] at h1
      exact Bool.noConfusion h1
    · exact h1
  have hpass'' := hpass'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpass''
  have hk : m.k < Hs.length := hpass''.1
  have hstar : starCheck TL (Hs.getD m.k KData.dflt) Est (El[i]) m = true := hpass''.2
  let D : KData := Hs.getD m.k KData.dflt
  have hDmem : D ∈ Hs := getD_mem_of_lt KData.dflt hk
  have hD : D.check TL = true := hHs D hDmem
  obtain ⟨hp, hmc, hnormEst, hstarall⟩ := by
    simpa only [starCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] using hstar
  obtain ⟨H, N, y, -, hH, hN, hNle, hyc, hmodel⟩ :=
    movModel_of_check hT hT2 hD (hHg D hDmem) hE hmc
  rw [hp] at hmodel
  have hnH : Es₀ ≤ normalizer (H : Set P10) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact normB_spec hEst hH hnormEst he hh
    · intro hh
      have h2 := normB_spec hEst hH hnormEst (inv_mem he) hh
      convert h2 using 1
      group
  refine ⟨H, zpowers y, hmodel, hnH, ?_⟩
  exact star_core hEst hN hNle hyc hmodel.card hstarall

end CFSG.LocalAnalysis.WeakClosure81.CoordA6
