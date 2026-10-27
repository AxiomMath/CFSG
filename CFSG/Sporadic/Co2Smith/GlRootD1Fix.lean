module

public import CFSG.Sporadic.Co2Smith.GlRootD1Phi
public import CFSG.Sporadic.Co2Smith.GlRootD1Core

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem d1Root_spec :
    (∀ r ∈ [0, 1, 2, 4, 5], ∀ s < 4, Native.validM (Native.glRootRows r s) = true ∧
      ∀ t < 4, s = t ∨ Native.glRootRows r s ≠ Native.glRootRows r t) ∧
    ∀ r < 18, ∀ t ∈ [1, 2, 3], Native.glInChart r 0 = true ∨
      (Native.commRows (Native.glRootRows r t) Native.glZ = false ∧
        Native.validM (Native.glRootRows r t) = true) := by
  have h := d1_parts.2.2.2.2.2.2.2.1
  rw [Native.d1RootOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun r hr s hs => ?_, fun r hr t ht => ?_⟩
  · have := List.all_eq_true.1 (h.1 r hr) s (List.mem_range.2 hs)
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at this
    exact ⟨this.1, this.2⟩
  · have := List.all_eq_true.1 (h.2 r (List.mem_range.2 hr)) t ht
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this

theorem xRootK_injOn {r : ℕ} (hr : r ∈ [0, 1, 2, 4, 5])
    {s t : ℕ} (hs : s < 4) (ht : t < 4) (h : xRootK r s = xRootK r t) : s = t := by
  rcases (d1Root_spec.1 r hr s hs).2 t ht with h' | h'
  · exact h'
  · exact absurd (eq_of_rowsMatrix_eq (d1Root_spec.1 r hr s hs).1 (d1Root_spec.1 r hr t ht).1
      (by rw [← xRootK_val, ← xRootK_val, h])) h'

theorem xRootK_zero_eq (r : ℕ) : xRootK r 0 = 1 := by simp [xRootK]

theorem xRootK_ne_one {r : ℕ} (hr : r ∈ [0, 1, 2, 4, 5]) :
    xRootK r 1 ≠ 1 := fun h =>
  absurd (xRootK_injOn hr (s := 1) (t := 0) (by norm_num) (by norm_num)
    (h.trans (xRootK_zero_eq r).symm)) (by decide)

theorem inChart_of_mem_Cz {r t : ℕ} (hr : r < 18)
    (ht : t ∈ [1, 2, 3]) (h : xRootK r t ∈ Cz) : Native.glInChart r 0 = true := by
  rcases d1Root_spec.2 r hr t ht with h' | ⟨hc, hv⟩
  · exact h'
  · exfalso
    have := (commute_iff_commRows (xRootK_val r t) z0_val' hv d1Elt_spec.1).1 (comm_of_mem_Cz h)
    rw [hc] at this
    exact absurd this (by decide)

theorem xRootK_mem_Ax25 {r : ℕ} (hr : r ∈ [0, 1, 2, 4, 5])
    {t : ℕ} (ht : t < 4) : xRootK r t ∈ Ax25 := by
  have hr' : r < 18 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  have h0 : Native.glInChart r 0 = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 : Native.glInChart r 1 = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  refine mem_Ax25.2 ⟨mem_Cz_of_comm ?_, ?_⟩
  · rw [← xLongK_zero]
    exact xRootK_comm_of_inChart hr' (by norm_num) h0 ht
  · rw [← xLongK_one]
    exact xRootK_comm_of_inChart hr' (by norm_num) h1 ht

variable (φ ρ) in
@[expose] noncomputable def chartD (y : K) : K := δ1hK * chartT φ ρ y * δ1hK

theorem chartD_mul {α : Cz}
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y y' : K} (hy : y ∈ Ax25)
    (hy' : y' ∈ Ax25) : chartD φ ρ (y * y') = chartD φ ρ y * chartD φ ρ y' := by
  unfold chartD
  rw [chartT_mul hm hφz hy hy', show δ1hK * chartT φ ρ y * δ1hK * (δ1hK * chartT φ ρ y' * δ1hK) =
    δ1hK * chartT φ ρ y * (δ1hK * δ1hK) * chartT φ ρ y' * δ1hK by group, δ1hK_mul_self]
  group

theorem δ1hK_comm_α3K : δ1hK * α3K = α3K * δ1hK :=
  ((mem_C0c.1 δ1hK_mem_C0c).1).symm

theorem chartD_α3K
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) : chartD φ ρ α3K = α3K := by
  rw [chartD, chartT_α3K hm hφz, δ1hK_comm_α3K, mul_assoc, δ1hK_mul_self, mul_one]

theorem chartD_of_mem_C0c {α : Cz}
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K}
    (hy : y ∈ Ax25) (hy0 : y ∈ C0c) : chartD φ ρ y = y := by
  rw [chartD, chartT_of_mem_C0c hm hφz hy hy0, show δ1hK * (δ1hK * y * δ1hK) * δ1hK =
    (δ1hK * δ1hK) * y * (δ1hK * δ1hK) by group, δ1hK_mul_self]
  group

theorem chartT_eq_of_chartD {y : K} (h : chartD φ ρ y = y) :
    chartT φ ρ y = δ1hK * y * δ1hK := by
  have e : chartT φ ρ y = δ1hK * chartD φ ρ y * δ1hK := by
    rw [chartD, show δ1hK * (δ1hK * chartT φ ρ y * δ1hK) * δ1hK =
      (δ1hK * δ1hK) * chartT φ ρ y * (δ1hK * δ1hK) by group, δ1hK_mul_self]
    group
  rw [e, h]

theorem chartD_ne_one {α : Cz}
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) {y : K} (hy : y ∈ Ax25) (h1 : y ≠ 1) :
    chartD φ ρ y ≠ 1 := by
  intro h
  apply h1
  have hT : chartT φ ρ y = 1 := by
    rw [chartD] at h
    have : chartT φ ρ y = δ1hK * (δ1hK * chartT φ ρ y * δ1hK) * δ1hK := by
      rw [show δ1hK * (δ1hK * chartT φ ρ y * δ1hK) * δ1hK =
        (δ1hK * δ1hK) * chartT φ ρ y * (δ1hK * δ1hK) by group, δ1hK_mul_self]
      group
    rw [this, h, mul_one, δ1hK_mul_self]
  rw [← chartT_chartT hm hφz hy, hT, chartT_one hm hφz]

theorem chartD_list_prod {α : Cz}
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    ∀ xs : List K, (∀ x ∈ xs, x ∈ Ax25) → chartD φ ρ xs.prod = (xs.map (chartD φ ρ)).prod
  | [], _ => by
    rw [List.prod_nil, chartD, chartT_one hm hφz, mul_one, δ1hK_mul_self]
    rfl
  | x :: xs, h => by
    rw [List.prod_cons, chartD_mul hm hφz (h x List.mem_cons_self)
      (Ax25.list_prod_mem fun y hy => h y (List.mem_cons_of_mem _ hy)), List.map_cons,
      List.prod_cons, chartD_list_prod hm hφz xs fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem f4_rot_cases : ∀ l ∈ [2, 3], ∀ ν ∈ [1, 2, 3], ∀ t ∈ [1, 2, 3],
    (t = 1 ∧ Native.f4mul ν t = ν) ∨
      (t = Native.f4mul l 1 ∧ Native.f4mul ν t = Native.f4mul l ν) ∨
      (t = Native.f4mul l (Native.f4mul l 1) ∧
        Native.f4mul ν t = Native.f4mul l (Native.f4mul l ν)) := by
  decide

theorem f4mul_mem : ∀ a ∈ [1, 2, 3], ∀ b ∈ [1, 2, 3], Native.f4mul a b ∈ [1, 2, 3] := by
  decide

theorem glRootChar_cases : ∀ r ∈ [0, 1, 2, 4, 5], Native.glRootChar[r]! ∈ [2, 3] := by
  decide

theorem rot_of {F : K → K}
    (hmul : ∀ a ∈ Ax25, ∀ b ∈ Ax25, F (a * b) = F a * F b) (hα : F α3K = α3K) {r : ℕ}
    (hr : r ∈ [0, 1, 2, 4, 5]) (hmap : ∀ t ∈ [1, 2, 3], ∃ s < 4, F (xRootK r t) = xRootK r s)
    (hne : F (xRootK r 1) ≠ 1) :
    ∃ ν ∈ [1, 2, 3], ∀ t ∈ [1, 2, 3], F (xRootK r t) = xRootK r (Native.f4mul ν t) := by
  have hr12 : r < 12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega
  obtain ⟨ν, hν4, hF1⟩ := hmap 1 (by simp)
  have hν : ν ∈ [1, 2, 3] := by
    have hν0 : ν ≠ 0 := by
      rintro rfl
      apply hne
      rw [hF1]
      simp [xRootK]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hmem : ∀ t < 4, xRootK r t ∈ Ax25 := fun t ht => xRootK_mem_Ax25 hr ht
  have key : ∀ t ∈ [1, 2, 3], ∀ u ∈ [1, 2, 3], F (xRootK r t) = xRootK r u →
      F (xRootK r (Native.f4mul Native.glRootChar[r]! t)) =
        xRootK r (Native.f4mul Native.glRootChar[r]! u) := by
    intro t ht u hu h
    have ht4 : t < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; omega
    rw [← xRootK_α3 hr12 ht, ← xRootK_α3 hr12 hu,
      hmul _ (Ax25.mul_mem (Ax25.mul_mem α3K_mem_Ax25 α3K_mem_Ax25) (hmem t ht4)) _ α3K_mem_Ax25,
      hmul _ (Ax25.mul_mem α3K_mem_Ax25 α3K_mem_Ax25) _ (hmem t ht4),
      hmul _ α3K_mem_Ax25 _ α3K_mem_Ax25, hα, h]
  have hl := glRootChar_cases r hr
  have hl1 : Native.f4mul Native.glRootChar[r]! 1 ∈ [1, 2, 3] :=
    f4mul_mem _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢; omega) 1
      (by simp)
  have hlν : Native.f4mul Native.glRootChar[r]! ν ∈ [1, 2, 3] :=
    f4mul_mem _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢; omega) ν hν
  have h2 := key 1 (by simp) ν hν hF1
  have h3 := key _ hl1 _ hlν h2
  refine ⟨ν, hν, fun t ht => ?_⟩
  rcases f4_rot_cases _ hl ν hν t ht with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
  · rw [e, hF1]
  · rw [e, h2]
  · rw [e, h3]

theorem δ1hK_conj_xRootK {r s : ℕ} (hr : r < 18) (hs : s < 4) :
    δ1hK * xRootK r s * δ1hK = xRootK (Native.glWAct 4 r s).1 (Native.glWAct 4 r s).2 :=
  conj_xRootK (g := 4) (by norm_num) hr hs

theorem x34K_δ1hK : δ1hK * x34K * δ1hK = x34K := by
  have h := δ1hK_conj_xRootK (r := 14) (s := 1) (by norm_num) (by norm_num)
  rwa [show Native.glWAct 4 14 1 = (14, 1) from rfl] at h

theorem x43K_δ1hK : δ1hK * x43K * δ1hK = x43K := by
  have h := δ1hK_conj_xRootK (r := 17) (s := 1) (by norm_num) (by norm_num)
  rwa [show Native.glWAct 4 17 1 = (17, 1) from rfl] at h

theorem x34K_mem_Ax25 : x34K ∈ Ax25 :=
  mem_Ax25.2 ⟨mem_Cz_of_comm (by
    have := xLongK_comm (k := 2) (l := 0) (by norm_num) (by norm_num) (by norm_num)
    rwa [xLongK_zero] at this), xLongK_comm (k := 2) (l := 1) (by norm_num) (by norm_num)
      (by norm_num)⟩

theorem x43K_mem_Ax25 : x43K ∈ Ax25 :=
  mem_Ax25.2 ⟨mem_Cz_of_comm (by
    have := xLongK_comm (k := 5) (l := 0) (by norm_num) (by norm_num) (by norm_num)
    rwa [xLongK_zero] at this), xLongK_comm (k := 5) (l := 1) (by norm_num) (by norm_num)
      (by norm_num)⟩

theorem x34K_mem_C0c : x34K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem δ0hK_mem_C0c x25K_mem_C0c) δ0hK_mem_C0c

theorem x43K_mem_C0c : x43K ∈ C0c :=
  C0c.mul_mem (C0c.mul_mem δ0hK_mem_C0c
    (C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c x61K_mem_C0c) δ1hK_mem_C0c)) δ0hK_mem_C0c

theorem chartT_x34K
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) :
    chartT φ ρ x34K = x34K := by
  rw [chartT_of_mem_C0c hm hφz x34K_mem_Ax25 x34K_mem_C0c, x34K_δ1hK]

theorem chartT_x43K
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) :
    chartT φ ρ x43K = x43K := by
  rw [chartT_of_mem_C0c hm hφz x43K_mem_Ax25 x43K_mem_C0c, x43K_δ1hK]

theorem chartT_xRootK_swap
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {t : ℕ} (ht : t ∈ [1, 2, 3]) :
    (∃ s < 4, chartT φ ρ (xRootK 1 t) = xRootK 4 s) ∧
      (∃ s < 4, chartT φ ρ (xRootK 2 t) = xRootK 5 s) ∧
      (∃ s < 4, chartT φ ρ (xRootK 4 t) = xRootK 1 s) ∧
      ∃ s < 4, chartT φ ρ (xRootK 5 t) = xRootK 2 s := by
  obtain ⟨⟨q1, hq1, e1⟩, ⟨q2, hq2, e2⟩, ⟨f4, hf4, e4⟩, ⟨f5, hf5, e5⟩⟩ := phiK_wit ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e1, chartT_phiK hm hφz x34K_mem_Ax25 (chartT_x34K hm hφz) (Qx25_le_Ax25 hq1)]
    exact phiK_x34_F0c (chartT_mem_F0c hm hφz hq1)
  · rw [← e2, chartT_phiK hm hφz x43K_mem_Ax25 (chartT_x43K hm hφz) (Qx25_le_Ax25 hq2)]
    exact phiK_x43_F0c (chartT_mem_F0c hm hφz hq2)
  · rw [← e4, chartT_phiK hm hφz x34K_mem_Ax25 (chartT_x34K hm hφz) (F0c_one_le_Ax25 hf4)]
    exact phiK_x34_Qx25 (chartT_mem_Qx25 hm hφz hf4)
  · rw [← e5, chartT_phiK hm hφz x43K_mem_Ax25 (chartT_x43K hm hφz) (F0c_one_le_Ax25 hf5)]
    exact phiK_x43_Qx25 (chartT_mem_Qx25 hm hφz hf5)

theorem δ1hK_conj_swap {r r' : ℕ}
    (h : (r = 4 ∧ r' = 1) ∨ (r = 5 ∧ r' = 2) ∨ (r = 1 ∧ r' = 4) ∨ (r = 2 ∧ r' = 5)) {s : ℕ}
    (hs : s < 4) : ∃ s' < 4, δ1hK * xRootK r s * δ1hK = xRootK r' s' := by
  have hr : r < 18 := by omega
  have htab : ∀ s < 4, ((Native.glWAct 4 4 s).1 = 1 ∨ (Native.glWAct 4 4 s).2 = 0) ∧
      ((Native.glWAct 4 5 s).1 = 2 ∨ (Native.glWAct 4 5 s).2 = 0) ∧
      ((Native.glWAct 4 1 s).1 = 4 ∨ (Native.glWAct 4 1 s).2 = 0) ∧
      ((Native.glWAct 4 2 s).1 = 5 ∨ (Native.glWAct 4 2 s).2 = 0) := by decide
  rw [δ1hK_conj_xRootK hr hs]
  refine ⟨(Native.glWAct 4 r s).2, (glWeyl_spec 4 (by norm_num) r hr s hs).2.1, ?_⟩
  have hc : (Native.glWAct 4 r s).1 = r' ∨ (Native.glWAct 4 r s).2 = 0 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (htab s hs).1
    · exact (htab s hs).2.1
    · exact (htab s hs).2.2.1
    · exact (htab s hs).2.2.2
  rcases hc with hc | hc
  · rw [hc]
  · rw [hc]
    simp [xRootK]

theorem chartD_xRootK_mem
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {r : ℕ} (hr : r ∈ [1, 2, 4, 5]) {t : ℕ}
    (ht : t ∈ [1, 2, 3]) : ∃ s < 4, chartD φ ρ (xRootK r t) = xRootK r s := by
  obtain ⟨h1, h2, h4, h5⟩ := chartT_xRootK_swap hm hφz ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨s, hs, e⟩ := h1
    rw [chartD, e]
    exact δ1hK_conj_swap (Or.inl ⟨rfl, rfl⟩) hs
  · obtain ⟨s, hs, e⟩ := h2
    rw [chartD, e]
    exact δ1hK_conj_swap (Or.inr (Or.inl ⟨rfl, rfl⟩)) hs
  · obtain ⟨s, hs, e⟩ := h4
    rw [chartD, e]
    exact δ1hK_conj_swap (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hs
  · obtain ⟨s, hs, e⟩ := h5
    rw [chartD, e]
    exact δ1hK_conj_swap (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hs

theorem chartD_rot
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {r : ℕ} (hr : r ∈ [1, 2, 4, 5]) :
    ∃ ν ∈ [1, 2, 3], ∀ t ∈ [1, 2, 3], chartD φ ρ (xRootK r t) = xRootK r (Native.f4mul ν t) := by
  have hr' : r ∈ [0, 1, 2, 4, 5] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  exact rot_of (fun a ha b hb => chartD_mul hm hφz ha hb) (chartD_α3K hm hφz) hr'
    (fun t ht => chartD_xRootK_mem hm hφz hr ht)
    (chartD_ne_one hm hφz (xRootK_mem_Ax25 hr' (by norm_num)) (xRootK_ne_one hr'))

theorem chartT_xRootK_15
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {t : ℕ}
    (ht : t ∈ [1, 2, 3]) : chartT φ ρ (xRootK 0 t) = xRootK 0 t := by
  have h0 : (0 : ℕ) ∈ [0, 1, 2, 4, 5] := by simp
  have hX : ∀ s < 4, xRootK 0 s ∈ X0g := fun s hs => mem_X0g.2 ⟨s, hs, rfl⟩
  obtain ⟨μ, hμ, hrot⟩ := rot_of (fun a ha b hb => chartT_mul hm hφz ha hb)
    (chartT_α3K hm hφz) h0 (fun t ht => by
      obtain ⟨s, hs, e⟩ := mem_X0g.1 (chartT_mem_X0g hm hφz (hX t (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; omega)))
      exact ⟨s, hs, e.symm⟩)
    (fun h1 => xRootK_ne_one h0 (by
      rw [← chartT_chartT hm hφz (xRootK_mem_Ax25 h0 (by norm_num)), h1, chartT_one hm hφz]))
  have hμ1 : Native.f4mul μ 1 = μ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl | rfl <;> rfl
  have e1 := hrot 1 (by simp)
  have e2 := hrot μ hμ
  rw [hμ1] at e1
  have hTT := chartT_chartT hm hφz (xRootK_mem_Ax25 h0 (by norm_num : 1 < 4))
  rw [e1, e2] at hTT
  have hμμ : Native.f4mul μ μ = 1 := xRootK_injOn h0 (by
    have := f4mul_mem μ hμ μ hμ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega) (by norm_num) hTT
  have hμ' : μ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl | rfl
    · rfl
    · exact absurd hμμ (by decide)
    · exact absurd hμμ (by decide)
  rw [hrot t ht, hμ']
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

end CFSG.Sporadic.Co2Smith
