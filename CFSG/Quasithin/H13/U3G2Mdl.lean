module

public import CFSG.Quasithin.H13.U3HullData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin CFSG.Quasithin.SteinbergCB Matrix Module

@[expose] def a1mask : ℕ := 19606274593

@[expose] def g1mask : ℕ := 9250393651798872089

@[expose] def g3mask : ℕ := 146652878160003073

@[expose] def eaPos (m : ℕ) : List ℕ := (List.range 64).filter fun k => m.testBit k

@[expose] def fixAll (ms : List (List ℕ)) (c : ℕ) : Bool := ms.all fun e => vapp e c == c

@[expose] def fixCnt (m : ℕ) : ℕ :=
  ((Finset.range 64).filter fun c => fixAll ((eaPos m).map s0m) c = true).card

theorem fixAll_eq (m c : ℕ) : fixAll ((eaPos m).map s0m) c = fixP m c := by
  simp only [fixAll, eaPos, fixP, List.all_map, List.all_filter]
  rfl

theorem ea64_codes : ∀ m ∈ eaMasks, m = 1 ∨ m = g1mask ∨ m = a1mask ∨ m = g3mask ∨
    (ofMask m).card * fixCnt m < 64 := by
  decide +kernel

theorem good_codes : (ofMask 1).card * fixCnt 1 = 64 ∧ (ofMask g1mask).card * fixCnt g1mask = 64 ∧
    (ofMask a1mask).card = 8 ∧ fixCnt a1mask = 8 ∧
    (ofMask g3mask).card * fixCnt g3mask = 64 := by
  decide +kernel

theorem xconj_codes : g1mask.testBit 3 = true ∧ g3mask.testBit 42 = true ∧
    a1mask.testBit 3 = false ∧ a1mask.testBit 42 = false ∧
    ∀ k < 64, (∃ c < 64, vapp (u6c 3) (vapp (s0m 3) (vapp (u6ci 3) c)) ≠ vapp (s0m k) c) ∧
      ∃ c < 64, vapp (u6c 3) (vapp (s0m 42) (vapp (u6ci 3) c)) ≠ vapp (s0m k) c := by
  decide +kernel

theorem a1_codes : ∀ k < 64, (vapp (s0m k) 15 = 15 ∧ vapp (s0m k) 18 = 18 ∧
    vapp (s0m k) 39 = 39) ↔ a1mask.testBit k = true := by
  decide +kernel

theorem a1_fix_codes : (∀ c < 64, fixP a1mask c = v3mask.testBit c) ∧
    (∀ k < 64, a1mask.testBit k = true → ∀ d < 64, v3mask.testBit (vapp (s0m k) d ^^^ d) = true) ∧
    (∀ c < 64, v3mask.testBit c = true →
      ∃ k < 64, a1mask.testBit k = true ∧ ∃ d < 64, vapp (s0m k) d ^^^ d = c) ∧
    a1mask.testBit 21 = true ∧ (∀ c < 64, (vapp (s0m 21) c == c) = v3mask.testBit c) ∧
    v3mask.testBit 15 = true ∧ v3mask.testBit 18 = true ∧ v3mask.testBit 39 = true := by
  decide +kernel

@[expose] def oppc : List ℕ := mul6 (mul6 (mul6 (mul6 (u6c 4) (u6c 3)) (u6c 4)) (u6c 3)) (u6c 4)

theorem opp_codes : ∀ c < 64, v3mask.testBit c = true → v3mask.testBit (vapp oppc c) = true →
    c = 0 := by
  decide +kernel

theorem natCard_linFix_eq
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) {m : ℕ} (hmE : ofMask m = IE E) :
    Nat.card (linFix E) = fixCnt m := by
  refine natCard_eq_of_vecOf ?_ fun c hc => ?_
  · intro c hc
    exact Finset.mem_range.1 (Finset.mem_filter.1 hc).1
  · rw [mem_linFix_IE hE hmE hc, Finset.mem_filter, Finset.mem_range, fixAll_eq]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩

theorem card_mul_card_linFix_le
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hab : IsElementaryAbelian 2 E) :
    Nat.card E * Nat.card (linFix E) ≤ 64 := by
  obtain ⟨m, hm, hmE⟩ := exists_mask_eq hab
  rw [card_eq_IE hE, ← hmE, natCard_linFix_eq hE hmE]
  obtain ⟨h1, h2, h3, h4, h5⟩ := good_codes
  rcases ea64_codes m hm with rfl | rfl | rfl | rfl | h
  · exact h1.le
  · exact h2.le
  · rw [h3, h4]
  · exact h5.le
  · exact h.le

theorem exists_mask_of_eq64
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hab : IsElementaryAbelian 2 E)
    (h64 : Nat.card E * Nat.card (linFix E) = 64) :
    ∃ m, ofMask m = IE E ∧ (m = 1 ∨ m = g1mask ∨ m = a1mask ∨ m = g3mask) := by
  obtain ⟨m, hm, hmE⟩ := exists_mask_eq hab
  refine ⟨m, hmE, ?_⟩
  rw [card_eq_IE hE, ← hmE, natCard_linFix_eq hE hmE] at h64
  rcases ea64_codes m hm with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · omega

theorem s0L_mem_of_mask
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} {m : ℕ} (hmE : ofMask m = IE E) {k : ℕ} (hk : k < 64)
    (hmk : m.testBit k = true) : s0L k ∈ E := by
  have : k ∈ IE E := by
    rw [← hmE]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hmk⟩
  exact (mem_IE.1 this).2

theorem exists_code_V3sub {w : W6} (hw : w ∈ V3sub) :
    ∃ c < 64, vecOf c = w ∧ v3mask.testBit c = true := by
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  exact ⟨c, hc, rfl, (hasMask_V3sub' c hc).1 hw⟩

theorem fixes_V3sub_iff
    {k : ℕ} (hk : k < 64) : (∀ w ∈ V3sub, s0L k w = w) ↔ a1mask.testBit k = true := by
  obtain ⟨h1, -, -, -, -, h15, h18, h39⟩ := a1_fix_codes
  rw [← a1_codes k hk]
  constructor
  · intro h
    have key : ∀ d < 64, v3mask.testBit d = true → vapp (s0m k) d = d := fun d hd hdm => by
      have h2 := h _ ((hasMask_V3sub' d hd).2 hdm)
      rw [s0L_vecOf hk] at h2
      exact vecOf_injective (vapp_s0m_lt hk d) hd h2
    exact ⟨key 15 (by norm_num) h15, key 18 (by norm_num) h18, key 39 (by norm_num) h39⟩
  · intro hkc w hw
    obtain ⟨c, hc, rfl, hcm⟩ := exists_code_V3sub hw
    have hfix := h1 c hc
    rw [hcm, fixP, List.all_eq_true] at hfix
    have h2 := hfix k (List.mem_range.2 hk)
    rw [(a1_codes k hk).1 hkc, Bool.not_true, Bool.false_or, beq_iff_eq] at h2
    rw [s0L_vecOf hk, h2]

theorem card_le_eight_of_fix
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hfix : ∀ e ∈ E, ∀ w ∈ V3sub, e w = w) :
    Nat.card E ≤ 8 := by
  rw [card_eq_IE hE, ← good_codes.2.2.1]
  refine Finset.card_le_card fun k hk => ?_
  obtain ⟨hk64, hkE⟩ := mem_IE.1 hk
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk64, (fixes_V3sub_iff hk64).1 (hfix _ hkE)⟩

@[expose] def IsA1
    (E : Subgroup (W6 ≃ₗ[ZMod 2] W6)) : Prop :=
  E ≤ S0L ∧ ofMask a1mask = IE E

theorem isA1_of_xStable
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hab : IsElementaryAbelian 2 E)
    (h64 : Nat.card E * Nat.card (linFix E) = 64) (hE1 : E ≠ ⊥)
    (hx : ∀ e ∈ E, glLin xGL * e * (glLin xGL)⁻¹ ∈ S0L) : IsA1 E := by
  obtain ⟨m, hmE, hm⟩ := exists_mask_of_eq64 hE hab h64
  obtain ⟨hg1, hg3, -, -, hx'⟩ := xconj_codes
  have hbad : ∀ k₀ < 64, m.testBit k₀ = true →
      (∀ k < 64, ∃ c < 64, vapp (u6c 3) (vapp (s0m k₀) (vapp (u6ci 3) c)) ≠ vapp (s0m k) c) →
      False := by
    intro k₀ hk₀ hmk₀ hne
    obtain ⟨k, hk, hkx⟩ := mem_S0L.1 (hx _ (s0L_mem_of_mask hmE hk₀ hmk₀))
    obtain ⟨c, hc, hc'⟩ := hne k hk
    apply hc'
    have h1 := congrArg (fun f : W6 ≃ₗ[ZMod 2] W6 => f (vecOf c)) hkx
    simp only [LinearEquiv.mul_apply] at h1
    rw [← map_inv, glLin_vecOf coe_xGL_inv, s0L_vecOf hk₀, glLin_vecOf coe_xGL,
      s0L_vecOf hk] at h1
    exact vecOf_injective (vapp_u6c_lt 3 _) (vapp_s0m_lt hk c) h1
  rcases hm with rfl | rfl | rfl | rfl
  · exfalso
    apply hE1
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := (mem_iff_IE hE).1 hg
    rw [← hmE, ofMask_one, Finset.mem_singleton] at hk
    rw [hk, s0L_zero]
    exact Subgroup.one_mem _
  · exact (hbad 3 (by norm_num) hg1 fun k hk => (hx' k hk).1).elim
  · exact ⟨hE, hmE⟩
  · exact (hbad 42 (by norm_num) hg3 fun k hk => (hx' k hk).2).elim

theorem isA1_of_fix
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hab : IsElementaryAbelian 2 E)
    (h64 : Nat.card E * Nat.card (linFix E) = 64) (hE1 : E ≠ ⊥)
    (hfix : ∀ e ∈ E, ∀ w ∈ V3sub, e w = w) : IsA1 E := by
  obtain ⟨m, hmE, hm⟩ := exists_mask_of_eq64 hE hab h64
  obtain ⟨hg1, hg3, h3, h42, -⟩ := xconj_codes
  have hbad : ∀ k₀ < 64, m.testBit k₀ = true → a1mask.testBit k₀ = false → False := by
    intro k₀ hk₀ hmk₀ ha
    have := (fixes_V3sub_iff hk₀).1 (hfix _ (s0L_mem_of_mask hmE hk₀ hmk₀))
    rw [ha] at this
    exact absurd this (by decide)
  rcases hm with rfl | rfl | rfl | rfl
  · exfalso
    apply hE1
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := (mem_iff_IE hE).1 hg
    rw [← hmE, ofMask_one, Finset.mem_singleton] at hk
    rw [hk, s0L_zero]
    exact Subgroup.one_mem _
  · exact (hbad 3 (by norm_num) hg1 h3).elim
  · exact ⟨hE, hmE⟩
  · exact (hbad 42 (by norm_num) hg3 h42).elim

namespace IsA1

theorem card
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (h : IsA1 E) : Nat.card E = 8 := by
  rw [card_eq_IE h.1, ← h.2, good_codes.2.2.1]

theorem linFix_eq
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (h : IsA1 E) : linFix E = V3sub := by
  ext w
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [mem_linFix_IE h.1 h.2 hc, a1_fix_codes.1 c hc, hasMask_V3sub' c hc]

theorem mem_of_fix
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (h : IsA1 E) {g : W6 ≃ₗ[ZMod 2] W6} (hg : g ∈ S0L)
    (hfix : ∀ w ∈ V3sub, g w = w) : g ∈ E := by
  obtain ⟨k, hk, rfl⟩ := mem_S0L.1 hg
  exact s0L_mem_of_mask h.2 hk ((fixes_V3sub_iff hk).1 hfix)

theorem exists_sub_eq
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (h : IsA1 E) {c : W6} (hc : c ∈ V3sub) :
    ∃ e ∈ E, ∃ w : W6, e w - w = c := by
  obtain ⟨c', hc', rfl, hcm⟩ := exists_code_V3sub hc
  obtain ⟨k, hk, hmk, d, hd, hkd⟩ := a1_fix_codes.2.2.1 c' hc' hcm
  refine ⟨s0L k, s0L_mem_of_mask h.2 hk hmk, vecOf d, ?_⟩
  rw [s0L_vecOf hk, sub_eq_add_W6, ← vecOf_xor, hkd]

theorem mem_21
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (h : IsA1 E) : s0L 21 ∈ E :=
  s0L_mem_of_mask h.2 (by norm_num) a1_fix_codes.2.2.2.1

theorem fix_21_iff
    (w : W6) : s0L 21 w = w ↔ w ∈ V3sub := by
  obtain ⟨c, hc, rfl⟩ := exists_vecOf w
  rw [s0L_vecOf (by norm_num), hasMask_V3sub' c hc, ← a1_fix_codes.2.2.2.2.1 c hc, beq_iff_eq]
  exact ⟨fun h1 => vecOf_injective (vapp_s0m_lt (by norm_num) c) hc h1, fun h1 => by rw [h1]⟩

end IsA1

noncomputable abbrev oppGL : GL (Fin 6) (ZMod 2) := yGL * xGL * yGL * xGL * yGL

theorem oppGL_mem : oppGL ∈ J6 :=
  mul_mem (mul_mem (mul_mem (mul_mem yGL_mem xGL_mem) yGL_mem) xGL_mem) yGL_mem

theorem coe_oppGL : (oppGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat oppc := by
  simp only [oppGL, Units.val_mul, coe_xGL, coe_yGL, oppc, colMat_mul6]

theorem opp_V3sub {w : W6} (hw : w ∈ V3sub) (hjw : glLin oppGL w ∈ V3sub) : w = 0 := by
  obtain ⟨c, hc, rfl, hcm⟩ := exists_code_V3sub hw
  rw [glLin_vecOf coe_oppGL] at hjw
  have hlt : vapp oppc c < 64 := vapp_lt_of_foldr c _ fun j hj => by
    have : ∀ j < 6, oppc.getD j 0 < 2 ^ 6 := by decide +kernel
    exact this j (List.mem_range.1 hj)
  have := opp_codes c hc hcm ((hasMask_V3sub' _ hlt).1 hjw)
  subst this
  ext i
  simp [vecOf, bit2]

end CFSG.Quasithin.H13.U3
