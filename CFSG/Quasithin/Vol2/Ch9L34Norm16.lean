module

public import CFSG.Quasithin.Vol2.Ch9L34NormGen
public import CFSG.Quasithin.Vol2.Ch9L34Ech
public import CFSG.Quasithin.Vol2.Ch9L34M16

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.Herm9
open CFSG.Quasithin.H13.Ch9.L34M

abbrev img16 : Subgroup (MulAut (Wn 16)) := img rho16GL

@[expose] def w0C16 : List ℕ := matOf 16 (act16 w0 w0)

theorem actsBy_w0_16 : ActsBy (MaskCoords.std 16) (rho16GL w0GL) w0C16 :=
  actsBy_rho16GL_matOf w0GL

theorem allLt_w0C16 : AllLt 16 w0C16 = true := allLt_matOf_act16 _ _

@[expose] def gen16 : Set (MulAut (Wn 16)) :=
  {slRep rho16GL (uSL (f4c 1) 0 0), slRep rho16GL (uSL (f4c 2) 0 0),
    slRep rho16GL (uSL 0 0 (f4c 1)), slRep rho16GL (uSL 0 0 (f4c 2))}

abbrev P16 : Subgroup (MulAut (Wn 16)) := Subgroup.closure gen16

theorem P16_le : P16 ≤ img16 := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl) <;> exact slRep_mem_img _ _

theorem actsBy_gen16 :
    (ActsBy (MaskCoords.std 16) (slRep rho16GL (uSL (f4c 1) 0 0)) (tabX12.getD 1 []) ∧
      AllLt 16 (tabX12.getD 1 []) = true) ∧
    (ActsBy (MaskCoords.std 16) (slRep rho16GL (uSL (f4c 2) 0 0)) (tabX12.getD 2 []) ∧
      AllLt 16 (tabX12.getD 2 []) = true) ∧
    (ActsBy (MaskCoords.std 16) (slRep rho16GL (uSL 0 0 (f4c 1))) (tabX23.getD 1 []) ∧
      AllLt 16 (tabX23.getD 1 []) = true) ∧
    (ActsBy (MaskCoords.std 16) (slRep rho16GL (uSL 0 0 (f4c 2))) (tabX23.getD 2 []) ∧
      AllLt 16 (tabX23.getD 2 []) = true) := by
  simp only [slRep_uSL]
  exact ⟨(actsBy_x16 (by norm_num : 1 < 4)).1, (actsBy_x16 (by norm_num : 2 < 4)).1,
    (actsBy_x16 (by norm_num : 1 < 4)).2.2, (actsBy_x16 (by norm_num : 2 < 4)).2.2⟩

@[expose] def st16 (w : ℕ) : ℕ :=
  stack4 16 (tabX12.getD 1 []) (tabX12.getD 2 []) (tabX23.getD 1 []) (tabX23.getD 2 []) w

@[expose] def ker16 : List ℕ := echKer 16 st16

theorem ker16_spec :
    ker16.length = 14 ∧ AllLt 16 ker16 = true ∧ echOK (ker16.map st16) = true := by
  decide +kernel

theorem card_fixV_P16_le : Nat.card (fixV P16) ≤ 4 := by
  obtain ⟨⟨h₁, c₁⟩, ⟨h₂, c₂⟩, ⟨h₃, c₃⟩, ⟨h₄, c₄⟩⟩ := actsBy_gen16
  obtain ⟨hl, hws, hech⟩ := ker16_spec
  have h := two_pow_mul_card_le_four (MaskCoords.std 16) h₁ h₂ h₃ h₄ c₁ c₂ c₃ c₄ hws hech
    (F := fixV P16) fun v hv => ⟨hv _ (Subgroup.subset_closure (Or.inl rfl)),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inl rfl))),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))),
      hv _ (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl))))⟩
  rw [hl] at h
  omega

theorem fix16_masks : ∀ m ∈ [0, 4, 8, 12],
    actM (tabX12.getD 1 []) m = m ∧ actM (tabX12.getD 2 []) m = m ∧
      actM (tabX23.getD 1 []) m = m ∧ actM (tabX23.getD 2 []) m = m := by
  decide +kernel

theorem mem_fixV_P16 {m : ℕ} (hm : m ∈ [0, 4, 8, 12]) : toW 16 m ∈ fixV P16 := by
  obtain ⟨⟨h₁, -⟩, ⟨h₂, -⟩, ⟨h₃, -⟩, ⟨h₄, -⟩⟩ := actsBy_gen16
  obtain ⟨e₁, e₂, e₃, e₄⟩ := fix16_masks m hm
  have hlt : m < 2 ^ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> norm_num
  apply mem_fixV_closure
  rintro _ (rfl | rfl | rfl | rfl)
  · exact (h₁ m hlt).trans (congrArg _ e₁)
  · exact (h₂ m hlt).trans (congrArg _ e₂)
  · exact (h₃ m hlt).trans (congrArg _ e₃)
  · exact (h₄ m hlt).trans (congrArg _ e₄)

theorem fixV_P16 {w : Wn 16} (hw : w ∈ fixV P16) :
    w = toW 16 0 ∨ w = toW 16 4 ∨ w = toW 16 8 ∨ w = toW 16 12 := by
  classical
  set T : Finset (Wn 16) := {toW 16 0, toW 16 4, toW 16 8, toW 16 12} with hT
  have hTcard : T.card = 4 := by
    have hinj : ∀ a b : ℕ, a < 2 ^ 16 → b < 2 ^ 16 → toW 16 a = toW 16 b → a = b :=
      fun a b ha hb h => toW_inj ha hb h
    rw [hT, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num),
        fun h => absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num),
        fun h => absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num),
        fun h => absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num)⟩
  have hsub : (T : Set (Wn 16)) ⊆ (fixV P16 : Set (Wn 16)) := by
    intro x hx
    simp only [hT, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact mem_fixV_P16 (by simp)
  have hfin : (fixV P16 : Set (Wn 16)).Finite := Set.toFinite _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
    exact card_fixV_P16_le) hfin
  have hw' : w ∈ (T : Set (Wn 16)) := heq ▸ hw
  simpa [hT] using hw'

@[expose] def words16 : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (32, 1), (0, 2), (0, 4), (1, 4), (2, 4), (4, 4), (8, 4), (16, 4), (17, 4),
    (18, 4), (20, 4), (24, 4), (32, 4), (0, 8)]

@[expose] def orb16 (v : ℕ) : List ℕ :=
  words16.map fun pq => actM (tabU16.getD pq.1 []) (actM w0C16 (actM (tabU16.getD pq.2 [])
    (actM w0C16 v)))

theorem orb16_spec : ∀ v ∈ [4, 8, 12],
    combOK (orb16 v) (echComb (orb16 v)) = true ∧
      pivOK 16 ((echComb (orb16 v)).map Prod.fst) = true := by
  decide +kernel

theorem allLt_tabU16 (p : ℕ) : AllLt 16 (tabU16.getD p []) = true := by
  by_cases hp : p < 64
  · have h : ∀ p < 64, AllLt 16 (tabU16.getD p []) = true := by decide +kernel
    exact h p hp
  · rw [List.getD_eq_default _ _ (by
      have : tabU16.length = 64 := by decide +kernel
      omega)]
    rfl

theorem words16_lt : ∀ pq ∈ words16, pq.1 < 64 ∧ pq.2 < 64 := by decide

theorem closure_orbit16 {v : ℕ} (hv : v ∈ [4, 8, 12]) :
    Subgroup.closure {x | ∃ γ ∈ img16, γ (toW 16 v) = x} = ⊤ := by
  obtain ⟨hc, hp⟩ := orb16_spec v hv
  refine eq_top_of_comb (MaskCoords.std 16) hc hp fun o ho => ?_
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := List.mem_map.1 ho
  obtain ⟨hp64, hq64⟩ := words16_lt _ hpq
  refine Subgroup.subset_closure ⟨slRep rho16GL (uSL (f4c p) (f4c (p / 4)) (f4c (p / 16)) *
    w0SL * uSL (f4c q) (f4c (q / 4)) (f4c (q / 16)) * w0SL), slRep_mem_img _ _, ?_⟩
  have hvlt : v < 2 ^ 16 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> norm_num
  have hw := actsBy_w0_16
  have hu := fun p => actsBy_uGL16 p
  have lt1 := actM_lt (allLt_spec allLt_w0C16) v
  have lt2 := actM_lt (allLt_spec (allLt_tabU16 (q % 64))) (actM w0C16 v)
  have lt3 := actM_lt (allLt_spec allLt_w0C16) (actM (tabU16.getD (q % 64) []) (actM w0C16 v))
  change slRep rho16GL _ ((MaskCoords.std 16).vm v) = _
  simp only [map_mul, MulAut.mul_apply, slRep_uSL, slRep_w0SL]
  rw [hw v hvlt, hu q _ lt1, hw _ lt2, hu p _ lt3, Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt hq64]

theorem nc16 : ∃ a b : SpecialLinearGroup (Fin 3) F4,
    slRep rho16GL a * slRep rho16GL b ≠ slRep rho16GL b * slRep rho16GL a := by
  refine ⟨uSL (f4c 1) 0 0, uSL 0 0 (f4c 1), fun h => ?_⟩
  obtain ⟨⟨h₁, c₁⟩, -, ⟨h₃, c₃⟩, -⟩ := actsBy_gen16
  have e := congrArg (fun F : MulAut (Wn 16) => F ((MaskCoords.std 16).vm 16)) h
  simp only [MulAut.mul_apply] at e
  rw [h₃ 16 (by norm_num), h₁ _ (actM_lt (allLt_spec c₃) 16), h₁ 16 (by norm_num),
    h₃ _ (actM_lt (allLt_spec c₁) 16)] at e
  have e2 := (MaskCoords.std 16).vm_inj _ _ (actM_lt (allLt_spec c₁) _)
    (actM_lt (allLt_spec c₃) _) e
  revert e2
  decide +kernel

theorem rho16GL_mem_range (g : GL (Fin 3) F4) : rho16GL g ∈ rho16.range :=
  ⟨SemidirectProduct.inl g, by rw [rho16_apply]; simp⟩

theorem fld16_mem_range : fld16 ∈ rho16.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1, 0)), ?_⟩
  rw [rho16_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out16, c22Hom_apply]
  simp

theorem gr16_mem_range : gr16 ∈ rho16.range := by
  refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (0, 1)), ?_⟩
  rw [rho16_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, one_mul,
    out16, c22Hom_apply]
  simp

theorem range_le_normalizer16 :
    rho16.range ≤ Subgroup.normalizer (img16 : Set (MulAut (Wn 16))) := by
  rintro _ ⟨x, rfl⟩
  rw [rho16_apply, out16]
  exact mul_c22Hom_mem_normalizer rho16GL rho16GL_frobGL rho16GL_grGL _ _ _ _ _

theorem odd16 : Odd (Nat.card {w : Wn 16 // w ≠ 1 ∧ (∀ p ∈ P16, p w = w) ∧
    Subgroup.closure {v | ∃ γ ∈ img16, γ w = v} = ⊤}) := by
  classical
  have hset : {w : Wn 16 | w ≠ 1 ∧ (∀ p ∈ P16, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img16, γ w = v} = ⊤} =
      ({toW 16 4, toW 16 8, toW 16 12} : Finset (Wn 16)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      rcases fixV_P16 h2 with rfl | h | h | h
      · exact absurd (toW_zero 16) h1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have key : ∀ m ∈ [4, 8, 12], toW 16 m ≠ 1 ∧ (∀ p ∈ P16, p (toW 16 m) = toW 16 m) ∧
          Subgroup.closure {v | ∃ γ ∈ img16, γ (toW 16 m) = v} = ⊤ := by
        intro m hm
        refine ⟨fun h => ?_, mem_fixV_P16 (by simp at hm ⊢; omega), closure_orbit16 hm⟩
        have hlt : m < 2 ^ 16 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl <;> norm_num
        have := toW_inj hlt (by norm_num) (h.trans (toW_zero 16).symm)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
      rintro (rfl | rfl | rfl)
      · exact key 4 (by simp)
      · exact key 8 (by simp)
      · exact key 12 (by simp)
  have hcard : Nat.card {w : Wn 16 // w ≠ 1 ∧ (∀ p ∈ P16, p w = w) ∧
      Subgroup.closure {v | ∃ γ ∈ img16, γ w = v} = ⊤} = Set.ncard {w : Wn 16 | w ≠ 1 ∧
        (∀ p ∈ P16, p w = w) ∧ Subgroup.closure {v | ∃ γ ∈ img16, γ w = v} = ⊤} :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_coe_finset]
  have hne : ∀ a b : ℕ, a < 2 ^ 16 → b < 2 ^ 16 → a ≠ b → toW 16 a ≠ toW 16 b :=
    fun a b ha hb hab h => hab (toW_inj ha hb h)
  rw [Finset.card_insert_of_notMem, Finset.card_pair (hne 8 12 (by norm_num) (by norm_num)
    (by norm_num))]
  · decide
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne 4 8 (by norm_num) (by norm_num) (by norm_num),
      hne 4 12 (by norm_num) (by norm_num) (by norm_num)⟩

theorem exists_conj_le16 {A : Subgroup (MulAut (Wn 16))}
    (hA : A ≤ Subgroup.normalizer (img16 : Set (MulAut (Wn 16)))) (h2 : IsPGroup 2 A) :
    ∃ n ∈ Subgroup.normalizer (img16 : Set (MulAut (Wn 16))),
      A.map (MulAut.conj n).toMonoidHom ≤ rho16.range :=
  exists_conj_le_of_normalizer rho16GL rho16GL_frobGL rho16GL_grGL nc16 rho16GL_mem_range
    fld16_mem_range gr16_mem_range range_le_normalizer16 P16_le odd16 hA h2

end CFSG.Quasithin.H13.Ch9.L34N
