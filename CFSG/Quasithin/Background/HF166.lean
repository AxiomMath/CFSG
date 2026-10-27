module

public import CFSG.Quasithin.Background.HF166Inputs
public import CFSG.Monster.Code.Cocycle
public import CFSG.Quasithin.Background.HMathieuFactsBase

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem zmod2_eq_of_add_eq_zero : ∀ {a b : ZMod 2}, a + b = 0 → b = a := by decide

theorem zmod2_eq_add_one_of_add_eq_one : ∀ {a b : ZMod 2}, a + b = 1 → a = b + 1 := by decide

theorem permWord_eq_of_mask {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {c Pm : ℕ}
    (hc : syndM c = 0) (hw : popc 24 c = 8) (h5 : 5 ≤ popc 24 (c &&& Pm))
    (hP : ∀ i : Fin 24, Pm.testBit i = true → σ i = i) :
    permWord σ (bvec 24 c) = bvec 24 c := by
  set x := bvec 24 c with hxdef
  have hx : x ∈ C := (bvec_mem_C_iff c).2 hc
  have hxw : hammingNorm x = 8 := by rw [hxdef, hammingNorm_bvec, hw]
  set y := permWord σ x with hydef
  have hy : y ∈ C := permWord_mem_of_mem_AutPerm hσ hx
  have hyw : hammingNorm y = 8 := (hammingNorm_comp_perm x σ⁻¹).trans hxw
  have hxy : 5 ≤ hammingNorm (x * y) := by
    calc 5 ≤ popc 24 (c &&& Pm) := h5
      _ = hammingNorm (bvec 24 (c &&& Pm)) := (hammingNorm_bvec 24 _).symm
      _ ≤ hammingNorm (x * y) := by
        unfold hammingNorm
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hb := (bvec_ne_zero_iff 24 _ i).1 hi
        rw [Nat.testBit_and, Bool.and_eq_true] at hb
        have hσi : σ⁻¹ i = i := by
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact (hP i hb.2).symm
        have hxi : x i = 1 := by simp [hxdef, bvec_apply, hb.1]
        have hyi : y i = 1 := by
          show x (σ⁻¹ i) = 1
          rw [hσi]
          exact hxi
        rw [Pi.mul_apply, hxi, hyi]
        exact one_ne_zero
  have hsum := hammingNorm_add_add x y
  have hlt : hammingNorm (x + y) < 8 := by omega
  by_contra hne
  have hne0 : x + y ≠ 0 := by
    intro h0
    apply hne
    funext i
    exact zmod2_eq_of_add_eq_zero (congrFun h0 i)
  have := eight_le_wt (C.add_mem hx hy) hne0
  omega

theorem testBit_perm_of_permWord_eq {σ : Equiv.Perm (Fin 24)} {c : ℕ}
    (h : permWord σ (bvec 24 c) = bvec 24 c) (i : Fin 24) :
    c.testBit (σ i) = c.testBit i := by
  have h1 := permWord_apply σ (bvec 24 c) i
  rw [h] at h1
  simp only [bvec_apply] at h1
  cases hb : c.testBit (σ i) <;> cases hc : c.testBit i <;> simp_all

theorem hammingNorm_add_Ω (x : Fin 24 → ZMod 2) : hammingNorm (x + Ω) + hammingNorm x = 24 := by
  have h := hammingNorm_add_add x Ω
  have hΩ : hammingNorm Ω = 24 := by decide
  have hxΩ : x * Ω = x := by
    funext i
    simp [Ω]
  rw [hxΩ, hΩ] at h
  omega

theorem permWord_Ω (σ : Equiv.Perm (Fin 24)) : permWord σ Ω = Ω := rfl

theorem permWord_add (σ : Equiv.Perm (Fin 24)) (x y : Fin 24 → ZMod 2) :
    permWord σ (x + y) = permWord σ x + permWord σ y := rfl

theorem psiC24_ofAdd (σ : ↥AutPerm) (x : Fin 24 → ZMod 2) :
    psiC24 σ (Multiplicative.ofAdd (κC x)) =
      Multiplicative.ofAdd (κC (permWord σ (liftC (κC x)))) := rfl

theorem liftC_κC_cases {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    liftC (κC x) = x ∨ liftC (κC x) = x + Ω := by
  have hd : liftC (κC x) + x ∈ C := C.add_mem (liftC_mem _) hx
  have hk : κC (liftC (κC x) + x) = 0 := by
    rw [map_add, κC_liftC]
    funext i
    exact CharTwo.add_self_eq_zero _
  rcases (κC_eq_zero_iff hd).1 hk with h | h
  · left
    funext i
    exact (zmod2_eq_of_add_eq_zero (congrFun h i)).symm
  · right
    funext i
    have := congrFun h i
    simp only [Pi.add_apply] at this ⊢
    exact zmod2_eq_add_one_of_add_eq_one this

theorem κC_permWord_liftC (σ : Equiv.Perm (Fin 24)) {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    κC (permWord σ (liftC (κC x))) = κC (permWord σ x) := by
  rcases liftC_κC_cases hx with h | h
  · rw [h]
  · rw [h, permWord_add, permWord_Ω, map_add, κC_Ω, add_zero]

theorem permWord_eq_of_rhoC11 {σ : ↥AutPerm} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (hw : hammingNorm x = 8)
    (hfix : psiC24 σ (Multiplicative.ofAdd (κC x)) = Multiplicative.ofAdd (κC x)) :
    permWord σ x = x := by
  rw [psiC24_ofAdd, κC_permWord_liftC _ hx] at hfix
  have h1 : κC (permWord σ x) = κC x := congrArg Multiplicative.toAdd hfix
  have hy : permWord σ x ∈ C := permWord_mem_of_mem_AutPerm σ.2 hx
  have hd : permWord σ x + x ∈ C := C.add_mem hy hx
  have hk : κC (permWord σ x + x) = 0 := by
    rw [map_add, h1]
    funext i
    exact CharTwo.add_self_eq_zero _
  rcases (κC_eq_zero_iff hd).1 hk with h | h
  · funext i
    exact (zmod2_eq_of_add_eq_zero (congrFun h i)).symm
  · exfalso
    have hyw : hammingNorm (permWord σ x) = 8 := (hammingNorm_comp_perm x _).trans hw
    have heq : permWord σ x = x + Ω := by
      funext i
      have := congrFun h i
      simp only [Pi.add_apply] at this ⊢
      exact zmod2_eq_add_one_of_add_eq_one this
    have := hammingNorm_add_Ω x
    rw [← heq, hyw, hw] at this
    omega

theorem rhoC11_fix_of_permWord_eq {σ : ↥AutPerm} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (h : permWord σ x = x) :
    psiC24 σ (Multiplicative.ofAdd (κC x)) = Multiplicative.ofAdd (κC x) := by
  rw [psiC24_ofAdd, κC_permWord_liftC _ hx, h]

@[expose] def oct0 : List ℕ :=
  [0x3c056, 0x5506c, 0x6903a, 0x960c5, 0xaa093, 0xc30a9, 0x114b44, 0x128b12, 0x141b28, 0x182b81,
    0x650c03, 0x81182b, 0x844847, 0x878811, 0x8d2882, 0x950303, 0xe14444, 0xe28412, 0xe41428,
    0xe82481, 0xf00f00]

@[expose] def oct1 : List ℕ :=
  [0x50a36, 0x53905, 0xf000f, 0x118887, 0x650c03, 0x81182b, 0x812417, 0x844847, 0x878811,
    0x8d2882, 0x950303, 0x950c0c, 0xa30906, 0xa500a5, 0xc59006, 0xc90a05]

@[expose] def pt7Mask : ℕ := 0x850807

@[expose] def fix6 : List ℕ := [0, 1, 11, 16, 18, 23]

theorem oct0_ok : oct0.all (fun c => syndM c == 0 && popc 24 c == 8 && permM s0Arr c == c) =
    true := by decide

theorem oct0_sep_fix : fix6.all (fun i => (List.range 24).all fun j =>
    j == i || oct0.any fun c => c.testBit i != c.testBit j) = true := by decide

theorem oct0_sep_two : (List.range 24).all (fun j =>
    j == 2 || j == 6 || j == 14 || oct0.any fun c => c.testBit 2 != c.testBit j) = true := by
  decide

theorem oct1_ok : oct1.all (fun c => syndM c == 0 && popc 24 c == 8 &&
    decide (5 ≤ popc 24 (c &&& pt7Mask))) = true := by decide

theorem oct1_sep : (List.range 24).all (fun i => i == 6 || i == 14 ||
    (List.range 24).all fun j => j == i || oct1.any fun c => c.testBit i != c.testBit j) =
      true := by decide

theorem oct2_ok : syndM 0xff = 0 ∧ popc 24 0xff = 8 ∧ 5 ≤ popc 24 (0xff &&& 0xffbfbf) ∧
    (0xff : ℕ).testBit 6 = true ∧ (0xff : ℕ).testBit 14 = false := by decide

theorem s0Arr_fix : fix6.all (fun i => s0Arr[i]! == i) = true ∧ s0Arr[2]! = 6 ∧
    s0Arr[6]! = 14 ∧ s0Arr[14]! = 2 := by decide

theorem pt7Mask_testBit (i : Fin 24) : pt7Mask.testBit i = true ↔ (i : ℕ) ∈ 2 :: fix6 := by
  revert i
  decide

theorem testBit_ffbfbf (i : Fin 24) :
    (0xffbfbf : ℕ).testBit i = true ↔ (i : ℕ) ≠ 6 ∧ (i : ℕ) ≠ 14 := by
  revert i
  decide

theorem eq_one_of_fix_seven {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm)
    (hP : ∀ i : Fin 24, pt7Mask.testBit i = true → τ i = i) : τ = 1 := by
  have h1 : ∀ c ∈ oct1, ∀ i : Fin 24, c.testBit (τ i) = c.testBit i := by
    intro c hc i
    have hok := List.all_eq_true.1 oct1_ok c hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    exact testBit_perm_of_permWord_eq (permWord_eq_of_mask hτ hok.1.1 hok.1.2 hok.2 hP) i
  have h2 : ∀ i : Fin 24, (i : ℕ) ≠ 6 → (i : ℕ) ≠ 14 → τ i = i := by
    intro i h6 h14
    by_contra hne
    have hs := List.all_eq_true.1 oct1_sep i (List.mem_range.2 i.2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
    rcases hs with (h | h) | h
    · exact h6 h
    · exact h14 h
    · have := h (τ i) (τ i).2
      simp only [List.any_eq_true, bne_iff_ne, ne_eq] at this
      rcases this with h' | ⟨c, hc, hne'⟩
      · exact hne (Fin.ext h')
      · exact hne' (h1 c hc i).symm
  have hP' : ∀ i : Fin 24, (0xffbfbf : ℕ).testBit i = true → τ i = i := fun i hi =>
    h2 i ((testBit_ffbfbf i).1 hi).1 ((testBit_ffbfbf i).1 hi).2
  have hO := testBit_perm_of_permWord_eq (permWord_eq_of_mask hτ oct2_ok.1 oct2_ok.2.1
    oct2_ok.2.2.1 hP')
  set p6 : Fin 24 := ⟨6, by norm_num⟩
  set p14 : Fin 24 := ⟨14, by norm_num⟩
  have h6 : τ p6 = p6 := by
    have hmem : (τ p6 : ℕ) = 6 ∨ (τ p6 : ℕ) = 14 := by
      by_contra hno
      push Not at hno
      have := h2 (τ p6) hno.1 hno.2
      have := τ.injective this
      exact hno.1 (by rw [this])
    rcases hmem with h | h
    · exact Fin.ext h
    · exfalso
      have := hO p6
      rw [show τ p6 = p14 from Fin.ext h] at this
      rw [oct2_ok.2.2.2.2] at this
      exact absurd (this.trans oct2_ok.2.2.2.1) (by decide)
  have h14 : τ p14 = p14 := by
    by_contra hne
    by_cases h : (τ p14 : ℕ) = 6
    · have : τ p14 = τ p6 := by rw [h6]; exact Fin.ext h
      exact absurd (congrArg Fin.val (τ.injective this)) (by decide)
    · have h' : (τ p14 : ℕ) ≠ 14 := fun h' => hne (Fin.ext h')
      exact hne (τ.injective (h2 (τ p14) h h'))
  ext i
  by_cases hi6 : (i : ℕ) = 6
  · rw [show i = p6 from Fin.ext hi6, h6]
    rfl
  · by_cases hi14 : (i : ℕ) = 14
    · rw [show i = p14 from Fin.ext hi14, h14]
      rfl
    · rw [h2 i hi6 hi14]
      rfl

theorem mem_zpowers_s0 {σ0 σ : ↥AutPerm} (h0 : HasArr (σ0 : Equiv.Perm (Fin 24)) s0Arr)
    (hσ : ∀ w, psiC24 σ0 w = w → psiC24 σ w = w) : σ ∈ Subgroup.zpowers σ0 := by
  have h1 : ∀ c ∈ oct0, ∀ i : Fin 24,
      c.testBit ((σ : Equiv.Perm (Fin 24)) i) = c.testBit i := by
    intro c hc i
    have hok := List.all_eq_true.1 oct0_ok c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hsyn, hpc⟩, hperm⟩ := hok
    have hxC : bvec 24 c ∈ C := (bvec_mem_C_iff c).2 hsyn
    have hxw : hammingNorm (bvec 24 c) = 8 := by rw [hammingNorm_bvec, hpc]
    have hfix0 : permWord (σ0 : Equiv.Perm (Fin 24)) (bvec 24 c) = bvec 24 c := by
      rw [permWord_bvec h0, hperm]
    exact testBit_perm_of_permWord_eq
      (permWord_eq_of_rhoC11 hxC hxw (hσ _ (rhoC11_fix_of_permWord_eq hxC hfix0))) i
  have hfix : ∀ i : Fin 24, (i : ℕ) ∈ fix6 → (σ : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    have hs := List.all_eq_true.1 oct0_sep_fix i hi
    have := List.all_eq_true.1 hs _ (List.mem_range.2 ((σ : Equiv.Perm (Fin 24)) i).2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | ⟨c, hc, hne⟩
    · exact Fin.ext h
    · exact absurd (h1 c hc i).symm hne
  set p2 : Fin 24 := ⟨2, by norm_num⟩ with hp2
  have h2 : ((σ : Equiv.Perm (Fin 24)) p2 : ℕ) = 2 ∨ ((σ : Equiv.Perm (Fin 24)) p2 : ℕ) = 6 ∨
      ((σ : Equiv.Perm (Fin 24)) p2 : ℕ) = 14 := by
    have := List.all_eq_true.1 oct0_sep_two _
      (List.mem_range.2 ((σ : Equiv.Perm (Fin 24)) p2).2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with ((h | h) | h) | ⟨c, hc, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (h1 c hc p2).symm hne
  have hσ0fix : ∀ i : Fin 24, (i : ℕ) ∈ fix6 → (σ0 : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    apply Fin.ext
    rw [h0 i]
    have := List.all_eq_true.1 s0Arr_fix.1 i hi
    simpa using this
  have hσ0_2 : ((σ0 : Equiv.Perm (Fin 24)) p2 : ℕ) = 6 := by rw [h0 p2]; exact s0Arr_fix.2.1
  have hσ0_6 : ((σ0 : Equiv.Perm (Fin 24)) ⟨6, by norm_num⟩ : ℕ) = 14 := by
    rw [h0 ⟨6, by norm_num⟩]; exact s0Arr_fix.2.2.1
  have hpowfix : ∀ k : ℕ, ∀ i : Fin 24, (i : ℕ) ∈ fix6 →
      ((σ0 ^ k : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i := by
    intro k i hi
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Subgroup.coe_mul, Equiv.Perm.mul_apply, hσ0fix i hi, ih]
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      ((σ0 ^ k : ↥AutPerm) : Equiv.Perm (Fin 24)) p2 = (σ : Equiv.Perm (Fin 24)) p2 := by
    rcases h2 with h | h | h
    · exact ⟨0, by rw [pow_zero]; exact (Fin.ext h).symm⟩
    · exact ⟨1, by rw [pow_one]; exact Fin.ext (hσ0_2.trans h.symm)⟩
    · refine ⟨2, ?_⟩
      rw [pow_two, Subgroup.coe_mul, Equiv.Perm.mul_apply]
      have : (σ0 : Equiv.Perm (Fin 24)) p2 = ⟨6, by norm_num⟩ := Fin.ext hσ0_2
      rw [this]
      exact Fin.ext (hσ0_6.trans h.symm)
  set τ : ↥AutPerm := (σ0 ^ k)⁻¹ * σ with hτdef
  have hτ : ∀ i : Fin 24, pt7Mask.testBit i = true → (τ : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    rw [pt7Mask_testBit] at hi
    rw [hτdef, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_eq_iff_eq]
    rcases List.mem_cons.1 hi with h | h
    · have hi2 : i = p2 := Fin.ext h
      rw [hi2, hk]
    · rw [hfix i h, hpowfix k i h]
  have hτ1 : τ = 1 := Subtype.ext (eq_one_of_fix_seven τ.2 hτ)
  rw [hτdef, inv_mul_eq_one] at hτ1
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [zpow_natCast]; exact hτ1⟩

end CFSG.Quasithin.H.Mathieu
