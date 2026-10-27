module

public import CFSG.Quasithin.Background.HF166
public import CFSG.Quasithin.Background.HF22Inputs

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem eq_one_of_octads {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm) {Pm Qm a b O2 : ℕ}
    {O1 : List ℕ}
    (hO1 : O1.all (fun c => syndM c == 0 && popc 24 c == 8 &&
      decide (5 ≤ popc 24 (c &&& Pm))) = true)
    (hsep : (List.range 24).all (fun i => i == a || i == b ||
      (List.range 24).all fun j => j == i || O1.any fun c => c.testBit i != c.testBit j) = true)
    (hO2 : syndM O2 = 0 ∧ popc 24 O2 = 8 ∧ 5 ≤ popc 24 (O2 &&& Qm) ∧ O2.testBit a = true ∧
      O2.testBit b = false)
    (hQ : ∀ i : Fin 24, Qm.testBit i = true ↔ (i : ℕ) ≠ a ∧ (i : ℕ) ≠ b)
    (ha : a < 24) (hb : b < 24) (hab : a ≠ b)
    (hP : ∀ i : Fin 24, Pm.testBit i = true → τ i = i) : τ = 1 := by
  have h1 : ∀ c ∈ O1, ∀ i : Fin 24, c.testBit (τ i) = c.testBit i := by
    intro c hc i
    have hok := List.all_eq_true.1 hO1 c hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    exact testBit_perm_of_permWord_eq (permWord_eq_of_mask hτ hok.1.1 hok.1.2 hok.2 hP) i
  have h2 : ∀ i : Fin 24, (i : ℕ) ≠ a → (i : ℕ) ≠ b → τ i = i := by
    intro i hia hib
    by_contra hne
    have hs := List.all_eq_true.1 hsep i (List.mem_range.2 i.2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
    rcases hs with (h | h) | h
    · exact hia h
    · exact hib h
    · have := h (τ i) (τ i).2
      simp only [List.any_eq_true, bne_iff_ne, ne_eq] at this
      rcases this with h' | ⟨c, hc, hne'⟩
      · exact hne (Fin.ext h')
      · exact hne' (h1 c hc i).symm
  have hP' : ∀ i : Fin 24, Qm.testBit i = true → τ i = i := fun i hi =>
    h2 i ((hQ i).1 hi).1 ((hQ i).1 hi).2
  have hO := testBit_perm_of_permWord_eq (permWord_eq_of_mask hτ hO2.1 hO2.2.1 hO2.2.2.1 hP')
  set pa : Fin 24 := ⟨a, ha⟩
  set pb : Fin 24 := ⟨b, hb⟩
  have hpa : τ pa = pa := by
    have hmem : (τ pa : ℕ) = a ∨ (τ pa : ℕ) = b := by
      by_contra hno
      push Not at hno
      have := τ.injective (h2 (τ pa) hno.1 hno.2)
      exact hno.1 (by rw [this])
    rcases hmem with h | h
    · exact Fin.ext h
    · exfalso
      have := hO pa
      rw [show τ pa = pb from Fin.ext h] at this
      have h3 : O2.testBit b = O2.testBit a := this
      rw [hO2.2.2.2.1, hO2.2.2.2.2] at h3
      exact absurd h3 (by decide)
  have hpb : τ pb = pb := by
    by_contra hne
    by_cases h : (τ pb : ℕ) = a
    · have : τ pb = τ pa := by rw [hpa]; exact Fin.ext h
      exact hab (congrArg Fin.val (τ.injective this)).symm
    · have h' : (τ pb : ℕ) ≠ b := fun h' => hne (Fin.ext h')
      exact hne (τ.injective (h2 (τ pb) h h'))
  ext i
  by_cases hia : (i : ℕ) = a
  · rw [show i = pa from Fin.ext hia, hpa]
    rfl
  · by_cases hib : (i : ℕ) = b
    · rw [show i = pb from Fin.ext hib, hpb]
      rfl
    · rw [h2 i hia hib]
      rfl

theorem psiC22_ofAdd (σ : ↥mog22plus) (x : Fin 24 → ZMod 2) :
    psiC22 σ (Multiplicative.ofAdd (κC22 x)) =
      Multiplicative.ofAdd (κC22 (permWord σ (lift22 (κC22 x)))) := rfl

theorem κC22_Ω : κC22 Ω = 0 :=
  (κC22_eq_zero_iff Ω_mem_C (by decide)).2 (Or.inr rfl)

theorem permWord_pair {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus) {x : Fin 24 → ZMod 2}
    (hx : x 0 + x 1 = 0) : permWord σ x 0 + permWord σ x 1 = 0 := by
  have hi : σ⁻¹ ∈ mog22plus := mog22plus.inv_mem hσ
  show x (σ⁻¹ 0) + x (σ⁻¹ 1) = 0
  rcases hi.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1, hx]
  · rw [h0, h1, add_comm, hx]

theorem lift22_κC22_cases {x : Fin 24 → ZMod 2} (hx : x ∈ C) (hx01 : x 0 + x 1 = 0) :
    lift22 (κC22 x) = x ∨ lift22 (κC22 x) = x + Ω := by
  have hd : lift22 (κC22 x) + x ∈ C := C.add_mem (lift22_mem _) hx
  have hd01 : (lift22 (κC22 x) + x) 0 + (lift22 (κC22 x) + x) 1 = 0 := by
    simp only [Pi.add_apply]
    have := lift22_pair (κC22 x)
    linear_combination this + hx01
  have hk : κC22 (lift22 (κC22 x) + x) = 0 := by
    rw [map_add, κC22_lift22]
    funext i
    exact CharTwo.add_self_eq_zero _
  rcases (κC22_eq_zero_iff hd hd01).1 hk with h | h
  · left
    funext i
    exact (zmod2_eq_of_add_eq_zero (congrFun h i)).symm
  · right
    funext i
    have := congrFun h i
    simp only [Pi.add_apply] at this ⊢
    exact zmod2_eq_add_one_of_add_eq_one this

theorem κC22_permWord_lift22 {σ : Equiv.Perm (Fin 24)} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (hx01 : x 0 + x 1 = 0) :
    κC22 (permWord σ (lift22 (κC22 x))) = κC22 (permWord σ x) := by
  rcases lift22_κC22_cases hx hx01 with h | h
  · rw [h]
  · rw [h, permWord_add, permWord_Ω, map_add, κC22_Ω, add_zero]

theorem permWord_eq_of_rhoC10 {σ : ↥mog22plus} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (hx01 : x 0 + x 1 = 0) (hw : hammingNorm x = 8)
    (hfix : psiC22 σ (Multiplicative.ofAdd (κC22 x)) = Multiplicative.ofAdd (κC22 x)) :
    permWord σ x = x := by
  rw [psiC22_ofAdd, κC22_permWord_lift22 hx hx01] at hfix
  have h1 : κC22 (permWord σ x) = κC22 x := congrArg Multiplicative.toAdd hfix
  have hy : permWord σ x ∈ C := permWord_mem_of_mem_AutPerm σ.2.1 hx
  have hy01 := permWord_pair σ.2 hx01
  have hd : permWord σ x + x ∈ C := C.add_mem hy hx
  have hd01 : (permWord σ x + x) 0 + (permWord σ x + x) 1 = 0 := by
    simp only [Pi.add_apply]
    linear_combination hy01 + hx01
  have hk : κC22 (permWord σ x + x) = 0 := by
    rw [map_add, h1]
    funext i
    exact CharTwo.add_self_eq_zero _
  rcases (κC22_eq_zero_iff hd hd01).1 hk with h | h
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

theorem rhoC10_fix_of_permWord_eq {σ : ↥mog22plus} {x : Fin 24 → ZMod 2} (hx : x ∈ C)
    (hx01 : x 0 + x 1 = 0) (h : permWord σ x = x) :
    psiC22 σ (Multiplicative.ofAdd (κC22 x)) = Multiplicative.ofAdd (κC22 x) := by
  rw [psiC22_ofAdd, κC22_permWord_lift22 hx hx01, h]

@[expose] def octW22 : List ℕ :=
  [0x93590, 0xf000f, 0x21d184, 0x28e414, 0x500a63, 0x812417, 0x871188, 0x881187, 0x8e2418,
    0xa6c00c, 0xa9c003]

@[expose] def oct1M22 : List ℕ :=
  [0xf000f, 0x81182b, 0x812417, 0x81428e, 0x81814d, 0x881187, 0x88224b, 0x88442d, 0x88881e,
    0x990066, 0x990099, 0xa9300c, 0xa9c003, 0xc9050a, 0xc90a05, 0xf0000f]

@[expose] def pt7Mask22 : ℕ := 0x89000f

@[expose] def fix4M22 : List ℕ := [2, 16, 19, 23]

theorem octW22_ok : octW22.all (fun c => syndM c == 0 && popc 24 c == 8 &&
    permM s0Arr22 c == c && c.testBit 0 == c.testBit 1) = true := by decide

theorem octW22_sep_fix : fix4M22.all (fun i => (List.range 24).all fun j =>
    j == i || octW22.any fun c => c.testBit i != c.testBit j) = true := by decide

theorem octW22_sep_three : (List.range 24).all (fun j =>
    j == 3 || j == 17 || j == 18 || octW22.any fun c => c.testBit 3 != c.testBit j) = true := by
  decide

theorem s0Arr22_fix : ([0, 1] ++ fix4M22).all (fun i => s0Arr22[i]! == i) = true ∧
    s0Arr22[3]! = 17 ∧ s0Arr22[17]! = 18 := by decide

theorem pt7Mask22_testBit (i : Fin 24) :
    pt7Mask22.testBit i = true ↔ (i : ℕ) ∈ [0, 1, 3] ++ fix4M22 := by
  revert i
  decide

theorem oct1M22_ok : oct1M22.all (fun c => syndM c == 0 && popc 24 c == 8 &&
    decide (5 ≤ popc 24 (c &&& pt7Mask22))) = true := by decide

theorem oct1M22_sep : (List.range 24).all (fun i => i == 17 || i == 18 ||
    (List.range 24).all fun j => j == i || oct1M22.any fun c => c.testBit i != c.testBit j) =
      true := by decide

theorem oct2M22_ok : syndM 0x3036a = 0 ∧ popc 24 0x3036a = 8 ∧
    5 ≤ popc 24 (0x3036a &&& 0xf9ffff) ∧ (0x3036a : ℕ).testBit 17 = true ∧
    (0x3036a : ℕ).testBit 18 = false := by decide

theorem testBit_f9ffff (i : Fin 24) :
    (0xf9ffff : ℕ).testBit i = true ↔ (i : ℕ) ≠ 17 ∧ (i : ℕ) ≠ 18 := by
  revert i
  decide

theorem eq_one_of_fix_seven22 {τ : Equiv.Perm (Fin 24)} (hτ : τ ∈ AutPerm)
    (hP : ∀ i : Fin 24, pt7Mask22.testBit i = true → τ i = i) : τ = 1 :=
  eq_one_of_octads hτ oct1M22_ok oct1M22_sep oct2M22_ok testBit_f9ffff (by norm_num)
    (by norm_num) (by norm_num) hP

theorem mem_zpowers_s0_22 {σ0 σ : ↥mog22plus} (h0 : HasArr (σ0 : Equiv.Perm (Fin 24)) s0Arr22)
    (hσ0 : (σ : Equiv.Perm (Fin 24)) 0 = 0)
    (hσ : ∀ w, psiC22 σ0 w = w → psiC22 σ w = w) : σ ∈ Subgroup.zpowers σ0 := by
  have h1 : ∀ c ∈ octW22, ∀ i : Fin 24,
      c.testBit ((σ : Equiv.Perm (Fin 24)) i) = c.testBit i := by
    intro c hc i
    have hok := List.all_eq_true.1 octW22_ok c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hsyn, hpc⟩, hperm⟩, h01⟩ := hok
    have hxC : bvec 24 c ∈ C := (bvec_mem_C_iff c).2 hsyn
    have hxw : hammingNorm (bvec 24 c) = 8 := by rw [hammingNorm_bvec, hpc]
    have hx01 : bvec 24 c 0 + bvec 24 c 1 = 0 := by
      have key : ∀ b1 b2 : Bool, b1 = b2 →
          ((if b1 = true then (1 : ZMod 2) else 0) + if b2 = true then 1 else 0) = 0 := by
        decide
      exact key _ _ h01
    have hfix0 : permWord (σ0 : Equiv.Perm (Fin 24)) (bvec 24 c) = bvec 24 c := by
      rw [permWord_bvec h0, hperm]
    exact testBit_perm_of_permWord_eq (permWord_eq_of_rhoC10 hxC hx01 hxw
      (hσ _ (rhoC10_fix_of_permWord_eq hxC hx01 hfix0))) i
  have hsep : ∀ i : Fin 24, (i : ℕ) ∈ fix4M22 → (σ : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    have hs := List.all_eq_true.1 octW22_sep_fix i hi
    have := List.all_eq_true.1 hs _ (List.mem_range.2 ((σ : Equiv.Perm (Fin 24)) i).2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | ⟨c, hc, hne⟩
    · exact Fin.ext h
    · exact absurd (h1 c hc i).symm hne
  have hσ1 : (σ : Equiv.Perm (Fin 24)) 1 = 1 := by
    rcases σ.2.2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (h.symm.trans hσ0) (by decide)
  have hfix : ∀ i : Fin 24, (i : ℕ) ∈ [0, 1] ++ fix4M22 → (σ : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · rw [show i = 0 from Fin.ext h]; exact hσ0
      · rw [show i = 1 from Fin.ext h]; exact hσ1
    · exact hsep i h
  set p3 : Fin 24 := ⟨3, by norm_num⟩ with hp3
  have h3 : ((σ : Equiv.Perm (Fin 24)) p3 : ℕ) = 3 ∨ ((σ : Equiv.Perm (Fin 24)) p3 : ℕ) = 17 ∨
      ((σ : Equiv.Perm (Fin 24)) p3 : ℕ) = 18 := by
    have := List.all_eq_true.1 octW22_sep_three _
      (List.mem_range.2 ((σ : Equiv.Perm (Fin 24)) p3).2)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with ((h | h) | h) | ⟨c, hc, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (h1 c hc p3).symm hne
  have hσ0fix : ∀ i : Fin 24, (i : ℕ) ∈ [0, 1] ++ fix4M22 →
      (σ0 : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    apply Fin.ext
    rw [h0 i]
    have := List.all_eq_true.1 s0Arr22_fix.1 i hi
    simpa using this
  have hσ0_3 : ((σ0 : Equiv.Perm (Fin 24)) p3 : ℕ) = 17 := by rw [h0 p3]; exact s0Arr22_fix.2.1
  have hσ0_17 : ((σ0 : Equiv.Perm (Fin 24)) ⟨17, by norm_num⟩ : ℕ) = 18 := by
    rw [h0 ⟨17, by norm_num⟩]; exact s0Arr22_fix.2.2
  have hpowfix : ∀ k : ℕ, ∀ i : Fin 24, (i : ℕ) ∈ [0, 1] ++ fix4M22 →
      ((σ0 ^ k : ↥mog22plus) : Equiv.Perm (Fin 24)) i = i := by
    intro k i hi
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Subgroup.coe_mul, Equiv.Perm.mul_apply, hσ0fix i hi, ih]
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      ((σ0 ^ k : ↥mog22plus) : Equiv.Perm (Fin 24)) p3 = (σ : Equiv.Perm (Fin 24)) p3 := by
    rcases h3 with h | h | h
    · exact ⟨0, by rw [pow_zero]; exact (Fin.ext h).symm⟩
    · exact ⟨1, by rw [pow_one]; exact Fin.ext (hσ0_3.trans h.symm)⟩
    · refine ⟨2, ?_⟩
      rw [pow_two, Subgroup.coe_mul, Equiv.Perm.mul_apply]
      have : (σ0 : Equiv.Perm (Fin 24)) p3 = ⟨17, by norm_num⟩ := Fin.ext hσ0_3
      rw [this]
      exact Fin.ext (hσ0_17.trans h.symm)
  set τ : ↥mog22plus := (σ0 ^ k)⁻¹ * σ with hτdef
  have hτ : ∀ i : Fin 24, pt7Mask22.testBit i = true → (τ : Equiv.Perm (Fin 24)) i = i := by
    intro i hi
    rw [pt7Mask22_testBit] at hi
    rw [hτdef, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_eq_iff_eq]
    have hi' : (i : ℕ) = 3 ∨ (i : ℕ) ∈ [0, 1] ++ fix4M22 := by
      rcases List.mem_append.1 hi with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h
        · right; simp [h]
        · right; simp [h]
        · left; exact h
      · right; exact List.mem_append_right _ h
    rcases hi' with h | h
    · have hi3 : i = p3 := Fin.ext h
      rw [hi3, hk]
    · rw [hfix i h, hpowfix k i h]
  have hτ1 : τ = 1 := Subtype.ext (eq_one_of_fix_seven22 τ.2.1 hτ)
  rw [hτdef, inv_mul_eq_one] at hτ1
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [zpow_natCast]; exact hτ1⟩

end CFSG.Quasithin.H.Mathieu
