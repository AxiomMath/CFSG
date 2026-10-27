module

public import CFSG.Quasithin.AppendixH.H16.OctadGroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH

theorem actC11_ko_xor_V5 : ∀ t : Fin 16, ∀ m ∈ combos oct5Basis,
    actC11 (koArr t) m ^^^ m = 0 ∨ actC11 (koArr t) m ^^^ m = 3 := by
  decide +kernel

theorem ko_faithful_V5 :
    ∀ t : Fin 16, (∀ b ∈ oct5Basis, actC11 (koArr t) b = b) → t = 0 := by
  decide +kernel

theorem ko_moves_V5 : ∀ m ∈ combos oct5Basis, m ≠ 0 → m ≠ 3 →
    ∃ t : Fin 16, actC11 (koArr t) m ≠ m := by
  decide +kernel

theorem ko_bits_surj : ∀ b₁ b₂ b₃ b₄ : Bool, ∃ t : Fin 16,
    (actC11 (koArr t) 12 != 12) = b₁ ∧ (actC11 (koArr t) 20 != 20) = b₂ ∧
    (actC11 (koArr t) 512 != 512) = b₃ ∧ (actC11 (koArr t) 1024 != 1024) = b₄ := by
  decide +kernel

theorem mem_octV1_iff (b : W11) : b ∈ octV1 ↔ b = 1 ∨ b = toW 11 3 := by
  rw [octV1, mem_maskSub]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have h : m = 0 ∨ m = 3 := by simpa [oct1Basis, combos] using hm
    rcases h with rfl | rfl
    · left; rw [toW_zero]
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, zero_mem_combos _, toW_zero 11⟩
    · exact ⟨3, mem_combos_of_mem (by simp [oct1Basis]), rfl⟩

theorem toW_three_ne_one : toW 11 3 ≠ 1 := by
  intro h
  have h' : toW 11 3 = toW 11 0 := by rw [toW_zero]; exact h
  exact absurd (toW_inj (by norm_num) (by norm_num) h') (by norm_num)

theorem ko11_mul_inv_mem_V1 (t : Fin 16) {x : W11} (hx : x ∈ octV5) : ko11 t x * x⁻¹ ∈ octV1 := by
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hx
  rw [ko11_toW, octW_inv, ← toW_xor, mem_octV1_iff]
  rcases actC11_ko_xor_V5 t m hm with h | h
  · left; rw [h, toW_zero]
  · right; rw [h]

theorem ko11_fix_three (t : Fin 16) : ko11 t (toW 11 3) = toW 11 3 := by
  rw [ko11_toW, actC11_ko_three]

theorem ko11_zero : ko11 0 = 1 := by
  have h : (⟨koPerm 0, (koPerm_mem_mog22 (0 : Fin 16)).1.1⟩ : ↥AutPerm) = 1 :=
    Subtype.ext koPerm_zero
  show rhoC11 AutPerm le_rfl ⟨koPerm 0, (koPerm_mem_mog22 (0 : Fin 16)).1.1⟩ = 1
  rw [h, map_one]

theorem ko11_eq_one_of_fix_V5 (t : Fin 16) (h : ∀ x ∈ octV5, ko11 t x = x) : t = 0 := by
  apply ko_faithful_V5
  intro b hb
  have hbV5 : toW 11 b ∈ octV5 := toW_mem_maskSub (mem_combos_of_mem hb)
  have hfix := h (toW 11 b) hbV5
  rw [ko11_toW] at hfix
  exact toW_inj (actC11_lt (koArr t) b) (oct5Basis_lt b hb) hfix

theorem imgCd_fixO_faithful_V5 : ∀ g ∈ imgCd fixO, (∀ x ∈ octV5, g x = x) → g = 1 := by
  intro g hg hfix
  obtain ⟨t, rfl⟩ := (mem_imgCd_fixO_iff g).1 hg
  rw [ko11_eq_one_of_fix_V5 t hfix, ko11_zero]

theorem exists_ko11_eq_of_transv (τ : MulAut ↥octV5)
    (hτ : ∀ x : ↥octV5, ((τ x : ↥octV5) : W11) * ((x : ↥octV5) : W11)⁻¹ ∈ octV1) :
    ∃ t : Fin 16, ∀ x : ↥octV5, ko11 t (x : W11) = ((τ x : ↥octV5) : W11) := by
  classical
  let c : W11 := toW 11 3
  have hc5 : c ∈ octV5 := octV1_le_octV5 ((mem_octV1_iff c).2 (Or.inr rfl))
  have hc_inv : c⁻¹ = c := octW_inv 3
  have hc_mul : c * c = 1 := by
    change toW 11 3 * toW 11 3 = 1
    rw [← toW_xor, Nat.xor_self, toW_zero]
  have htau_c : ((τ ⟨c, hc5⟩ : ↥octV5) : W11) = c := by
    have h := hτ ⟨c, hc5⟩
    change ((τ ⟨c, hc5⟩ : ↥octV5) : W11) * c⁻¹ ∈ octV1 at h
    rw [hc_inv] at h
    rcases (mem_octV1_iff _).1 h with h1 | h1
    · have h1' : ((τ ⟨c, hc5⟩ : ↥octV5) : W11) * c⁻¹ = 1 := by rw [hc_inv]; exact h1
      exact (mul_inv_eq_one).1 h1'
    · exfalso
      have h2 : ((τ ⟨c, hc5⟩ : ↥octV5) : W11) = 1 :=
        mul_right_cancel (h1.trans (one_mul c).symm)
      have h4 : (⟨c, hc5⟩ : ↥octV5) = 1 := by
        apply τ.injective
        rw [map_one]
        exact Subtype.ext (by simpa using h2)
      exact toW_three_ne_one (by simpa [c] using congrArg Subtype.val h4)
  have h12m : 12 ∈ oct5Basis := by simp [oct5Basis]
  have h20m : 20 ∈ oct5Basis := by simp [oct5Basis]
  have h512m : 512 ∈ oct5Basis := by simp [oct5Basis]
  have h1024m : 1024 ∈ oct5Basis := by simp [oct5Basis]
  have h12 : toW 11 12 ∈ octV5 := toW_mem_maskSub (mem_combos_of_mem h12m)
  have h20 : toW 11 20 ∈ octV5 := toW_mem_maskSub (mem_combos_of_mem h20m)
  have h512 : toW 11 512 ∈ octV5 := toW_mem_maskSub (mem_combos_of_mem h512m)
  have h1024 : toW 11 1024 ∈ octV5 := toW_mem_maskSub (mem_combos_of_mem h1024m)
  let b12 : Bool := decide ((τ ⟨toW 11 12, h12⟩ : ↥octV5) ≠ ⟨toW 11 12, h12⟩)
  let b20 : Bool := decide ((τ ⟨toW 11 20, h20⟩ : ↥octV5) ≠ ⟨toW 11 20, h20⟩)
  let b512 : Bool := decide ((τ ⟨toW 11 512, h512⟩ : ↥octV5) ≠ ⟨toW 11 512, h512⟩)
  let b1024 : Bool := decide ((τ ⟨toW 11 1024, h1024⟩ : ↥octV5) ≠ ⟨toW 11 1024, h1024⟩)
  obtain ⟨t, ht12, ht20, ht512, ht1024⟩ := ko_bits_surj b12 b20 b512 b1024
  have gen : ∀ (b : ℕ) (hb : toW 11 b ∈ octV5) (hm : b ∈ combos oct5Basis)
      (hbit : (actC11 (koArr t) b != b) = decide (τ ⟨toW 11 b, hb⟩ ≠ ⟨toW 11 b, hb⟩)),
      ko11 t (toW 11 b) = ((τ ⟨toW 11 b, hb⟩ : ↥octV5) : W11) := by
    intro b hb hm hbit
    rw [ko11_toW]
    by_cases hfix : τ ⟨toW 11 b, hb⟩ = ⟨toW 11 b, hb⟩
    · have hbit0 : (actC11 (koArr t) b != b) = false := by
        rw [hbit, decide_eq_false_iff_not]
        exact fun h => h hfix
      have hact : actC11 (koArr t) b = b := (bne_eq_false_iff_eq).1 hbit0
      rw [hact]
      exact (congrArg Subtype.val hfix).symm
    · have hbit1 : (actC11 (koArr t) b != b) = true := by
        rw [hbit, decide_eq_true_eq]
        exact hfix
      have hact_ne : actC11 (koArr t) b ≠ b := by
        rw [← bne_iff_ne]; exact hbit1
      have htx : ((τ ⟨toW 11 b, hb⟩ : ↥octV5) : W11) = toW 11 b * c := by
        have h := hτ ⟨toW 11 b, hb⟩
        rcases (mem_octV1_iff _).1 h with h1 | h1
        · exfalso
          exact hfix (Subtype.ext ((mul_inv_eq_one).1 h1))
        · have h2 : ((τ ⟨toW 11 b, hb⟩ : ↥octV5) : W11) = toW 11 3 * toW 11 b := by
            simpa [mul_assoc] using congrArg (· * toW 11 b) h1
          show ((τ ⟨toW 11 b, hb⟩ : ↥octV5) : W11) = toW 11 b * c
          rw [h2, mul_comm]
      have hact : actC11 (koArr t) b = b ^^^ 3 := by
        rcases actC11_ko_xor_V5 t b hm with h0 | h3
        · exfalso
          apply hact_ne
          have hh := congrArg (· ^^^ b) h0
          rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at hh
        · have hh := congrArg (· ^^^ b) h3
          rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.xor_comm] at hh
          exact hh
      rw [hact, htx]
      change toW 11 (b ^^^ 3) = toW 11 b * toW 11 3
      rw [← toW_xor]
  have g12 : ko11 t (toW 11 12) = ((τ ⟨toW 11 12, h12⟩ : ↥octV5) : W11) :=
    gen 12 h12 (mem_combos_of_mem h12m) ht12
  have g20 : ko11 t (toW 11 20) = ((τ ⟨toW 11 20, h20⟩ : ↥octV5) : W11) :=
    gen 20 h20 (mem_combos_of_mem h20m) ht20
  have g512 : ko11 t (toW 11 512) = ((τ ⟨toW 11 512, h512⟩ : ↥octV5) : W11) :=
    gen 512 h512 (mem_combos_of_mem h512m) ht512
  have g1024 : ko11 t (toW 11 1024) = ((τ ⟨toW 11 1024, h1024⟩ : ↥octV5) : W11) :=
    gen 1024 h1024 (mem_combos_of_mem h1024m) ht1024
  have g3 : ko11 t (toW 11 3) = ((τ ⟨toW 11 3, hc5⟩ : ↥octV5) : W11) := by
    rw [ko11_fix_three]
    exact htau_c.symm
  let P : ℕ → Prop := fun m => toW 11 m ∈ octV5 ∧
    ∀ hm : toW 11 m ∈ octV5, ko11 t (toW 11 m) = ((τ ⟨toW 11 m, hm⟩ : ↥octV5) : W11)
  have hP0 : P 0 := by
    refine ⟨?_, ?_⟩
    · rw [toW_zero]; exact octV5.one_mem
    · intro hm
      have h1 : ko11 t (toW 11 0) = 1 := by rw [toW_zero, map_one]
      rw [h1]
      have e : (⟨toW 11 0, hm⟩ : ↥octV5) = 1 := Subtype.ext (toW_zero 11)
      rw [e, map_one]
      rfl
  have hP : ∀ a b, P a → P b → P (a ^^^ b) := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · rw [toW_xor]; exact octV5.mul_mem ha.1 hb.1
    · intro hm
      have hmul : (⟨toW 11 (a ^^^ b), hm⟩ : ↥octV5) =
          ⟨toW 11 a, ha.1⟩ * ⟨toW 11 b, hb.1⟩ := Subtype.ext (toW_xor 11 a b)
      have htau : ((τ ⟨toW 11 (a ^^^ b), hm⟩ : ↥octV5) : W11) =
          ((τ ⟨toW 11 a, ha.1⟩ : ↥octV5) : W11) *
            ((τ ⟨toW 11 b, hb.1⟩ : ↥octV5) : W11) := by
        rw [hmul, map_mul]
        rfl
      rw [htau]
      have hko : ko11 t (toW 11 (a ^^^ b)) =
          ((τ ⟨toW 11 a, ha.1⟩ : ↥octV5) : W11) *
            ((τ ⟨toW 11 b, hb.1⟩ : ↥octV5) : W11) := by
        have h1 : ko11 t (toW 11 (a ^^^ b)) = ko11 t (toW 11 a) * ko11 t (toW 11 b) := by
          rw [toW_xor, map_mul]
        have e1 : ko11 t (toW 11 a) = ((τ ⟨toW 11 a, ha.1⟩ : ↥octV5) : W11) := ha.2 ha.1
        have e2 : ko11 t (toW 11 b) = ((τ ⟨toW 11 b, hb.1⟩ : ↥octV5) : W11) := hb.2 hb.1
        rw [h1]
        exact (congrArg (fun u => u * ko11 t (toW 11 b)) e1).trans
          (congrArg (fun v => ((τ ⟨toW 11 a, ha.1⟩ : ↥octV5) : W11) * v) e2)
      exact hko
  have hl : ∀ a ∈ oct5Basis, P a := by
    intro a ha
    simp only [oct5Basis, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · refine ⟨hc5, ?_⟩
      intro hm
      have e : (⟨toW 11 3, hm⟩ : ↥octV5) = ⟨c, hc5⟩ := Subtype.ext rfl
      rw [ko11_fix_three, e]
      exact htau_c.symm
    · refine ⟨h12, ?_⟩
      intro hm
      have e : (⟨toW 11 12, hm⟩ : ↥octV5) = ⟨toW 11 12, h12⟩ := Subtype.ext rfl
      rw [e]; exact g12
    · refine ⟨h20, ?_⟩
      intro hm
      have e : (⟨toW 11 20, hm⟩ : ↥octV5) = ⟨toW 11 20, h20⟩ := Subtype.ext rfl
      rw [e]; exact g20
    · refine ⟨h512, ?_⟩
      intro hm
      have e : (⟨toW 11 512, hm⟩ : ↥octV5) = ⟨toW 11 512, h512⟩ := Subtype.ext rfl
      rw [e]; exact g512
    · refine ⟨h1024, ?_⟩
      intro hm
      have e : (⟨toW 11 1024, hm⟩ : ↥octV5) = ⟨toW 11 1024, h1024⟩ := Subtype.ext rfl
      rw [e]; exact g1024
  refine ⟨t, ?_⟩
  intro x
  obtain ⟨m, hm, hx⟩ := mem_maskSub.1 x.2
  have hPm : P m := mem_of_combos P hP0 hP oct5Basis hl m hm
  have hmV5 : toW 11 m ∈ octV5 := by rw [hx]; exact x.2
  have hxm : (⟨toW 11 m, hmV5⟩ : ↥octV5) = x := Subtype.ext hx
  rw [← hx, ← hxm]
  exact hPm.2 hmV5

theorem fullTranspCenter_octV5 :
    FullTranspCenter (imgCd (octStab octad0)) (imgCd fixO) octV5 octV1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg x hx
    obtain ⟨t, rfl⟩ := (mem_imgCd_fixO_iff g).1 hg
    exact ko11_mul_inv_mem_V1 t hx
  · intro τ hτ
    obtain ⟨t, ht⟩ := exists_ko11_eq_of_transv τ hτ
    exact ⟨ko11 t, ko11_mem_imgCd_fixO t, ht⟩
  · intro g hg
    exact imgCd_fixO_faithful_V5 g hg
  · intro h hh g hg
    exact imgCd_fixO_normal h hh g hg

open scoped Classical in
private noncomputable def pairBit {V : Type*} [One V] (u : V) : ZMod 2 :=
  if u = 1 then 0 else 1

private theorem pairBit_one {V : Type*} [One V] : pairBit (1 : V) = 0 := by
  unfold pairBit
  rw [if_pos rfl]

private theorem pairBit_eq_zero {V : Type*} [One V] (u : V) : pairBit u = 0 ↔ u = 1 := by
  unfold pairBit
  by_cases h : u = 1
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

open scoped Classical in
private noncomputable def transvPr {V : Type*} [CommGroup V] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (x : V) (k : S24) : ZMod 2 :=
  if h : k ∈ Γ then (if ρ ⟨k, h⟩ x * x⁻¹ = 1 then 0 else 1) else 0

private theorem transvPr_eq_pairBit {V : Type*} [CommGroup V] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) {x : V} {k : S24} (h : k ∈ Γ) :
    transvPr ρ x k = pairBit (ρ ⟨k, h⟩ x * x⁻¹) := by
  unfold transvPr
  rw [dif_pos h]
  rfl

theorem isDualOfConj_of_transv {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (G K : Subgroup S24) (A B : Subgroup V) (c : V) (hKΓ : K ≤ Γ)
    (hB : ∀ b : V, b ∈ B ↔ b = 1 ∨ b = c) (hc : c ≠ 1) (hBA : B ≤ A)
    (hfixc : ∀ g : ↥Γ, (g : S24) ∈ G → ρ g c = c)
    (htr : ∀ k : ↥Γ, (k : S24) ∈ K → ∀ x ∈ A, ρ k x * x⁻¹ ∈ B)
    (hfaith : ∀ k : ↥Γ, (k : S24) ∈ K → (∀ x ∈ A, ρ k x = x) → (k : S24) = 1)
    (hnd : ∀ x ∈ A, x ∉ B → ∃ k : ↥Γ, (k : S24) ∈ K ∧ ρ k x ≠ x) :
    IsDualOfConj ρ G A B K := by
  classical
  have hB1 : (1 : V) ∈ B := (hB 1).2 (Or.inl rfl)
  have hBc : c ∈ B := (hB c).2 (Or.inr rfl)
  have hc_mul : c * c = 1 := by
    have hmem : c * c ∈ B := B.mul_mem hBc hBc
    rcases (hB (c * c)).1 hmem with h | h
    · exact h
    · exact absurd (mul_right_cancel (h.trans (one_mul c).symm)) hc
  have hfixB_K : ∀ k : ↥Γ, (k : S24) ∈ K → ∀ b ∈ B, ρ k b = b := by
    intro k hk b hb
    rcases (hB b).1 hb with hb1 | hbc
    · rw [hb1, map_one]
    · rw [hbc]
      have hmem : ρ k c * c⁻¹ ∈ B := htr k hk c (hBA hBc)
      rcases (hB (ρ k c * c⁻¹)).1 hmem with h1 | h1
      · exact (mul_inv_eq_one).1 h1
      · exfalso
        have h2 : ρ k c = 1 := by
          have h3 := congrArg (· * c) h1
          rwa [mul_assoc, inv_mul_cancel, mul_one, hc_mul] at h3
        exact hc ((ρ k).injective (by rw [map_one]; exact h2))
  have hfixB_G : ∀ g : ↥Γ, (g : S24) ∈ G → ∀ b ∈ B, ρ g b = b := by
    intro g hg b hb
    rcases (hB b).1 hb with hb1 | hbc
    · rw [hb1, map_one]
    · rw [hbc]
      exact hfixc g hg
  have hu_mul : ∀ (k k' : ↥Γ), (k : S24) ∈ K → (k' : S24) ∈ K → ∀ x ∈ A,
      ρ (k * k') x * x⁻¹ = (ρ k x * x⁻¹) * (ρ k' x * x⁻¹) := by
    intro k k' hk hk' x hx
    have hu : ρ k' x * x⁻¹ ∈ B := htr k' hk' x hx
    have hstep : ρ k (ρ k' x) * x⁻¹ = (ρ k' x * x⁻¹) * (ρ k x * x⁻¹) := by
      have hx' : ρ k' x = (ρ k' x * x⁻¹) * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
      conv_lhs => rw [hx']
      rw [map_mul, hfixB_K k hk _ hu, mul_assoc]
    rw [map_mul, MulAut.mul_apply, hstep, mul_comm]
  have hu_add : ∀ (k : ↥Γ) (x x' : V), x ∈ A → x' ∈ A →
      ρ k (x * x') * (x * x')⁻¹ = (ρ k x * x⁻¹) * (ρ k x' * x'⁻¹) := by
    intro k x x' hx hx'
    rw [map_mul, mul_inv_rev]
    ac_rfl
  have hc1 : pairBit c = 1 := by unfold pairBit; rw [if_neg hc]
  have pairBit_add : ∀ u ∈ B, ∀ v ∈ B, pairBit (u * v) = pairBit u + pairBit v := by
    intro u hu v hv
    rcases (hB u).1 hu with rfl | rfl <;> rcases (hB v).1 hv with rfl | rfl
    · rw [one_mul, pairBit_one]; decide
    · rw [one_mul, pairBit_one, hc1]; decide
    · rw [mul_one, pairBit_one, hc1]; decide
    · rw [hc1, hc_mul, pairBit_one]; decide
  refine ⟨transvPr ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    have hkk' : k * k' ∈ K := K.mul_mem hk hk'
    rw [transvPr_eq_pairBit ρ (hKΓ hkk'), transvPr_eq_pairBit ρ (hKΓ hk),
      transvPr_eq_pairBit ρ (hKΓ hk')]
    have harg : ρ ⟨k * k', hKΓ hkk'⟩ x * x⁻¹ =
        (ρ ⟨k, hKΓ hk⟩ x * x⁻¹) * (ρ ⟨k', hKΓ hk'⟩ x * x⁻¹) := by
      have e : (⟨k * k', hKΓ hkk'⟩ : ↥Γ) = ⟨k, hKΓ hk⟩ * ⟨k', hKΓ hk'⟩ := rfl
      rw [e]
      exact hu_mul ⟨k, hKΓ hk⟩ ⟨k', hKΓ hk'⟩ hk hk' x hx
    rw [harg]
    exact pairBit_add _ (htr ⟨k, hKΓ hk⟩ hk x hx) _ (htr ⟨k', hKΓ hk'⟩ hk' x hx)
  · intro x hx x' hx' k hk
    rw [transvPr_eq_pairBit ρ (hKΓ hk), transvPr_eq_pairBit ρ (hKΓ hk),
      transvPr_eq_pairBit ρ (hKΓ hk)]
    rw [hu_add ⟨k, hKΓ hk⟩ x x' hx hx']
    exact pairBit_add _ (htr ⟨k, hKΓ hk⟩ hk x hx) _ (htr ⟨k, hKΓ hk⟩ hk x' hx')
  · intro x hx k hk
    rw [transvPr_eq_pairBit ρ (hKΓ hk)]
    have hfx : ρ ⟨k, hKΓ hk⟩ x = x := hfixB_K ⟨k, hKΓ hk⟩ hk x hx
    rw [hfx, mul_inv_cancel, pairBit_one]
  · intro x hx hxB
    obtain ⟨k, hk, hkx⟩ := hnd x hx hxB
    refine ⟨k, hk, ?_⟩
    rw [transvPr_eq_pairBit ρ (hKΓ hk)]
    intro hzero
    have h1 : ρ ⟨k, hKΓ hk⟩ x * x⁻¹ = 1 := (pairBit_eq_zero _).1 hzero
    exact hkx ((mul_inv_eq_one).1 h1)
  · intro k hk hk1
    have hkne : (⟨k, hKΓ hk⟩ : ↥Γ) ≠ 1 := by
      intro h
      exact hk1 (Subtype.ext_iff.mp h)
    have hnotfix : ¬ (∀ x ∈ A, ρ ⟨k, hKΓ hk⟩ x = x) := by
      intro hfix
      exact hkne (Subtype.ext (hfaith ⟨k, hKΓ hk⟩ hk hfix))
    push Not at hnotfix
    obtain ⟨x, hxA, hxne⟩ := hnotfix
    refine ⟨x, hxA, ?_⟩
    rw [transvPr_eq_pairBit ρ (hKΓ hk)]
    intro hzero
    have h1 : ρ ⟨k, hKΓ hk⟩ x * x⁻¹ = 1 := (pairBit_eq_zero _).1 hzero
    exact hxne ((mul_inv_eq_one).1 h1)
  · intro g hg x hx k hk
    have hconjΓ : (g : S24) * k * (g : S24)⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem g.2 (hKΓ hk)) (Γ.inv_mem g.2)
    rw [transvPr_eq_pairBit ρ hconjΓ, transvPr_eq_pairBit ρ (hKΓ hk)]
    have hmain : ρ ⟨(g : S24) * k * (g : S24)⁻¹, hconjΓ⟩ (ρ g x) * (ρ g x)⁻¹ =
        ρ ⟨k, hKΓ hk⟩ x * x⁻¹ := by
      have e : (⟨(g : S24) * k * (g : S24)⁻¹, hconjΓ⟩ : ↥Γ) =
          g * ⟨k, hKΓ hk⟩ * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [← map_inv, ← map_mul]
      exact hfixB_G g hg _ (htr ⟨k, hKΓ hk⟩ hk x hx)
    rw [hmain]

theorem isDualOfConj_octV5 :
    IsDualOfConj (rhoC11 AutPerm le_rfl) (octStab octad0) octV5 octV1 fixO := by
  refine isDualOfConj_of_transv (rhoC11 AutPerm le_rfl) (octStab octad0) fixO octV5 octV1
    (toW 11 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm
  · exact mem_octV1_iff
  · exact toW_three_ne_one
  · exact octV1_le_octV5
  · intro g hg
    have hmem : rhoCd g.2 ∈ imgCd (octStab octad0) := rhoCd_mem_imgCd g.2 hg
    have h1 : rhoCd g.2 (toW 11 3) ∈ octV1 :=
      isActsInv_octV1 (fun v => rhoCd g.2 v) ⟨rhoCd g.2, hmem, rfl⟩ (toW 11 3)
        ((mem_octV1_iff _).2 (Or.inr rfl))
    rcases (mem_octV1_iff _).1 h1 with h2 | h2
    · exact absurd ((rhoCd g.2).injective (by rw [map_one]; exact h2)) toW_three_ne_one
    · exact h2
  · intro k hk x hx
    obtain ⟨t, ht⟩ := (mem_fixO_iff (k : S24)).1 hk
    have hk' : k = ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ := Subtype.ext ht
    rw [hk']
    exact ko11_mul_inv_mem_V1 t hx
  · intro k hk hfix
    obtain ⟨t, ht⟩ := (mem_fixO_iff (k : S24)).1 hk
    have hk' : k = ⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ := Subtype.ext ht
    have hfix' : ∀ x ∈ octV5, ko11 t x = x := by
      intro x hx
      have h := hfix x hx
      rw [hk'] at h
      exact h
    have ht0 : t = 0 := ko11_eq_one_of_fix_V5 t hfix'
    rw [ht, ht0, koPerm_zero]
  · intro x hx hx1
    obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hx
    have hm_lt : m < 2 ^ 11 := combos_lt oct5Basis_lt m hm
    have hm0 : m ≠ 0 := by
      intro h0
      apply hx1
      rw [h0, toW_zero]
      exact ⟨0, zero_mem_combos oct1Basis, toW_zero 11⟩
    have hm3 : m ≠ 3 := by
      intro h3
      apply hx1
      rw [h3]
      exact ⟨3, mem_combos_of_mem (by simp [oct1Basis]), rfl⟩
    obtain ⟨t, ht⟩ := ko_moves_V5 m hm hm0 hm3
    refine ⟨⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩, (mem_fixO_iff _).2 ⟨t, rfl⟩, ?_⟩
    change ko11 t (toW 11 m) ≠ toW 11 m
    intro h
    apply ht
    rw [ko11_toW] at h
    exact toW_inj (actC11_lt (koArr t) m) hm_lt h

end CFSG.ASVolI.H16
