module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem mulVec_sgnOn_apply {k : ℕ} (T : Finset (Fin k)) (v : Fin k → ZMod 3) (x : Fin k) :
    (spMat 1 (sgnOn T) *ᵥ v) x = sgnOn T x * v x := by
  simp only [spMat_mulVec, Equiv.Perm.one_symm, Equiv.Perm.one_apply]

theorem sgnOn_isolate {k : ℕ} {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l)
    (v : Fin k → ZMod 3) :
    (v - spMat 1 (sgnOn {i, j}) *ᵥ v) +
        spMat 1 (sgnOn {j, l}) *ᵥ (v - spMat 1 (sgnOn {i, j}) *ᵥ v) = Pi.single i (v i) := by
  funext x
  simp only [Pi.add_apply, mulVec_sgnOn_apply, Pi.sub_apply, sgnOn, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hxi : x = i
  · rw [hxi]
    simp only [true_or, if_true, Pi.single_eq_same, hij, hil, or_self, if_false]
    ring_nf
    rw [show (4 : ZMod 3) = 1 from rfl, mul_one]
  · rw [Pi.single_eq_of_ne hxi]
    by_cases hxj : x = j
    · rw [hxj]
      simp only [hij.symm, false_or, if_true, true_or]
      ring
    · simp only [hxi, hxj, false_or, if_false]
      by_cases hxl : x = l
      · simp only [hxl, if_true]
        ring
      · simp only [hxl, if_false]
        ring

theorem subset_of_evenFix0_invariant {n : ℕ} (hn : 3 ≤ n)
    {U : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3)}
    (hW : ∀ A ∈ evenFix0 n, ∀ u ∈ U, A *ᵥ u ∈ U) {v : Fin (n + 1) → ZMod 3} (hv : v ∈ U)
    {i : Fin (n + 1)} (hi0 : i ≠ 0) (hvi : v i ≠ 0) {w : Fin (n + 1) → ZMod 3} (hw : w 0 = 0) :
    w ∈ U := by
  have hcard : 1 < ((Finset.univ : Finset (Fin (n + 1))) \ {0, i}).card := by
    have h := Finset.le_card_sdiff ({0, i} : Finset (Fin (n + 1))) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hi0.symm] at h
    omega
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or] at hj hl
  obtain ⟨hj0, hji⟩ := hj
  obtain ⟨hl0, hli⟩ := hl
  have hT0 : ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → (0 : Fin (n + 1)) ∉ ({a, b} : Finset _) :=
    fun a b ha hb => by simp [ha.symm, hb.symm]
  have hd₁ := hW _ (sgnOn_mem_evenFix0 {i, j} (hT0 i j hi0 hj0)
    (by rw [Finset.card_pair (Ne.symm hji)]; exact even_two))
  have hd₂ := hW _ (sgnOn_mem_evenFix0 {j, l} (hT0 j l hj0 hl0)
    (by rw [Finset.card_pair hjl]; exact even_two))
  have huU : v - spMat 1 (sgnOn {i, j}) *ᵥ v ∈ U := U.sub_mem hv (hd₁ v hv)
  have hu'U := U.add_mem huU (hd₂ _ huU)
  have hei : Pi.single i 1 ∈ U := by
    have := U.smul_mem (v i)⁻¹ hu'U
    rwa [sgnOn_isolate (Ne.symm hji) (Ne.symm hli), ← Pi.single_smul', smul_eq_mul,
      inv_mul_cancel₀ hvi] at this
  have hek : ∀ k : Fin (n + 1), k ≠ 0 → Pi.single k 1 ∈ U := by
    intro k hk0
    have hP := hW _ (perm_mem_evenFix0 (Equiv.swap i k)
      (Equiv.swap_apply_of_ne_of_ne hi0.symm hk0.symm)) _ hei
    rwa [spMat_mulVec_single, Equiv.swap_apply_left, one_mul] at hP
  rw [← Finset.univ_sum_single w]
  refine U.sum_mem fun k _ => ?_
  by_cases hk0 : k = 0
  · subst hk0
    rw [hw, Pi.single_zero]
    exact U.zero_mem
  · have := U.smul_mem (w k) (hek k hk0)
    rwa [← Pi.single_smul', smul_eq_mul, mul_one] at this

theorem eq_top_of_A_le {n : ℕ} {U : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3)}
    (hA : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → w ∈ U) {v : Fin (n + 1) → ZMod 3} (hv : v ∈ U)
    (hv0 : v 0 ≠ 0) (w : Fin (n + 1) → ZMod 3) : w ∈ U := by
  have he : Pi.single 0 1 ∈ U := by
    have h1 : v - (v - Pi.single 0 (v 0)) ∈ U := U.sub_mem hv (hA _ (by simp))
    rw [sub_sub_cancel] at h1
    have := U.smul_mem (v 0)⁻¹ h1
    rwa [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hv0] at this
  have h2 : w - w 0 • Pi.single 0 1 ∈ U := hA _ (by simp)
  have := U.add_mem h2 (U.smul_mem (w 0) he)
  rwa [sub_add_cancel] at this

theorem transv_of_normal3_of_irred {n : ℕ}
    {Xg Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hirr : ∀ U : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3),
      (∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        Pi.single 0 1 → ∀ u ∈ U, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u ∈ U) →
      ∀ v ∈ U, ∀ i : Fin (n + 1), i ≠ 0 → v i ≠ 0 → ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → w ∈ U)
    (hfus : ∃ x ∈ Xg, ∃ i : Fin (n + 1), i ≠ 0 ∧
      ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i ≠ 0)
    (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hM3 : ∀ m ∈ Mg, m ^ 3 = 1) (hne : Mg ≠ ⊥) :
    (∀ x ∈ Xg, ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
        ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 = 0) ∧
      ∀ β : Fin (n + 1) → ZMod 3, β 0 = 0 → ∃ m ∈ Mg,
        (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 + β ∧
          ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
            (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v := by
  let F : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3) :=
    { carrier := {v | ∀ m ∈ Mg, (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v}
      add_mem' := fun {a b} ha hb m hm => by
        simp only [Set.mem_setOf_eq] at ha hb
        rw [Matrix.mulVec_add, ha m hm, hb m hm]
      zero_mem' := fun m _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv m hm => by
        simp only [Set.mem_setOf_eq] at hv
        rw [Matrix.mulVec_smul, hv m hm] }
  have hmemF : ∀ v, v ∈ F ↔ ∀ m ∈ Mg, (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v :=
    fun v => Iff.rfl
  have hFinv : ∀ x ∈ Xg, ∀ v ∈ F, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v ∈ F := by
    intro x hx v hv m hm
    have hm' : x⁻¹ * m * x ∈ Mg := by
      have := hMn x⁻¹ (Xg.inv_mem hx) m hm
      rwa [inv_inv] at this
    have hconj : m * x = x * (x⁻¹ * m * x) := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hconj, Units.val_mul, ← Matrix.mulVec_mulVec,
      hv _ hm']
  have hCF : ∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → ∀ u ∈ F, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u ∈ F :=
    fun x hx _ u hu => hFinv x hx u hu
  have hFne : ∃ v ∈ F, v ≠ 0 := by
    let act : MulAction ↥Mg (Fin (n + 1) → ZMod 3) :=
      { smul := fun g v => ((g : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v
        one_smul := fun v => by
          show ((1 : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v
          simp
        mul_smul := fun g h v => by
          show (((g * h : ↥Mg) : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v =
            ((g : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
              (((h : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v)
          rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul] }
    have hP : IsPGroup 3 ↥Mg := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, hM3 g g.2, Subgroup.coe_one])⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmod := hP.card_modEq_card_fixedPoints (Fin (n + 1) → ZMod 3)
    have hcardV : Nat.card (Fin (n + 1) → ZMod 3) = 3 ^ (n + 1) := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcardV] at hmod
    by_contra hcon
    push Not at hcon
    have hfix : MulAction.fixedPoints ↥Mg (Fin (n + 1) → ZMod 3) = {0} := by
      ext v
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hv
        exact hcon v (fun m hm => hv ⟨m, hm⟩)
      · rintro rfl g
        exact Matrix.mulVec_zero _
    rw [hfix, Nat.card_unique] at hmod
    have h3 : 3 ^ (n + 1) % 3 = 0 := by
      rw [pow_succ, Nat.mul_mod_left]
    unfold Nat.ModEq at hmod
    rw [h3] at hmod
    exact absurd hmod (by norm_num)
  obtain ⟨m₀, hm₀, hm₀1⟩ : ∃ m ∈ Mg, m ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall Mg).mpr h)
  have hfaith : ∀ m : GL (Fin (n + 1)) (ZMod 3),
      (∀ v : Fin (n + 1) → ZMod 3, (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v) → m = 1 := by
    intro m hm
    apply Units.ext
    rw [Units.val_one]
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [hm, Matrix.one_mulVec]
  have hFtop : ∃ w : Fin (n + 1) → ZMod 3, w ∉ F := by
    by_contra h
    push Not at h
    exact hm₀1 (hfaith m₀ fun v => h v m₀ hm₀)
  have hFA : ∀ w : Fin (n + 1) → ZMod 3, w 0 = 0 → w ∈ F := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ v ∈ F, ∀ i : Fin (n + 1), i ≠ 0 → v i = 0 := by
      intro v hv i hi
      by_contra hvi
      obtain ⟨w, hw0, hwF⟩ := hcon
      exact hwF (hirr F hCF v hv i hi hvi w hw0)
    obtain ⟨v, hvF, hv0⟩ := hFne
    have hv00 : v 0 ≠ 0 := by
      intro h
      apply hv0
      funext i
      by_cases hi : i = 0
      · rw [hi, h]; rfl
      · exact hsub v hvF i hi
    have he : Pi.single 0 1 ∈ F := by
      have he' : (v 0)⁻¹ • v = Pi.single 0 1 := by
        funext i
        by_cases hi : i = 0
        · subst hi
          simp [inv_mul_cancel₀ hv00]
        · simp [hsub v hvF i hi, hi]
      rw [← he']
      exact F.smul_mem _ hvF
    obtain ⟨x, hx, i, hi, hxi⟩ := hfus
    exact hxi (hsub _ (hFinv x hx _ he) i hi)
  have hFA' : ∀ v ∈ F, v 0 = 0 := by
    intro v hv
    by_contra h
    obtain ⟨w, hw⟩ := hFtop
    exact hw (eq_top_of_A_le hFA hv h w)
  refine ⟨fun x hx v hv => hFA' _ (hFinv x hx v (hFA v hv)), ?_⟩
  have hfixA : ∀ m ∈ Mg, ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
      (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v := fun m hm v hv => hFA v hv m hm
  have hcoord : ∀ m ∈ Mg, ((m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 1 := by
    intro m hm
    set c := ((m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 with hc
    have hlin : ∀ (y : GL (Fin (n + 1)) (ZMod 3)), y ∈ Mg → ∀ v : Fin (n + 1) → ZMod 3,
        ((y : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 =
          v 0 * ((y : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 := by
      intro y hy v
      have hv : v = v 0 • Pi.single 0 1 + (v - v 0 • Pi.single 0 1) := by abel
      have hA0 : ((v - v 0 • Pi.single 0 1 : Fin (n + 1) → ZMod 3)) 0 = 0 := by simp
      conv_lhs => rw [hv]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hfixA y hy _ hA0, Pi.add_apply, hA0, add_zero,
        Pi.smul_apply, smul_eq_mul]
    have hpow : ∀ k : ℕ, (((m ^ k : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) 0 = c ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, hlin m hm, ih, pow_succ', mul_comm]
    have h3 := hpow 3
    rw [hM3 m hm, Units.val_one, Matrix.one_mulVec, Pi.single_eq_same] at h3
    have : ∀ c : ZMod 3, 1 = c ^ 3 → c = 1 := by decide
    exact this c h3
  let I : Submodule (ZMod 3) (Fin (n + 1) → ZMod 3) :=
    { carrier := {β | ∃ m ∈ Mg,
        (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 + β}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨m, hm, hma⟩ := ha
        obtain ⟨m', hm', hmb⟩ := hb
        have hb0 : b 0 = 0 := by
          have := hcoord m' hm'
          rw [hmb, Pi.add_apply, Pi.single_eq_same] at this
          exact add_eq_left.mp this
        refine ⟨m * m', Mg.mul_mem hm hm', ?_⟩
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hmb, Matrix.mulVec_add, hma, hfixA m hm b hb0]
        abel
      zero_mem' := ⟨1, Mg.one_mem, by rw [Units.val_one, Matrix.one_mulVec, add_zero]⟩
      smul_mem' := fun c a ha => by
        have hval : c • a = c.val • a := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
        show ∃ m ∈ Mg, _
        rw [hval]
        obtain ⟨m, hm, hma⟩ := ha
        have ha0 : a 0 = 0 := by
          have := hcoord m hm
          rw [hma, Pi.add_apply, Pi.single_eq_same] at this
          exact add_eq_left.mp this
        induction c.val with
        | zero => exact ⟨1, Mg.one_mem, by rw [Units.val_one, Matrix.one_mulVec, zero_smul, add_zero]⟩
        | succ k ih =>
          obtain ⟨m', hm', hm'a⟩ := ih
          refine ⟨m * m', Mg.mul_mem hm hm', ?_⟩
          have hk0 : (k • a) 0 = 0 := by simp [ha0]
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hm'a, Matrix.mulVec_add, hma,
            hfixA m hm _ hk0, succ_nsmul]
          abel }
  have hCI : ∀ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → ∀ u ∈ I, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u ∈ I := by
    intro x hx hxe u hu
    obtain ⟨m, hm, hmu⟩ := hu
    have hxie : ((x⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1 = Pi.single 0 1 := by
      conv_lhs => rw [← hxe]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨x * m * x⁻¹, hMn x hx m hm, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxie, hmu,
      Matrix.mulVec_add, hxe]
  obtain ⟨β₀, hβ₀I, i, hi, hβi⟩ : ∃ β ∈ I, ∃ i : Fin (n + 1), i ≠ 0 ∧ β i ≠ 0 := by
    refine ⟨((m₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) - Pi.single 0 1,
      ⟨m₀, hm₀, by abel⟩, ?_⟩
    by_contra h
    push Not at h
    apply hm₀1
    refine hfaith m₀ fun v => ?_
    have he : (m₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      funext j
      by_cases hj : j = 0
      · subst hj
        rw [hcoord m₀ hm₀]
        simp
      · have := h j hj
        rw [Pi.sub_apply, sub_eq_zero] at this
        exact this
    have hv : v = v 0 • Pi.single 0 1 + (v - v 0 • Pi.single 0 1) := by abel
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, he, hfixA m₀ hm₀ _ (by simp)]
  intro β hβ
  obtain ⟨m, hm, hmβ⟩ := hirr I hCI β₀ hβ₀I i hi hβi β hβ
  exact ⟨m, hm, hmβ, hfixA m hm⟩

theorem orth_transv_of_normal3 {n : ℕ} (hn : 3 ≤ n)
    {Xg Mg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    (hW : ∀ A ∈ evenFix0 n, ∃ x ∈ Xg, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = A)
    (hfus : ∃ x ∈ Xg, ∃ i : Fin (n + 1), i ≠ 0 ∧
      ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) i ≠ 0)
    (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hM3 : ∀ m ∈ Mg, m ^ 3 = 1) (hne : Mg ≠ ⊥) :
    (∀ x ∈ Xg, ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
        ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v) 0 = 0) ∧
      ∀ β : Fin (n + 1) → ZMod 3, β 0 = 0 → ∃ m ∈ Mg,
        (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 + β ∧
          ∀ v : Fin (n + 1) → ZMod 3, v 0 = 0 →
            (m : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ v = v :=
  transv_of_normal3_of_irred (fun _ hU _ hv _ hi hvi _ hw =>
    subset_of_evenFix0_invariant hn (fun A hA u hu => by
      obtain ⟨x, hx, rfl⟩ := hW A hA
      obtain ⟨σ, s, -, ⟨hσ0, hs0, -⟩, hAσ⟩ := hA
      exact hU x hx (by rw [hAσ]; exact spMat_mulVec_e0 hσ0 hs0) u hu) hv hi hvi hw)
    hfus hMn hM3 hne

end CFSG.StandardType.FrameRoute.FS81

end
