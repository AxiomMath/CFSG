module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitCoord
import CFSG.CGT.PushingUpLit.CGT6E.Emb55GL

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

@[expose] def fixSub {k : ℕ} (X : Matrix (Fin k) (Fin k) (ZMod 3)) :
    Submodule (ZMod 3) (Fin k → ZMod 3) where
  carrier := {v | X *ᵥ v = v}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [Matrix.mulVec_add, hv, hw]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [Matrix.mulVec_smul, hv]

theorem mem_fixSub {k : ℕ} {X : Matrix (Fin k) (Fin k) (ZMod 3)} {v : Fin k → ZMod 3} :
    v ∈ fixSub X ↔ X *ᵥ v = v :=
  Iff.rfl

theorem fixSub_ne_top {k : ℕ} {X : Matrix (Fin k) (Fin k) (ZMod 3)} (hX : X ≠ 1) :
    fixSub X ≠ ⊤ := by
  intro htop
  apply hX
  ext i j
  have h1 : Pi.single j 1 ∈ fixSub X := htop ▸ Submodule.mem_top
  rw [mem_fixSub, Matrix.mulVec_single_one] at h1
  have h2 := congrFun h1 i
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h2

theorem ne_bot_of_mem {k : ℕ} {W : Submodule (ZMod 3) (Fin k → ZMod 3)} {v : Fin k → ZMod 3}
    (hv : v ∈ W) (hv0 : v ≠ 0) : W ≠ ⊥ := by
  rintro rfl
  exact hv0 ((Submodule.mem_bot _).mp hv)

theorem fix_of_cube_entries : ∀ a b c d : ZMod 3,
    (!![a, b; c, d] : Mat2) * !![a, b; c, d] * !![a, b; c, d] = 1 →
      ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ (!![a, b; c, d] : Mat2) *ᵥ v = v := by
  decide +kernel

theorem fix_of_invol_entries : ∀ a b c d : ZMod 3,
    (!![a, b; c, d] : Mat2) * !![a, b; c, d] = 1 →
      (!![a, b; c, d] : Mat2) = -1 ∨
        ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ (!![a, b; c, d] : Mat2) *ᵥ v = v := by
  decide +kernel

theorem sq_of_two_transvections_entries : ∀ a b c d a' b' c' d' : ZMod 3,
    (!![a, b; c, d] : Mat2) * !![a, b; c, d] * !![a, b; c, d] = 1 →
    (!![a', b'; c', d'] : Mat2) * !![a', b'; c', d'] * !![a', b'; c', d'] = 1 →
    (!![a', b'; c', d'] : Mat2) ≠ 1 →
    ∀ w : Fin 2 → ZMod 3, (!![a', b'; c', d'] : Mat2) *ᵥ w = w →
      (!![a, b; c, d] : Mat2) *ᵥ w ≠ w →
      (!![a, b; c, d] * !![a', b'; c', d'] : Mat2) * (!![a, b; c, d] * !![a', b'; c', d']) = -1 ∨
        (!![a, b; c, d] * (!![a', b'; c', d'] * !![a', b'; c', d']) : Mat2) *
          (!![a, b; c, d] * (!![a', b'; c', d'] * !![a', b'; c', d'])) = -1 := by
  decide +kernel

theorem sq_of_two_element_entries : ∀ a b c d : ZMod 3,
    (!![a, b; c, d] : Mat2) ^ 16 = 1 → (!![a, b; c, d] : Mat2) * !![a, b; c, d] ≠ 1 →
      (!![a, b; c, d] : Mat2) * !![a, b; c, d] = -1 ∨
        ((!![a, b; c, d] : Mat2) * !![a, b; c, d]) * (!![a, b; c, d] * !![a, b; c, d]) = -1 := by
  decide +kernel

theorem fix_of_cube (X : Mat2) (h3 : X * X * X = 1) : ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ X *ᵥ v = v := by
  have := fix_of_cube_entries (X 0 0) (X 0 1) (X 1 0) (X 1 1)
  rw [← Matrix.eta_fin_two X] at this
  exact this h3

theorem fix_of_invol (X : Mat2) (h2 : X * X = 1) (hX : X ≠ -1) :
    ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ X *ᵥ v = v := by
  have := fix_of_invol_entries (X 0 0) (X 0 1) (X 1 0) (X 1 1)
  rw [← Matrix.eta_fin_two X] at this
  exact (this h2).resolve_left hX

theorem sq_of_two_transvections (X Y : Mat2) (hX : X * X * X = 1) (hY : Y * Y * Y = 1)
    (hY1 : Y ≠ 1) (w : Fin 2 → ZMod 3) (hYw : Y *ᵥ w = w) (hXw : X *ᵥ w ≠ w) :
    (X * Y) * (X * Y) = -1 ∨ (X * (Y * Y)) * (X * (Y * Y)) = -1 := by
  have := sq_of_two_transvections_entries (X 0 0) (X 0 1) (X 1 0) (X 1 1) (Y 0 0) (Y 0 1)
    (Y 1 0) (Y 1 1)
  rw [← Matrix.eta_fin_two X, ← Matrix.eta_fin_two Y] at this
  exact this hX hY hY1 w hYw hXw

theorem sq_of_two_element (X : Mat2) (h16 : X ^ 16 = 1) (h2 : X * X ≠ 1) :
    X * X = -1 ∨ (X * X) * (X * X) = -1 := by
  have := sq_of_two_element_entries (X 0 0) (X 0 1) (X 1 0) (X 1 1)
  rw [← Matrix.eta_fin_two X] at this
  exact this h16 h2

theorem card_GL_two : Nat.card (GL (Fin 2) (ZMod 3)) = 48 :=
  CFSG.CGT.PushingUpLit.CGT6E.natCard_gl23

theorem not_irreducible_of_scalar {M : Subgroup (GL (Fin 2) (ZMod 3))}
    (hM : CFSG.RankThree.SubgroupLists.IsIrreducibleOn M) :
    ∃ x ∈ M, x ≠ 1 ∧ x ≠ -1 := by
  by_contra hcon
  push Not at hcon
  set W : Submodule (ZMod 3) (Fin 2 → ZMod 3) := Submodule.span (ZMod 3) {Pi.single 0 1}
  have hinv : ∀ g ∈ M, ∀ w ∈ W, (g : Mat2) *ᵥ w ∈ W := by
    intro g hg w hw
    by_cases h1 : g = 1
    · rw [h1, Units.val_one, Matrix.one_mulVec]
      exact hw
    · rw [hcon g hg h1, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
      exact W.neg_mem hw
  rcases hM W hinv with h0 | h1
  · have : (Pi.single 0 1 : Fin 2 → ZMod 3) ∈ W := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at this
    have := congrFun this 0
    simp at this
  · have : (Pi.single 1 1 : Fin 2 → ZMod 3) ∈ W := h1 ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have := congrFun hc 1
    simp at this

theorem exists_sq_eq_neg_one {M : Subgroup (GL (Fin 2) (ZMod 3))}
    (hM : CFSG.RankThree.SubgroupLists.IsIrreducibleOn M) : ∃ s ∈ M, s * s = -1 := by
  by_cases h3 : ∃ x ∈ M, x * x * x = 1 ∧ x ≠ 1
  · obtain ⟨x, hxM, hx3, hx1⟩ := h3
    have hX3 : (x : Mat2) * x * x = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, hx3, Units.val_one]
    have hX1 : (x : Mat2) ≠ 1 := fun e => hx1 (Units.ext (by rw [e, Units.val_one]))
    obtain ⟨v₀, hv₀, hxv₀⟩ := fix_of_cube _ hX3
    have hL0 : fixSub (x : Mat2) ≠ ⊥ := ne_bot_of_mem (mem_fixSub.mpr hxv₀) hv₀
    obtain ⟨g, hgM, v, hv, hgv⟩ : ∃ g ∈ M, ∃ v ∈ fixSub (x : Mat2),
        (g : Mat2) *ᵥ v ∉ fixSub (x : Mat2) := by
      by_contra hcon
      push Not at hcon
      rcases hM _ hcon with h0 | ht
      · exact hL0 h0
      · exact fixSub_ne_top hX1 ht
    set y : GL (Fin 2) (ZMod 3) := g * x * g⁻¹ with hy
    have hyM : y ∈ M := M.mul_mem (M.mul_mem hgM hxM) (M.inv_mem hgM)
    have hy3 : (y : Mat2) * y * y = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, hy]
      rw [show g * x * g⁻¹ * (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x * x) * g⁻¹ by group,
        hx3, mul_one, mul_inv_cancel, Units.val_one]
    have hy1 : (y : Mat2) ≠ 1 := by
      intro e
      apply hx1
      have : y = 1 := Units.ext (by rw [e, Units.val_one])
      rw [hy] at this
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have hyw : (y : Mat2) *ᵥ ((g : Mat2) *ᵥ v) = (g : Mat2) *ᵥ v := by
      rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, show g * x * g⁻¹ * g = g * x by group,
        Units.val_mul, ← Matrix.mulVec_mulVec, mem_fixSub.mp hv]
    rcases sq_of_two_transvections _ _ hX3 hy3 hy1 _ hyw hgv with e | e
    · exact ⟨x * y, M.mul_mem hxM hyM, Units.ext (by simpa using e)⟩
    · exact ⟨x * (y * y), M.mul_mem hxM (M.mul_mem hyM hyM), Units.ext (by simpa using e)⟩
  · push Not at h3
    have h16 : ∀ s ∈ M, s ^ 16 = 1 := by
      intro s hs
      have h48 : s ^ 48 = 1 := by
        rw [← card_GL_two]
        exact pow_card_eq_one'
      refine h3 _ (M.pow_mem hs 16) ?_
      rw [← pow_add, ← pow_add]
      exact h48
    by_cases h2 : ∃ s ∈ M, s * s ≠ 1
    · obtain ⟨s, hs, hs2⟩ := h2
      have hS16 : (s : Mat2) ^ 16 = 1 := by rw [← Units.val_pow_eq_pow_val, h16 s hs, Units.val_one]
      have hS2 : (s : Mat2) * s ≠ 1 := fun e => hs2 (Units.ext (by simpa using e))
      rcases sq_of_two_element _ hS16 hS2 with e | e
      · exact ⟨s, hs, Units.ext (by simpa using e)⟩
      · exact ⟨s * s, M.mul_mem hs hs, Units.ext (by simpa using e)⟩
    · push Not at h2
      have hcomm : ∀ s ∈ M, ∀ t ∈ M, s * t = t * s := by
        intro s hs t ht
        have h1 := inv_eq_of_mul_eq_one_right (h2 (s * t) (M.mul_mem hs ht))
        have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right (h2 s hs)
        have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right (h2 t ht)
        rw [mul_inv_rev, hs1, ht1] at h1
        exact h1.symm
      obtain ⟨x, hxM, hx1, hxm1⟩ := not_irreducible_of_scalar hM
      have hX2 : (x : Mat2) * x = 1 := by rw [← Units.val_mul, h2 x hxM, Units.val_one]
      have hXm1 : (x : Mat2) ≠ -1 := fun e => hxm1 (Units.ext (by rw [e, Units.val_neg,
        Units.val_one]))
      have hX1 : (x : Mat2) ≠ 1 := fun e => hx1 (Units.ext (by rw [e, Units.val_one]))
      obtain ⟨v₀, hv₀, hxv₀⟩ := fix_of_invol _ hX2 hXm1
      have hinv : ∀ g ∈ M, ∀ v ∈ fixSub (x : Mat2), (g : Mat2) *ᵥ v ∈ fixSub (x : Mat2) := by
        intro g hg v hv
        rw [mem_fixSub, Matrix.mulVec_mulVec, ← Units.val_mul, hcomm x hxM g hg, Units.val_mul,
          ← Matrix.mulVec_mulVec, mem_fixSub.mp hv]
      rcases hM _ hinv with h0 | ht
      · exact absurd h0 (ne_bot_of_mem (mem_fixSub.mpr hxv₀) hv₀)
      · exact absurd ht (fixSub_ne_top hX1)

variable {G : Type} [Group G] {A B N : Subgroup G}

theorem QuotHyp.elemB (h : QuotHyp A B N) : CFSG.Assembly.IsElemAbelian 3 B :=
  ⟨⟨⟨fun x y => Subtype.ext (h.comm (h.le x.2) (h.le y.2))⟩⟩, fun _ hx => h.cube (h.le hx)⟩

theorem eq_zero_of_neg_eq {k : ℕ} {v : Fin k → ZMod 3} (hv : -v = v) : v = 0 := by
  funext i
  have h1 := congrFun hv i
  simp only [Pi.neg_apply, Pi.zero_apply] at h1 ⊢
  generalize v i = a at h1 ⊢
  revert a
  decide

theorem SplitHyp.concl_of_card_nine [Finite G] (h : SplitHyp A B N) (hB : Nat.card B = 3 ^ 2)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a) :
    SplitConcl A B N := by
  obtain ⟨f⟩ := Sec12.exists_coords h.elemB hB
  obtain ⟨s, hsM, hs2⟩ := exists_sq_eq_neg_one (h.isIrreducibleOn_M1 f)
  obtain ⟨n, hn, hns⟩ := h.exists_of_mem_M1 f hsM
  have hw : n * n ∈ N := N.mul_mem hn hn
  have hwmat : matB f (h.nb hw) = -1 := by
    rw [show h.nb hw = h.nb hn * h.nb hn from rfl, map_mul, hns, hs2]
  have hq : TrivQ A B (n * n) := h.trivQ_sq hn
  have hfix : ∀ b ∈ B, (n * n) * b * (n * n)⁻¹ = b → b = 1 := by
    intro b hb hwb
    obtain ⟨v, rfl⟩ := exists_eltB f hb
    rw [h.conj_eltB_eq_iff f hw, hwmat, Units.val_neg, Units.val_one, Matrix.neg_mulVec,
      Matrix.one_mulVec] at hwb
    rw [eq_zero_of_neg_eq hwb, eltB_zero]
  obtain ⟨c, hcA, hcB, hwc⟩ := h.exists_fixed_of_fpf hw hq hfix
  refine h.exists_of_fixSet {r | ∃ hr : r ∈ N, matB f (h.nb hr) = -1} ?_ hcA hcB ?_ ?_
  · intro b hb hR
    exact hfix b hb (hR _ ⟨hw, hwmat⟩)
  · rintro r ⟨hr, hrm⟩
    rw [h.conj_eq_of_matB_eq f hfB hr hw (hrm.trans hwmat.symm) c hcA, hwc]
  · rintro m hm r ⟨hr, hrm⟩
    have hmr : m * r * m⁻¹ ∈ N := N.mul_mem (N.mul_mem hm hr) (N.inv_mem hm)
    refine ⟨m * r * m⁻¹, ⟨hmr, ?_⟩, fun a _ => rfl⟩
    rw [show h.nb hmr = h.nb hm * h.nb hr * (h.nb hm)⁻¹ from rfl, map_mul, map_mul, map_inv,
      hrm, mul_neg_one, neg_mul, mul_inv_cancel]

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
