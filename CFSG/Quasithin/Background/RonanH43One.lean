module

public import CFSG.Quasithin.Background.RonanH43Trv
public import CFSG.Quasithin.Background.RonanH43Fin
public import CFSG.Quasithin.Background.RonanH43Sub

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

theorem card_perp_three :
    ∀ φ : Fin 3 → ZMod 2, φ ≠ 0 →
      (Finset.univ.filter (fun v : Fin 3 → ZMod 2 => φ ⬝ᵥ v = 0)).card = 4 := by
  decide +kernel

theorem card_fixV_part1 {A : Subgroup (MulAut PV)} {a b : MulAut PV} {c φ : Fin 3 → ZMod 2}
    {H D : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA : ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) (haA : a ∈ A) (hbA : b ∈ A)
    (hc : c ≠ 0) (hφ : φ ≠ 0) (hφc : φ ⬝ᵥ c = 0)
    (ha : ∀ v w, a (mk v w) = mk (v + (φ ⬝ᵥ v) • c) (w + (c ⬝ᵥ w) • φ))
    (hb : ∀ v w, b (mk v w) = mk (D *ᵥ w) (H *ᵥ v))
    (hHs : Hᵀ = H) (hHc : H *ᵥ c = φ) (hDH : D * H = 1) :
    Nat.card ↥(fixV A) = 4 := by
  have hfix : ∀ x : PV, x ∈ fixV A ↔ a x = x ∧ b x = x := by
    intro x
    constructor
    · intro hx
      exact ⟨(CFSG.Quasithin.mem_fixV.mp hx) a haA, (CFSG.Quasithin.mem_fixV.mp hx) b hbA⟩
    · intro hx
      refine CFSG.Quasithin.mem_fixV.mpr ?_
      intro y hy
      rcases hA y hy with h | h | h | h
      · subst h
        rfl
      · rw [h]
        exact hx.1
      · rw [h]
        exact hx.2
      · rw [h]
        show a (b x) = x
        rw [hx.2, hx.1]
  have ha_fix : ∀ v w : Fin 3 → ZMod 2, a (mk v w) = mk v w ↔ φ ⬝ᵥ v = 0 ∧ c ⬝ᵥ w = 0 := by
    intro v w
    rw [ha, mk_inj]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa [hc] using h1, by simpa [hφ] using h2⟩
    · rintro ⟨h1, h2⟩
      simp [h1, h2]
  have hb_fix : ∀ v w : Fin 3 → ZMod 2, b (mk v w) = mk v w ↔ w = H *ᵥ v := by
    intro v w
    rw [hb, mk_inj]
    constructor
    · rintro ⟨_, h2⟩
      exact h2.symm
    · rintro rfl
      refine ⟨?_, rfl⟩
      rw [Matrix.mulVec_mulVec, hDH, Matrix.one_mulVec]
  have hcH : c ᵥ* H = φ := by
    rw [← Matrix.mulVec_transpose, hHs, hHc]
  have key : ∀ v : Fin 3 → ZMod 2, c ⬝ᵥ (H *ᵥ v) = φ ⬝ᵥ v := fun v => by
    rw [Matrix.dotProduct_mulVec, hcH]
  have hfixmk : ∀ v w : Fin 3 → ZMod 2, mk v w ∈ fixV A ↔ φ ⬝ᵥ v = 0 ∧ w = H *ᵥ v := by
    intro v w
    rw [hfix (mk v w), ha_fix v w, hb_fix v w]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [h3, key v]
      exact h1
  have hmem : ∀ x : PV, x ∈ fixV A ↔ φ ⬝ᵥ Multiplicative.toAdd x.1 = 0 ∧
      Multiplicative.toAdd x.2 = H *ᵥ Multiplicative.toAdd x.1 := by
    intro x
    have h := hfixmk (Multiplicative.toAdd x.1) (Multiplicative.toAdd x.2)
    rw [← eq_mk x] at h
    exact h
  have hrep : ∀ x : PV, x ∈ fixV A →
      mk (Multiplicative.toAdd x.1) (H *ᵥ Multiplicative.toAdd x.1) = x := by
    intro x hx
    rw [← ((hmem x).1 hx).2, ← eq_mk x]
  have hcard : Nat.card ↥(fixV A) = Nat.card {v : Fin 3 → ZMod 2 // φ ⬝ᵥ v = 0} :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1.1, ((hmem x.1).1 x.2).1⟩
        invFun := fun v => ⟨mk v.1 (H *ᵥ v.1), (hfixmk v.1 (H *ᵥ v.1)).2 ⟨v.2, rfl⟩⟩
        left_inv := fun x => Subtype.ext (hrep x.1 x.2)
        right_inv := fun v => rfl }
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_perp_three φ hφ

theorem p2_add_self : ∀ s : ZMod 2, s + s = 0 := by decide

theorem p2_add_add_cancel : ∀ s t : ZMod 2, s + (t + s) = t := by decide

theorem p2_vec_add_add_cancel (p q : Fin 3 → ZMod 2) : p + (q + p) = q := by
  funext i
  exact p2_add_add_cancel (p i) (q i)

theorem p2_mem_fixV {g : MulAut PV} {v : PV} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  mem_fixV_zpowers_iff_apply

theorem xi_eq_part1 {A : Subgroup (MulAut PV)} {a b : MulAut PV} {c φ : Fin 3 → ZMod 2}
    {H D : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA : ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) (haA : a ∈ A) (hbA : b ∈ A)
    (hc : c ≠ 0) (hφ : φ ≠ 0) (hφc : φ ⬝ᵥ c = 0)
    (ha : ∀ v w, a (mk v w) = mk (v + (φ ⬝ᵥ v) • c) (w + (c ⬝ᵥ w) • φ))
    (hb : ∀ v w, b (mk v w) = mk (D *ᵥ w) (H *ᵥ v))
    (hHs : Hᵀ = H) (hHc : H *ᵥ c = φ) (hDH : D * H = 1)
    (haa : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    xi A = hyper c φ := by
  have hcp : c ⬝ᵥ φ = 0 := (dotProduct_comm c φ).trans hφc
  have F3 : ∀ u : Fin 3 → ZMod 2, c ⬝ᵥ (H *ᵥ u) = φ ⬝ᵥ u := fun u => by
    rw [dotProduct_mulVec, ← hHs, vecMul_transpose, hHc]
  have hDv : ∀ u : Fin 3 → ZMod 2, D *ᵥ (H *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hDH, one_mulVec]
  apply le_antisymm
  · apply xi_le
    intro y hy hy1 x hx
    rw [p2_mem_fixV] at hx
    obtain ⟨v, w, rfl⟩ : ∃ v w, x = mk v w := ⟨_, _, eq_mk x⟩
    refine mem_hyper.2 ?_
    show φ ⬝ᵥ v + c ⬝ᵥ w = 0
    rcases hA y hy with h | h | h | h
    · exact absurd h hy1
    ·
      rw [h] at hx
      have h1 : mk (v + (φ ⬝ᵥ v) • c) (w + (c ⬝ᵥ w) • φ) = mk v w := (ha v w).symm.trans hx
      obtain ⟨e1, e2⟩ := mk_inj.1 h1
      have s1 : (φ ⬝ᵥ v) • c = 0 := add_left_cancel (e1.trans (add_zero v).symm)
      have s2 : (c ⬝ᵥ w) • φ = 0 := add_left_cancel (e2.trans (add_zero w).symm)
      have t1 : φ ⬝ᵥ v = 0 := (smul_eq_zero.1 s1).resolve_right hc
      have t2 : c ⬝ᵥ w = 0 := (smul_eq_zero.1 s2).resolve_right hφ
      rw [t1, t2, add_zero]
    ·
      rw [h] at hx
      have h1 : mk (D *ᵥ w) (H *ᵥ v) = mk v w := (hb v w).symm.trans hx
      obtain ⟨-, e2⟩ := mk_inj.1 h1
      have h3 : φ ⬝ᵥ v = c ⬝ᵥ w := by rw [← F3 v, e2]
      rw [h3, p2_add_self]
    ·
      rw [h, MulAut.mul_apply] at hx
      have h1 : (a * a) (b (mk v w)) = b (mk v w) := by rw [haa, MulAut.one_apply]
      rw [MulAut.mul_apply] at h1
      have hz : b (mk v w) = a (mk v w) := by rw [← h1, hx]
      rw [hb, ha] at hz
      obtain ⟨-, e2⟩ := mk_inj.1 hz
      have h3 : c ⬝ᵥ (H *ᵥ v) = c ⬝ᵥ w := by
        rw [e2, dotProduct_add, dotProduct_smul, hcp, smul_eq_mul, mul_zero, add_zero]
      have h4 : φ ⬝ᵥ v = c ⬝ᵥ w := (F3 v).symm.trans h3
      rw [h4, p2_add_self]
  · intro x hx
    obtain ⟨v, w, rfl⟩ : ∃ v w, x = mk v w := ⟨_, _, eq_mk x⟩
    have hsum : φ ⬝ᵥ v + c ⬝ᵥ w = 0 := mem_hyper.1 hx
    have hcw : c ⬝ᵥ (w + H *ᵥ v) = 0 := by
      rw [dotProduct_add, F3 v]
      linear_combination hsum
    have hB : mk v (H *ᵥ v) ∈ fixV (Subgroup.zpowers b) := by
      rw [p2_mem_fixV, hb, hDv]
    have hA' : mk 0 (w + H *ᵥ v) ∈ fixV (Subgroup.zpowers a) := by
      rw [p2_mem_fixV, ha, dotProduct_zero, zero_smul, zero_add, hcw, zero_smul, add_zero]
    have hfac : mk v w = mk v (H *ᵥ v) * mk 0 (w + H *ᵥ v) := by
      rw [mk_mul, add_zero, p2_vec_add_add_cancel]
    rw [hfac]
    exact Subgroup.mul_mem _ (fixV_le_xi hbA hb1 hB) (fixV_le_xi haA ha1 hA')

theorem swap_mul_swap (h' h : GL (Fin 3) (ZMod 2)) :
    (swapAut (ZMod 2) * pairHom h') * (swapAut (ZMod 2) * pairHom h) =
      pairHom (dualGL h' * h) := by
  have e := swapAut_conj (K := ZMod 2) h'
  rw [swapAut_inv] at e
  rw [map_mul, ← e]
  group

theorem pairHom_mul_swap (g : GL (Fin 3) (ZMod 2)) :
    pairHom g * swapAut (ZMod 2) = swapAut (ZMod 2) * pairHom (dualGL g) := by
  have e := swapAut_conj (K := ZMod 2) (dualGL g)
  rw [swapAut_inv, dualGL_dualGL] at e
  calc pairHom g * swapAut (ZMod 2)
      = (swapAut (ZMod 2) * pairHom (dualGL g) * swapAut (ZMod 2)) * swapAut (ZMod 2) := by
        rw [e]
    _ = swapAut (ZMod 2) * pairHom (dualGL g) := by
        rw [mul_assoc, swapAut_mul_self, mul_one]

theorem classify_four {A : Subgroup (MulAut PV)} (hA4 : Nat.card A = 4) {a b : MulAut PV}
    (haA : a ∈ A) (hbA : b ∈ A) (hbb : b * b = 1) (haL : a ∈ pairSL (ZMod 2)) (ha1 : a ≠ 1)
    (hbL : b ∉ pairSL (ZMod 2)) : ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ Subgroup.one_mem _)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  intro x hx
  have key := eq_of_card_four hA4 (a := (⟨1, A.one_mem⟩ : ↥A)) (b := ⟨a, haA⟩) (c := ⟨b, hbA⟩)
    (d := ⟨a * b, A.mul_mem haA hbA⟩)
    (fun h => ha1 (congrArg Subtype.val h).symm)
    (fun h => hb1 (congrArg Subtype.val h).symm)
    (fun h => by
      have h' : (1 : MulAut PV) = a * b := congrArg Subtype.val h
      apply hbL
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h'.symm
      rw [this]
      exact Subgroup.inv_mem _ haL)
    (fun h => by
      have h' : a = b := congrArg Subtype.val h
      exact hbL (h' ▸ haL))
    (fun h => by
      have h' : a = a * b := congrArg Subtype.val h
      have : a * b = a * 1 := by rw [mul_one]; exact h'.symm
      exact hb1 (mul_left_cancel this))
    (fun h => by
      have h' : b = a * b := congrArg Subtype.val h
      have : a * b = 1 * b := by rw [one_mul]; exact h'.symm
      exact ha1 (mul_right_cancel this))
    ⟨x, hx⟩
  rcases key with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem exists_ab {A : Subgroup (MulAut PV)} (hAN : A ≤ pairNorm (ZMod 2))
    (hA2 : IsElemAbelian2 A) (hA4 : Nat.card A = 4) (hAL : ¬ A ≤ pairSL (ZMod 2)) :
    ∃ a b : MulAut PV, a ∈ A ∧ b ∈ A ∧ a ∈ pairSL (ZMod 2) ∧ a ≠ 1 ∧ b ∉ pairSL (ZMod 2) ∧
      ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  haveI : Finite (MulAut PV) := MulEquiv.finite_left
  obtain ⟨b, hbA, hbL⟩ := SetLike.not_le_iff_exists.mp hAL
  have hbb : b * b = 1 := by rw [← sq]; exact hA2.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ Subgroup.one_mem _)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  obtain ⟨a', ha'A, ha'1, ha'b⟩ : ∃ a' ∈ A, a' ≠ 1 ∧ a' ≠ b := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers b := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · rw [hcon x hx hx1]
        exact Subgroup.mem_zpowers b
    have := Subgroup.card_le_of_le hle
    rw [card_zpowers_eq_two hbb hb1, hA4] at this
    omega
  by_cases ha'L : a' ∈ pairSL (ZMod 2)
  · exact ⟨a', b, ha'A, hbA, ha'L, ha'1, hbL, classify_four hA4 ha'A hbA hbb ha'L ha'1 hbL⟩
  · obtain ⟨h', ha'e⟩ := (norm_cases (hAN ha'A)).resolve_left ha'L
    obtain ⟨h, hbe⟩ := (norm_cases (hAN hbA)).resolve_left hbL
    have haA : a' * b ∈ A := A.mul_mem ha'A hbA
    have haL : a' * b ∈ pairSL (ZMod 2) := by
      rw [ha'e, hbe, swap_mul_swap]
      exact pairHom_mem_pairSL _
    have ha1 : a' * b ≠ 1 := by
      intro h1
      apply ha'b
      rw [eq_inv_of_mul_eq_one_left h1, hbinv]
    refine ⟨a' * b, b, haA, hbA, haL, ha1, hbL, ?_⟩
    have hcl := classify_four hA4 haA hbA hbb haL ha1 hbL
    exact hcl

theorem part1_data {a b : MulAut PV} (haL : a ∈ pairSL (ZMod 2)) (ha1 : a ≠ 1)
    (hbN : b ∈ pairNorm (ZMod 2)) (hbL : b ∉ pairSL (ZMod 2))
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) :
    ∃ (c φ : Fin 3 → ZMod 2) (H D : Matrix (Fin 3) (Fin 3) (ZMod 2)), c ≠ 0 ∧ φ ≠ 0 ∧
      φ ⬝ᵥ c = 0 ∧
      (∀ v w, a (mk v w) = mk (v + (φ ⬝ᵥ v) • c) (w + (c ⬝ᵥ w) • φ)) ∧
      (∀ v w, b (mk v w) = mk (D *ᵥ w) (H *ᵥ v)) ∧ Hᵀ = H ∧ H *ᵥ c = φ ∧ D * H = 1 := by
  obtain ⟨g, -, rfl⟩ := haL
  obtain ⟨h, rfl⟩ := (norm_cases hbN).resolve_left hbL
  have hgg : g * g = 1 := pairHom_injective (by rw [map_mul, map_one]; exact haa)
  have hg1 : g ≠ 1 := fun h' => ha1 (by rw [h', map_one])
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hdh : dualGL h * h = 1 := pairHom_injective (by
    have := swap_mul_swap h h
    rw [hbb] at this
    rw [map_one]
    exact this.symm)
  have hcomm : dualGL g * h = h * g := by
    have e1 : pairHom g * (swapAut (ZMod 2) * pairHom h) =
        swapAut (ZMod 2) * pairHom (dualGL g * h) := by
      rw [← mul_assoc, pairHom_mul_swap, mul_assoc, ← map_mul]
    have e2 : (swapAut (ZMod 2) * pairHom h) * pairHom g =
        swapAut (ZMod 2) * pairHom (h * g) := by
      rw [mul_assoc, ← map_mul]
    rw [e1, e2] at hab
    exact pairHom_injective (mul_left_cancel hab)
  have hG : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * g = 1 := by
    have := congrArg Units.val hgg
    simpa using this
  have hG1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h' => hg1 (Units.ext h')
  have hDH : ((dualGL h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * h = 1 := by
    have := congrArg Units.val hdh
    simpa using this
  have hHs : (h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = h := by
    have h1 := hDH
    rw [coe_dualGL] at h1
    have h2 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2
    have h3 : ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * h = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ
        = (h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
            (((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * h) := by
          rw [h3, mul_one]
      _ = ((h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
            ((h⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) * h := by
          rw [mul_assoc]
      _ = h := by rw [h2, one_mul]
  have hinj : ∀ v, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have := congrArg (fun u => ((dualGL h : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u) hv
    simpa [Matrix.mulVec_mulVec, hDH] using this
  have hGT : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) * h =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * g := by
    have := congrArg Units.val hcomm
    rw [Units.val_mul, Units.val_mul, coe_dualGL, hgi] at this
    exact this
  obtain ⟨c, φ, hc, hφ, hφc, hGe⟩ := inv_eq_trv _ hG hG1
  have hcomm' : (1 + vecMulVec φ c) * (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (1 + vecMulVec c φ) := by
    have e : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) = 1 + vecMulVec φ c := by
      rw [hGe, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
    rw [← e, ← hGe]
    exact hGT
  have hHc := symm_mulVec_eq c φ hc hφ hφc _ hHs hinj hcomm'
  have hge : g = trvGL hφc := Units.ext (by rw [coe_trvGL]; exact hGe)
  refine ⟨c, φ, h, (dualGL h : GL (Fin 3) (ZMod 2)), hc, hφ, hφc, fun v w => ?_,
    fun v w => swap_pairHom_apply_mk h v w, hHs, hHc, hDH⟩
  rw [hge, pairHom_trvGL_apply]
  simp only [toAdd_ofAdd]

theorem part1 {A : Subgroup (MulAut PV)} (hAN : A ≤ pairNorm (ZMod 2))
    (hA2 : IsElemAbelian2 A) (hA4 : Nat.card A = 4) (hAL : ¬ A ≤ pairSL (ZMod 2)) :
    rk ↥(fixV A) = 2 ∧ rk ↥(xi A) = 5 := by
  obtain ⟨a, b, haA, hbA, haL, ha1, hbL, hcl⟩ := exists_ab hAN hA2 hA4 hAL
  have haa : a * a = 1 := by rw [← sq]; exact hA2.2 a haA
  have hbb : b * b = 1 := by rw [← sq]; exact hA2.2 b hbA
  have hab : a * b = b * a := hA2.1 a haA b hbA
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ Subgroup.one_mem _)
  obtain ⟨c, φ, H, D, hc, hφ, hφc, ha, hb, hHs, hHc, hDH⟩ :=
    part1_data haL ha1 (hAN hbA) hbL haa hbb hab
  refine ⟨rk_of_card (k := 2) ?_, rk_of_card (k := 5) ?_⟩
  · rw [card_fixV_part1 hcl haA hbA hc hφ hφc ha hb hHs hHc hDH]
    norm_num
  · rw [xi_eq_part1 hcl haA hbA hc hφ hφc ha hb hHs hHc hDH haa ha1 hb1, card_hyper c φ hφ]
    norm_num

end CFSG.Quasithin.RonanH43
