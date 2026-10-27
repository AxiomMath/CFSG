module

public import CFSG.Quasithin.Background.F918W3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.D35ValChk

open Matrix

private theorem expand_kid : expand kid = idm := by decide

private theorem toM_expand_kid : toM (expand kid) = 1 := by
  rw [expand_kid, toM_idm]

private theorem toM_expand_kmul {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    toM (expand (kmul a b)) = toM (expand a) * toM (expand b) := by
  rw [expand_kmul ha hb, toM_bmul]

private theorem code_inj {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : toM (expand a) = toM (expand b)) : a = b :=
  expand_inj ha hb (toM_inj (expand_lt a) (expand_lt b) h)

private theorem kid_lt : kid < 2 ^ 18 := by decide

private theorem kmul_kid_left {a : Nat} (ha : a < 2 ^ 18) : kmul kid a = a :=
  code_inj (kmul_lt _ _) ha (by rw [toM_expand_kmul kid_lt ha, toM_expand_kid, Matrix.one_mul])

private theorem kmul_kid_right {a : Nat} (ha : a < 2 ^ 18) : kmul a kid = a :=
  code_inj (kmul_lt _ _) ha (by rw [toM_expand_kmul ha kid_lt, toM_expand_kid, Matrix.mul_one])

private theorem kmul_assoc' {a b c : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) (hc : c < 2 ^ 18) :
    kmul (kmul a b) c = kmul a (kmul b c) :=
  code_inj (kmul_lt _ _) (kmul_lt _ _) (by
    rw [toM_expand_kmul (kmul_lt _ _) hc, toM_expand_kmul ha hb, toM_expand_kmul ha (kmul_lt _ _),
      toM_expand_kmul hb hc, Matrix.mul_assoc])

private theorem genK_cases (i : Nat) : genK i = u0 ∨ genK i = a0 ∨ genK i = b0 := by
  unfold genK
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem genK_lt (i : Nat) : genK i < 2 ^ 18 := by
  rcases genK_cases i with h | h | h <;> rw [h] <;> decide

private theorem genK_sq (i : Nat) : kmul (genK i) (genK i) = kid := by
  rcases genK_cases i with h | h | h <;> rw [h] <;> decide

private theorem inClos_lt {c : Nat} (h : InClos c) : c < 2 ^ 18 := by
  cases h with
  | one => exact kid_lt
  | mul i _ _ => exact kmul_lt _ _

private theorem exists_unit_of_code {c c' : Nat} (hc : c < 2 ^ 18) (hc' : c' < 2 ^ 18) (h : kmul c c' = kid) :
    ∃ u : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2),
      ((u : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c) := by
  have h1 : toM (expand c) * toM (expand c') = 1 := by
    rw [← toM_expand_kmul hc hc', h, toM_expand_kid]
  exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩

private theorem inv_mem_of_closed {G : Type*} [Group G] [Finite G] (T : Set G) (h1 : (1 : G) ∈ T)
    (hmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T) {g : G} (hg : g ∈ T) : g⁻¹ ∈ T := by
  have hpow : ∀ n : ℕ, g ^ n ∈ T := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have : g⁻¹ = g ^ (orderOf g - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [this]
  exact hpow _

private theorem exists_gen (i : Nat) (hi : i < 3) : ∃ s : G0,
    (((s : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand (genK i)) := by
  obtain ⟨u, hu⟩ := exists_unit_of_code (genK_lt i) (genK_lt i) (genK_sq i)
  exact ⟨⟨u, Subgroup.subset_closure ⟨i, hi, hu⟩⟩, hu⟩

private theorem exists_G0_of_inClos {c : Nat} (hc : InClos c) : ∃ g : G0,
    (((g : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand c) := by
  induction hc with
  | one => exact ⟨1, by simp [toM_expand_kid]⟩
  | @mul g i hi hg ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨s, hs⟩ := exists_gen i hi
    refine ⟨x * s, ?_⟩
    rw [toM_expand_kmul (inClos_lt hg) (genK_lt i)]
    simp only [Subgroup.coe_mul, Units.val_mul, hx, hs]

private theorem genK_mem_gl (hF : D35Facts) (i : Nat) : genK i ∈ gl := by
  rcases genK_cases i with h | h | h <;> rw [h]
  · exact hF.gl_mem.2.1
  · exact hF.gl_mem.2.2.1
  · exact hF.gl_mem.2.2.2

private theorem gl_mul_inClos (hF : D35Facts) {c1 c2 : Nat} (h1 : c1 ∈ gl) (h2 : InClos c2) : kmul c1 c2 ∈ gl := by
  induction h2 with
  | one => rwa [kmul_kid_right (hF.gl_lt c1 h1)]
  | @mul g i hi hg ih =>
    rw [← kmul_assoc' (hF.gl_lt c1 h1) (inClos_lt hg) (genK_lt i)]
    exact hF.gl_closed _ ih i hi

private theorem gl_mul (hF : D35Facts) {c1 c2 : Nat} (h1 : c1 ∈ gl) (h2 : c2 ∈ gl) : kmul c1 c2 ∈ gl :=
  gl_mul_inClos hF h1 (hF.gl_gen c2 h2)

theorem G0_code (hF : D35Facts) (g : G0) : ∃ c ∈ gl,
    ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c) := by
  let T : Set (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :=
    {x | ∃ c ∈ gl, ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      toM (expand c)}
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) ∈ T := ⟨kid, hF.gl_mem.1, by simp [toM_expand_kid]⟩
  have hmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := by
    rintro a ⟨c1, hc1, ha⟩ b ⟨c2, hc2, hb⟩
    refine ⟨kmul c1 c2, gl_mul hF hc1 hc2, ?_⟩
    rw [Units.val_mul, ha, hb, toM_expand_kmul (hF.gl_lt c1 hc1) (hF.gl_lt c2 hc2)]
  let P : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :=
    { carrier := T
      one_mem' := h1
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      inv_mem' := fun {x} hx => inv_mem_of_closed T h1 hmul hx }
  have hle : G0 ≤ P := by
    unfold G0
    rw [Subgroup.closure_le]
    rintro x ⟨i, hi, hx⟩
    exact ⟨genK i, genK_mem_gl hF i, hx⟩
  exact hle g.2

theorem exists_G0 (hF : D35Facts) {c : Nat} (hc : c ∈ gl) : ∃ g : G0,
    ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c) :=
  exists_G0_of_inClos (hF.gl_gen c hc)

private theorem isScalK_iff (m : Nat) : isScalK m = true ↔ m = kid ∨ m = kom ∨ m = kom2 := by
  unfold isScalK
  simp [Nat.beq_eq, or_assoc]

private theorem scal_lt {c : Nat} (h : isScalK c = true) : c < 2 ^ 18 := by
  rcases (isScalK_iff c).mp h with rfl | rfl | rfl <;> decide

private theorem scal_mem_gl (hF : D35Facts) {c : Nat} (h : isScalK c = true) : c ∈ gl := by
  rcases (isScalK_iff c).mp h with rfl | rfl | rfl
  · exact hF.gl_mem.1
  · exact hF.scal_mem.1
  · exact hF.scal_mem.2

private theorem scal_comm_gen (hF : D35Facts) {c : Nat} (h : isScalK c = true) (i : Nat) (hi : i < 3) :
    kmul c (genK i) = kmul (genK i) c := by
  rcases (isScalK_iff c).mp h with rfl | rfl | rfl
  · rw [kmul_kid_left (genK_lt i), kmul_kid_right (genK_lt i)]
  · exact (hF.scal_central i hi).1
  · exact (hF.scal_central i hi).2

theorem center_G0 (hF : D35Facts) (g : G0) : g ∈ Subgroup.center G0 ↔ ∃ c, isScalK c = true ∧
    ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c) := by
  constructor
  · intro hg
    obtain ⟨c, hc, hgc⟩ := G0_code hF g
    refine ⟨c, hF.center_scal c hc (fun i hi => ?_), hgc⟩
    obtain ⟨s, hs⟩ := exists_gen i hi
    have hcomm : s * g = g * s := (Subgroup.mem_center_iff.mp hg) s
    have := congrArg (fun x : G0 => ((x : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2))) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, hs, hgc] at this
    apply code_inj (kmul_lt _ _) (kmul_lt _ _)
    rw [toM_expand_kmul (hF.gl_lt c hc) (genK_lt i), toM_expand_kmul (genK_lt i) (hF.gl_lt c hc)]
    exact this.symm
  · rintro ⟨c, hcs, hgc⟩
    have hc : c ∈ gl := scal_mem_gl hF hcs
    rw [Subgroup.mem_center_iff]
    intro h
    have hle : G0 ≤ Subgroup.centralizer {(g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))} := by
      unfold G0
      rw [Subgroup.closure_le]
      rintro x ⟨i, hi, hx⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hgc, hx, ← toM_expand_kmul (scal_lt hcs) (genK_lt i),
        ← toM_expand_kmul (genK_lt i) (scal_lt hcs), scal_comm_gen hF hcs i hi]
    have := (Subgroup.mem_centralizer_iff.mp (hle h.2)) _ (Set.mem_singleton _)
    exact Subtype.ext this.symm

theorem center_pow_three (hF : D35Facts) {z : G0} (hz : z ∈ Subgroup.center G0) : z ^ 3 = 1 := by
  obtain ⟨c, hcs, hzc⟩ := (center_G0 hF z).mp hz
  have hc := scal_lt hcs
  have h3 : kmul (kmul c c) c = kid := by
    rcases (isScalK_iff c).mp hcs with rfl | rfl | rfl <;> decide
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hzc, pow_three', ← toM_expand_kmul hc hc,
    ← toM_expand_kmul (kmul_lt _ _) hc, h3, toM_expand_kid]
  rfl

theorem exists_invol_lift (hF : D35Facts) (x : G0 ⧸ Subgroup.center G0) (hx : x * x = 1) :
    ∃ y : G0, y * y = 1 ∧ QuotientGroup.mk y = x := by
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ℓ * ℓ ∈ Subgroup.center G0 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hx
  have h3 := center_pow_three hF h1
  refine ⟨ℓ ^ 3, ?_, ?_⟩
  · rw [← pow_add, show 3 + 3 = 2 * 3 from rfl, pow_mul, pow_two]
    exact h3
  · have : (QuotientGroup.mk ℓ : G0 ⧸ Subgroup.center G0) ^ 3 = QuotientGroup.mk ℓ := by
      rw [pow_succ, pow_two, hx, one_mul]
    rw [← this]
    simp [QuotientGroup.mk_pow]

end CFSG.Quasithin.D35ValChk
