module

public import CFSG.Quasithin.Background.FLcFlagU

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem stab_entry_zero {n m : ℕ} {g : SLt n} (hg : g ∈ stabilizer (flagSpace n (ZMod 2) m))
    {c r : Fin n} (hc : c.val < m) (hr : m ≤ r.val) : mat g r c = 0 := by
  have hv : (Pi.single c (1 : ZMod 2) : Vt n) ∈ flagSpace n (ZMod 2) m := by
    rw [mem_flagSpace]
    intro j hj
    have : j ≠ c := fun h => by subst h; omega
    simp [this]
  have h1 := ((mem_stabilizer_iff.1 hg) _).1 hv
  rw [mem_flagSpace] at h1
  have h2 := h1 r hr
  simpa [Matrix.mulVec_single_one] using h2

theorem mem_stabilizer_of_forall {n m : ℕ} {g : SLt n}
    (h : ∀ v ∈ flagSpace n (ZMod 2) m, mat g *ᵥ v ∈ flagSpace n (ZMod 2) m) :
    g ∈ stabilizer (flagSpace n (ZMod 2) m) := by
  rw [mem_stabilizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have e : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have hcancel : ∀ x y : Vt n, mat g *ᵥ x = mat g *ᵥ y → x = y := by
    intro x y hxy
    have h2 := congrArg (fun z => mat g⁻¹ *ᵥ z) hxy
    simp only [mulVec_mulVec] at h2
    rw [e, one_mulVec, one_mulVec] at h2
    exact h2
  let f : ↥(flagSpace n (ZMod 2) m) → ↥(flagSpace n (ZMod 2) m) := fun w =>
    ⟨mat g *ᵥ (w : Vt n), h w w.2⟩
  have hinj : Function.Injective f := fun w₁ w₂ hw =>
    Subtype.ext (hcancel _ _ (congrArg Subtype.val hw))
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.1 hinj ⟨_, hv⟩
  have h1 : (w : Vt n) = v := hcancel _ _ (congrArg Subtype.val hw)
  rw [← h1]
  exact w.2

theorem mem_Ut_of_stab_all {n : ℕ} {g : SLt n}
    (h : ∀ j, 1 ≤ j → j < n → g ∈ stabilizer (flagSpace n (ZMod 2) j)) : g ∈ Ut n := by
  rw [Ut_eq_QI, mem_flagStabilizer]
  intro j hj
  exact h j hj.1 hj.2

@[expose] def Qn (n i : ℕ) : Subgroup (SLt n) := QI n {j | 1 ≤ j ∧ j < n ∧ j ≠ i}

theorem mem_Qn {n i : ℕ} {g : SLt n} :
    g ∈ Qn n i ↔ ∀ j, 1 ≤ j → j < n → j ≠ i → g ∈ stabilizer (flagSpace n (ZMod 2) j) := by
  unfold Qn
  rw [mem_flagStabilizer]
  constructor
  · intro h j h1 h2 h3
    exact h j ⟨h1, h2, h3⟩
  · intro h j hj
    exact h j hj.1 hj.2.1 hj.2.2

theorem Ut_le_Qn (n i : ℕ) : Ut n ≤ Qn n i := Ut_le_QI n _

@[expose] def blk {n : ℕ} (P Q : Fin n) (g : SLt n) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![mat g P P, mat g P Q; mat g Q P, mat g Q Q]

theorem blk_one {n : ℕ} {P Q : Fin n} (hPQ : P ≠ Q) : blk P Q (1 : SLt n) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blk, hPQ, Ne.symm hPQ]

theorem blk_mul_of_entries {n : ℕ} {P Q : Fin n} (hPQ : P.val + 1 = Q.val) {g h : SLt n}
    (hg : ∀ c r : Fin n, c < P → P ≤ r → mat g r c = 0)
    (hh : ∀ b r : Fin n, b ≤ Q → Q < r → mat h r b = 0) :
    blk P Q (g * h) = blk P Q g * blk P Q h := by
  have hne : P ≠ Q := fun h => by rw [h] at hPQ; omega
  have key : ∀ r s : Fin n, P ≤ r → s ≤ Q →
      mat (g * h) r s = mat g r P * mat h P s + mat g r Q * mat h Q s := by
    intro r s hr hs
    rw [mat_mul, Matrix.mul_apply]
    refine Fintype.sum_eq_add P Q hne ?_
    rintro x ⟨hxP, hxQ⟩
    have hx : x < P ∨ Q < x := by
      have h1 : x.val ≠ P.val := fun h => hxP (Fin.ext h)
      have h2 : x.val ≠ Q.val := fun h => hxQ (Fin.ext h)
      rw [Fin.lt_def, Fin.lt_def]
      omega
    rcases hx with hx | hx
    · rw [hg x r hx hr, zero_mul]
    · rw [hh s x hs hx, mul_zero]
  have hPQ' : P ≤ Q := by
    rw [Fin.le_def]
    omega
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_two, key P P le_rfl hPQ',
      key P Q le_rfl le_rfl, key Q P hPQ' hPQ', key Q Q hPQ' le_rfl]

theorem Qn_low {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {g : SLt n} (hg : g ∈ Qn n i)
    {c r : Fin n} (hc : c.val + 1 < i) (hr : i ≤ r.val + 1) : mat g r c = 0 := by
  have hst := (mem_Qn.1 hg) (i - 1) (by omega) (by omega) (by omega)
  exact stab_entry_zero hst (by omega) (by omega)

theorem Qn_high {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {g : SLt n} (hg : g ∈ Qn n i)
    {b r : Fin n} (hb : b.val ≤ i) (hr : i < r.val) : mat g r b = 0 := by
  have hst := (mem_Qn.1 hg) (i + 1) (by omega) hin (by omega)
  exact stab_entry_zero hst (by omega) (by omega)

theorem blk_mul_Qn {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n} (hP : P.val + 1 = i)
    (hQ : Q.val = i) {g h : SLt n} (hg : g ∈ Qn n i) (hh : h ∈ Qn n i) :
    blk P Q (g * h) = blk P Q g * blk P Q h := by
  refine blk_mul_of_entries (by omega) (fun c r hc hr => ?_) (fun b r hb hr => ?_)
  · rw [Fin.lt_def] at hc
    rw [Fin.le_def] at hr
    exact Qn_low hi hin hg (by omega) (by omega)
  · rw [Fin.le_def] at hb
    rw [Fin.lt_def] at hr
    exact Qn_high hi hin hh (by omega) (by omega)

theorem blk_pow_Qn {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n} (hP : P.val + 1 = i)
    (hQ : Q.val = i) {g : SLt n} (hg : g ∈ Qn n i) (k : ℕ) :
    blk P Q (g ^ k) = (blk P Q g) ^ k := by
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact blk_one hne
  | succ k ih =>
    rw [pow_succ, pow_succ, blk_mul_Qn hi hin hP hQ ((Qn n i).pow_mem hg k) hg, ih]

theorem mem_Ut_of_blk_one {n i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n}
    (hP : P.val + 1 = i) (hQ : Q.val = i) {g : SLt n} (hg : g ∈ Qn n i) (hb : blk P Q g = 1) :
    g ∈ Ut n := by
  have hQP : mat g Q P = 0 := by
    have h1 := congrFun (congrFun hb 1) 0
    simpa [blk] using h1
  have hF : g ∈ stabilizer (flagSpace n (ZMod 2) i) := by
    apply mem_stabilizer_of_forall
    intro v hv
    rw [mem_flagSpace] at hv ⊢
    intro r hr
    show ∑ x, mat g r x * v x = 0
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : i ≤ x.val
    · rw [hv x hx, mul_zero]
    · have h0 : mat g r x = 0 := by
        by_cases hri : r.val = i
        · by_cases hxP : x.val + 1 = i
          · have hrQ : r = Q := Fin.ext (by omega)
            have hxP' : x = P := Fin.ext (by omega)
            rw [hrQ, hxP']
            exact hQP
          · exact Qn_low hi hin hg (by omega) (by omega)
        · exact Qn_high hi hin hg (by omega) (by omega)
      rw [h0, zero_mul]
  refine mem_Ut_of_stab_all fun j hj1 hjn => ?_
  by_cases hji : j = i
  · rw [hji]
    exact hF
  · exact mem_Qn.1 hg j hj1 hjn hji

theorem reflection_mem_Qn {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    reflection n (ZMod 2) i hi hin ∈ Qn n i := by
  rw [mem_Qn]
  intro j hj1 hjn hji
  have h := (reflection_mem_QI (n := n) (I := {j}) (i := i) ⟨hi, hin⟩).2
    (by simpa [eq_comm] using hji)
  rw [QI, mem_flagStabilizer] at h
  exact h j rfl

@[expose] def tv {n : ℕ} (a b : Fin n) (h : a < b) : SLt n :=
  SpecialLinearGroup.transvection h.ne (1 : ZMod 2)

theorem tv_mem_Ut {n : ℕ} {a b : Fin n} (h : a < b) : tv a b h ∈ Ut n := by
  rw [mem_unitriangular]
  have hco : mat (tv a b h) = 1 + Matrix.single a b (1 : ZMod 2) :=
    SpecialLinearGroup.transvection_coe h.ne 1
  constructor
  · intro i j hji
    show mat (tv a b h) i j = 0
    rw [hco, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hne : i ≠ j := ne_of_gt hji
    by_cases hh : a = i ∧ b = j
    · exfalso
      obtain ⟨h1, h2⟩ := hh
      subst h1
      subst h2
      exact absurd hji (not_lt.2 h.le)
    · simp [hne, hh]
  · intro i
    show mat (tv a b h) i i = 1
    rw [hco, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have : ¬ (a = i ∧ b = i) := fun ⟨h1, h2⟩ => h.ne (h1.trans h2.symm)
    simp [this]

@[expose] def tau2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]

theorem gl2_pow_six : ∀ X Y : Matrix (Fin 2) (Fin 2) (ZMod 2), X * Y = 1 → X ^ 6 = 1 := by
  decide

theorem gl2_key : ∀ X : Matrix (Fin 2) (Fin 2) (ZMod 2), X ^ 3 = 1 → tau2 * X * tau2 * X = 1 := by
  decide

end CFSG.Quasithin.FLc
