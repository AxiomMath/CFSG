module

public import CFSG.Quasithin.Vol2.Ch6SL2Fix
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.Quasithin.H13

variable {F : Type} [Field F] [Finite F]

theorem charP_two_of_two_dvd (hF : 2 ∣ Nat.card F) : CharP F 2 := by
  have := Fintype.ofFinite F
  have hchar : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.mod_eq_zero_of_dvd hF
  exact ringChar.of_eq hchar

theorem exists_pairing (hF : 2 ∣ Nat.card F) :
    ∃ τ : F →+ ZMod 2,
      (∀ a : Fin 2 → F, (∀ w : Fin 2 → F, τ (a 0 * w 0 + a 1 * w 1) = 0) → a = 0) ∧
      ∀ H : AddSubgroup (Fin 2 → F), H.index = 2 →
        ∃ a : Fin 2 → F, ∀ w, w ∈ H ↔ τ (a 0 * w 0 + a 1 * w 1) = 0 := by
  classical
  have : CharP F 2 := charP_two_of_two_dvd hF
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let τ0 : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F
  obtain ⟨c, hc⟩ : ∃ c : F, τ0 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Algebra.trace_ne_zero (ZMod 2) F (LinearMap.ext hcon)
  have hnd : ∀ a : Fin 2 → F, (∀ w : Fin 2 → F, τ0 (a 0 * w 0 + a 1 * w 1) = 0) → a = 0 := by
    intro a ha
    have h0 : a 0 = 0 := by
      by_contra hai
      have := ha ![c / a 0, 0]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at this
      rw [mul_div_cancel₀ _ hai] at this
      exact hc this
    have h1 : a 1 = 0 := by
      by_contra hai
      have := ha ![0, c / a 1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add] at this
      rw [mul_div_cancel₀ _ hai] at this
      exact hc this
    funext i
    fin_cases i
    · exact h0
    · exact h1
  refine ⟨τ0.toAddMonoidHom, hnd, fun H hH => ?_⟩
  have hfin : Module.Finite (ZMod 2) (Fin 2 → F) := Module.Finite.of_finite
  obtain ⟨e⟩ := (Basis.linearEquiv_dual_iff_finiteDimensional (K := ZMod 2)
    (V := Fin 2 → F)).mpr inferInstance
  have : Finite (Module.Dual (ZMod 2) (Fin 2 → F)) := Finite.of_equiv _ e.toEquiv
  let χ : (Fin 2 → F) → Module.Dual (ZMod 2) (Fin 2 → F) := fun a =>
    { toFun := fun w => τ0 (a 0 * w 0 + a 1 * w 1)
      map_add' := fun w w' => by
        simp only [Pi.add_apply, mul_add]
        rw [← map_add]
        congr 1
        ring
      map_smul' := fun r w => by
        simp only [Pi.smul_apply, mul_smul_comm, RingHom.id_apply]
        rw [← smul_add, map_smul] }
  have hχ : Function.Injective χ := by
    intro a a' haa'
    have h1 : ∀ w : Fin 2 → F, τ0 ((a - a') 0 * w 0 + (a - a') 1 * w 1) = 0 := by
      intro w
      have := LinearMap.congr_fun haa' w
      simp only [χ, LinearMap.coe_mk, AddHom.coe_mk] at this
      have e1 : (a - a') 0 * w 0 + (a - a') 1 * w 1 =
          (a 0 * w 0 + a 1 * w 1) - (a' 0 * w 0 + a' 1 * w 1) := by
        simp only [Pi.sub_apply]
        ring
      rw [e1, map_sub, this]
      exact sub_self _
    exact sub_eq_zero.mp (hnd _ h1)
  have hbij : Function.Bijective χ := hχ.bijective_of_nat_card_le (Nat.card_congr e.toEquiv).ge
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  let ψ : Module.Dual (ZMod 2) (Fin 2 → F) :=
    { toFun := fun w => if w ∈ H then 0 else 1
      map_add' := fun w w' => by
        have := AddSubgroup.add_mem_iff_of_index_two hH (a := w) (b := w')
        by_cases hw : w ∈ H <;> by_cases hw' : w' ∈ H
        · have h1 : w + w' ∈ H := this.mpr (iff_of_true hw hw')
          simp only [h1, hw, hw', ↓reduceIte, add_zero]
        · have h1 : w + w' ∉ H := fun h => hw' ((this.mp h).mp hw)
          simp only [h1, hw, hw', ↓reduceIte, zero_add]
        · have h1 : w + w' ∉ H := fun h => hw ((this.mp h).mpr hw')
          simp only [h1, hw, hw', ↓reduceIte, add_zero]
        · have h1 : w + w' ∈ H := this.mpr (iff_of_false hw hw')
          simp only [h1, hw, hw', ↓reduceIte]
          decide
      map_smul' := fun r w => by
        rw [RingHom.id_apply]
        rcases h01 r with rfl | rfl
        · simp
        · simp }
  obtain ⟨a, ha⟩ := hbij.2 ψ
  refine ⟨a, fun w => ?_⟩
  have := LinearMap.congr_fun ha w
  simp only [χ, ψ, LinearMap.coe_mk, AddHom.coe_mk] at this
  change w ∈ H ↔ τ0 (a 0 * w 0 + a 1 * w 1) = 0
  rw [this]
  by_cases hw : w ∈ H <;> simp [hw]

omit [Finite F] in
theorem ne_zero_of_hyperplane {τ : F →+ ZMod 2} {H : AddSubgroup (Fin 2 → F)}
    (hH : H.index = 2) {a : Fin 2 → F} (ha : ∀ w, w ∈ H ↔ τ (a 0 * w 0 + a 1 * w 1) = 0) :
    a ≠ 0 := by
  rintro rfl
  have : H = ⊤ := eq_top_iff.mpr fun w _ => (ha w).mpr (by simp)
  rw [this, AddSubgroup.index_top] at hH
  exact absurd hH (by norm_num)

theorem exists_sl2_hyperplane (hF : 2 ∣ Nat.card F) {H H' : AddSubgroup (Fin 2 → F)}
    (hH : H.index = 2) (hH' : H'.index = 2) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ w, w ∈ H' ↔ (A : Matrix (Fin 2) (Fin 2) F).mulVec w ∈ H := by
  obtain ⟨τ, -, hker⟩ := exists_pairing hF
  obtain ⟨a, ha⟩ := hker H hH
  obtain ⟨a', ha'⟩ := hker H' hH'
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_eq a a' (ne_zero_of_hyperplane hH ha)
    (ne_zero_of_hyperplane hH' ha')
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨(B : Matrix (Fin 2) (Fin 2) F).transpose, by rw [Matrix.det_transpose]; exact B.2⟩
  refine ⟨A, fun w => ?_⟩
  rw [ha', ha, ← hB]
  have e : ((B : Matrix (Fin 2) (Fin 2) F).mulVec a) 0 * w 0 +
      ((B : Matrix (Fin 2) (Fin 2) F).mulVec a) 1 * w 1 =
      a 0 * ((A : Matrix (Fin 2) (Fin 2) F).mulVec w) 0 +
        a 1 * ((A : Matrix (Fin 2) (Fin 2) F).mulVec w) 1 := by
    simp only [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
    ring
  rw [e]

theorem odd_card_hyperplanes (hF : 2 ∣ Nat.card F) :
    ¬ 2 ∣ Nat.card {H : AddSubgroup (Fin 2 → F) // H.index = 2} := by
  classical
  obtain ⟨τ, hnd, hker⟩ := exists_pairing hF
  let χ : (Fin 2 → F) → (Fin 2 → F) →+ ZMod 2 := fun a =>
    { toFun := fun w => τ (a 0 * w 0 + a 1 * w 1)
      map_zero' := by simp
      map_add' := fun w w' => by
        simp only [Pi.add_apply, mul_add]
        rw [← map_add]
        congr 1
        ring }
  have hχ : ∀ a w, χ a w = τ (a 0 * w 0 + a 1 * w 1) := fun _ _ => rfl
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hidx : ∀ a : Fin 2 → F, a ≠ 0 → (χ a).ker.index = 2 := by
    intro a ha
    obtain ⟨w₀, hw₀⟩ : ∃ w₀, χ a w₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (hnd a fun w => hcon w)
    rw [AddSubgroup.index_ker]
    have htop : (χ a).range = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      rcases h01 x with rfl | rfl
      · exact (χ a).range.zero_mem
      · rcases h01 (χ a w₀) with h | h
        · exact absurd h hw₀
        · exact ⟨w₀, h⟩
    rw [htop]
    simp
  let Φ : {a : Fin 2 → F // a ≠ 0} → {H : AddSubgroup (Fin 2 → F) // H.index = 2} :=
    fun a => ⟨(χ a.1).ker, hidx a.1 a.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hab' : (χ a).ker = (χ b).ker := congrArg Subtype.val hab
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply hnd
      intro w
      have hw : χ a w = χ b w := by
        have h1 : χ a w = 0 ↔ χ b w = 0 := by
          rw [← AddMonoidHom.mem_ker, ← AddMonoidHom.mem_ker, hab']
        rcases h01 (χ a w) with h | h <;> rcases h01 (χ b w) with h' | h'
        · rw [h, h']
        · exact absurd (h1.mp h) (by rw [h']; decide)
        · exact absurd (h1.mpr h') (by rw [h]; decide)
        · rw [h, h']
      have e : (a - b) 0 * w 0 + (a - b) 1 * w 1 =
          (a 0 * w 0 + a 1 * w 1) - (b 0 * w 0 + b 1 * w 1) := by
        simp only [Pi.sub_apply]
        ring
      rw [e, map_sub, ← hχ, ← hχ, hw]
      exact sub_self _
    · rintro ⟨H, hH⟩
      obtain ⟨a, ha⟩ := hker H hH
      refine ⟨⟨a, ne_zero_of_hyperplane hH ha⟩, Subtype.ext ?_⟩
      ext w
      exact (ha w).symm
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ)]
  have := Fintype.ofFinite (Fin 2 → F)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin]
  intro h2
  have hpos : 1 ≤ Nat.card F ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Finite.card_pos.ne')
  have h3 : 2 ∣ Nat.card F ^ 2 := hF.trans (Dvd.intro _ (by ring))
  omega

end CFSG.Quasithin.H13
