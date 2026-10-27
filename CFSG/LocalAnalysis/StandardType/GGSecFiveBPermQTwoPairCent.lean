module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField

public section

namespace CFSG.StandardType.QTwoBlocks

open Polynomial Matrix CoordSL SLNS CFSG.RankThree.CALinearPlane
open scoped MatrixGroups commutatorElement

section PairCent

private theorem aligned_of_zero_one {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)]
    {hζ : AdjoinRoot.root g ^ 3 = 1} {β : Fin 3 → ZMod 3} (hβ : ∀ l, β l = 0 ∨ β l = 1) :
    Aligned hζ β := by
  intro a b hb u _ hab
  rcases hβ b with h | h
  · exact absurd h hb
  · rcases hβ a with h' | h'
    · rw [h', h, mul_one] at hab
      exact absurd hab.symm u.ne_zero
    · rw [h, h']

private theorem eq_one_of_ne_zero {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {t : F}
    (ht : t ≠ 0) : t = 1 := by
  classical
  by_contra h1t
  have : Fintype F := Fintype.ofFinite F
  have h3 : ({0, 1, t} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ht.symm]), Finset.card_pair (Ne.symm h1t)]
  have h4 := Finset.card_le_univ ({0, 1, t} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at h4
  omega

private theorem eq_of_ne_zero_of_le_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {d : ℕ} (hd : d ≤ 1) {a b : Fin d → F} (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  have : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr hd
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp ha
  obtain ⟨l₁, hl₁⟩ := Function.ne_iff.mp hb
  funext l
  rw [Subsingleton.elim l l₀, eq_one_of_ne_zero hF hl₀, ← eq_one_of_ne_zero hF hl₁,
    Subsingleton.elim l₀ l₁]

private theorem fin_three_cases {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  revert i j k l
  decide

private theorem not_mem_pair_iff {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (l : Fin 3) : l ∉ ({i, j} : Finset (Fin 3)) ↔ l = k := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    rcases fin_three_cases hij hki hkj l with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  · rintro rfl
    exact ⟨hki, hkj⟩

private theorem kdiag_mul {L : Type*} [CommRing L] {k : Fin 3} {A B : Matrix (Fin 3) (Fin 3) L}
    (hA : ∀ a b, (a = k ↔ ¬ b = k) → A a b = 0) (hB : ∀ a b, (a = k ↔ ¬ b = k) → B a b = 0) :
    (∀ a b, (a = k ↔ ¬ b = k) → (A * B) a b = 0) ∧ (A * B) k k = A k k * B k k := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases ha : a = k <;> by_cases hc : c = k
    · rw [hB c b ⟨fun _ => hab.mp ha, fun _ => hc⟩, mul_zero]
    · rw [hA a c ⟨fun _ => hc, fun _ => ha⟩, zero_mul]
    · rw [hA a c ⟨fun h => absurd h ha, fun h => absurd hc h⟩, zero_mul]
    · have hb : b = k := by
        by_contra hb
        exact ha (hab.mpr hb)
      rw [hB c b ⟨fun h => absurd h hc, fun h => absurd hb h⟩, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · intro c _ hc
      rw [hA k c ⟨fun _ => hc, fun _ => rfl⟩, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h

private theorem diagonal_comm_of_mem {L : Type*} [Field L] {i j k : Fin 3} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) {M : Matrix.SpecialLinearGroup (Fin 3) L}
    (hM : M ∈ coordBlockSL L {i, j}) {v : Fin 3 → L} (hv : ∀ a b, a ≠ k → b ≠ k → v a = v b) :
    Matrix.diagonal v * (M : Matrix (Fin 3) (Fin 3) L) =
      (M : Matrix (Fin 3) (Fin 3) L) * Matrix.diagonal v := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hM' := mem_coordBlockSL_iff.mp hM
  have hoff : a = k ∨ b = k → (M : Matrix (Fin 3) (Fin 3) L) a b = if a = b then 1 else 0 :=
    fun h => hM' a b (h.imp (not_mem_pair_iff hij hki hkj a).mpr
      (not_mem_pair_iff hij hki hkj b).mpr)
  by_cases hab : a = k ∨ b = k
  · rw [hoff hab]
    split_ifs with h
    · rw [h, mul_one, one_mul]
    · rw [mul_zero, zero_mul]
  · rw [not_or] at hab
    rw [hv a b hab.1 hab.2, mul_comm]

variable {F : Type} [Field F] [Finite F] {g : F[X]} [Fact (Irreducible g)] {m d : ℕ}
  {ε : Fin m ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin d} {hC : (rootMat g).det = 1}

omit [Finite F] in
theorem thetaMat_injective :
    Function.Injective (thetaMat g ε : Matrix (Fin 3) (Fin 3) (AdjoinRoot g) → _) := by
  intro M N h
  have h1 := congrArg (frameForm g ε) h
  rw [frameForm_thetaMat, frameForm_thetaMat] at h1
  ext a b
  have h2 := congrArg (fun φ => (φ ((Pi.single b 1 : Fin 3 → AdjoinRoot g),
    (0 : Fin d → F))).1 a) h1
  simp only [blockAct_apply] at h2
  rw [mulVec_single_apply', mulVec_single_apply', mul_one, mul_one] at h2
  exact h2

omit [Finite F] in
private theorem nsSL_comm_theta {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {M : Matrix.SpecialLinearGroup (Fin 3) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) {i, j}) {κ : Fin 3 → ℕ}
    (hκ : ∀ a b, a ≠ k → b ≠ k → κ a = κ b) :
    nsSL ε hC κ * theta g ε M = theta g ε M * nsSL ε hC κ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_theta]
  show nsMat ε (rootMat g) κ * thetaMat g ε M = thetaMat g ε M * nsMat ε (rootMat g) κ
  rw [← thetaMat_diagonal, ← thetaMat_mul, ← thetaMat_mul,
    diagonal_comm_of_mem hij hki hkj hM (fun a b ha hb => by rw [hκ a b ha hb])]

variable (ε) in
@[expose] noncomputable def pairLMat (u : SL(m, F)) : Matrix (Fin 3) (Fin 3) (AdjoinRoot g) :=
  fun a b => (frameForm g ε (u : Matrix (Fin m) (Fin m) F)
    ((Pi.single b 1 : Fin 3 → AdjoinRoot g), (0 : Fin d → F))).1 a

theorem pairCent_frameForm (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    (hF : Nat.card F = 2) (hd : d ≤ 1) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) {u : SL(m, F)}
    (hu₁ : u * nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) * u)
    (hu₂ : u * nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) * u) :
    frameForm g ε (u : Matrix (Fin m) (Fin m) F) = blockAct g (pairLMat ε u) ∧
      ∀ a b, (a = k ↔ ¬ b = k) → pairLMat ε u a b = 0 := by
  classical
  set β : Fin 3 → ZMod 3 := Pi.single i 1 + Pi.single j 1 with hβdef
  set γ : Fin 3 → ZMod 3 := Pi.single k 1 with hγdef
  have hζ : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  have hβi : β i = 1 := by simp [hβdef, hij]
  have hβj : β j = 1 := by simp [hβdef, hij.symm]
  have hβk : β k = 0 := by simp [hβdef, hki, hkj]
  have hγk : γ k = 1 := by simp [hγdef]
  have hγi : γ i = 0 := by simp [hγdef, hki.symm]
  have hγj : γ j = 0 := by simp [hγdef, hkj.symm]
  have hcases := fin_three_cases hij hki hkj
  have hβ01 : ∀ l, β l = 0 ∨ β l = 1 := fun l => by
    rcases hcases l with rfl | rfl | rfl
    · exact Or.inr hβi
    · exact Or.inr hβj
    · exact Or.inl hβk
  have hγ01 : ∀ l, γ l = 0 ∨ γ l = 1 := fun l => by
    rcases hcases l with rfl | rfl | rfl
    · exact Or.inl hγi
    · exact Or.inl hγj
    · exact Or.inr hγk
  have halβ : Aligned hζ β := aligned_of_zero_one hβ01
  have halγ : Aligned hζ γ := aligned_of_zero_one hγ01
  obtain ⟨hφβ, -, -⟩ := frameForm_comm_of_mem (hC := hC) hu₁
  obtain ⟨hφγ, -, -⟩ := frameForm_comm_of_mem (hC := hC) hu₂
  set φ := frameForm g ε (u : Matrix (Fin m) (Fin m) F) with hφdef
  have hβne : ∀ l, l ≠ k → β l ≠ 0 := fun l hl => by
    rcases hcases l with rfl | rfl | rfl
    · rw [hβi]; exact one_ne_zero
    · rw [hβj]; exact one_ne_zero
    · exact absurd rfl hl
  have hγne : ∀ l, l ≠ k → γ l ≠ 1 := fun l hl => by
    rcases hcases l with rfl | rfl | rfl
    · rw [hγi]; exact zero_ne_one
    · rw [hγj]; exact zero_ne_one
    · exact absurd rfl hl
  have hγk0 : γ k ≠ 0 := by rw [hγk]; exact one_ne_zero
  have hzero : ∀ a b, (a = k ↔ ¬ b = k) → pairLMat ε u a b = 0 := by
    intro a b hab
    by_cases hb : b = k
    · have ha : a ≠ k := fun h => hab.mp h hb
      rw [hb]
      refine apply_single_eq_zero_of_ne hprim halγ hφγ hγk0 1 ?_
      rw [hγk]
      exact hγne a ha
    · have ha : a = k := hab.mpr hb
      rw [ha]
      refine apply_single_eq_zero_of_ne hprim halβ hφβ (hβne b hb) 1 ?_
      rw [hβk]
      exact (hβne b hb).symm
  refine ⟨frame_ext (fun b z => ?_) (fun w => ?_), hzero⟩
  ·
    rw [blockAct_apply]
    have key : ∀ {δ : Fin 3 → ZMod 3}, Aligned hζ δ →
        (∀ x, φ (torusAct g (fun i => (δ i).val) x) = torusAct g (fun i => (δ i).val) (φ x)) →
        δ b ≠ 0 → φ ((Pi.single b z : Fin 3 → AdjoinRoot g), (0 : Fin d → F)) =
          (pairLMat ε u *ᵥ (Pi.single b z : Fin 3 → AdjoinRoot g), (0 : Fin d → F)) := by
      intro δ hal hφ hb
      rw [apply_single_of_comm hprim hal hφ hb z]
      refine Prod.ext (funext fun a => ?_) rfl
      simp only
      rw [mulVec_single_apply']
      split_ifs with hab
      · rw [mul_comm]
        rfl
      · rw [show pairLMat ε u a b = 0 from apply_single_eq_zero_of_ne hprim hal hφ hb 1 hab,
          zero_mul]
    by_cases hb : b = k
    · exact key halγ hφγ (hb ▸ hγk0)
    · exact key halβ hφβ (hβne b hb)
  ·
    rw [blockAct_apply, Matrix.mulVec_zero]
    set v := φ ((0 : Fin 3 → AdjoinRoot g), w) with hv
    have hv1 : v.1 = 0 := by
      funext a
      by_cases ha : a = k
      · rw [ha]
        exact apply_fixed_of_comm hprim hφγ (fun _ _ => rfl) hγk0
      · exact apply_fixed_of_comm hprim hφβ (fun _ _ => rfl) (hβne a ha)
    have hleft : ∀ z, frameForm g ε ((u⁻¹ : SL(m, F)) : Matrix (Fin m) (Fin m) F) (φ z) = z :=
      fun z => by
        rw [hφdef, ← LinearMap.comp_apply, ← frameForm_mul, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, frameForm_one, LinearMap.id_apply]
    refine Prod.ext hv1 ?_
    show v.2 = w
    by_cases hw : w = 0
    · rw [hv, hw, show ((0 : Fin 3 → AdjoinRoot g), (0 : Fin d → F)) = 0 from rfl, map_zero]
      rfl
    · have hv0 : v.2 ≠ 0 := by
        intro h0
        have hv00 : v = 0 := Prod.ext hv1 h0
        have h1 := hleft ((0 : Fin 3 → AdjoinRoot g), w)
        rw [← hv, hv00, map_zero] at h1
        exact hw (congrArg Prod.snd h1).symm
      exact eq_of_ne_zero_of_le_one hF hd hv0 hw

theorem pairCent_coe_eq_thetaMat (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    (hF : Nat.card F = 2) (hd : d ≤ 1) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) {u : SL(m, F)}
    (hu₁ : u * nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) * u)
    (hu₂ : u * nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) * u) :
    (u : Matrix (Fin m) (Fin m) F) = thetaMat g ε (pairLMat ε u) :=
  frameForm_injective g ε (by
    rw [frameForm_thetaMat]
    exact (pairCent_frameForm hprim hF hd hij hki hkj hu₁ hu₂).1)

theorem pairCent_commutator_mem (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    (hF : Nat.card F = 2) (hd : d ≤ 1) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) {x y : SL(m, F)}
    (hx₁ : x * nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) * x)
    (hx₂ : x * nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) * x)
    (hy₁ : y * nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single i 1 + Pi.single j 1 : Fin 3 → ZMod 3) l).val) * y)
    (hy₂ : y * nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) =
      nsSL ε hC (fun l => ((Pi.single k 1 : Fin 3 → ZMod 3) l).val) * y) :
    ⁅x, y⁆ ∈ (coordBlockSL (AdjoinRoot g) {i, j}).map (theta g ε) := by
  classical
  have hinv : ∀ {u s : SL(m, F)}, u * s = s * u → u⁻¹ * s = s * u⁻¹ := by
    intro u s h
    exact (show Commute u s from h).inv_left.eq
  have hθx := pairCent_coe_eq_thetaMat hprim hF hd hij hki hkj hx₁ hx₂
  have hθy := pairCent_coe_eq_thetaMat hprim hF hd hij hki hkj hy₁ hy₂
  have hθx' := pairCent_coe_eq_thetaMat hprim hF hd hij hki hkj (hinv hx₁) (hinv hx₂)
  have hθy' := pairCent_coe_eq_thetaMat hprim hF hd hij hki hkj (hinv hy₁) (hinv hy₂)
  have hbx := (pairCent_frameForm hprim hF hd hij hki hkj hx₁ hx₂).2
  have hby := (pairCent_frameForm hprim hF hd hij hki hkj hy₁ hy₂).2
  have hbx' := (pairCent_frameForm hprim hF hd hij hki hkj (hinv hx₁) (hinv hx₂)).2
  have hby' := (pairCent_frameForm hprim hF hd hij hki hkj (hinv hy₁) (hinv hy₂)).2
  set X := pairLMat ε x with hX
  set Y := pairLMat ε y with hY
  set X' := pairLMat ε x⁻¹ with hX'
  set Y' := pairLMat ε y⁻¹ with hY'
  have hone : ∀ {u : SL(m, F)} {A A' : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)},
      (u : Matrix (Fin m) (Fin m) F) = thetaMat g ε A →
      ((u⁻¹ : SL(m, F)) : Matrix (Fin m) (Fin m) F) = thetaMat g ε A' → A * A' = 1 := by
    intro u A A' hA hA'
    apply thetaMat_injective (ε := ε)
    rw [thetaMat_mul, ← hA, ← hA', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, thetaMat_one]
  have hXX' : X * X' = 1 := hone hθx hθx'
  have hYY' : Y * Y' = 1 := hone hθy hθy'
  set N := X * Y * X' * Y' with hN
  have hcoe : ((⁅x, y⁆ : SL(m, F)) : Matrix (Fin m) (Fin m) F) = thetaMat g ε N := by
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hθx, hθy, hθx', hθy',
      ← thetaMat_mul, ← thetaMat_mul, ← thetaMat_mul]
  have hdet : N.det = 1 := by
    have h1 := congrArg Matrix.det hXX'
    have h2 := congrArg Matrix.det hYY'
    rw [Matrix.det_mul, Matrix.det_one] at h1 h2
    rw [hN, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc X.det * Y.det * X'.det * Y'.det = (X.det * X'.det) * (Y.det * Y'.det) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  obtain ⟨hXY, hXYk⟩ := kdiag_mul hbx hby
  obtain ⟨hXYX', hXYX'k⟩ := kdiag_mul hXY hbx'
  obtain ⟨hNb, hNk⟩ := kdiag_mul hXYX' hby'
  have hk1 : X k k * X' k k = 1 := by
    rw [← (kdiag_mul hbx hbx').2, hXX', Matrix.one_apply_eq]
  have hk2 : Y k k * Y' k k = 1 := by
    rw [← (kdiag_mul hby hby').2, hYY', Matrix.one_apply_eq]
  have hNkk : N k k = 1 := by
    rw [hN, hNk, hXYX'k, hXYk]
    calc X k k * Y k k * X' k k * Y' k k = (X k k * X' k k) * (Y k k * Y' k k) := by ring
      _ = 1 := by rw [hk1, hk2, one_mul]
  obtain ⟨N', hN'⟩ : ∃ N' : Matrix.SpecialLinearGroup (Fin 3) (AdjoinRoot g),
      (N' : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) = N := ⟨⟨N, hdet⟩, rfl⟩
  have hmem : N' ∈ coordBlockSL (AdjoinRoot g) {i, j} := by
    rw [mem_coordBlockSL_iff]
    intro a b hab
    rw [not_mem_pair_iff hij hki hkj, not_mem_pair_iff hij hki hkj] at hab
    rw [hN']
    by_cases ha : a = k <;> by_cases hb : b = k
    · rw [ha, hb, if_pos rfl]
      exact hNkk
    · rw [if_neg (show a ≠ b from fun h => hb (h ▸ ha))]
      exact hNb a b ⟨fun _ => hb, fun _ => ha⟩
    · rw [if_neg (show a ≠ b from fun h => ha (h ▸ hb))]
      exact hNb a b ⟨fun h => absurd h ha, fun h => absurd hb h⟩
    · exact absurd (hab.resolve_left ha) hb
  refine ⟨N', hmem, Subtype.ext ?_⟩
  rw [coe_theta, hN']
  exact hcoe.symm

end PairCent

theorem pair_centralizer_derived_of_le_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (h3 : ((3 : ℕ) : F) ≠ 0) {g : F[X]} [Fact (Irreducible g)] (hg : g ∣ cyclotomic 3 F)
    {m d : ℕ} (hd : d ≤ 1) (ε : Fin m ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin d)
    (hC : (rootMat g).det = 1) (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    let β : Fin 3 → ZMod 3 := Pi.single i 1 + Pi.single j 1
    let γ : Fin 3 → ZMod 3 := Pi.single k 1
    let D : Subgroup (SL(m, F)) := Subgroup.centralizer
      ({nsSL ε hC (fun l => (β l).val), nsSL ε hC (fun l => (γ l).val)} : Set (SL(m, F)))
    ⁅D, D⁆ = (coordBlockSL (AdjoinRoot g) {i, j}).map (theta g ε) := by
  intro β γ D
  classical
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3 := root_isPrimitiveRoot Nat.prime_three h3 hg
  have hmemD : ∀ {x : SL(m, F)}, x ∈ D →
      x * nsSL ε hC (fun l => (β l).val) = nsSL ε hC (fun l => (β l).val) * x ∧
        x * nsSL ε hC (fun l => (γ l).val) = nsSL ε hC (fun l => (γ l).val) * x := fun hx =>
    ⟨(Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_insert _ _)).symm,
      (Subgroup.mem_centralizer_iff.mp hx _ (Set.mem_insert_of_mem _ rfl)).symm⟩
  set R := (coordBlockSL (AdjoinRoot g) {i, j}).map (theta g ε) with hRdef
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨hx₁, hx₂⟩ := hmemD hx
    obtain ⟨hy₁, hy₂⟩ := hmemD hy
    exact pairCent_commutator_mem hprim hF hd hij hki hkj hx₁ hx₂ hy₁ hy₂
  ·
    have hcases := fin_three_cases hij hki hkj
    have hRD : R ≤ D := by
      rintro _ ⟨M, hM, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro h (rfl | rfl)
      · refine nsSL_comm_theta hij hki hkj hM fun a b ha hb => ?_
        have hv : ∀ l, l ≠ k → (β l).val = 1 := fun l hl => by
          have hβl : β l = 1 := by
            rcases hcases l with rfl | rfl | rfl
            · simp [β, hij]
            · simp [β, hij.symm]
            · exact absurd rfl hl
          rw [hβl]
          rfl
        rw [hv a ha, hv b hb]
      · refine nsSL_comm_theta hij hki hkj hM fun a b ha hb => ?_
        simp [γ, ha, hb]
    have : Module.Finite F (AdjoinRoot g) := (rootPB g).finite
    have hdim : (rootPB g).dim = 2 :=
      SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) h3 hg ⟨1, by rw [hF]⟩
    have h4 : 4 ≤ Nat.card (AdjoinRoot g) := by
      rw [Module.natCard_eq_pow_finrank (K := F) (V := AdjoinRoot g), (rootPB g).finrank, hdim,
        hF]
      norm_num
    have hq : CFSG.IsQuasisimple (coordBlockSL (AdjoinRoot g) {i, j}) :=
      isQuasisimple_coordBlockSL (by rw [Finset.card_pair hij]) h4
    have hperf : ⁅coordBlockSL (AdjoinRoot g) {i, j}, coordBlockSL (AdjoinRoot g) {i, j}⁆ =
        coordBlockSL (AdjoinRoot g) {i, j} := by
      have h1 : commutator (coordBlockSL (AdjoinRoot g) {i, j}) = ⊤ := hq.1.commutator_eq_top
      have h2 := Subgroup.map_commutator (⊤ : Subgroup (coordBlockSL (AdjoinRoot g) {i, j})) ⊤
        (coordBlockSL (AdjoinRoot g) {i, j}).subtype
      rw [← commutator_def, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      exact h2.symm
    have hRR : ⁅R, R⁆ = R := by
      rw [hRdef, ← Subgroup.map_commutator, hperf]
    calc R = ⁅R, R⁆ := hRR.symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hRD hRD

theorem pair_centralizer_derived
    {m d : ℕ} (hm : m = 6 ∨ m = 7)
    {g : (ZMod 2)[X]} [Fact (Irreducible g)]
    (hg : g ∣ cyclotomic 3 (ZMod 2))
    (ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin 3) ⊕ Fin d)
    (hC : (CoordSL.rootMat g).det = 1) (_hCp : CoordSL.rootMat g ^ 3 = 1)
    (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    let β : Fin 3 → ZMod 3 := Pi.single i 1 + Pi.single j 1
    let γ : Fin 3 → ZMod 3 := Pi.single k 1
    let D : Subgroup (SL(m, ZMod 2)) := Subgroup.centralizer
      ({SLNS.nsSL ε hC (fun l => (β l).val),
        SLNS.nsSL ε hC (fun l => (γ l).val)} : Set (SL(m, ZMod 2)))
    ⁅D, D⁆ =
      (coordBlockSL (AdjoinRoot g) {i, j}).map (CoordSL.theta g ε) := by
  have h3 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hdim : (rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) h3 hg ⟨1, by rw [Nat.card_zmod]⟩
  have hmd : m = (rootPB g).dim * 3 + d := by
    have h := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using h
  have hd : d ≤ 1 := by omega
  exact pair_centralizer_derived_of_le_one (Nat.card_zmod 2) h3 hg hd ε hC i j k hij hki hkj

end CFSG.StandardType.QTwoBlocks

end
