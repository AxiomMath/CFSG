module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl

public section

namespace CFSG.StandardType.ZS.FFourCoord

@[expose] def reflB3 : Fin 9 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 0, -1; 0, 1, 0; -1, 0, 0],
    !![1, 0, 0; 0, 0, -1; 0, -1, 0]]

theorem reflB3_trichotomy : ∀ i j k : Fin 9,
    (reflB3 i * reflB3 j) ^ 2 ≠ 1 ∧ (reflB3 i * reflB3 j) ^ 3 ≠ 1 ∧ reflB3 k ≠ reflB3 i ∧
      reflB3 k ≠ reflB3 j ∧ reflB3 k ≠ reflB3 i * reflB3 j * reflB3 i ∧
      reflB3 k ≠ reflB3 j * reflB3 i * reflB3 j ∧
      reflB3 k * (reflB3 i * reflB3 j * reflB3 i) ≠ reflB3 i * reflB3 j * reflB3 i * reflB3 k →
    (reflB3 j * reflB3 k * reflB3 j * reflB3 i = reflB3 i * (reflB3 j * reflB3 k * reflB3 j) ∧
        (reflB3 k * reflB3 j) ^ 3 = 1) ∨
      (reflB3 k * reflB3 i = reflB3 i * reflB3 k ∧ (reflB3 k * reflB3 j) ^ 3 = 1) ∨
      ((reflB3 i * reflB3 k) ^ 3 = 1 ∧ reflB3 j * reflB3 k = reflB3 k * reflB3 j) := by
  decide +kernel

variable {p : ℕ} [Fact p.Prime]

private lemma zsf4b_one_ne_zero : (1 : ZMod p) ≠ 0 :=
  fun h => (Fact.out : p.Prime).ne_one (ZMod.one_eq_zero_iff.mp h)

private lemma zsf4b_neg_one_ne_one (hp : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  rcases (ZMod.neg_one_eq_one_iff (n := p)).mp h with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h1

private lemma zsf4b_neg_one_mul_neg_one : ((-1 : ZMod p) * (-1)) = 1 := by
  have h : ((-1 : ZMod p) * (-1)) = 1 * 1 := neg_mul_neg 1 1
  rwa [mul_one] at h

private lemma zsf4b_mul_sign {a b : ZMod p} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2]
  · left; rw [one_mul]
  · right; rw [one_mul]
  · right; rw [mul_one]
  · left; exact zsf4b_neg_one_mul_neg_one

theorem exists_signedPerm_of_mem_g2mmn {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (e : Module.Basis (Fin 3) (ZMod p) W) {y : W ≃ₗ[ZMod p] W} (hy : y ∈ g2mmn p e 0 1 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ s : Fin 3 → ZMod p, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i, y (e i) = s i • e (σ i) := by
  rw [g2mmn] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rw [Set.mem_union] at hx
    rcases hx with ⟨σ, rfl⟩ | hx
    · exact ⟨σ, fun _ => 1, fun _ => Or.inl rfl, fun i => by
        rw [permMap_apply_basis, one_smul]⟩
    · rw [Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · refine ⟨1, fun i => (((if i = 0 then (-1 : (ZMod p)ˣ) else 1) : (ZMod p)ˣ) : ZMod p),
          fun i => ?_, fun i => ?_⟩
        · by_cases h : i = 0
          · right; dsimp only; rw [if_pos h]; rfl
          · left; dsimp only; rw [if_neg h]; rfl
        · rw [diagMap_apply_basis]
          rfl
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
        simp [diagMap_apply_basis, pairUnit_one]
  | one => exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun i => by simp⟩
  | mul x y hx hy IHx IHy =>
    obtain ⟨σ, s, hs, hxσ⟩ := IHx
    obtain ⟨τ, t, ht, hyτ⟩ := IHy
    refine ⟨σ * τ, fun i => t i * s (τ i), fun i => zsf4b_mul_sign (ht i) (hs (τ i)), fun i => ?_⟩
    rw [LinearEquiv.mul_apply, hyτ i, map_smul, hxσ (τ i), smul_smul, Equiv.Perm.mul_apply]
  | inv x hx IH =>
    obtain ⟨σ, s, hs, hxσ⟩ := IH
    refine ⟨σ.symm, fun i => s (σ.symm i), fun i => hs _, fun i => ?_⟩
    have h1 : x (e (σ.symm i)) = s (σ.symm i) • e i := by
      rw [hxσ (σ.symm i), Equiv.apply_symm_apply]
    have hss : s (σ.symm i) * s (σ.symm i) = 1 := by
      rcases hs (σ.symm i) with h | h <;> rw [h]
      · rw [one_mul]
      · exact zsf4b_neg_one_mul_neg_one
    have h2 : s (σ.symm i) • x (e (σ.symm i)) = e i := by
      rw [h1, smul_smul, hss, one_smul]
    calc x⁻¹ (e i) = x⁻¹ (s (σ.symm i) • x (e (σ.symm i))) := by rw [h2]
      _ = s (σ.symm i) • x⁻¹ (x (e (σ.symm i))) := by rw [map_smul]
      _ = s (σ.symm i) • e (σ.symm i) := by
        change s (σ.symm i) • x.symm (x (e (σ.symm i))) = s (σ.symm i) • e (σ.symm i)
        rw [LinearEquiv.symm_apply_apply]

private lemma zsf4b_toMatrix {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (e : Module.Basis (Fin 3) (ZMod p) W) {y : W ≃ₗ[ZMod p] W} {σ : Equiv.Perm (Fin 3)}
    {s : Fin 3 → ZMod p} (hσ : ∀ i, y (e i) = s i • e (σ i)) :
    LinearMap.toMatrix e e y.toLinearMap = fun a b => if σ b = a then s b else 0 := by
  ext a b
  simp only [LinearMap.toMatrix_apply]
  change e.repr (y (e b)) a = if σ b = a then s b else 0
  rw [hσ b]
  rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases h : σ b = a
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

private lemma zsf4b_mapMatrix_reflB3 (k : Fin 9) :
    (Int.castRingHom (ZMod p)).mapMatrix (reflB3 k) =
      fun a b : Fin 3 => ((reflB3 k a b : ℤ) : ZMod p) := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

private lemma zsf4b_reflB3_sign_cast (i a b : Fin 3) :
    (((reflB3 ⟨i.val, by omega⟩ a b : ℤ) : ZMod p)) =
      if b = a then (if b = i then (-1 : ZMod p) else 1) else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [reflB3] <;> rfl

private def zsf4b_swapIndex (i j : Fin 3) (ε : ZMod p) : Fin 9 :=
  if ε = 1 then
    (if i.val + j.val = 1 then 3 else if i.val + j.val = 2 then 4 else 5)
  else
    (if i.val + j.val = 1 then 6 else if i.val + j.val = 2 then 7 else 8)

private lemma zsf4b_reflB3_swap_cast (hp : p ≠ 2) (i j : Fin 3) (hij : i ≠ j)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) (a b : Fin 3) :
    (((reflB3 (zsf4b_swapIndex i j ε) a b : ℤ) : ZMod p)) =
      if b = i then (if a = j then ε else 0)
      else if b = j then (if a = i then ε else 0)
      else if a = b then 1 else 0 := by
  rcases hε with rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
      (first
        | (exfalso; exact (hij rfl).elim)
        | (fin_cases a <;> fin_cases b <;>
            simp [zsf4b_swapIndex, reflB3, zsf4b_neg_one_ne_one hp] <;> rfl))

private lemma zsf4b_toMatrix_sign {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (e : Module.Basis (Fin 3) (ZMod p) W) {y : W ≃ₗ[ZMod p] W} {σ : Equiv.Perm (Fin 3)}
    {s : Fin 3 → ZMod p} {i : Fin 3} (hσ : ∀ b, y (e b) = s b • e (σ b)) (hσ1 : σ = 1)
    (hsval : ∀ b : Fin 3, s b = if b = i then (-1 : ZMod p) else 1) :
    LinearMap.toMatrix e e y.toLinearMap =
      (Int.castRingHom (ZMod p)).mapMatrix (reflB3 ⟨i.val, by omega⟩) := by
  rw [zsf4b_toMatrix e hσ, hσ1]
  change (fun a b : Fin 3 => if b = a then s b else 0) =
    fun a b : Fin 3 => ((reflB3 ⟨i.val, by omega⟩ a b : ℤ) : ZMod p)
  ext a b
  rw [zsf4b_reflB3_sign_cast, hsval b]

private lemma zsf4b_toMatrix_swap (hp : p ≠ 2) {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] (e : Module.Basis (Fin 3) (ZMod p) W) {y : W ≃ₗ[ZMod p] W}
    {i j : Fin 3} (hij : i ≠ j) {s : Fin 3 → ZMod p}
    (hσ : ∀ b, y (e b) = s b • e (Equiv.swap i j b))
    (hs : ∀ b, s b = 1 ∨ s b = -1) (hsj_eq : s j = s i)
    (hsk : ∀ b, b ≠ i → b ≠ j → s b = 1) :
    LinearMap.toMatrix e e y.toLinearMap =
      (Int.castRingHom (ZMod p)).mapMatrix (reflB3 (zsf4b_swapIndex i j (s i))) := by
  rw [zsf4b_toMatrix e hσ, zsf4b_mapMatrix_reflB3]
  funext a b
  rw [zsf4b_reflB3_swap_cast hp i j hij (hs i)]
  by_cases hbi : b = i
  · rw [hbi]
    by_cases haj : j = a <;> simp [haj, eq_comm]
  · by_cases hbj : b = j
    · subst hbj
      rw [Equiv.swap_apply_right, hsj_eq]
      rw [if_neg (Ne.symm hij), if_pos rfl]
      by_cases hai : i = a
      · rw [if_pos hai, if_pos hai.symm]
      · rw [if_neg hai, if_neg (fun h => hai h.symm)]
    · have hswap : Equiv.swap i j b = b := Equiv.swap_apply_of_ne_of_ne hbi hbj
      have hsb : s b = 1 := hsk b hbi hbj
      by_cases hab : a = b
      · simp [hswap, hsb, hbi, hbj, hab]
      · have hba : b ≠ a := fun h => hab h.symm
        simp [hswap, hbi, hbj, hba, hab]

theorem exists_reflB3_of_isRefl (hp : p ≠ 2) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (e : Module.Basis (Fin 3) (ZMod p) W) {y : W ≃ₗ[ZMod p] W} (hy : y ∈ g2mmn p e 0 1 1)
    (hr : IsRefl p y) :
    ∃ k : Fin 9, LinearMap.toMatrix e e y.toLinearMap =
      (Int.castRingHom (ZMod p)).mapMatrix (reflB3 k) := by
  obtain ⟨σ, s, hs, hσ⟩ := exists_signedPerm_of_mem_g2mmn e hy
  have hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsne : ∀ i, s i ≠ 0 := by
    intro i
    rcases hs i with h | h
    · rw [h]; exact zsf4b_one_ne_zero
    · rw [h]; exact neg_ne_zero.mpr zsf4b_one_ne_zero
  have hGG : CFSG.StandardType.GGLinRefl y := hr
  rcases CFSG.StandardType.ggRC_monomial_refl_shape hp e y hGG σ s hsne hσ with
    ⟨i, hσ1, hsi, hsj⟩ | ⟨i, j, hij, hσswap, hsc, hsk⟩
  · have hsval : ∀ b : Fin 3, s b = if b = i then (-1 : ZMod p) else 1 := by
      intro b
      by_cases h : b = i
      · rw [if_pos h, h]; exact hsi
      · rw [if_neg h]; exact hsj b h
    exact ⟨⟨i.val, by omega⟩, zsf4b_toMatrix_sign e hσ hσ1 hsval⟩
  · subst σ
    have hsj_eq : s j = s i := by
      rcases hs i with hi | hi
      · have hj : s j = 1 := by simpa [hi] using hsc
        rw [hj, hi]
      · have hmul : ((-1 : ZMod p) * s j) = 1 := by simpa [hi] using hsc
        have hj : s j = -1 := by
          have h2 := congrArg (fun x => (-1 : ZMod p) * x) hmul
          rw [← mul_assoc, zsf4b_neg_one_mul_neg_one, one_mul, mul_one] at h2
          exact h2
        rw [hj, hi]
    exact ⟨zsf4b_swapIndex i j (s i), zsf4b_toMatrix_swap hp e hij hσ hs hsj_eq hsk⟩


end CFSG.StandardType.ZS.FFourCoord

end
