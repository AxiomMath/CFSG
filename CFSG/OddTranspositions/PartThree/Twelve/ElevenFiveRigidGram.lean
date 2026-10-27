module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelBridge
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap

set_option backward.isDefEq.respectTransparency false

theorem exists_fiveReflOf_of_mem_fiveReflectionsIn {k : ℕ} {ε π : Bool}
    {U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {r : GL (Fin (k + 1)) (ZMod 5)} (hr : r ∈ fiveReflectionsIn k ε π U) :
    ∃ c ∈ U, fiveForm k ε c c ≠ 0 ∧ (IsSquare (fiveForm k ε c c) ↔ π = true) ∧
      r = fiveReflOf k ε c := by
  rcases hr with ⟨c, hcU, hcQ, hcπ, hform⟩
  refine ⟨c, hcU, hcQ, hcπ, ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hform (Pi.single i 1), fiveReflOf_mulVec]

private theorem isSquare_mul_of_iff :
    ∀ a b : ZMod 5, (IsSquare a ↔ IsSquare b) → IsSquare (a * b) := by
  decide

private theorem isSquare_mul_inv_of_iff {a b : ZMod 5} (h : IsSquare a ↔ IsSquare b) :
    IsSquare (a * b⁻¹) := by
  have hb' : IsSquare b ↔ IsSquare b⁻¹ :=
    ⟨IsSquare.inv, fun hb1 => by rw [← inv_inv b]; exact IsSquare.inv hb1⟩
  exact isSquare_mul_of_iff a b⁻¹ (h.trans hb')

theorem mul_inv_eq_one_or_neg_one {x y : ZMod 5} (hy : y ≠ 0) (h : x ^ 2 = y ^ 2) :
    y * x⁻¹ = 1 ∨ y * x⁻¹ = -1 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [pow_two, mul_zero] at h
    exact hy (sq_eq_zero_iff.mp h.symm)
  rcases (sq_eq_sq_iff_eq_or_eq_neg.1 h) with h | h
  · left; rw [h]; exact mul_inv_cancel₀ hy
  · right; rw [h]; field_simp

theorem exists_smul_mem_sq_eq {k : ℕ} {ε π : Bool}
    {U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {c b : Fin (k + 1) → ZMod 5} (hcU : c ∈ U) (hc : fiveForm k ε c c ≠ 0)
    (hcπ : IsSquare (fiveForm k ε c c) ↔ π = true)
    (hb : fiveForm k ε b b ≠ 0) (hbπ : IsSquare (fiveForm k ε b b) ↔ π = true) :
    ∃ c' ∈ U, fiveForm k ε c' c' = fiveForm k ε b b ∧
      fiveReflOf k ε c' = fiveReflOf k ε c := by
  obtain ⟨ν, hν⟩ := isSquare_mul_inv_of_iff (a := fiveForm k ε b b) (b := fiveForm k ε c c)
    (hbπ.trans hcπ.symm)
  have hνne : ν ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hν
    exact (mul_ne_zero hb (inv_ne_zero hc)) hν
  refine ⟨ν • c, Submodule.smul_mem _ _ hcU, ?_, ?_⟩
  · have h1 : fiveForm k ε (ν • c) (ν • c) = (ν * ν) * fiveForm k ε c c := by
      rw [fiveForm_smul_left, fiveForm_smul_right]; ring
    rw [h1, ← hν, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [fiveReflOf_smul k ε c hνne]

theorem orderOf_fiveReflOf_mul_eq_five_iff {k : ℕ} {ε π : Bool}
    {a b : Fin (k + 1) → ZMod 5} (ha : fiveForm k ε a a ≠ 0)
    (haπ : IsSquare (fiveForm k ε a a) ↔ π = true)
    (hb : fiveForm k ε b b ≠ 0) (hbπ : IsSquare (fiveForm k ε b b) ↔ π = true)
    (hab : ∀ μ : ZMod 5, b ≠ μ • a) (hne : fiveForm k ε a b ≠ 0) :
    (orderOf (fiveReflOf k ε a * fiveReflOf k ε b) = 5 ↔
      fiveForm k ε a b ^ 2 = fiveForm k ε a a * fiveForm k ε b b) := by
  rw [orderOf_fiveReflOf_mul k ε π ha haπ hb hbπ hab, if_neg hne]
  by_cases h : fiveForm k ε a b ^ 2 = fiveForm k ε a a * fiveForm k ε b b
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem orderOf_fiveReflOf_mul_eq_two_iff {k : ℕ} {ε π : Bool}
    {a b : Fin (k + 1) → ZMod 5} (ha : fiveForm k ε a a ≠ 0)
    (haπ : IsSquare (fiveForm k ε a a) ↔ π = true)
    (hb : fiveForm k ε b b ≠ 0) (hbπ : IsSquare (fiveForm k ε b b) ↔ π = true)
    (hab : ∀ μ : ZMod 5, b ≠ μ • a) :
    (fiveForm k ε a b = 0 ↔ orderOf (fiveReflOf k ε a * fiveReflOf k ε b) = 2) := by
  rw [orderOf_fiveReflOf_mul k ε π ha haπ hb hbπ hab]
  by_cases h : fiveForm k ε a b = 0
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    by_cases h2 : fiveForm k ε a b ^ 2 = fiveForm k ε a a * fiveForm k ε b b
    · rw [if_pos h2]; simp [h]
    · rw [if_neg h2]; simp [h]

private theorem sq_eq_one_or_four {x : ZMod 5} (hx : x ≠ 0) : x ^ 2 = 1 ∨ x ^ 2 = 4 :=
  (by decide : ∀ y : ZMod 5, y ≠ 0 → y ^ 2 = 1 ∨ y ^ 2 = 4) x hx

theorem eq_of_sq_eq_iff_sq_eq_of_isSquare (q x y : ZMod 5) (hq : IsSquare q) (hq0 : q ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 2 = q ↔ y ^ 2 = q) : x ^ 2 = y ^ 2 := by
  have hq14 : q = 1 ∨ q = 4 := by
    rcases hq with ⟨s, hs⟩
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hq0 hs
    rcases sq_eq_one_or_four hs0 with h1 | h1
    · left; rw [hs, ← h1, pow_two]
    · right; rw [hs, ← h1, pow_two]
  rcases hq14 with hq1 | hq4
  · rw [hq1] at h
    rcases sq_eq_one_or_four hx with hx1 | hx4 <;>
      rcases sq_eq_one_or_four hy with hy1 | hy4
    · rw [hx1, hy1]
    · rw [hx1] at h; rw [hy4] at h; exact absurd h (by decide)
    · rw [hx4] at h; rw [hy1] at h; exact absurd h (by decide)
    · rw [hx4, hy4]
  · rw [hq4] at h
    rcases sq_eq_one_or_four hx with hx1 | hx4 <;>
      rcases sq_eq_one_or_four hy with hy1 | hy4
    · rw [hx1, hy1]
    · rw [hx1] at h; rw [hy4] at h; exact absurd h (by decide)
    · rw [hx4] at h; rw [hy1] at h; exact absurd h (by decide)
    · rw [hx4, hy4]

theorem gram_data_of_orderOf_eq {k : ℕ} {ε π : Bool}
    {v w v' w' : Fin (k + 1) → ZMod 5}
    (hv : fiveForm k ε v v ≠ 0) (hvπ : IsSquare (fiveForm k ε v v) ↔ π = true)
    (hw : fiveForm k ε w w ≠ 0) (hwπ : IsSquare (fiveForm k ε w w) ↔ π = true)
    (hv' : fiveForm k ε v' v' ≠ 0) (hv'π : IsSquare (fiveForm k ε v' v') ↔ π = true)
    (hw' : fiveForm k ε w' w' ≠ 0) (hw'π : IsSquare (fiveForm k ε w' w') ↔ π = true)
    (hvw : ∀ μ : ZMod 5, w ≠ μ • v) (hv'w' : ∀ μ : ZMod 5, w' ≠ μ • v')
    (hQv : fiveForm k ε v v = fiveForm k ε v' v')
    (hQw : fiveForm k ε w w = fiveForm k ε w' w')
    (horder : orderOf (fiveReflOf k ε v' * fiveReflOf k ε w') =
      orderOf (fiveReflOf k ε v * fiveReflOf k ε w)) :
    (fiveForm k ε v' w' = 0 ↔ fiveForm k ε v w = 0) ∧
      fiveForm k ε v' w' ^ 2 = fiveForm k ε v w ^ 2 := by
  have htwo := orderOf_fiveReflOf_mul_eq_two_iff (k := k) (ε := ε) (π := π)
    hv hvπ hw hwπ hvw
  have htwo' := orderOf_fiveReflOf_mul_eq_two_iff (k := k) (ε := ε) (π := π)
    hv' hv'π hw' hw'π hv'w'
  have hord2 : orderOf (fiveReflOf k ε v' * fiveReflOf k ε w') = 2 ↔
      orderOf (fiveReflOf k ε v * fiveReflOf k ε w) = 2 := by rw [horder]
  have hz : fiveForm k ε v' w' = 0 ↔ fiveForm k ε v w = 0 :=
    htwo'.trans (hord2.trans htwo.symm)
  refine ⟨hz, ?_⟩
  by_cases h0 : fiveForm k ε v w = 0
  · have h0' : fiveForm k ε v' w' = 0 := hz.mpr h0
    rw [h0, h0']
  · have h0' : fiveForm k ε v' w' ≠ 0 := fun h => h0 (hz.mp h)
    have hQQ : fiveForm k ε v' v' * fiveForm k ε w' w' =
        fiveForm k ε v v * fiveForm k ε w w := by rw [hQv, hQw]
    have h5 := orderOf_fiveReflOf_mul_eq_five_iff (k := k) (ε := ε) (π := π)
      hv hvπ hw hwπ hvw h0
    have h5' := orderOf_fiveReflOf_mul_eq_five_iff (k := k) (ε := ε) (π := π)
      hv' hv'π hw' hw'π hv'w' h0'
    have h5b : orderOf (fiveReflOf k ε v' * fiveReflOf k ε w') = 5 ↔
        fiveForm k ε v' w' ^ 2 = fiveForm k ε v v * fiveForm k ε w w := by
      rw [h5', hQQ]
    have hord5 : orderOf (fiveReflOf k ε v' * fiveReflOf k ε w') = 5 ↔
        orderOf (fiveReflOf k ε v * fiveReflOf k ε w) = 5 := by rw [horder]
    have hiff : (fiveForm k ε v' w' ^ 2 = fiveForm k ε v v * fiveForm k ε w w) ↔
        (fiveForm k ε v w ^ 2 = fiveForm k ε v v * fiveForm k ε w w) :=
      h5b.symm.trans (hord5.trans h5)
    have hq_sq : IsSquare (fiveForm k ε v v * fiveForm k ε w w) :=
      isSquare_mul_of_iff (fiveForm k ε v v) (fiveForm k ε w w) (hvπ.trans hwπ.symm)
    exact eq_of_sq_eq_iff_sq_eq_of_isSquare
      (fiveForm k ε v v * fiveForm k ε w w) (fiveForm k ε v' w')
      (fiveForm k ε v w) hq_sq (mul_ne_zero hv hw) h0' h0 hiff

theorem exists_smul_c_of_gram {k : ℕ} {ε : Bool} {d : ℕ}
    {b c : Fin d → Fin (k + 1) → ZMod 5} {p : Fin d → Fin d}
    (hQ : ∀ i : Fin d, fiveForm k ε (c i) (c i) = fiveForm k ε (b i) (b i))
    (hzero : ∀ i j : Fin d, fiveForm k ε (c i) (c j) = 0 ↔ fiveForm k ε (b i) (b j) = 0)
    (hsq : ∀ i j : Fin d, fiveForm k ε (c i) (c j) ^ 2 = fiveForm k ε (b i) (b j) ^ 2)
    (hpar : ∀ i : Fin d, (i : ℕ) ≠ 0 → (p i : ℕ) < (i : ℕ) ∧
      fiveForm k ε (b i) (b (p i)) ≠ 0)
    (htree : ∀ i j : Fin d, fiveForm k ε (b i) (b j) ≠ 0 →
      i = j ∨ ((i : ℕ) ≠ 0 ∧ j = p i) ∨ ((j : ℕ) ≠ 0 ∧ i = p j)) :
    ∃ s : Fin d → ZMod 5, (∀ i : Fin d, s i = 1 ∨ s i = -1) ∧
      ∀ i j : Fin d, fiveForm k ε (s i • c i) (s j • c j) = fiveForm k ε (b i) (b j) := by
  have hedge : ∃ s : Fin d → ZMod 5, (∀ i : Fin d, s i = 1 ∨ s i = -1) ∧
      ∀ i : Fin d, (i : ℕ) ≠ 0 → fiveForm k ε (s i • c i) (s (p i) • c (p i)) =
        fiveForm k ε (b i) (b (p i)) := by
    have key : ∀ n, n ≤ d → ∃ s : Fin d → ZMod 5,
        (∀ i : Fin d, (i : ℕ) < n → s i = 1 ∨ s i = -1) ∧
        (∀ i : Fin d, (i : ℕ) < n → (i : ℕ) ≠ 0 →
          fiveForm k ε (s i • c i) (s (p i) • c (p i)) = fiveForm k ε (b i) (b (p i))) := by
      intro n
      induction n with
      | zero =>
        intro _
        exact ⟨fun _ => 1, by intro i hi; omega, by intro i hi; omega⟩
      | succ n ih =>
        intro hle
        obtain ⟨s, hs, hse⟩ := ih (by omega)
        have hn : n < d := by omega
        let i₀ : Fin d := ⟨n, hn⟩
        by_cases hn0 : n = 0
        · subst hn0
          refine ⟨Function.update s i₀ 1, ?_, ?_⟩
          · intro i hi
            have hii : i = i₀ := by
              apply Fin.ext
              simp only [i₀]
              omega
            subst hii
            rw [Function.update_self]
            exact Or.inl rfl
          · intro i hi hne
            exfalso
            apply hne
            omega
        · have hp_lt : (p i₀ : ℕ) < n := (hpar i₀ hn0).1
          have hp_ne : p i₀ ≠ i₀ := by
            intro h
            have h1 : (p i₀ : ℕ) = n := congrArg Fin.val h
            exact (ne_of_lt hp_lt) h1
          have hxc : fiveForm k ε (c i₀) (c (p i₀)) ≠ 0 :=
            fun h => (hpar i₀ hn0).2 ((hzero i₀ (p i₀)).mp h)
          let xb : ZMod 5 := fiveForm k ε (b i₀) (b (p i₀))
          let xc : ZMod 5 := fiveForm k ε (c i₀) (c (p i₀))
          let val : ZMod 5 := s (p i₀) * (xb * xc⁻¹)
          refine ⟨Function.update s i₀ val, ?_, ?_⟩
          · intro i hi
            by_cases hii : i = i₀
            · subst hii
              rw [Function.update_self]
              have hs1 : s (p i₀) = 1 ∨ s (p i₀) = -1 := hs (p i₀) hp_lt
              have hr : xb * xc⁻¹ = 1 ∨ xb * xc⁻¹ = -1 := by
                have h : xc ^ 2 = xb ^ 2 := by
                  dsimp only [xc, xb]
                  exact hsq i₀ (p i₀)
                exact mul_inv_eq_one_or_neg_one (hpar i₀ hn0).2 h
              rcases hs1 with h1 | h1 <;> rcases hr with h2 | h2 <;>
                · dsimp only [val]; rw [h1, h2]; decide
            · have hii' : (i : ℕ) ≠ n := by
                intro h
                apply hii
                apply Fin.ext
                simpa only [i₀] using h
              rw [Function.update_of_ne hii]
              exact hs i (by omega)
          · intro i hi hne
            by_cases hii : i = i₀
            · subst hii
              rw [Function.update_self, Function.update_of_ne hp_ne]
              rw [show val = s (p i₀) * (fiveForm k ε (b i₀) (b (p i₀)) *
                    (fiveForm k ε (c i₀) (c (p i₀)))⁻¹) from rfl]
              rw [fiveForm_smul_left, fiveForm_smul_right]
              have hs2 : s (p i₀) * s (p i₀) = 1 := by
                rcases hs (p i₀) hp_lt with h | h <;> rw [h] <;> decide
              calc s (p i₀) * (fiveForm k ε (b i₀) (b (p i₀)) *
                      (fiveForm k ε (c i₀) (c (p i₀)))⁻¹) *
                    (s (p i₀) * fiveForm k ε (c i₀) (c (p i₀)))
                  = (s (p i₀) * s (p i₀)) * (fiveForm k ε (b i₀) (b (p i₀)) *
                      ((fiveForm k ε (c i₀) (c (p i₀)))⁻¹ *
                        fiveForm k ε (c i₀) (c (p i₀)))) := by ring
                _ = fiveForm k ε (b i₀) (b (p i₀)) := by
                    rw [hs2, inv_mul_cancel₀ hxc]; ring
            · have hnm : (i : ℕ) ≠ n := by
                intro hh; exact hii (Fin.ext hh)
              have hi_n : (i : ℕ) < n := by omega
              have hpi_ne : p i ≠ i₀ := by
                intro h
                have h1 : (p i : ℕ) = n := congrArg Fin.val h
                have h2 : (p i : ℕ) < (i : ℕ) := (hpar i hne).1
                omega
              rw [Function.update_of_ne hii, Function.update_of_ne hpi_ne]
              exact hse i hi_n hne
    obtain ⟨s, hs, hse⟩ := key d le_rfl
    exact ⟨s, fun i => hs i i.isLt, fun i hi => hse i i.isLt hi⟩
  obtain ⟨s, hs, hse⟩ := hedge
  refine ⟨s, hs, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    have hs1 : s i * s i = 1 := by
      rcases hs i with h | h <;> rw [h] <;> decide
    rw [fiveForm_smul_left, fiveForm_smul_right, hQ i, ← mul_assoc, hs1, one_mul]
  · by_cases hb0 : fiveForm k ε (b i) (b j) = 0
    · rw [hb0]
      have hcij : fiveForm k ε (c i) (c j) = 0 := (hzero i j).mpr hb0
      simp [fiveForm_smul_left, fiveForm_smul_right, hcij]
    · have hcij : fiveForm k ε (c i) (c j) ≠ 0 := fun h => hb0 ((hzero i j).mp h)
      rcases htree i j hb0 with h | h | h
      · exact absurd h hij
      · rcases h with ⟨hi0, rfl⟩
        exact hse i hi0
      · rcases h with ⟨hj0, hji⟩
        rw [hji, fiveForm_comm, hse j hj0, fiveForm_comm]

theorem isFiveNondeg_restrict {k : ℕ} {ε : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W) :
    ((fiveQ k ε).restrict W).Nondegenerate := by
  let : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide : (2 : ZMod 5) ≠ 0)
  rw [← QuadraticMap.nondegenerate_polar_iff]
  constructor
  · intro x hx
    apply Subtype.ext
    apply isFiveNondeg_iff.1 hW x x.2
    intro y hy
    have h := hx ⟨y, hy⟩
    rw [QuadraticMap.polarBilin_apply_apply] at h
    have hp : QuadraticMap.polar ((fiveQ k ε).restrict W) x ⟨y, hy⟩ =
        QuadraticMap.polar (fiveQ k ε) (x : Fin (k + 1) → ZMod 5) y := rfl
    rw [hp, fiveQ_polar] at h
    exact (mul_eq_zero.mp h).resolve_left (by decide : (2 : ZMod 5) ≠ 0)
  · intro y hy
    apply Subtype.ext
    apply isFiveNondeg_iff.1 hW y y.2
    intro x hx
    have h := hy ⟨x, hx⟩
    rw [QuadraticMap.polarBilin_apply_apply] at h
    have hp : QuadraticMap.polar ((fiveQ k ε).restrict W) ⟨x, hx⟩ y =
        QuadraticMap.polar (fiveQ k ε) x (y : Fin (k + 1) → ZMod 5) := rfl
    rw [hp, fiveQ_polar] at h
    rw [fiveForm_comm]
    exact (mul_eq_zero.mp h).resolve_left (by decide : (2 : ZMod 5) ≠ 0)

theorem exists_isometry_of_gram {k : ℕ} {ε : Bool}
    {W W' : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {d : ℕ}
    (hW : IsFiveNondeg k ε W) (b : Fin d → Fin (k + 1) → ZMod 5) (hbW : ∀ i, b i ∈ W)
    (hbind : LinearIndependent (ZMod 5) b) (hd : d = Module.finrank (ZMod 5) W)
    (c : Fin d → Fin (k + 1) → ZMod 5) (hcW' : ∀ i, c i ∈ W')
    (hdim : d = Module.finrank (ZMod 5) W') (hG : ∀ i j, fiveForm k ε (c i) (c j) =
      fiveForm k ε (b i) (b j)) :
    ∃ M : GL (Fin (k + 1)) (ZMod 5),
      (∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
          ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y) ∧
      (∀ i, (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b i = c i) ∧
      W.map (Matrix.toLin' (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))) = W' := by
  have hcard : Fintype.card (Fin d) = Module.finrank (ZMod 5) W := by
    rw [Fintype.card_fin, hd]
  let bW : Module.Basis (Fin d) (ZMod 5) W :=
    basisOfLinearIndependentOfCardEqFinrank' (K := ZMod 5)
      (Set.codRestrict b W hbW) (hbind.codRestrict W hbW) hcard
  have hbW_coe : ∀ i, ((bW i : W) : Fin (k + 1) → ZMod 5) = b i := by
    intro i
    simp [bW]
  let M₀ : W →ₗ[ZMod 5] (Fin (k + 1) → ZMod 5) := bW.constr (ZMod 5) c
  have hM₀ : ∀ i, M₀ (bW i) = c i := fun i => bW.constr_basis (ZMod 5) c i
  have hB : ∀ x y : W, fiveForm k ε (M₀ x) (M₀ y) = fiveForm k ε (x : _) (y : _) := by
    let F : (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5]
        ((Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5) := fiveBilin k ε true
    have hB₁ : LinearMap.compl₂ (LinearMap.comp F M₀) M₀ =
        LinearMap.compl₂ (LinearMap.comp F W.subtype) W.subtype := by
      apply LinearMap.BilinForm.ext_basis bW
      intro i j
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hM₀, F, fiveBilin_apply,
        fiveSignRep, if_true, inv_one, one_mul, Submodule.subtype_apply]
      rw [hbW_coe i, hbW_coe j, hG i j]
    intro x y
    simpa only [F, LinearMap.compl₂_apply, LinearMap.comp_apply, fiveBilin_apply,
      fiveSignRep, if_true, inv_one, one_mul, Submodule.subtype_apply] using
      LinearMap.congr_fun (LinearMap.congr_fun hB₁ x) y
  have hinj : Function.Injective M₀ := by
    intro x y hxy
    have hz : M₀ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hxy0 : x - y = 0 := by
      apply Subtype.ext
      apply isFiveNondeg_iff.1 hW (x - y) (Submodule.sub_mem _ x.2 y.2)
      intro z hz'
      change fiveForm k ε ((x - y : W) : Fin (k + 1) → ZMod 5) z = 0
      have h := hB (x - y) ⟨z, hz'⟩
      rw [hz] at h
      rw [h.symm]
      simp
    exact sub_eq_zero.mp hxy0
  have hrange_le : LinearMap.range M₀ ≤ W' := by
    rintro y ⟨x, rfl⟩
    rw [← bW.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul, hM₀]
      exact Submodule.smul_mem _ _ (hcW' i)
  have hfinrange : Module.finrank (ZMod 5) (LinearMap.range M₀) = d := by
    have h1 : Module.finrank (ZMod 5) W = Module.finrank (ZMod 5) (LinearMap.range M₀) :=
      (LinearEquiv.ofInjective M₀ hinj).finrank_eq
    rw [← h1, Module.finrank_eq_card_basis bW]
    simp
  have hrange : LinearMap.range M₀ = W' := by
    apply Submodule.eq_of_le_of_finrank_eq hrange_le
    rw [hfinrange, hdim]
  let M₀' : W →ₗ[ZMod 5] W' :=
    M₀.codRestrict W' fun x => hrange_le (LinearMap.mem_range_self M₀ x)
  have hM₀'_coe : ∀ x : W, ((M₀' x : W') : Fin (k + 1) → ZMod 5) = M₀ x := fun x => rfl
  have hinj' : Function.Injective M₀' := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hsurj' : Function.Surjective M₀' := by
    intro y
    have hy : (y : Fin (k + 1) → ZMod 5) ∈ LinearMap.range M₀ := by
      rw [hrange]; exact y.2
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let g : W ≃ₗ[ZMod 5] W' := LinearEquiv.ofBijective M₀' ⟨hinj', hsurj'⟩
  have hg_apply : ∀ x : W, ((g x : W') : Fin (k + 1) → ZMod 5) = M₀ x := fun x => rfl
  let f : ((fiveQ k ε).restrict W).IsometryEquiv ((fiveQ k ε).restrict W') :=
    { g with
      map_app' := fun x => by
        show fiveQ k ε ((g x : W') : Fin (k + 1) → ZMod 5) = fiveQ k ε (x : W)
        rw [hg_apply x, fiveQ_apply, fiveQ_apply]
        exact hB x x }
  let : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide : (2 : ZMod 5) ≠ 0)
  obtain ⟨e, he⟩ := f.exists_extension (isFiveNondeg_restrict (k := k) (ε := ε) hW)
  let M : GL (Fin (k + 1)) (ZMod 5) := (fiveGLIso k).symm e.toLinearEquiv
  have hM : fiveGLIso k M = e.toLinearEquiv := (fiveGLIso k).apply_symm_apply e.toLinearEquiv
  have hMx : ∀ x : Fin (k + 1) → ZMod 5,
      (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = e x := by
    intro x
    have h1 : fiveGLIso k M x = (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x :=
      fiveGLIso_apply k M x
    rw [← h1, hM]
    rfl
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x y
    rw [hMx x, hMx y]
    have hpol : QuadraticMap.polar (fiveQ k ε) (e x) (e y) =
        QuadraticMap.polar (fiveQ k ε) x y := by
      simp only [QuadraticMap.polar]
      rw [← map_add, e.map_app, e.map_app, e.map_app]
    have h2 : 2 * fiveForm k ε (e x) (e y) = 2 * fiveForm k ε x y := by
      rw [← fiveQ_polar k ε (e x) (e y), hpol, fiveQ_polar k ε x y]
    exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h2
  · intro i
    rw [hMx, ← hbW_coe i, he (bW i)]
    change ((f (bW i) : W') : Fin (k + 1) → ZMod 5) = c i
    rw [show ((f (bW i) : W') : Fin (k + 1) → ZMod 5) = (g (bW i) : _) from rfl,
      hg_apply (bW i)]
    exact hM₀ i
  · have htl : Matrix.toLin' (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) =
        (fiveGLIso k M : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)).toLinearMap := by
      apply LinearMap.ext
      intro x
      rw [Matrix.toLin'_apply]
      exact (fiveGLIso_apply k M x).symm
    rw [htl, hM]
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change e ((⟨x, hx⟩ : W) : Fin (k + 1) → ZMod 5) ∈ W'
      rw [he ⟨x, hx⟩]
      exact (f ⟨x, hx⟩).2
    · intro y hy
      rw [Submodule.mem_map]
      refine ⟨((f.symm ⟨y, hy⟩ : W) : Fin (k + 1) → ZMod 5), (f.symm ⟨y, hy⟩).2, ?_⟩
      change e ((f.symm ⟨y, hy⟩ : W) : Fin (k + 1) → ZMod 5) = y
      rw [he ((f.symm ⟨y, hy⟩ : W))]
      simp

end CFSG.OddTranspositions.PartThree

end
