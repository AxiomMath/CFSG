module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofGen
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofIrr
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

namespace ProofKSL3Two

open ProofHess

@[expose] def cycDiag {K : Type*} (a b c : K) : Fin 3 → Fin 3 → K :=
  ![![a, b, c], ![c, a, b], ![b, c, a]]

theorem exists_cycDiag_ne {K : Type*} {a b c : K} (habc : ¬ (a = b ∧ b = c)) {i j : Fin 3}
    (hij : i ≠ j) :
    ∃ t : Fin 3, cycDiag a b c t i ≠ cycDiag a b c t j := by
  by_contra h
  push Not at h
  apply habc
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  fin_cases i <;> fin_cases j <;>
    simp [cycDiag] at h0 h1 h2 hij ⊢ <;> grind

section Coordinates

variable {K : Type} [Field K]

theorem eq_or_eq_of_ne {i j l m : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hmi : m ≠ i) : m = j ∨ m = l := by
  have h1 := Fin.val_ne_of_ne hij
  have h2 := Fin.val_ne_of_ne hil
  have h3 := Fin.val_ne_of_ne hjl
  have h4 := Fin.val_ne_of_ne hmi
  have := m.isLt
  have := i.isLt
  have := j.isLt
  have := l.isLt
  have : m.val = j.val ∨ m.val = l.val := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem single_mem_of_sep {W : Submodule K (Fin 3 → K)} {x y : Fin 3 → K}
    (hx : ∀ v ∈ W, diagonal x *ᵥ v ∈ W) (hy : ∀ v ∈ W, diagonal y *ᵥ v ∈ W)
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hxij : x i ≠ x j)
    (hyil : y i ≠ y l) {v : Fin 3 → K} (hv : v ∈ W) : Pi.single i (v i) ∈ W := by
  set w₁ := diagonal x *ᵥ v - x j • v with hw₁
  have hw₁W : w₁ ∈ W := W.sub_mem (hx v hv) (W.smul_mem _ hv)
  set w₂ := diagonal y *ᵥ w₁ - y l • w₁ with hw₂
  have hw₂W : w₂ ∈ W := W.sub_mem (hy w₁ hw₁W) (W.smul_mem _ hw₁W)
  have hc : (y i - y l) * (x i - x j) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hyil) (sub_ne_zero.mpr hxij)
  have heq : w₂ = ((y i - y l) * (x i - x j)) • Pi.single i (v i) := by
    funext m
    simp only [hw₂, hw₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    by_cases hmi : m = i
    · subst hmi
      simp only [Pi.single_eq_same]
      ring
    · rw [Pi.single_eq_of_ne hmi, mul_zero]
      rcases eq_or_eq_of_ne hij hil hjl hmi with rfl | rfl <;> ring
  have h1 := W.smul_mem ((y i - y l) * (x i - x j))⁻¹ hw₂W
  rwa [heq, smul_smul, inv_mul_cancel₀ hc, one_smul] at h1

theorem diag_invariant_of_cyc {W : Submodule K (Fin 3 → K)} {a b c : K}
    (habc : ¬ (a = b ∧ b = c))
    (hW : ∀ t : Fin 3, ∀ v ∈ W, diagonal (cycDiag a b c t) *ᵥ v ∈ W) (d : Fin 3 → K) :
    ∀ v ∈ W, diagonal d *ᵥ v ∈ W := by
  intro v hv
  have hsing : ∀ k : Fin 3, Pi.single k (v k) ∈ W := by
    have key : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Pi.single i (v i) ∈ W := by
      intro i j l hij hil hjl
      obtain ⟨t₁, ht₁⟩ := exists_cycDiag_ne habc hij
      obtain ⟨t₂, ht₂⟩ := exists_cycDiag_ne habc hil
      exact single_mem_of_sep (hW t₁) (hW t₂) hij hil hjl ht₁ ht₂ hv
    intro k
    fin_cases k
    · exact key 0 1 2 (by decide) (by decide) (by decide)
    · exact key 1 0 2 (by decide) (by decide) (by decide)
    · exact key 2 0 1 (by decide) (by decide) (by decide)
  have heq : diagonal d *ᵥ v =
      d 0 • Pi.single 0 (v 0) + d 1 • Pi.single 1 (v 1) + d 2 • Pi.single 2 (v 2) := by
    funext m
    fin_cases m <;> simp [Matrix.mulVec_diagonal]
  rw [heq]
  exact add_mem (add_mem (W.smul_mem _ (hsing 0)) (W.smul_mem _ (hsing 1)))
    (W.smul_mem _ (hsing 2))

theorem cycThree_mulVec_single (k : Fin 3) :
    ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single k 1 =
      Pi.single (k + 1) 1 := by
  rw [coe_cycThree]
  funext m
  fin_cases k <;> fin_cases m <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem eq_bot_or_eq_top_of_diag_cyc {W : Submodule K (Fin 3 → K)}
    (hd : ∀ d : Fin 3 → K, ∀ v ∈ W, diagonal d *ᵥ v ∈ W)
    (hc : ∀ v ∈ W, ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hek : Pi.single k (1 : K) ∈ W := by
    have h1 := hd (Pi.single k (v k)⁻¹) v hv
    have h2 : diagonal (Pi.single k (v k)⁻¹) *ᵥ v = Pi.single k 1 := by
      funext m
      rw [Matrix.mulVec_diagonal]
      by_cases hmk : m = k
      · subst hmk
        simp [inv_mul_cancel₀ hk]
      · simp [Pi.single_eq_of_ne hmk]
    rwa [h2] at h1
  have hall : ∀ m : Fin 3, Pi.single m (1 : K) ∈ W := by
    have h1 : Pi.single (k + 1) (1 : K) ∈ W := by
      rw [← cycThree_mulVec_single]
      exact hc _ hek
    have h2 : Pi.single (k + 1 + 1) (1 : K) ∈ W := by
      rw [← cycThree_mulVec_single]
      exact hc _ h1
    intro m
    have : m = k ∨ m = k + 1 ∨ m = k + 1 + 1 := by
      fin_cases k <;> fin_cases m <;> decide
    rcases this with rfl | rfl | rfl
    · exact hek
    · exact h1
    · exact h2
  rw [eq_top_iff]
  intro u _
  have hu : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 + u 2 • Pi.single 2 1 := by
    funext m
    fin_cases m <;> simp
  rw [hu]
  exact add_mem (add_mem (W.smul_mem _ (hall 0)) (W.smul_mem _ (hall 1)))
    (W.smul_mem _ (hall 2))

theorem eq_smul_one_of_commute_cyc {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c : K}
    (habc : ¬ (a = b ∧ b = c)) {T : Matrix (Fin 3) (Fin 3) K}
    (hT : ∀ t : Fin 3, T * diagonal (cycDiag a b c t) = diagonal (cycDiag a b c t) * T)
    (hc : T * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * T) :
    T = T 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hoff : ∀ i j : Fin 3, i ≠ j → T i j = 0 := by
    intro i j hij
    obtain ⟨t, ht⟩ := exists_cycDiag_ne habc hij
    exact entry_eq_zero_of_commute_diagonal (hT t) ht
  have hTd : T = diagonal fun i => T i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  refine eq_smul_one_of_commute hτ hτ1 ?_ hc
  rw [hTd, coe_diagTau_eq_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end Coordinates

section Frame

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem cyc_mul_diagonal_mul_inv (a b c : K) :
    ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] *
      ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![c, a, b] := by
  rw [coe_cycThree, coe_cycThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem cyc_inv_mul_diagonal_mul (a b c : K) :
    ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] *
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![b, c, a] := by
  rw [coe_cycThree, coe_cycThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem exists_cyc_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y₁ 1) (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧ ∃ z ∈ StatedScalars (Fin 3) K, ∃ g : GL (Fin 3) K,
      g⁻¹ * (y₁ * z) * g = diagTau hτ ∧
        (g⁻¹ * y₂ * g = cycThree ∨ g⁻¹ * y₂ * g = cycThree⁻¹) := by
  obtain ⟨τ, hτ, hτ1, z₁, hz₁, g₁, hg₁, hD⟩ := h1
  have hz₁s := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₁
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hζ3 : (ζ : K) ^ 3 = 1 := by
    have h := congrArg Units.val (pow_three_eq_one_of_conj_eq_scalar_mul hζ)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hζ1' : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  refine ⟨τ, hτ, hτ1, z₁, hz₁s, ?_⟩
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hζ3 with h | h | h
  · exact absurd h hζ1'
  · obtain ⟨g, -, hgc, hgd⟩ := exists_heis_normal_form hK hq hτ hτ1 hy₂ hg₁ hz₁s hD h hζ
    exact ⟨g, hgd, Or.inl hgc⟩
  · have hζ' : y₁ * y₂⁻¹ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * y₂⁻¹ := by
      calc y₁ * y₂⁻¹ * y₁⁻¹ = (y₁ * y₂ * y₁⁻¹)⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) ζ * y₂)⁻¹ := by rw [hζ]
        _ = y₂⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
        _ = _ := by rw [hsc]
    have hτζ : ((ζ⁻¹ : Kˣ) : K) = τ := by
      rw [Units.val_inv_eq_inv_val, h]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hτ])
    obtain ⟨g, -, hgc, hgd⟩ :=
      exists_heis_normal_form hK hq hτ hτ1 (inv_mem hy₂) hg₁ hz₁s hD hτζ hζ'
    refine ⟨g, hgd, Or.inr ?_⟩
    calc g⁻¹ * y₂ * g = (g⁻¹ * y₂⁻¹ * g)⁻¹ := by group
      _ = cycThree⁻¹ := by rw [hgc]

theorem comap_invariant {W : Submodule K (Fin 3 → K)} (g : GL (Fin 3) K)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : ∀ v ∈ W, A *ᵥ v ∈ W) :
    ∀ v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)),
      (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (g : Matrix (Fin 3) (Fin 3) K)) *ᵥ
        v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
  intro v hv
  rw [Submodule.mem_comap, Matrix.toLin'_apply] at hv ⊢
  have h1 : ((g : Matrix (Fin 3) (Fin 3) K) *
      (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (g : Matrix (Fin 3) (Fin 3) K))) =
        A * (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
  exact hA _ hv

theorem invariant_of_comap {W : Submodule K (Fin 3 → K)} (g : GL (Fin 3) K)
    {B : Matrix (Fin 3) (Fin 3) K}
    (hB : ∀ v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)),
      B *ᵥ v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K))) :
    ∀ v ∈ W, ((g : Matrix (Fin 3) (Fin 3) K) * B *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ v ∈ W := by
  intro v hv
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈
      W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
    rw [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact hv
  have h2 := hB _ h1
  rw [Submodule.mem_comap, Matrix.toLin'_apply] at h2
  have h3 : ((g : Matrix (Fin 3) (Fin 3) K) * B *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ v =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (B *ᵥ
        (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h3]
  exact h2

theorem diag_of_commute_frame {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y₁ z g : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) (hD : g⁻¹ * (y₁ * z) * g = diagTau hτ)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : M * y₁ = y₁ * M) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M * g =
      diagonal fun i => (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M * g) i i := by
  apply eq_diagonal_of_commute hτ hτ1
  have hPQ : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYPD : ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g =
      g * diagonal ![τ, τ ^ 2, 1] := by
    rw [← coe_diagTau_eq_diagonal hτ, ← hD, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hMY : M * ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
    obtain ⟨u, rfl⟩ := hz
    have hsc : ∀ N : Matrix (Fin 3) (Fin 3) K,
        N * ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N :=
      fun N => by
        rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    rw [Units.val_mul, ← Matrix.mul_assoc, hM, Matrix.mul_assoc, hsc M, ← Matrix.mul_assoc]
  exact conj_commute hPQ hQP hYPD hMY

theorem frame_cycDiag {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y₁ y₂ z g s : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) (hD : g⁻¹ * (y₁ * z) * g = diagTau hτ)
    (hC : g⁻¹ * y₂ * g = cycThree ∨ g⁻¹ * y₂ * g = cycThree⁻¹)
    (hs : (s : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * s) (hsns : s ∉ StatedScalars (Fin 3) K) :
    ∃ a b c : K, ¬ (a = b ∧ b = c) ∧
      ((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (cycDiag a b c 0) ∧
      (((g⁻¹ * (y₂ * s * y₂⁻¹) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (cycDiag a b c 1) ∧
        ((g⁻¹ * (y₂⁻¹ * s * y₂) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (cycDiag a b c 2) ∨
        ((g⁻¹ * (y₂ * s * y₂⁻¹) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (cycDiag a b c 2) ∧
        ((g⁻¹ * (y₂⁻¹ * s * y₂) * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal (cycDiag a b c 1)) := by
  set S := ((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hSdef
  have hSd : S = diagonal fun i => S i i := by
    have h := diag_of_commute_frame hτ hτ1 hz hD hs
    simp only [hSdef, Units.val_mul]
    exact h
  have hS : S = diagonal ![S 0 0, S 1 1, S 2 2] := by
    rw [hSd]
    congr 1
    funext i
    fin_cases i <;> simp [diagonal]
  refine ⟨S 0 0, S 1 1, S 2 2, ?_, by rw [hS]; rfl, ?_⟩
  · rintro ⟨h01, h12⟩
    apply hsns
    have hSs : S = S 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hS, ← h01, ← h12, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [h01, h12]
    have h1 : ((g⁻¹ * s * g : GL (Fin 3) K)) ∈ StatedScalars (Fin 3) K := by
      refine mem_statedScalars_of_eq_smul hSs ?_
      intro h0
      have hdet := congrArg Matrix.det hSs
      rw [h0, zero_smul, det_zero] at hdet
      exact ((g⁻¹ * s * g).isUnit.map (Matrix.detMonoidHom)).ne_zero hdet
    have h2 := (inv_conj_mem_statedScalars_iff g s).mp h1
    exact h2
  · have e1 : g⁻¹ * (y₂ * s * y₂⁻¹) * g = (g⁻¹ * y₂ * g) * (g⁻¹ * s * g) * (g⁻¹ * y₂ * g)⁻¹ := by
      group
    have e2 : g⁻¹ * (y₂⁻¹ * s * y₂) * g = (g⁻¹ * y₂ * g)⁻¹ * (g⁻¹ * s * g) * (g⁻¹ * y₂ * g) := by
      group
    have hcS : ((cycThree * (g⁻¹ * s * g) * cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (cycDiag (S 0 0) (S 1 1) (S 2 2) 1) := by
      rw [Units.val_mul, Units.val_mul, ← hSdef, hS, cyc_mul_diagonal_mul_inv]
      rfl
    have hSc : ((cycThree⁻¹ * (g⁻¹ * s * g) * cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (cycDiag (S 0 0) (S 1 1) (S 2 2) 2) := by
      rw [Units.val_mul, Units.val_mul, ← hSdef, hS, cyc_inv_mul_diagonal_mul]
      rfl
    rcases hC with hC | hC
    · left
      rw [e1, e2, hC]
      exact ⟨hcS, hSc⟩
    · right
      rw [e1, e2, hC, inv_inv]
      exact ⟨hSc, hcS⟩

theorem inv_commute_of_inv_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ s : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y₁ 1) (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (hs : (s : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * s) (hsns : s ∉ StatedScalars (Fin 3) K)
    {W : Submodule K (Fin 3 → K)} (hW1 : ∀ v ∈ W, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W)
    (hW2 : ∀ v ∈ W, ((y₂ * s * y₂⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W)
    (hW3 : ∀ v ∈ W, ((y₂⁻¹ * s * y₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) :
    ∀ M : Matrix (Fin 3) (Fin 3) K, M * y₁ = y₁ * M → ∀ v ∈ W, M *ᵥ v ∈ W := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, hD, hC⟩ := exists_cyc_frame hK hq h1 hy₂ hζ1 hζ
  obtain ⟨a, b, c, habc, hS0, hS12⟩ := frame_cycDiag hτ hτ1 hz hD hC hs hsns
  have hval : ∀ A : GL (Fin 3) K, ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
        ((g⁻¹ * A * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun A => by
    simp only [Units.val_mul]
  have h0 := comap_invariant g hW1
  have h2 := comap_invariant g hW2
  have h3 := comap_invariant g hW3
  rw [hval] at h0 h2 h3
  have hcyc : ∀ t : Fin 3, ∀ v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)),
      diagonal (cycDiag a b c t) *ᵥ v ∈ W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
    intro t
    fin_cases t
    · show ∀ v ∈ _, diagonal (cycDiag a b c 0) *ᵥ v ∈ _
      rw [← hS0]
      exact h0
    · show ∀ v ∈ _, diagonal (cycDiag a b c 1) *ᵥ v ∈ _
      rcases hS12 with ⟨h, -⟩ | ⟨-, h⟩
      · rw [← h]
        exact h2
      · rw [← h]
        exact h3
    · show ∀ v ∈ _, diagonal (cycDiag a b c 2) *ᵥ v ∈ _
      rcases hS12 with ⟨-, h⟩ | ⟨h, -⟩
      · rw [← h]
        exact h3
      · rw [← h]
        exact h2
  intro M hM v hv
  have hMd := diag_of_commute_frame hτ hτ1 hz hD hM
  have hinv := invariant_of_comap g
    (diag_invariant_of_cyc habc hcyc fun i =>
      (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M * g) i i) v hv
  rw [← hMd] at hinv
  have hgM : (g : Matrix (Fin 3) (Fin 3) K) * (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      M * g) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = M := by
    have hPQ : (g : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [← Matrix.mul_assoc]
    rw [hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  rwa [hgM] at hinv

theorem eq_bot_or_eq_top_of_inv_commute (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y₁ 1) (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {W : Submodule K (Fin 3 → K)}
    (hall : ∀ M : Matrix (Fin 3) (Fin 3) K, M * y₁ = y₁ * M → ∀ v ∈ W, M *ᵥ v ∈ W)
    (hy : ∀ v ∈ W, (y₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, hD, hC⟩ := exists_cyc_frame hK hq h1 hy₂ hζ1 hζ
  have hPQ : (g : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set W₀ := W.comap (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) with hW₀
  have hd : ∀ d : Fin 3 → K, ∀ v ∈ W₀, diagonal d *ᵥ v ∈ W₀ := by
    intro d
    set M := (g : Matrix (Fin 3) (Fin 3) K) * diagonal d *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
    have hyz : ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← coe_diagTau_eq_diagonal hτ, ← hD]
      simp only [Units.val_mul]
      simp only [← Matrix.mul_assoc]
      rw [hPQ, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    have hcm : ∀ A B : Matrix (Fin 3) (Fin 3) K,
        ((g : Matrix (Fin 3) (Fin 3) K) * A * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
          ((g : Matrix (Fin 3) (Fin 3) K) * B *
            ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
        (g : Matrix (Fin 3) (Fin 3) K) * (A * B) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro A B
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), hQP,
        Matrix.one_mul]
    have hMyz : M * ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
      rw [hyz, hM, hcm, hcm, diagonal_mul_diagonal, diagonal_mul_diagonal]
      have hdc : (fun i => d i * ![τ, τ ^ 2, 1] i) = fun i => ![τ, τ ^ 2, 1] i * d i :=
        funext fun i => mul_comm _ _
      rw [hdc]
    have hMy : M * y₁ = y₁ * M := by
      obtain ⟨u, hu⟩ := hz
      have hsc : ∀ N : Matrix (Fin 3) (Fin 3) K, N * (z : Matrix (Fin 3) (Fin 3) K) =
          (z : Matrix (Fin 3) (Fin 3) K) * N := fun N => by
        rw [← hu, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul]
      have hzi : (z : Matrix (Fin 3) (Fin 3) K) * ((z⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hy1 : (y₁ : Matrix (Fin 3) (Fin 3) K) =
          ((y₁ * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((z⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by
        rw [Units.val_mul, Matrix.mul_assoc, hzi, Matrix.mul_one]
      have hszi : ∀ N : Matrix (Fin 3) (Fin 3) K, N * ((z⁻¹ : GL (Fin 3) K) : Matrix _ _ K) =
          ((z⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * N := fun N => by
        have hzm : z⁻¹ ∈ StatedScalars (Fin 3) K := inv_mem ⟨u, hu⟩
        obtain ⟨u', hu'⟩ := hzm
        rw [← hu', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul]
      rw [hy1, ← Matrix.mul_assoc, hMyz, Matrix.mul_assoc, hszi M, ← Matrix.mul_assoc]
    have h1 := comap_invariant g (hall M hMy)
    have hgM : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
        (g : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
      rw [hM]
      simp only [← Matrix.mul_assoc]
      rw [hQP, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
    rwa [hgM] at h1
  have hC0 := comap_invariant g hy
  have hc : ∀ v ∈ W₀, ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W₀ := by
    have hval : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (y₂ : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
          ((g⁻¹ * y₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      simp only [Units.val_mul]
    rw [hval] at hC0
    rcases hC with hC | hC
    · rw [hC] at hC0
      exact hC0
    · rw [hC] at hC0
      intro v hv
      have h2 := hC0 _ (hC0 v hv)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul] at h2
      have hc3 : (cycThree⁻¹ : GL (Fin 3) K) * cycThree⁻¹ = cycThree := by
        have h := cycThree_pow_three (K := K)
        calc (cycThree⁻¹ : GL (Fin 3) K) * cycThree⁻¹ =
            cycThree⁻¹ * cycThree⁻¹ * cycThree ^ 3 := by rw [h, mul_one]
          _ = cycThree := by group
      rwa [hc3] at h2
  rcases eq_bot_or_eq_top_of_diag_cyc hd hc with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W₀ := by
      rw [hW₀, Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPQ,
        Matrix.one_mulVec]
      exact hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    have h2 := congrArg (fun u => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h1
    simp only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ W₀ := by
      rw [h]
      exact Submodule.mem_top
    rw [hW₀, Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hPQ,
      Matrix.one_mulVec] at h1
    exact h1

theorem mem_scalars_of_commute_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ s : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y₁ 1) (hy₂ : y₂ ∈ slPi π 3 (p ^ f) K)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (hs : (s : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * s) (hsns : s ∉ StatedScalars (Fin 3) K)
    {t : GL (Fin 3) K} (ht1 : t * s = s * t) (ht2 : t * (y₂ * s * y₂⁻¹) = (y₂ * s * y₂⁻¹) * t)
    (ht3 : t * (y₂⁻¹ * s * y₂) = (y₂⁻¹ * s * y₂) * t) (ht4 : t * y₂ = y₂ * t) :
    t ∈ StatedScalars (Fin 3) K := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, hD, hC⟩ := exists_cyc_frame hK hq h1 hy₂ hζ1 hζ
  obtain ⟨a, b, c, habc, hS0, hS12⟩ := frame_cycDiag hτ hτ1 hz hD hC hs hsns
  set T := g⁻¹ * t * g with hT
  have hconj : ∀ A : GL (Fin 3) K, t * A = A * t → T * (g⁻¹ * A * g) = (g⁻¹ * A * g) * T := by
    intro A hA
    rw [hT]
    calc g⁻¹ * t * g * (g⁻¹ * A * g) = g⁻¹ * (t * A) * g := by group
      _ = g⁻¹ * (A * t) * g := by rw [hA]
      _ = g⁻¹ * A * g * (g⁻¹ * t * g) := by group
  have hm : ∀ A : GL (Fin 3) K, t * A = A * t →
      (T : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * A * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g⁻¹ * A * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * T := fun A hA => by
    rw [← Units.val_mul, ← Units.val_mul, hconj A hA]
  have hcyc : ∀ k : Fin 3, (T : Matrix (Fin 3) (Fin 3) K) * diagonal (cycDiag a b c k) =
      diagonal (cycDiag a b c k) * T := by
    intro k
    fin_cases k
    · show (T : Matrix (Fin 3) (Fin 3) K) * diagonal (cycDiag a b c 0) =
        diagonal (cycDiag a b c 0) * T
      rw [← hS0]
      exact hm s ht1
    · show (T : Matrix (Fin 3) (Fin 3) K) * diagonal (cycDiag a b c 1) =
        diagonal (cycDiag a b c 1) * T
      rcases hS12 with ⟨h, -⟩ | ⟨-, h⟩
      · rw [← h]
        exact hm _ ht2
      · rw [← h]
        exact hm _ ht3
    · show (T : Matrix (Fin 3) (Fin 3) K) * diagonal (cycDiag a b c 2) =
        diagonal (cycDiag a b c 2) * T
      rcases hS12 with ⟨-, h⟩ | ⟨h, -⟩
      · rw [← h]
        exact hm _ ht3
      · rw [← h]
        exact hm _ ht2
  have hTc : (T : Matrix (Fin 3) (Fin 3) K) * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * T := by
    have h4 := hm y₂ ht4
    rcases hC with hC | hC
    · rwa [hC] at h4
    · rw [hC] at h4
      have h5 : T * cycThree⁻¹ = cycThree⁻¹ * T := by
        rw [← Units.val_mul, ← Units.val_mul] at h4
        exact Units.ext h4
      have h6 : T * cycThree = cycThree * T := by
        calc T * cycThree = cycThree * (cycThree⁻¹ * T) * cycThree := by group
          _ = cycThree * (T * cycThree⁻¹) * cycThree := by rw [h5]
          _ = cycThree * T := by group
      rw [← Units.val_mul, ← Units.val_mul, h6]
  have hTs := eq_smul_one_of_commute_cyc hτ hτ1 habc hcyc hTc
  have hTsc : T ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_eq_smul hTs ?_
    intro h0
    have hdet := congrArg Matrix.det hTs
    rw [h0, zero_smul, det_zero] at hdet
    exact (T.isUnit.map (Matrix.detMonoidHom)).ne_zero hdet
  exact (inv_conj_mem_statedScalars_iff g t).mp hTsc

end Frame

end ProofKSL3Two

namespace ProofKSL3Two

open ProofHess

variable {K : Type} [Field K] {f : ℕ} {π : Bool}

theorem inv_conj_mem_of_conj_mem {M : Type*} [Group M] {H : Subgroup M} {x : M}
    (hx3 : x ^ 3 = 1) (hH : ∀ u ∈ H, x * u * x⁻¹ ∈ H) : ∀ u ∈ H, x⁻¹ * u * x ∈ H := by
  intro u hu
  have h1 := hH _ (hH u hu)
  have e : x * (x * u * x⁻¹) * x⁻¹ = x ^ 3 * (x⁻¹ * u * x) * (x ^ 3)⁻¹ := by
    rw [pow_three']
    group
  rw [hx3, one_mul, inv_one, mul_one] at e
  rw [← e]
  exact h1

theorem three_dvd_card_sup_model (hI : KSL3TwoIrrThree) (hK : PiField π 2 f K)
    (hq : ModThree π (2 ^ f)) (h9 : ¬ 9 ∣ Nat.card K - 1) {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : y₁ ∈ slPi π 3 (2 ^ f) K) (hy₂ : y₂ ∈ slPi π 3 (2 ^ f) K)
    (h₁3 : ProjGenLinGroup.mk y₁ ^ 3 = 1) (h₂3 : ProjGenLinGroup.mk y₂ ^ 3 = 1)
    (h₁1 : ProjGenLinGroup.mk y₁ ≠ 1)
    (hcomm : ProjGenLinGroup.mk y₁ * ProjGenLinGroup.mk y₂ =
      ProjGenLinGroup.mk y₂ * ProjGenLinGroup.mk y₁)
    (h₂ : ProjGenLinGroup.mk y₂ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₁))
    (h₁ : ProjGenLinGroup.mk y₁ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₂))
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) {U V : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hUS : U ≤ projImage (slPi π 3 (2 ^ f) K)) (hVS : V ≤ projImage (slPi π 3 (2 ^ f) K))
    (hUr : IsPGroup r U) (hVr : IsPGroup r V) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥)
    (hUc : ∀ u ∈ U, u * ProjGenLinGroup.mk y₁ = ProjGenLinGroup.mk y₁ * u)
    (hVc : ∀ v ∈ V, v * ProjGenLinGroup.mk y₂ = ProjGenLinGroup.mk y₂ * v)
    (hUn : ∀ u ∈ U, ProjGenLinGroup.mk y₂ * u * (ProjGenLinGroup.mk y₂)⁻¹ ∈ U)
    (hVn : ∀ v ∈ V, ProjGenLinGroup.mk y₁ * v * (ProjGenLinGroup.mk y₁)⁻¹ ∈ V) :
    3 ∣ Nat.card (U ⊔ V : Subgroup (ProjGenLinGroup (Fin 3) K)) := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  have : Fact r.Prime := ⟨hr⟩
  have h₂1 : ProjGenLinGroup.mk y₂ ≠ 1 := fun h => h₂ (h ▸ Subgroup.one_mem _)
  have hT1 := type1_of_lift hK hq h9 hy₁ h₁3 h₁1
  have hT2 := type1_of_lift hK hq h9 hy₂ h₂3 h₂1
  obtain ⟨ζ, hζ1, hζ⟩ := exists_heis_scalar hK hq h9 hy₁ hy₂ h₁3 h₂3 h₁1 hcomm h₂
  obtain ⟨ζ', hζ'1, hζ'⟩ := exists_heis_scalar hK hq h9 hy₂ hy₁ h₂3 h₁3 h₂1 hcomm.symm h₁
  have hmkc : ∀ a x : GL (Fin 3) K, ProjGenLinGroup.mk (a * x * a⁻¹) =
      ProjGenLinGroup.mk a * ProjGenLinGroup.mk x * (ProjGenLinGroup.mk a)⁻¹ := fun a x => by
    rw [map_mul, map_mul, map_inv]
  have hmkc' : ∀ a x : GL (Fin 3) K, ProjGenLinGroup.mk (a⁻¹ * x * a) =
      (ProjGenLinGroup.mk a)⁻¹ * ProjGenLinGroup.mk x * ProjGenLinGroup.mk a := fun a x => by
    rw [map_mul, map_mul, map_inv]
  have hUn' := inv_conj_mem_of_conj_mem h₂3 hUn
  have hVn' := inv_conj_mem_of_conj_mem h₁3 hVn
  have hcop : ∀ {X : Subgroup (ProjGenLinGroup (Fin 3) K)}, IsPGroup r X → ∀ x ∈ X,
      Nat.Coprime 3 (orderOf x) := by
    intro X hX x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3))
  obtain ⟨ub, hubU, hub1⟩ : ∃ ub ∈ U, ub ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨û, hûS, hûmk, hûo⟩ := exists_lift_pow_eq_one hK (hUS hubU) (hcop hUr ub hubU)
  have hû₁ : û * y₁ = y₁ * û := commute_of_mk_commute hK hûS hy₁
    (by rw [hûmk]; exact (hUc ub hubU).symm) (hcop hUr ub hubU).symm hûo
  have hû₁m : (û : Matrix (Fin 3) (Fin 3) K) * y₁ = y₁ * û := by
    rw [← Units.val_mul, ← Units.val_mul, hû₁]
  have hûns : û ∉ StatedScalars (Fin 3) K := fun h =>
    hub1 (by rw [← hûmk]; exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr h)
  obtain ⟨vb, hvbV, hvb1⟩ : ∃ vb ∈ V, vb ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨vh, hvhS, hvhmk, hvho⟩ := exists_lift_pow_eq_one hK (hVS hvbV) (hcop hVr vb hvbV)
  have hvh₂ : vh * y₂ = y₂ * vh := commute_of_mk_commute hK hvhS hy₂
    (by rw [hvhmk]; exact (hVc vb hvbV).symm) (hcop hVr vb hvbV).symm hvho
  have hvh₂m : (vh : Matrix (Fin 3) (Fin 3) K) * y₂ = y₂ * vh := by
    rw [← Units.val_mul, ← Units.val_mul, hvh₂]
  have hvhns : vh ∉ StatedScalars (Fin 3) K := fun h =>
    hvb1 (by rw [← hvhmk]; exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr h)
  by_contra h3
  set J := U ⊔ V with hJ
  have hJS : J ≤ projImage (slPi π 3 (2 ^ f) K) := sup_le hUS hVS
  set Y := J.subgroupOf (projImage (slPi π 3 (2 ^ f) K)) with hY
  have hYc : Nat.card Y = Nat.card J := Proof1617.card_subgroupOf_of_le hJS
  obtain ⟨Ĵ, -, e, he⟩ := exists_lift_model hK hq Y (by rw [hYc]; exact h3)
  have hĴc : Nat.card Ĵ = Nat.card J := by rw [Nat.card_congr e.toEquiv, hYc]
  have hlift : ∀ x ∈ J, ∃ a : Ĵ, ProjGenLinGroup.mk (a : GL (Fin 3) K) = x := by
    intro x hx
    refine ⟨e.symm ⟨⟨x, hJS hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩, ?_⟩
    rw [← he, MulEquiv.apply_symm_apply]
  have hinvS : ∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ Ĵ, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      ∀ s : GL (Fin 3) K, ProjGenLinGroup.mk s ∈ J →
        ∀ v ∈ W, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro W hW s hs v hv
    obtain ⟨a, ha⟩ := hlift _ hs
    have hsa : s * (a : GL (Fin 3) K)⁻¹ ∈ StatedScalars (Fin 3) K := by
      rw [← KFacts.mk_eq_one_iff_mem_statedScalars', map_mul, map_inv, ha, mul_inv_cancel]
    obtain ⟨c, hc⟩ := hsa
    have hs' : (s : Matrix (Fin 3) (Fin 3) K) =
        (c : K) • ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have h1 : s = GeneralLinearGroup.scalar (Fin 3) c * a := by rw [hc]; group
      rw [h1, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rw [hs', Matrix.smul_mulVec]
    exact W.smul_mem _ (hW _ a.2 v hv)
  have hUJ : ∀ s : GL (Fin 3) K, ProjGenLinGroup.mk s ∈ U → ProjGenLinGroup.mk s ∈ J :=
    fun s hs => Subgroup.mem_sup_left hs
  have hVJ : ∀ s : GL (Fin 3) K, ProjGenLinGroup.mk s ∈ V → ProjGenLinGroup.mk s ∈ J :=
    fun s hs => Subgroup.mem_sup_right hs
  have hû0 : ProjGenLinGroup.mk û ∈ U := by rw [hûmk]; exact hubU
  have hû1 : ProjGenLinGroup.mk (y₂ * û * y₂⁻¹) ∈ U := by rw [hmkc, hûmk]; exact hUn _ hubU
  have hû2 : ProjGenLinGroup.mk (y₂⁻¹ * û * y₂) ∈ U := by rw [hmkc', hûmk]; exact hUn' _ hubU
  have hvh0 : ProjGenLinGroup.mk vh ∈ V := by rw [hvhmk]; exact hvbV
  have hvh1 : ProjGenLinGroup.mk (y₁ * vh * y₁⁻¹) ∈ V := by rw [hmkc, hvhmk]; exact hVn _ hvbV
  have hvh2 : ProjGenLinGroup.mk (y₁⁻¹ * vh * y₁) ∈ V := by rw [hmkc', hvhmk]; exact hVn' _ hvbV
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ Ĵ, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hall₁ := inv_commute_of_inv_three hK hq hT1 hy₂ hζ1 hζ hû₁m hûns
      (hinvS W hW _ (hUJ _ hû0)) (hinvS W hW _ (hUJ _ hû1)) (hinvS W hW _ (hUJ _ hû2))
    have hall₂ := inv_commute_of_inv_three hK hq hT2 hy₁ hζ'1 hζ' hvh₂m hvhns
      (hinvS W hW _ (hVJ _ hvh0)) (hinvS W hW _ (hVJ _ hvh1)) (hinvS W hW _ (hVJ _ hvh2))
    exact eq_bot_or_eq_top_of_inv_commute hK hq hT1 hy₂ hζ1 hζ hall₁ (hall₂ _ rfl)
  have hna : ∃ a ∈ Ĵ, ∃ b ∈ Ĵ, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hJc : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := hlift x hx
      obtain ⟨b, rfl⟩ := hlift y hy
      rw [← map_mul, ← map_mul, hab a a.2 b b.2]
    have hcv : ∀ t : GL (Fin 3) K, ProjGenLinGroup.mk t ∈ U → t ∈ slPi π 3 (2 ^ f) K →
        vh * t = t * vh := by
      intro t ht htS
      refine commute_of_mk_commute hK hvhS htS ?_ (hcop hVr vb hvbV).symm hvho
      rw [hvhmk]
      exact hJc _ (hUJ _ ht) _ (Subgroup.mem_sup_right hvbV)
    have hS1 : y₂ * û * y₂⁻¹ ∈ slPi π 3 (2 ^ f) K := mul_mem (mul_mem hy₂ hûS) (inv_mem hy₂)
    have hS2 : y₂⁻¹ * û * y₂ ∈ slPi π 3 (2 ^ f) K := mul_mem (mul_mem (inv_mem hy₂) hûS) hy₂
    have hsc := mem_scalars_of_commute_three hK hq hT1 hy₂ hζ1 hζ hû₁m hûns
      (hcv _ hû0 hûS) (hcv _ hû1 hS1) (hcv _ hû2 hS2) hvh₂
    exact hvhns hsc
  exact h3 (hĴc ▸ hI K Ĵ hirr hna)

end ProofKSL3Two

open ProofKSL3Two ProofHess in
theorem kS1620Gen_of (hI : KSL3TwoIrrThree) : KS1620Gen := by
  intro X _ _ n hn hn3 hX D hD hD9 b hbD hb1 r hr hr3 U V hUr hVr hU1 hV1 hUb hVb hDU hDV w hwD
    hwb
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hn hX
  have h9K := not_nine_dvd_card_sub_one hK (not_two_pow_mod_nine hn3)
  set ψ : X →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (2 ^ n) K)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψS : ∀ x : X, ψ x ∈ projImage (slPi π 3 (2 ^ n) K) := fun x => (φ x).2
  set b' := w * b * w⁻¹ with hb'
  have hb'D : b' ∈ D := (Subgroup.mem_normalizer_iff.mp hwD b).mp hbD
  have hwD' : w⁻¹ ∈ Subgroup.normalizer (D : Set X) := inv_mem hwD
  obtain ⟨y₁, hy₁S, hy₁⟩ := (φ b).2
  obtain ⟨y₂, hy₂S, hy₂⟩ := (φ b').2
  have hψb : ψ b = ProjGenLinGroup.mk y₁ := hy₁.symm
  have hψb' : ψ b' = ProjGenLinGroup.mk y₂ := hy₂.symm
  have h₁3 : ProjGenLinGroup.mk y₁ ^ 3 = 1 := by rw [← hψb, ← map_pow, hD.2 b hbD, map_one]
  have h₂3 : ProjGenLinGroup.mk y₂ ^ 3 = 1 := by rw [← hψb', ← map_pow, hD.2 b' hb'D, map_one]
  have h₁1 : ProjGenLinGroup.mk y₁ ≠ 1 := by
    rw [← hψb]
    exact fun h => hb1 (hψinj (by rw [h, map_one]))
  have hbb' : b * b' = b' * b := congrArg Subtype.val (hD.1.is_comm.comm ⟨b, hbD⟩ ⟨b', hb'D⟩)
  have hcomm : ProjGenLinGroup.mk y₁ * ProjGenLinGroup.mk y₂ =
      ProjGenLinGroup.mk y₂ * ProjGenLinGroup.mk y₁ := by
    rw [← hψb, ← hψb', ← map_mul, ← map_mul, hbb']
  have hnot : ∀ x y : X, ProjGenLinGroup.mk y₁ = ψ x → ProjGenLinGroup.mk y₂ = ψ y →
      True := fun _ _ _ _ => trivial
  clear hnot
  have h₂ : ProjGenLinGroup.mk y₂ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₁) := by
    rintro ⟨k, hk⟩
    apply hwb
    refine ⟨k, hψinj ?_⟩
    simp only at hk ⊢
    rw [map_zpow, hψb, hψb', hk]
  have hb3 : Nat.card (Subgroup.zpowers b') = 3 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime (hD.2 b' hb'D) ?_
    intro h
    apply hb1
    have : w * b * w⁻¹ = 1 := h
    calc b = w⁻¹ * (w * b * w⁻¹) * w := by group
      _ = 1 := by rw [this]; group
  have h₁ : ProjGenLinGroup.mk y₁ ∉ Subgroup.zpowers (ProjGenLinGroup.mk y₂) := by
    rintro ⟨k, hk⟩
    have hbz : b ∈ Subgroup.zpowers b' := by
      refine ⟨k, hψinj ?_⟩
      simp only at hk ⊢
      rw [map_zpow, hψb, hψb', hk]
    have heq := Proof169.zpowers_eq_of_mem_of_ne_one hb3 hbz hb1
    apply hwb
    rw [heq]
    exact Subgroup.mem_zpowers b'
  set V' := V.map (MulAut.conj w).toMonoidHom with hV'
  have hV'r : IsPGroup r V' := hVr.map _
  have hV'1 : V' ≠ ⊥ := by
    rw [hV', Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj w).injective]
    exact hV1
  have hV'b : ∀ x ∈ V', x * b' = b' * x := by
    rintro _ ⟨v, hv, rfl⟩
    have hvb : v * b = b * v := Subgroup.mem_centralizer_singleton_iff.mp (hVb hv)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hb']
    calc w * v * w⁻¹ * (w * b * w⁻¹) = w * (v * b) * w⁻¹ := by group
      _ = w * (b * v) * w⁻¹ := by rw [hvb]
      _ = w * b * w⁻¹ * (w * v * w⁻¹) := by group
  have hV'n : ∀ x ∈ V', b * x * b⁻¹ ∈ V' := by
    rintro _ ⟨v, hv, rfl⟩
    have hd : w⁻¹ * b * w⁻¹⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hwD' b).mp hbD
    rw [inv_inv] at hd
    have h1 : (w⁻¹ * b * w) * v * (w⁻¹ * b * w)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hDV hd) v).mp hv
    refine ⟨(w⁻¹ * b * w) * v * (w⁻¹ * b * w)⁻¹, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set Ub := U.map ψ with hUbdef
  set Vb := V'.map ψ with hVbdef
  have hmapS : ∀ H : Subgroup X, H.map ψ ≤ projImage (slPi π 3 (2 ^ n) K) := by
    rintro H _ ⟨x, -, rfl⟩
    exact hψS x
  have hne : ∀ H : Subgroup X, H ≠ ⊥ → H.map ψ ≠ ⊥ := by
    intro H hH
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hψinj]
  have h3 := three_dvd_card_sup_model hI hK hq h9K hy₁S hy₂S h₁3 h₂3 h₁1 hcomm h₂ h₁ hr
    (by omega) (hmapS U) (hmapS V') (hUr.map ψ) (hV'r.map ψ) (hne U hU1) (hne V' hV'1)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← hψb, ← map_mul, ← map_mul,
        (Subgroup.mem_centralizer_singleton_iff.mp (hUb hx))])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← hψb', ← map_mul, ← map_mul, hV'b x hx])
    (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨b' * x * b'⁻¹, (Subgroup.mem_normalizer_iff.mp (hDU hb'D) x).mp hx, ?_⟩
      rw [← hψb', map_mul, map_mul, map_inv])
    (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨b * x * b⁻¹, hV'n x hx, ?_⟩
      rw [← hψb, map_mul, map_mul, map_inv])
  rwa [← Subgroup.map_sup, Subgroup.card_map_of_injective hψinj] at h3

end CFSG.RankThree.PartTwo.Sec16
