module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Field

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

noncomputable section

def s16kTheta : (Fin 6 → ZMod 2) →+ (Fin 3 → S16kF4) where
  toFun v i := s16kEmb (v ⟨2 * i.val, by omega⟩) + s16kAlpha * s16kEmb (v ⟨2 * i.val + 1, by omega⟩)
  map_zero' := by
    ext i
    simp
  map_add' := by
    intro v w
    ext i
    simp only [Pi.add_apply, map_add]
    ring

private def s16k_even (i : Fin 3) : Fin 6 := ⟨2 * i.val, by omega⟩

private def s16k_odd (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by omega⟩

private lemma s16kTheta_apply (v : Fin 6 → ZMod 2) (i : Fin 3) :
    s16kTheta v i = s16kEmb (v (s16k_even i)) + s16kAlpha * s16kEmb (v (s16k_odd i)) := rfl

private lemma s16kAlpha_sq : s16kAlpha ^ 2 = s16kAlpha + 1 := by
  have h := s16kAlpha_spec
  rw [add_assoc] at h
  exact (CharTwo.add_eq_zero (R := S16kF4)).mp h

private lemma s16k_alpha_ne_zero : s16kAlpha ≠ 0 := by
  intro h
  have hs := s16kAlpha_spec
  rw [h] at hs
  exact (one_ne_zero : (1 : S16kF4) ≠ 0) (by simpa using hs)

private lemma s16k_one_add_alpha_ne_zero : 1 + s16kAlpha ≠ 0 := by
  intro h
  have h2 : (2 : S16kF4) = 0 := CharTwo.two_eq_zero
  have hα : s16kAlpha = 1 := ((CharTwo.add_eq_zero (R := S16kF4)).mp h).symm
  have hs := s16kAlpha_spec
  rw [hα] at hs
  have h1 : (1 : S16kF4) = 0 := by linear_combination hs - h2
  exact (one_ne_zero : (1 : S16kF4) ≠ 0) h1

private lemma s16k_zmod_two_eq (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private lemma s16k_emb_add_alpha_eq_zero {a b : ZMod 2}
    (h : s16kEmb a + s16kAlpha * s16kEmb b = 0) : a = 0 ∧ b = 0 := by
  have ha : a = 0 ∨ a = 1 := s16k_zmod_two_eq a
  have hb : b = 0 ∨ b = 1 := s16k_zmod_two_eq b
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact absurd (by simpa [map_zero, map_one, mul_one] using h) s16k_alpha_ne_zero
  · exact absurd (by simpa using h) (one_ne_zero : (1 : S16kF4) ≠ 0)
  · exact absurd (by simpa [map_one, mul_one] using h) s16k_one_add_alpha_ne_zero

private lemma s16k_fin6_cases (n : Fin 6) :
    (∃ i : Fin 3, n = s16k_even i) ∨ (∃ i : Fin 3, n = s16k_odd i) := by
  fin_cases n
  · exact Or.inl ⟨0, by decide⟩
  · exact Or.inr ⟨0, by decide⟩
  · exact Or.inl ⟨1, by decide⟩
  · exact Or.inr ⟨1, by decide⟩
  · exact Or.inl ⟨2, by decide⟩
  · exact Or.inr ⟨2, by decide⟩

private lemma s16k_mulVec_apply (i : Fin 3) (v : Fin 6 → ZMod 2) (r : Fin 6) :
    (s16kBlockMat i).mulVec v r =
      if r.val / 2 = i.val then
        (if r.val % 2 = 0 then v (s16k_odd i) else v (s16k_even i) + v (s16k_odd i))
      else v r := by
  rw [Matrix.mulVec_apply_eq_sum]
  fin_cases i <;> fin_cases r <;>
    simp only [s16kBlockMat, Matrix.of_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.val_zero, Fin.val_succ, Fin.val_one] <;>
    norm_num [s16k_even, s16k_odd]

private lemma s16kTheta_alpha_action (x y : ZMod 2) :
    s16kEmb y + s16kAlpha * (s16kEmb x + s16kEmb y) =
      s16kAlpha * (s16kEmb x + s16kAlpha * s16kEmb y) := by
  have hα : s16kAlpha ^ 2 = s16kAlpha + 1 := s16kAlpha_sq
  have h1 : s16kAlpha * (s16kAlpha * s16kEmb y) = s16kAlpha ^ 2 * s16kEmb y := by
    rw [← mul_assoc, ← pow_two]
  simp only [mul_add, add_mul, one_mul]
  rw [h1, hα]
  ring

theorem s16kTheta_bijective : Function.Bijective s16kTheta := by
  have hker : ∀ v : Fin 6 → ZMod 2, s16kTheta v = 0 → v = 0 := by
    intro v hv
    funext k
    rcases s16k_fin6_cases k with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨h1, _⟩ := s16k_emb_add_alpha_eq_zero (a := v (s16k_even i))
        (b := v (s16k_odd i)) (by
          have h := congrFun hv i
          rwa [s16kTheta_apply, Pi.zero_apply] at h)
      exact h1
    · obtain ⟨_, h2⟩ := s16k_emb_add_alpha_eq_zero (a := v (s16k_even i))
        (b := v (s16k_odd i)) (by
          have h := congrFun hv i
          rwa [s16kTheta_apply, Pi.zero_apply] at h)
      exact h2
  have hinj : Function.Injective s16kTheta := by
    intro v w hvw
    have h0 : s16kTheta (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker (v - w) h0)
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_pi, Nat.card_pi]
  simp [GaloisField.card 2 2 (by norm_num), ZMod.card]

theorem s16kTheta_block (i : Fin 3) (v : Fin 6 → ZMod 2) :
    s16kTheta ((s16kBlockMat i).mulVec v) =
      Function.update (s16kTheta v) i (s16kAlpha * s16kTheta v i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [s16kTheta_apply, s16k_mulVec_apply, Function.update_apply, s16k_even,
      s16k_odd] <;>
    norm_num <;>
    first
      | exact s16kTheta_alpha_action _ _
      | rfl

abbrev s16kOmegaBlk : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2

theorem s16kTheta_omega (v : Fin 6 → ZMod 2) :
    s16kTheta (s16kOmegaBlk.mulVec v) = s16kAlpha • s16kTheta v := by
  rw [s16kOmegaBlk, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    s16kTheta_block, s16kTheta_block, s16kTheta_block]
  ext i
  fin_cases i <;> simp [Function.update, Pi.smul_apply, smul_eq_mul]

private noncomputable def s16k_omegaUnit : S16kGL6 where
  val := s16kOmegaBlk
  inv := s16kOmegaBlk * s16kOmegaBlk
  val_inv := by decide
  inv_val := by decide

private lemma s16k_omegaUnit_val :
    ((s16k_omegaUnit : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kOmegaBlk := rfl

theorem s16k_centralizer_scal_iff (g : S16kGL6) :
    g ∈ Subgroup.centralizer (s16kScal : Set S16kGL6) ↔
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaBlk =
        s16kOmegaBlk * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  constructor
  · intro hg
    have hω : s16k_omegaUnit ∈ s16kScal := Subgroup.subset_closure rfl
    have hcomm := (Subgroup.mem_centralizer_iff.mp hg) s16k_omegaUnit hω
    have hmat := congrArg (fun u : S16kGL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hcomm
    simp only [Units.val_mul, s16k_omegaUnit_val] at hmat
    exact hmat.symm
  · intro hm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [s16kScal] at hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_setOf_eq] at hy
        apply Units.ext
        simp only [Units.val_mul, hy]
        exact hm.symm
    | one => group
    | mul a b ha hb iha ihb =>
        calc (a * b) * g = a * (b * g) := by group
          _ = a * (g * b) := by rw [ihb]
          _ = (a * g) * b := by group
          _ = (g * a) * b := by rw [iha]
          _ = g * (a * b) := by group
    | inv a ha iha =>
        have h1 : g * a⁻¹ = a⁻¹ * g := by
          calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
            _ = a⁻¹ * (g * a) * a⁻¹ := by rw [iha]
            _ = a⁻¹ * g := by group
        exact h1.symm

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
