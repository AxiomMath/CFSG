module

public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Open (StatedSL)

@[expose] def GL3Excl : Prop :=
  ∀ (r p : ℕ) [Fact r.Prime], (r = 7 ∧ p = 3 ∨ r = 31 ∧ p = 5) →
    ∀ W H : Subgroup (GL (Fin 3) (ZMod r)), IsIrreducibleMatrixRep W.subtype → H ≤ W →
      IsStronglyPEmbedded p (H.subgroupOf W) → ¬ r ∣ Nat.card H →
      (∀ g ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single 0 1 ∈
        Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 3 → ZMod r)} → g ∈ H) →
      ∀ t₁ ∈ H, (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1] →
      ∀ t₂ ∈ H, (t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1] →
      ∀ y ∈ H, y ^ p = 1 → ∀ α : Fin 3 → ZMod r,
        (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α → (∃ i j, α i ≠ α j) → False

theorem diagonal_apply_eq_of_commute_irreducible {F : Type*} [Field F] {n : ℕ}
    {K : Subgroup (GL (Fin n) F)} (hK : IsIrreducibleMatrixRep K.subtype) {α : Fin n → F}
    (hα : ∀ k ∈ K, (k : Matrix (Fin n) (Fin n) F) * diagonal α = diagonal α * k) (i j : Fin n) :
    α i = α j := by
  let E : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.toLin' (diagonal α) - α i • LinearMap.id)
  have hmem : ∀ v, v ∈ E ↔ diagonal α *ᵥ v = α i • v := fun v => by
    simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hsingle : ∀ k, diagonal α *ᵥ Pi.single k (1 : F) = α k • Pi.single k 1 := fun k => by
    rw [diagonal_mulVec_single]
    ext m
    by_cases h : m = k
    · subst h
      simp
    · simp [h]
  have hinv : ∀ k : K, ∀ v ∈ E, (K.subtype k : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ E := by
    intro k v hv
    rw [hmem] at hv ⊢
    change diagonal α *ᵥ ((k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v =
      α i • ((k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v
    rw [mulVec_mulVec, ← hα k k.2, ← mulVec_mulVec, hv, mulVec_smul]
  rcases hK E hinv with hbot | htop
  · have hi : Pi.single i (1 : F) ∈ E := (hmem _).mpr (hsingle i)
    rw [hbot, Submodule.mem_bot] at hi
    exact absurd (congrFun hi i) (by simp)
  · have hj : Pi.single j (1 : F) ∈ E := by
      rw [htop]
      exact Submodule.mem_top
    rw [hmem, hsingle j] at hj
    have h := congrFun hj j
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
    exact h.symm

theorem dvd_card_of_statedSL_le {r : ℕ} [Fact r.Prime] {W H : Subgroup (GL (Fin 3) (ZMod r))}
    (hSL : StatedSL 3 (ZMod r) ≤ W)
    (hstab : ∀ g ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single 0 1 ∈
      Submodule.span (ZMod r) {(Pi.single 0 1 : Fin 3 → ZMod r)} → g ∈ H) :
    r ∣ Nat.card H := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin 3) (ZMod r),
      (u : Matrix (Fin 3) (Fin 3) (ZMod r)) = transvection 0 1 1 :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (transvection 0 1 1)
      (by rw [det_transvection_of_ne _ _ h01]; exact one_ne_zero), rfl⟩
  have hpow : ∀ k : ℕ, ((u ^ k : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) =
      transvection 0 1 (k : ZMod r) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, ih, hu, transvection_mul_transvection_same _ _ h01,
        Nat.cast_succ]
  have hur : u ^ r = 1 := by
    apply Units.ext
    rw [hpow, ZMod.natCast_self, transvection_zero, Units.val_one]
  have hu1 : u ≠ 1 := by
    intro h
    have h' := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r)) 0 1) h
    simp only [hu, Units.val_one, transvection, Matrix.add_apply, one_apply_ne h01,
      single_apply_same, zero_add] at h'
    exact one_ne_zero h'
  have huW : u ∈ W :=
    hSL (CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [hu, det_transvection_of_ne _ _ h01]))
  have hfix : (u : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [hu, transvection, add_mulVec, one_mulVec, single_mulVec, Pi.single_eq_of_ne h01.symm,
      mul_zero]
    funext m
    simp [Function.update_apply]
  have huH : u ∈ H := hstab u huW (by rw [hfix]; exact Submodule.mem_span_singleton_self _)
  have hdvd := Subgroup.orderOf_dvd_natCard H huH
  rwa [orderOf_eq_prime hur hu1] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
