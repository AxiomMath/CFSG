module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUComp

public section

namespace CFSG.StandardType

namespace CoordSU

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag SUTB NsFrameComp
  Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

@[expose] def Realizable (F : PieceFrame f n K h p A) (π : Equiv.Perm (Fin F.r))
    (η : Fin F.r → (ZMod p)ˣ) : Prop :=
  ∃ w : ↥(unitarySU 2 f K n), ∀ s : Fin F.r → ZMod p,
    w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun k => (η k : ZMod p) * s (π k))

@[expose] def pairTwist {r : ℕ} (c : (ZMod p)ˣ) (i j : Fin r) : Fin r → (ZMod p)ˣ :=
  fun k => if k = i then c else if k = j then c⁻¹ else 1

@[expose] def FrameSwapsTwists (F : PieceFrame f n K h p A) (u : (ZMod p)ˣ) : Prop :=
  (∀ i j : Fin F.r, i ≠ j → Realizable F (Equiv.swap i j) 1) ∧
    ∀ i j : Fin F.r, i ≠ j → Realizable F 1 (pairTwist u i j)

variable {F : PieceFrame f n K h p A}

theorem realizable_one : Realizable F 1 1 :=
  ⟨1, fun s => by simp⟩

theorem realizable_comp {π₁ π₂ : Equiv.Perm (Fin F.r)} {η₁ η₂ : Fin F.r → (ZMod p)ˣ}
    (h₁ : Realizable F π₁ η₁) (h₂ : Realizable F π₂ η₂) :
    Realizable F (π₁ * π₂) fun k => η₂ k * η₁ (π₂ k) := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  refine ⟨w₁ * w₂, fun s => ?_⟩
  have e1 : (w₁ * w₂)⁻¹ * F.ι (ofAdd s) * (w₁ * w₂) = w₂⁻¹ * (w₁⁻¹ * F.ι (ofAdd s) * w₁) * w₂ := by
    group
  rw [e1, hw₁, hw₂]
  congr 2
  funext k
  rw [Units.val_mul, mul_assoc, Equiv.Perm.mul_apply]

theorem realizable_perm (hsw : ∀ i j : Fin F.r, i ≠ j → Realizable F (Equiv.swap i j) 1)
    (π : Equiv.Perm (Fin F.r)) : Realizable F π 1 := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact realizable_one
  | swap_mul g x y hxy ih =>
    have h1 := realizable_comp (hsw x y hxy) ih
    have h2 : (fun k => (1 : Fin F.r → (ZMod p)ˣ) k * (1 : Fin F.r → (ZMod p)ˣ) (g k)) = 1 := by
      funext k
      simp
    rwa [h2] at h1

theorem realizable_diag_mul {η₁ η₂ : Fin F.r → (ZMod p)ˣ} (h₁ : Realizable F 1 η₁)
    (h₂ : Realizable F 1 η₂) : Realizable F 1 (η₂ * η₁) := by
  have h := realizable_comp h₁ h₂
  rwa [one_mul] at h

theorem pairTwist_pow_succ {r : ℕ} (c : (ZMod p)ˣ) (i j : Fin r) (m : ℕ) :
    pairTwist (c ^ (m + 1)) i j = pairTwist c i j * pairTwist (c ^ m) i j := by
  funext k
  simp only [pairTwist, Pi.mul_apply]
  by_cases hki : k = i
  · simp only [hki, ↓reduceIte, pow_succ']
  · by_cases hkj : k = j
    · subst hkj
      simp only [hki, ↓reduceIte]
      rw [pow_succ', mul_inv_rev, mul_comm]
    · simp only [hki, hkj, ↓reduceIte, one_mul]

theorem realizable_pairTwist_pow {u : (ZMod p)ˣ} {i j : Fin F.r}
    (htw : Realizable F 1 (pairTwist u i j)) (m : ℕ) : Realizable F 1 (pairTwist (u ^ m) i j) := by
  induction m with
  | zero =>
    have h1 : pairTwist (u ^ 0) i j = 1 := by
      funext k
      simp [pairTwist]
    rw [h1]
    exact realizable_one
  | succ m ih =>
    rw [pairTwist_pow_succ u i j m]
    exact realizable_diag_mul ih htw

theorem realizable_diag {u : (ZMod p)ˣ} {O : Subgroup (ZMod p)ˣ} (hu : ∀ c ∈ O, ∃ m : ℕ, c = u ^ m)
    (htw : ∀ i j : Fin F.r, i ≠ j → Realizable F 1 (pairTwist u i j)) (η : Fin F.r → (ZMod p)ˣ)
    (hη : ∀ k, η k ∈ O) (hprod : ∏ k, η k = 1) : Realizable F 1 η := by
  classical
  rcases Nat.eq_zero_or_pos F.r with hr | hr
  · have h1 : η = 1 := funext fun k => absurd k.2 (by omega)
    rw [h1]
    exact realizable_one
  set k₀ : Fin F.r := ⟨0, hr⟩
  have hpair : ∀ k, k ≠ k₀ → Realizable F 1 (pairTwist (η k) k k₀) := by
    intro k hk
    obtain ⟨m, hm⟩ := hu _ (hη k)
    rw [hm]
    exact realizable_pairTwist_pow (htw k k₀ hk) m
  have hfin : ∀ s : Finset (Fin F.r), k₀ ∉ s →
      Realizable F 1 (∏ k ∈ s, pairTwist (η k) k k₀) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; rw [Finset.prod_empty]; exact realizable_one
    | insert a s has ih =>
      intro hs
      rw [Finset.prod_insert has]
      exact realizable_diag_mul (ih fun h' => hs (Finset.mem_insert_of_mem h'))
        (hpair a fun h' => hs (h' ▸ Finset.mem_insert_self a s))
  have heq : η = ∏ k ∈ Finset.univ.erase k₀, pairTwist (η k) k k₀ := by
    funext j
    rw [Finset.prod_apply]
    by_cases hj : j = k₀
    · have h1 : ∀ k ∈ Finset.univ.erase k₀, pairTwist (η k) k k₀ j = (η k)⁻¹ := by
        intro k hk
        have hk0 : k ≠ k₀ := Finset.ne_of_mem_erase hk
        simp [pairTwist, hj, Ne.symm hk0]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib, hj]
      have h2 := Finset.mul_prod_erase Finset.univ η (Finset.mem_univ k₀)
      rw [hprod] at h2
      exact eq_inv_of_mul_eq_one_left h2
    · have h1 : ∀ k ∈ Finset.univ.erase k₀, pairTwist (η k) k k₀ j = if j = k then η k else 1 := by
        intro k _
        simp only [pairTwist, hj, ↓reduceIte]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      simp [hj]
  rw [heq]
  exact hfin _ (Finset.notMem_erase k₀ _)

theorem frameMoves_of_swapsTwists {u : (ZMod p)ˣ}
    (hu : ∀ c ∈ negQ p (2 ^ f), ∃ m : ℕ, c = u ^ m) (hst : FrameSwapsTwists F u) :
    FrameMoves F := by
  intro π η hη hprod
  have hd := realizable_diag hu hst.2 (fun k => η (π.symm k)) (fun k => hη _)
    (by rw [Equiv.prod_comp π.symm η]; exact hprod)
  obtain ⟨w, hw⟩ := realizable_comp hd (realizable_perm hst.1 π)
  refine ⟨w, fun s => ?_⟩
  rw [hw s]
  congr 2
  funext k
  simp

end CoordSU

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open SUTB NsFrameComp

theorem CoordSU.exists_pow_of_mem_negQ {p q : ℕ} [NeZero p] {u : (ZMod p)ˣ}
    (hu : (u : ZMod p) = -(q : ZMod p)) {c : (ZMod p)ˣ} (hc : c ∈ CoordSU.negQ p q) :
    ∃ m : ℕ, c = u ^ m := by
  have hset : {v : (ZMod p)ˣ | (v : ZMod p) = -(q : ZMod p)} = {u} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hv
      exact Units.ext (hv.trans hu.symm)
    · rintro rfl
      exact hu
  unfold CoordSU.negQ at hc
  rw [hset, ← Subgroup.zpowers_eq_closure] at hc
  obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr hc
  exact ⟨m, hm.symm⟩

@[expose] def GGSUPieceSwapInput : Prop :=
  ∀ (f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (p : ℕ)
    (A : Subgroup ↥(unitarySU 2 f K n)), MaxElemAb p A →
      ∃ F : PieceFrame f n K h p A, ∀ u : (ZMod p)ˣ, (u : ZMod p) = -((2 ^ f : ℕ) : ZMod p) →
        CoordSU.FrameSwapsTwists F u

theorem ggSUPieceMoveInput_of_swap (hswap : GGSUPieceSwapInput) : GGSUPieceMoveInput := by
  intro f n K _ hK p A hA
  obtain ⟨F, hF⟩ := hswap f n K hK p A hA
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  set u₀ : (ZMod p)ˣ := -ZMod.unitOfCoprime (2 ^ f) (CoordSU.coprime_two_pow hp hA.ne_two f)
    with hu₀
  have hu₀v : (u₀ : ZMod p) = -((2 ^ f : ℕ) : ZMod p) := by simp [hu₀]
  exact ⟨F, CoordSU.frameMoves_of_swapsTwists
    (fun c hc => CoordSU.exists_pow_of_mem_negQ hu₀v hc) (hF u₀ hu₀v)⟩

section Model

theorem ggStepTwoCoordModelOn_PSU_of_swap_shape (hswap : GGSUPieceSwapInput)
    (hshape : GGSUPieceShapeInput) : GGStepTwoCoordModelOn .PSU :=
  ggStepTwoCoordModelOn_PSU_of_move_shape (ggSUPieceMoveInput_of_swap hswap) hshape

end Model

end CFSG.StandardType
