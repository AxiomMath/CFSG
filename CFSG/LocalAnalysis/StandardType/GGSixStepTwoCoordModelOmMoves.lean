module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMain

public section

namespace CFSG.StandardType

namespace CoordOm

open Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

section Realized

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

@[expose] def RealizedIn (F : SevOm.Frame Q p A r) (H : Subgroup (V ≃ₗ[K] V))
    (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ) : Prop :=
  ∃ w ∈ H ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)), ∀ s : Fin r → ZMod p,
    w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun k => (η k : ZMod p) * s (π k))

variable {F : SevOm.Frame Q p A r} {H : Subgroup (V ≃ₗ[K] V)}

theorem realizedIn_one : RealizedIn F H 1 1 :=
  ⟨1, Subgroup.mem_inf.mpr ⟨H.one_mem, Subgroup.one_mem _⟩, fun s => by simp⟩

theorem realizedIn_comp {π₁ π₂ : Equiv.Perm (Fin r)} {η₁ η₂ : Fin r → (ZMod p)ˣ}
    (h₁ : RealizedIn F H π₁ η₁) (h₂ : RealizedIn F H π₂ η₂) :
    RealizedIn F H (π₁ * π₂) fun k => η₂ k * η₁ (π₂ k) := by
  obtain ⟨w₁, hw₁, hs₁⟩ := h₁
  obtain ⟨w₂, hw₂, hs₂⟩ := h₂
  refine ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, fun s => ?_⟩
  have e1 : (w₁ * w₂)⁻¹ * F.ι (ofAdd s) * (w₁ * w₂) =
      w₂⁻¹ * (w₁⁻¹ * F.ι (ofAdd s) * w₁) * w₂ := by group
  rw [e1, hs₁, hs₂]
  congr 2
  funext k
  rw [Units.val_mul, mul_assoc, Equiv.Perm.mul_apply]

theorem realizedIn_inv_diag {η : Fin r → (ZMod p)ˣ} (h : RealizedIn F H 1 η) :
    RealizedIn F H 1 η⁻¹ := by
  obtain ⟨w, hw, hs⟩ := h
  refine ⟨w⁻¹, Subgroup.inv_mem _ hw, fun s => ?_⟩
  have h1 := hs fun k => (↑(η k)⁻¹ : ZMod p) * s k
  have h3 : w⁻¹ * F.ι (ofAdd fun k => (↑(η k)⁻¹ : ZMod p) * s k) * w = F.ι (ofAdd s) := by
    rw [h1]
    congr 2
    funext k
    rw [Equiv.Perm.one_apply, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]
  have h4 : F.ι (ofAdd fun k => (↑(η k)⁻¹ : ZMod p) * s k) = w * F.ι (ofAdd s) * w⁻¹ := by
    rw [← h3]
    group
  rw [inv_inv, ← h4]
  rfl

theorem realizedIn_perm (hsw : ∀ i j : Fin r, i ≠ j → RealizedIn F H (Equiv.swap i j) 1)
    (π : Equiv.Perm (Fin r)) : RealizedIn F H π 1 := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => exact realizedIn_one
  | swap_mul g x y hxy ih =>
    have h1 := realizedIn_comp (hsw x y hxy) ih
    have h2 : (fun k => (1 : Fin r → (ZMod p)ˣ) k * (1 : Fin r → (ZMod p)ˣ) (g k)) = 1 := by
      funext k
      simp
    rwa [h2] at h1

theorem realizedIn_diag_mul {η₁ η₂ : Fin r → (ZMod p)ˣ} (h₁ : RealizedIn F H 1 η₁)
    (h₂ : RealizedIn F H 1 η₂) : RealizedIn F H 1 (η₂ * η₁) := by
  have h := realizedIn_comp h₁ h₂
  rwa [one_mul] at h

end Realized

section Twists

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
  {F : SevOm.Frame Q p A r}

@[expose] def singleTw {r : ℕ} (u : (ZMod p)ˣ) (i : Fin r) : Fin r → (ZMod p)ˣ :=
  fun k => if k = i then u else 1

@[expose] def pairTw {r : ℕ} (u : (ZMod p)ˣ) (i j : Fin r) : Fin r → (ZMod p)ˣ :=
  fun k => (if k = i then u else 1) * (if k = j then u⁻¹ else 1)

theorem pairTw_one {r : ℕ} (i j : Fin r) : pairTw (1 : (ZMod p)ˣ) i j = 1 := by
  funext k
  simp [pairTw]

theorem pairTw_mul {r : ℕ} (u v : (ZMod p)ˣ) (i j : Fin r) :
    pairTw (u * v) i j = pairTw u i j * pairTw v i j := by
  funext k
  simp only [pairTw, Pi.mul_apply]
  split_ifs
  · rw [mul_inv_cancel, mul_inv_cancel, mul_inv_cancel, mul_one]
  · simp
  · simp only [one_mul, mul_inv_rev]
    exact mul_comm _ _
  · simp

theorem pairTw_inv {r : ℕ} (u : (ZMod p)ˣ) (i j : Fin r) :
    pairTw u⁻¹ i j = (pairTw u i j)⁻¹ := by
  funext k
  simp only [pairTw, Pi.inv_apply]
  split_ifs <;> simp

theorem realizedIn_pairTw {i j : Fin r} (hij : i ≠ j) {u : (ZMod p)ˣ}
    (hw : RealizedIn F (orthDerived Q) (Equiv.swap i j) 1)
    (hg : RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1 (singleTw u i)) :
    RealizedIn F (orthDerived Q) 1 (pairTw u i j) := by
  classical
  obtain ⟨w, hw, hws⟩ := hw
  obtain ⟨g, hg, hgs⟩ := hg
  obtain ⟨hwΩ, hwN⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨hgO, hgN⟩ := Subgroup.mem_inf.mp hg
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hwΩ
  have e1 : ∀ s : Fin r → ZMod p, w * F.ι (ofAdd s) * w⁻¹ =
      F.ι (ofAdd fun k => s (Equiv.swap i j k)) := by
    intro s
    have h1 := hws fun k => s (Equiv.swap i j k)
    simp only [Pi.one_apply, Units.val_one, one_mul, Equiv.swap_apply_self] at h1
    rw [← h1]
    group
  have e2 : ∀ s : Fin r → ZMod p, g * F.ι (ofAdd s) * g⁻¹ =
      F.ι (ofAdd fun k => (↑(singleTw u i k)⁻¹ : ZMod p) * s k) := by
    intro s
    have h1 := hgs fun k => (↑(singleTw u i k)⁻¹ : ZMod p) * s k
    simp only [Equiv.Perm.one_apply] at h1
    have h2 : (fun k => (singleTw u i k : ZMod p) * ((↑(singleTw u i k)⁻¹ : ZMod p) * s k)) =
        s := by
      funext k
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [h2] at h1
    rw [← h1]
    group
  refine ⟨g * w⁻¹ * g⁻¹ * w, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, fun s => ?_⟩
  · have : g * w⁻¹ * g⁻¹ * w = ⁅g, w⁻¹⁆ := by rw [commutatorElement_def, inv_inv]
    rw [this]
    exact Subgroup.commutator_mem_commutator hgO (Subgroup.inv_mem _ hwO)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN
      (Subgroup.inv_mem _ hwN)) (Subgroup.inv_mem _ hgN)) hwN
  · have e : (g * w⁻¹ * g⁻¹ * w)⁻¹ * F.ι (ofAdd s) * (g * w⁻¹ * g⁻¹ * w) =
        w⁻¹ * (g * (w * (g⁻¹ * F.ι (ofAdd s) * g) * w⁻¹) * g⁻¹) * w := by group
    rw [e, hgs, e1, e2, hws]
    congr 2
    funext k
    simp only [Equiv.Perm.one_apply, Pi.one_apply, Units.val_one, one_mul, Equiv.swap_apply_self]
    simp only [singleTw, pairTw, Units.val_mul]
    by_cases hki : k = i
    · rw [hki]
      simp [hij, Ne.symm hij, Equiv.swap_apply_left]
    · by_cases hkj : k = j
      · rw [hkj]
        simp [Ne.symm hij, Equiv.swap_apply_right]
      · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

end Twists

section Generation

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
  {F : SevOm.Frame Q p A r}

theorem realizedIn_diag {O : Subgroup (ZMod p)ˣ} {H : Subgroup (V ≃ₗ[K] V)} (k₀ : Fin r)
    (htw : ∀ c ∈ O, ∀ k, k ≠ k₀ → RealizedIn F H 1 (pairTw c k k₀))
    (η : Fin r → (ZMod p)ˣ) (hη : ∀ k, η k ∈ O) (hprod : ∏ k, η k = 1) :
    RealizedIn F H 1 η := by
  classical
  have hfin : ∀ s : Finset (Fin r), k₀ ∉ s →
      RealizedIn F H 1 (∏ k ∈ s, pairTw (η k) k k₀) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; rw [Finset.prod_empty]; exact realizedIn_one
    | insert a s has ih =>
      intro hs
      rw [Finset.prod_insert has]
      exact realizedIn_diag_mul (ih fun h' => hs (Finset.mem_insert_of_mem h'))
        (htw _ (hη a) a fun h' => hs (h' ▸ Finset.mem_insert_self a s))
  have heq : η = ∏ k ∈ Finset.univ.erase k₀, pairTw (η k) k k₀ := by
    funext j
    rw [Finset.prod_apply]
    by_cases hj : j = k₀
    · have h1 : ∀ k ∈ Finset.univ.erase k₀, pairTw (η k) k k₀ j = (η k)⁻¹ := by
        intro k hk
        have hk0 : k ≠ k₀ := Finset.ne_of_mem_erase hk
        simp [pairTw, hj, Ne.symm hk0]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib, hj]
      have h2 := Finset.mul_prod_erase Finset.univ η (Finset.mem_univ k₀)
      rw [hprod] at h2
      exact eq_inv_of_mul_eq_one_left h2
    · have h1 : ∀ k ∈ Finset.univ.erase k₀, pairTw (η k) k k₀ j = if j = k then η k else 1 := by
        intro k _
        simp only [pairTw, hj, ↓reduceIte, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      simp [hj]
  rw [heq]
  exact hfin _ (Finset.notMem_erase k₀ _)

theorem frameMoves_of_elem (F : SevOm.Frame Q p A r)
    (hsw : ∀ i j : Fin r, i ≠ j → RealizedIn F (orthDerived Q) (Equiv.swap i j) 1)
    (htw : ∀ (i : Fin r) (u : (ZMod p)ˣ), ((u : ZMod p) = Nat.card K ∨ (u : ZMod p) = -1) →
      RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1 (singleTw u i)) :
    FrameMoves F (CoordSpNs.galSigns p (Nat.card K)) := by
  classical
  intro π η hη hprod
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, fun s => ?_⟩
    have : (fun i : Fin 0 => (η i : ZMod p) * s (π i)) = s := funext fun i => i.elim0
    rw [this]
    group
  set k₀ : Fin r := ⟨0, hr⟩
  have hpair : ∀ c ∈ CoordSpNs.galSigns p (Nat.card K), ∀ k, k ≠ k₀ →
      RealizedIn F (orthDerived Q) 1 (pairTw c k k₀) := by
    intro c hc k hk
    let S : Subgroup (ZMod p)ˣ :=
      { carrier := {c | RealizedIn F (orthDerived Q) 1 (pairTw c k k₀)}
        mul_mem' := fun {a b} ha hb => by
          show RealizedIn F (orthDerived Q) 1 (pairTw (a * b) k k₀)
          rw [mul_comm, pairTw_mul]
          exact realizedIn_diag_mul ha hb
        one_mem' := by
          show RealizedIn F (orthDerived Q) 1 (pairTw 1 k k₀)
          rw [pairTw_one]
          exact realizedIn_one
        inv_mem' := fun {a} ha => by
          show RealizedIn F (orthDerived Q) 1 (pairTw a⁻¹ k k₀)
          rw [pairTw_inv]
          exact realizedIn_inv_diag ha }
    have hle : CoordSpNs.galSigns p (Nat.card K) ≤ S :=
      (Subgroup.closure_le S).mpr fun u hu => realizedIn_pairTw hk (hsw k k₀ hk) (htw k u hu)
    exact hle hc
  have hd := realizedIn_diag k₀ hpair (fun k => η (π.symm k)) (fun k => hη _)
    (by rw [Equiv.prod_comp π.symm η]; exact hprod)
  obtain ⟨w, hw, hws⟩ := realizedIn_comp hd (realizedIn_perm hsw π)
  refine ⟨w, hw, fun s => ?_⟩
  rw [hws s]
  congr 2
  funext k
  simp

end Generation

end CoordOm

open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def GGOmFrameElemMoveInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ Q : QuadraticForm K V, (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) →
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ orthDerived Q → (∀ a ∈ A, a ^ p = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) →
      ∃ (r : ℕ) (F : SevOm.Frame Q p A r),
        (∀ i j : Fin r, i ≠ j → CoordOm.RealizedIn F (orthDerived Q) (Equiv.swap i j) 1) ∧
        ∀ (i : Fin r) (u : (ZMod p)ˣ), ((u : ZMod p) = Nat.card K ∨ (u : ZMod p) = -1) →
          CoordOm.RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1 (CoordOm.singleTw u i)

theorem ggOmFrameMoveInput_of_elem (h : GGOmFrameElemMoveInput) : GGOmFrameMoveInput := by
  intro K _ _ _ V _ _ _ p _ hp2 Q hQ hT A hAΩ hApow hAcomm hmax
  obtain ⟨r, F, hsw, htw⟩ := h K V p hp2 Q hQ hT A hAΩ hApow hAcomm hmax
  exact ⟨r, F, CoordOm.frameMoves_of_elem F hsw htw⟩

section Certified

theorem ggStepTwoCoordModelOn_POmegaPlus_of_elem (h : GGOmFrameElemMoveInput) :
    GGStepTwoCoordModelOn .POmegaPlus :=
  ggStepTwoCoordModelOn_POmegaPlus_of_move (ggOmFrameMoveInput_of_elem h)

theorem ggStepTwoCoordModelOn_POmegaMinus_of_elem (h : GGOmFrameElemMoveInput) :
    GGStepTwoCoordModelOn .POmegaMinus :=
  ggStepTwoCoordModelOn_POmegaMinus_of_move (ggOmFrameMoveInput_of_elem h)

theorem ggStepTwoToralWitnessOn_POmegaPlus_of_elem (h : GGOmFrameElemMoveInput) :
    GGStepTwoToralWitnessOn .POmegaPlus :=
  ggStepTwoToralWitnessOn_POmegaPlus_of_move (ggOmFrameMoveInput_of_elem h)

theorem ggStepTwoToralWitnessOn_POmegaMinus_of_elem (h : GGOmFrameElemMoveInput) :
    GGStepTwoToralWitnessOn .POmegaMinus :=
  ggStepTwoToralWitnessOn_POmegaMinus_of_move (ggOmFrameMoveInput_of_elem h)

end Certified

end CFSG.StandardType
