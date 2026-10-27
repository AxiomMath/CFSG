module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpFixed

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin Matrix

namespace AutPSp

variable {n : ℕ} {K : Type} [Field K]

section Fix

@[expose] def spFixVec (S : Subgroup (StatedSp n K)) : Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {v | ∀ s ∈ S, mat n K s *ᵥ v = v}
  add_mem' := by
    intro v w hv hw s hs
    rw [Matrix.mulVec_add, hv s hs, hw s hs]
  zero_mem' := fun s _ => Matrix.mulVec_zero _
  smul_mem' := by
    intro c v hv s hs
    rw [Matrix.mulVec_smul, hv s hs]

theorem mem_spFixVec {S : Subgroup (StatedSp n K)} {v : Fin n ⊕ Fin n → K} :
    v ∈ spFixVec S ↔ ∀ s ∈ S, mat n K s *ᵥ v = v :=
  Iff.rfl

theorem mulVec_mem_spFixVec {S : Subgroup (StatedSp n K)} {y : StatedSp n K}
    (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) {v : Fin n ⊕ Fin n → K} (hv : v ∈ spFixVec S) :
    mat n K y *ᵥ v ∈ spFixVec S := by
  intro s hs
  have h := hv _ (hy s hs)
  have hyy : mat n K s * mat n K y = mat n K y * mat n K (y⁻¹ * s * y) := by
    rw [← map_mul, ← map_mul, show y * (y⁻¹ * s * y) = s * y by group]
  rw [Matrix.mulVec_mulVec, hyy, ← Matrix.mulVec_mulVec, h]

theorem exists_ne_zero_mem_spFixVec [Finite K] [CharP K 2] [NeZero n]
    {S : Subgroup (StatedSp n K)} (hS : IsPGroup 2 S) :
    ∃ w : Fin n ⊕ Fin n → K, w ≠ 0 ∧ w ∈ spFixVec S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S (Fin n ⊕ Fin n → K) :=
    { smul := fun s v => mat n K s *ᵥ v
      one_smul := fun v => by
        change mat n K ((1 : S) : StatedSp n K) *ᵥ v = v
        rw [Subgroup.coe_one, map_one, Matrix.one_mulVec]
      mul_smul := fun s t v => by
        change mat n K ((s * t : S) : StatedSp n K) *ᵥ v =
          mat n K (s : StatedSp n K) *ᵥ (mat n K (t : StatedSp n K) *ᵥ v)
        rw [Subgroup.coe_mul, map_mul, Matrix.mulVec_mulVec] }
  have h2 : 2 ∣ Nat.card (Fin n ⊕ Fin n → K) := by
    have hord : addOrderOf (Pi.single (Sum.inl 0) (1 : K) : Fin n ⊕ Fin n → K) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · rw [two_nsmul]
        funext i
        exact CharTwo.add_self_eq_zero _
      · intro h
        have := congrFun h (Sum.inl 0)
        simp at this
    exact hord ▸ addOrderOf_dvd_natCard _
  have h0 : (0 : Fin n ⊕ Fin n → K) ∈ MulAction.fixedPoints S (Fin n ⊕ Fin n → K) :=
    fun s => Matrix.mulVec_zero (mat n K (s : StatedSp n K))
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ h2 h0
  exact ⟨b, hne.symm, fun s hs => hb ⟨s, hs⟩⟩

theorem eq_bot_of_forall_single_mem {S : Subgroup (StatedSp n K)}
    (h : ∀ a, Pi.single a (1 : K) ∈ spFixVec S) : S = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  apply mat_injective
  rw [map_one]
  ext a b
  have := congrFun (h b s hs) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

end Fix

section Spread

theorem E_mulVec_mem {W : Submodule K (Fin n ⊕ Fin n → K)} {ρ : RootSubgroupIndex n}
    (hW : ∀ v ∈ W, mat n K (elt ρ 1) *ᵥ v ∈ W) {v : Fin n ⊕ Fin n → K} (hv : v ∈ W) :
    E K ρ *ᵥ v ∈ W := by
  have h := W.sub_mem (hW v hv) hv
  rwa [mat_elt, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left] at h

theorem single_one_mem {W : Submodule K (Fin n ⊕ Fin n → K)} {a : Fin n ⊕ Fin n} {c : K}
    (hc : c ≠ 0) (h : Pi.single a c ∈ W) : Pi.single a (1 : K) ∈ W := by
  have h2 := W.smul_mem c⁻¹ h
  rwa [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hc] at h2

theorem E_positiveLong_mulVec (i : Fin n) (v : Fin n ⊕ Fin n → K) :
    E K (.positiveLong i) *ᵥ v = Pi.single (Sum.inl i) (v (Sum.inr i)) := by
  rw [show E K (.positiveLong i) = single (Sum.inl i) (Sum.inr i) 1 from rfl,
    Matrix.single_mulVec, one_mul]
  rfl

theorem E_negativeLong_mulVec (i : Fin n) (v : Fin n ⊕ Fin n → K) :
    E K (.negativeLong i) *ᵥ v = Pi.single (Sum.inr i) (v (Sum.inl i)) := by
  rw [show E K (.negativeLong i) = single (Sum.inr i) (Sum.inl i) 1 from rfl,
    Matrix.single_mulVec, one_mul]
  rfl

theorem E_difference_mulVec {i j : Fin n} (hji : j ≠ i) :
    E K (.difference j i hji) *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl j) 1 := by
  rw [show E K (.difference j i hji) =
      single (Sum.inl j) (Sum.inl i) 1 - single (Sum.inr i) (Sum.inr j) 1 from rfl,
    Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  simp
  rfl

theorem single_mem_of_invariant {W : Submodule K (Fin n ⊕ Fin n → K)}
    (hW : ∀ ρ : RootSubgroupIndex n, ∀ v ∈ W, mat n K (elt ρ 1) *ᵥ v ∈ W)
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ W) (hw0 : w ≠ 0) (a : Fin n ⊕ Fin n) :
    Pi.single a (1 : K) ∈ W := by
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hw0
    exact ⟨b, hb⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n, Pi.single (Sum.inl i) (1 : K) ∈ W := by
    rcases b with i | i
    · refine ⟨i, ?_⟩
      have h1 := E_mulVec_mem (hW (.negativeLong i)) hw
      rw [E_negativeLong_mulVec] at h1
      have h2 := E_mulVec_mem (hW (.positiveLong i)) (single_one_mem hb h1)
      rwa [E_positiveLong_mulVec, Pi.single_eq_same] at h2
    · refine ⟨i, ?_⟩
      have h1 := E_mulVec_mem (hW (.positiveLong i)) hw
      rw [E_positiveLong_mulVec] at h1
      exact single_one_mem hb h1
  have hinl : ∀ j : Fin n, Pi.single (Sum.inl j) (1 : K) ∈ W := by
    intro j
    by_cases hji : j = i
    · rwa [hji]
    · have h := E_mulVec_mem (hW (.difference j i hji)) hi
      rwa [E_difference_mulVec] at h
  rcases a with j | j
  · exact hinl j
  · have h := E_mulVec_mem (hW (.negativeLong j)) (hinl j)
    rwa [E_negativeLong_mulVec, Pi.single_eq_same] at h

end Spread

section Core

variable [Finite K] [CharP K 2]

theorem eq_bot_of_normalized [NeZero n] (Q : Subgroup (StatedProj (StatedSp n K)))
    (hQ : IsPGroup 2 Q) (hN : ∀ ρ : RootSubgroupIndex n, ∀ q ∈ Q,
      proj n K (elt ρ 1) * q * (proj n K (elt ρ 1))⁻¹ ∈ Q) : Q = ⊥ := by
  set S := Q.comap (proj n K)
  have hS : IsPGroup 2 S := hQ.comap_of_injective _ proj_injective
  have hinv : ∀ ρ : RootSubgroupIndex n, (elt ρ (1 : K))⁻¹ = elt ρ 1 := fun ρ => by
    rw [← elt_neg, CharTwo.neg_eq]
  have hyS : ∀ ρ : RootSubgroupIndex n, ∀ s ∈ S, (elt ρ (1 : K))⁻¹ * s * elt ρ 1 ∈ S := by
    intro ρ s hs
    have h := hN ρ _ hs
    change proj n K ((elt ρ (1 : K))⁻¹ * s * elt ρ 1) ∈ Q
    rw [hinv, map_mul, map_mul]
    rwa [← map_inv, hinv] at h
  have hW : ∀ ρ : RootSubgroupIndex n, ∀ v ∈ spFixVec S, mat n K (elt ρ 1) *ᵥ v ∈ spFixVec S :=
    fun ρ v hv => mulVec_mem_spFixVec (hyS ρ) hv
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_mem_spFixVec hS
  have hS1 : S = ⊥ := eq_bot_of_forall_single_mem (single_mem_of_invariant hW hw hw0)
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨s, rfl⟩ := proj_surjective q
  have hs : s ∈ S := hq
  rw [hS1, Subgroup.mem_bot] at hs
  rw [hs, map_one]
  exact Subgroup.one_mem _

theorem fieldAut_core [NeZero n] (σ : K ≃+* K) (Q : Subgroup (StatedProj (StatedSp n K)))
    (_hQf : ∀ q ∈ Q, fieldAut n K σ q = q) (hQ : IsPGroup 2 Q)
    (hy : ∀ y : StatedProj (StatedSp n K), fieldAut n K σ y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) :
    Q = ⊥ :=
  eq_bot_of_normalized Q hQ fun ρ => hy _ (fieldAut_fixes_elt_one σ ρ)

theorem compl_core [NeZero n] {c : MulAut (StatedProj (StatedSp n K))} (hc : c ∈ compl)
    (Q : Subgroup (StatedProj (StatedSp n K))) (hQf : ∀ q ∈ Q, c q = q) (hQ : IsPGroup 2 Q)
    (hy : ∀ y : StatedProj (StatedSp n K), c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : Q = ⊥ := by
  obtain ⟨σ, rfl⟩ := hc
  exact fieldAut_core σ Q hQf hQ hy

end Core

end AutPSp

end CFSG.StandardType
