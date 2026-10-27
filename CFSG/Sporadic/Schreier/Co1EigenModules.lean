module

public import CFSG.Sporadic.Schreier.Co1EigenPlanes

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD)
open ElemThree Matrix

@[expose] noncomputable def planeAct
    (j : Fin 12) (x : E) : plane j →ₗ[ZMod 2] plane j :=
  (Matrix.mulVecLin ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))).restrict
    fun _ hv => E_mulVec_mem_plane x.2 hv

theorem planeAct_apply
    (j : Fin 12) (x : E) (v : plane j) :
    (planeAct j x v : Vec24) = ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (v : Vec24) :=
  rfl

@[expose] noncomputable def planeRep
    (j : Fin 12) : Representation (ZMod 2) E (plane j) where
  toFun := planeAct j
  map_one' := by
    ext v
    rw [planeAct_apply, OneMemClass.coe_one, Units.val_one, one_mulVec]
    rfl
  map_mul' x y := by
    ext v
    rw [planeAct_apply, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    rfl

theorem planeRep_apply
    (j : Fin 12) (x : E) (v : plane j) :
    (planeRep j x v : Vec24) = ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (v : Vec24) :=
  rfl

theorem q_ne_zero
    (j : Fin 12) : q j ≠ 0 := by
  intro h
  have := linearIndependent_q.ne_zero (j, 0)
  simp only [Fin.val_zero, pow_zero, one_mulVec] at this
  exact this h

theorem linearIndependent_pair_of_ne {v w : Vec24} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    LinearIndependent (ZMod 2) ![v, w] := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have key : ∀ s t : ZMod 2, s • v + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst
      exact absurd hst hw
    · rw [zero_smul, one_smul, add_zero] at hst
      exact absurd hst hv
    · rw [one_smul, one_smul] at hst
      refine absurd ?_ hvw
      rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
      exact hst
  have h2 : (f 0 - g 0) • v + (f 1 - g 1) • w = 0 := by
    linear_combination (norm := module) h
  obtain ⟨h0, h1⟩ := key _ _ h2
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1

theorem zM_mulVec_ne_zero
    {v : Vec24} (hv : v ≠ 0) : zM *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← one_mulVec v, ← zM_cube, pow_succ, ← mulVec_mulVec, h, mulVec_zero]

theorem finrank_plane
    (j : Fin 12) : Module.finrank (ZMod 2) (plane j) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![q j, zM *ᵥ q j] :=
    linearIndependent_pair_of_ne (q_ne_zero j) (zM_mulVec_ne_zero (q_ne_zero j))
      (fun h => zM_mulVec_ne_self (q_ne_zero j) h.symm)
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  unfold plane
  rw [show ({q j, zM *ᵥ q j} : Set Vec24) = Set.range ![q j, zM *ᵥ q j] by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]]
  exact this

theorem zM_pow_inj
    {w : Vec24} (hw : w ≠ 0) {m n : ℕ} (hm : m < 3) (hn : n < 3)
    (h : (zM ^ m) *ᵥ w = (zM ^ n) *ᵥ w) : m = n := by
  have h1 : (zM ^ ((3 - n) + m)) *ᵥ w = w := by
    rw [pow_add, ← mulVec_mulVec, h, mulVec_mulVec, ← pow_add, show 3 - n + n = 3 by omega,
      zM_cube, one_mulVec]
  have := zM_pow_mulVec_eq_self hw h1
  omega

theorem γ_injective : Function.Injective γ := by decide

@[expose] noncomputable def zE : E := ⟨a 0, a_mem_E 0⟩

theorem planeRep_zE_pow
    (j : Fin 12) (m : ℕ) (v : plane j) :
    (planeRep j (zE ^ m) v : Vec24) = (zM ^ m) *ᵥ (v : Vec24) := by
  rw [planeRep_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  change ((a 0 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ^ m *ᵥ _ = _
  rw [a_zero]

theorem exists_zM_pow_eq_q
    {j : Fin 12} {v : Vec24} (hv : v ∈ plane j) (hv0 : v ≠ 0) :
    ∃ m : ℕ, (zM ^ m) *ᵥ v = q j := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h01 α with rfl | rfl <;> rcases h01 β with rfl | rfl
  · rw [zero_smul, zero_smul, add_zero] at hv0
    exact absurd rfl hv0
  · refine ⟨2, ?_⟩
    rw [zero_smul, one_smul, zero_add, mulVec_mulVec, ← pow_succ, show 2 + 1 = 3 from rfl,
      zM_cube, one_mulVec]
  · refine ⟨0, ?_⟩
    rw [one_smul, zero_smul, add_zero, pow_zero, one_mulVec]
  · refine ⟨1, ?_⟩
    rw [one_smul, one_smul, pow_one, mulVec_add, mulVec_mulVec, zM_sq, add_mulVec, one_mulVec,
      ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem plane_irreducible
    (j : Fin 12) (S : Submodule (ZMod 2) (plane j))
    (hS : ∀ (x : E), ∀ v ∈ S, planeRep j x v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases h : S = ⊥
  · exact Or.inl h
  right
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hv0' : (v : Vec24) ≠ 0 := fun h' => hv0 (Submodule.coe_eq_zero.mp h')
  obtain ⟨m, hm⟩ := exists_zM_pow_eq_q v.2 hv0'
  have hq : (⟨q j, q_mem_plane j⟩ : plane j) ∈ S := by
    have e : (⟨q j, q_mem_plane j⟩ : plane j) = planeRep j (zE ^ m) v :=
      Subtype.ext (by rw [planeRep_zE_pow, hm])
    rw [e]
    exact hS _ v hvS
  have hzq : (⟨zM *ᵥ q j, zq_mem_plane j⟩ : plane j) ∈ S := by
    have e : (⟨zM *ᵥ q j, zq_mem_plane j⟩ : plane j) =
        planeRep j (zE ^ 1) ⟨q j, q_mem_plane j⟩ :=
      Subtype.ext (by rw [planeRep_zE_pow, pow_one])
    rw [e]
    exact hS _ _ hq
  rw [eq_top_iff]
  rintro ⟨u, hu⟩ -
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hu
  have e : (⟨u, hu⟩ : plane j) =
      α • (⟨q j, q_mem_plane j⟩ : plane j) + β • ⟨zM *ᵥ q j, zq_mem_plane j⟩ :=
    Subtype.ext hαβ.symm
  rw [e]
  exact S.add_mem (S.smul_mem _ hq) (S.smul_mem _ hzq)

theorem plane_not_iso
    {j k : Fin 12} (hjk : j ≠ k) :
    ¬ ∃ f : plane j ≃ₗ[ZMod 2] plane k, ∀ (x : E) (v : plane j),
      f (planeRep j x v) = planeRep k x (f v) := by
  rintro ⟨f, hf⟩
  apply hjk
  apply γ_injective
  funext i
  have hv0 : (⟨q j, q_mem_plane j⟩ : plane j) ≠ 0 := fun h =>
    q_ne_zero j ((Submodule.coe_eq_zero (x := (⟨q j, q_mem_plane j⟩ : plane j))).mpr h)
  have hw : ((f ⟨q j, q_mem_plane j⟩ : plane k) : Vec24) ≠ 0 := fun h =>
    hv0 (f.map_eq_zero_iff.mp (Submodule.coe_eq_zero.mp h))
  have h1 : planeRep j ⟨a i, a_mem_E i⟩ ⟨q j, q_mem_plane j⟩ =
      planeRep j (zE ^ (γ j i).val) ⟨q j, q_mem_plane j⟩ := by
    apply Subtype.ext
    rw [planeRep_apply, planeRep_zE_pow]
    exact a_mulVec_q i j
  have h2 := congrArg Subtype.val (hf ⟨a i, a_mem_E i⟩ ⟨q j, q_mem_plane j⟩)
  rw [h1, hf, planeRep_zE_pow, planeRep_apply,
    a_mulVec_plane i (f ⟨q j, q_mem_plane j⟩).2] at h2
  exact ZMod.val_injective _ (zM_pow_inj hw (ZMod.val_lt _) (ZMod.val_lt _) h2)

end CFSG.Sporadic.Co1Schreier
