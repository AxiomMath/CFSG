module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBasic2
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem spUCited_hyp_eval_add_smul (hr : 2 ≤ r) (c : K) :
    (((Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) +
        c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K))
      (Sum.inl (⟨0, by omega⟩ : Fin r))) = c := by
  have hne : (Sum.inl (⟨1, by omega⟩ : Fin r) : HypIndex r ε) ≠
      Sum.inl (⟨0, by omega⟩ : Fin r) := by
    intro h
    exact absurd (Sum.inl.inj h) (by simp)
  simp [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne, smul_eq_mul]

theorem uCited_mem_rootGroupsIn (h : UnitaryFieldData p f K) (hr : 2 ≤ r) :
    uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) ∈
      rootGroupsIn (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)))
        (hypUnitriangular h r ε) := by
  obtain ⟨c, hc, hc0⟩ := h.exists_mem_traceZero_ne_zero
  refine ⟨⟨(uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc)⁻¹, ?_⟩, ?_⟩
  · rw [CFSG.Quasithin.conjSubgroup, inv_inv]
    exact (uCited_conj_root_zero h hr hc hc0).symm
  · exact uCited_root_le_unipotent h ⟨1, by omega⟩

theorem uCited_unipotent_apply_one (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    {u : ↥(hypSU h r ε)} (hu : u ∈ hypUnitriangular h r ε) :
    ∃ c : K, ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) =
      (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) +
        c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) := by
  classical
  let e0 : Fin r := ⟨0, by omega⟩
  let e1 : Fin r := ⟨1, by omega⟩
  let v0 : HypIndex r ε → K := Pi.single (Sum.inl e0) 1
  let v1 : HypIndex r ε → K := Pi.single (Sum.inl e1) 1
  have he2 : v1 ∈ posFlag r ε K 2 := by
    intro a ha
    by_cases ha1 : a = Sum.inl e1
    · exfalso
      rw [ha1] at ha
      have hpos : fullPos (Sum.inl e1 : HypIndex r ε) = 1 := by simp [e1]
      omega
    · simp only [v1, Pi.single_eq_of_ne ha1]
  have hsub := unitriangular_sub_mem_posFlag hu (i := 1) he2
  have hflag : posFlag r ε K 1 = K ∙ v0 := by
    rw [posFlag_one (by omega : 1 ≤ r)]
  have hspan : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v1 -
      v1 ∈ K ∙ v0 := by
    rw [← hflag]
    exact hsub
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨c, ?_⟩
  change ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v1 =
    v1 + c • v0
  rw [hc]
  abel

theorem uCited_index_le [Finite K] (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1) :
    (Subgroup.normalizer
        (uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) :
          Set ↥(hypSU h r ε))).relIndex (hypUnitriangular h r ε) ≤ Nat.card K := by
  classical
  let S := ↥(hypSU h r ε)
  let U : Subgroup S := hypUnitriangular h r ε
  let X₂ : Subgroup S :=
    uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K))
  let N : Subgroup S := Subgroup.normalizer (X₂ : Set S)
  let H : Subgroup U := N.subgroupOf U
  let e0 : Fin r := ⟨0, by omega⟩
  let e1 : Fin r := ⟨1, by omega⟩
  let v0 : HypIndex r ε → K := Pi.single (Sum.inl e0) 1
  let v1 : HypIndex r ε → K := Pi.single (Sum.inl e1) 1
  let m : S → Matrix (HypIndex r ε) (HypIndex r ε) K :=
    fun g => ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  have hmulS : ∀ a b : S, m (a * b) = m a * m b := fun a b => rfl
  have hinvS : ∀ a : S, m a⁻¹ = (m a)⁻¹ := fun a =>
    Matrix.GeneralLinearGroup.coe_inv (A := (a : GL (HypIndex r ε) K))
  let T : Type _ := {w : HypIndex r ε → K // ∃ c : K, w = v1 + c • v0}
  have hTcard : Nat.card T = Nat.card K := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun w => w.1 (Sum.inl (⟨0, by omega⟩ : Fin r))
        invFun := fun c => ⟨v1 + c • v0, c, rfl⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro w
      obtain ⟨c, hc⟩ := w.2
      apply Subtype.ext
      have hcw : w.1 (Sum.inl (⟨0, by omega⟩ : Fin r)) = c := by
        rw [hc]
        simpa [v0, v1, e0, e1] using spUCited_hyp_eval_add_smul (ε := ε) hr c
      dsimp only
      rw [hcw]
      exact hc.symm
    · intro c
      simpa [v0, v1, e0, e1] using spUCited_hyp_eval_add_smul (ε := ε) hr c
  let f : U ⧸ H → T := Quotient.lift
    (fun u : U =>
      ⟨m (u : S) *ᵥ v1, by
        obtain ⟨c, hc⟩ := uCited_unipotent_apply_one h hr hε (u := (u : S)) u.2
        exact ⟨c, by simpa [v0, v1, e0, e1, m] using hc⟩⟩)
    (fun u v huv => by
      apply Subtype.ext
      have huvH : u⁻¹ * v ∈ H := QuotientGroup.leftRel_apply.mp huv
      have huvN : (((u⁻¹ * v : U)) : S) ∈ N := (Subgroup.mem_subgroupOf).mp huvH
      have hg : (((u⁻¹ * v : U)) : S) = (u : S)⁻¹ * (v : S) := by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      have hfix : m (((u⁻¹ * v : U)) : S) *ᵥ v1 = v1 := by
        obtain ⟨c, _hcne, hc⟩ :=
          (uCited_mem_normalizer_root_iff h (⟨1, by omega⟩ : Fin r)
            (((u⁻¹ * v : U)) : S)).mp huvN
        obtain ⟨c', hc'⟩ := uCited_unipotent_apply_one h hr hε ((u⁻¹ * v : U)).2
        have hcv : m (((u⁻¹ * v : U)) : S) *ᵥ v1 = c • v1 := by
          simpa [v0, v1, e0, e1, m] using hc
        have hc'v : m (((u⁻¹ * v : U)) : S) *ᵥ v1 = v1 + c' • v0 := by
          simpa [v0, v1, e0, e1, m] using hc'
        have heq : c • v1 = v1 + c' • v0 := hcv.symm.trans hc'v
        have hc1 : c = 1 := by
          have h := congrFun heq (Sum.inl (⟨1, by omega⟩ : Fin r))
          have h2 : (c • v1 : HypIndex r ε → K)
              (Sum.inl (⟨1, by omega⟩ : Fin r)) = c := by
            simp [v1, e1, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
          have h3 : (v1 + c' • v0 : HypIndex r ε → K)
              (Sum.inl (⟨1, by omega⟩ : Fin r)) = 1 := by
            simpa [v0, v1, e0, e1] using spUCited_hyp_eval_add_smul_one (ε := ε) hr c'
          rw [h2, h3] at h
          exact h
        have hc2 : c' = 0 := by
          have h := congrFun heq (Sum.inl (⟨0, by omega⟩ : Fin r))
          have hne : (Sum.inl (⟨1, by omega⟩ : Fin r) : HypIndex r ε) ≠
              Sum.inl (⟨0, by omega⟩ : Fin r) := by
            intro hh
            exact absurd (Sum.inl.inj hh) (by simp)
          have h2 : (c • v1 : HypIndex r ε → K)
              (Sum.inl (⟨0, by omega⟩ : Fin r)) = 0 := by
            simp [v1, e1, Pi.smul_apply, Pi.single_eq_of_ne' hne, smul_eq_mul]
          have h3 : (v1 + c' • v0 : HypIndex r ε → K)
              (Sum.inl (⟨0, by omega⟩ : Fin r)) = c' := by
            simpa [v0, v1, e0, e1] using spUCited_hyp_eval_add_smul (ε := ε) hr c'
          rw [h2, h3] at h
          exact h.symm
        rw [hc2] at hc'v
        simpa using hc'v
      have hgroup : (u : S) * ((u : S)⁻¹ * (v : S)) = (v : S) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      have hfinal : m (v : S) *ᵥ v1 = m (u : S) *ᵥ v1 := by
        calc m (v : S) *ᵥ v1
            = m ((u : S) * ((u : S)⁻¹ * (v : S)) : S) *ᵥ v1 := by rw [hgroup]
          _ = (m (u : S) * m ((u : S)⁻¹ * (v : S) : S)) *ᵥ v1 := by
                rw [← hmulS (u : S) ((u : S)⁻¹ * (v : S))]
          _ = m (u : S) *ᵥ (m ((u : S)⁻¹ * (v : S) : S) *ᵥ v1) := by
                rw [← Matrix.mulVec_mulVec]
          _ = m (u : S) *ᵥ v1 := by
                rw [show m ((u : S)⁻¹ * (v : S) : S) = m (((u⁻¹ * v : U)) : S) by
                      rw [← hg], hfix]
      exact hfinal.symm)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | _ u => ?_
    induction y using Quotient.inductionOn with | _ v => ?_
    have hsp : m (u : S) *ᵥ v1 = m (v : S) *ᵥ v1 := congrArg Subtype.val hxy
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    rw [Subgroup.mem_subgroupOf, uCited_mem_normalizer_root_iff h (⟨1, by omega⟩ : Fin r)]
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    have hfix : m (((u⁻¹ * v : U)) : S) *ᵥ v1 = v1 := by
      have hg : (((u⁻¹ * v : U)) : S) = (u : S)⁻¹ * (v : S) := by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hg]
      have hmul : m ((u : S)⁻¹ * (v : S) : S) = (m (u : S))⁻¹ * m (v : S) := by
        rw [hmulS ((u : S)⁻¹) (v : S), hinvS (u : S)]
      have hinv : (m (u : S))⁻¹ * m (u : S) = 1 := by
        rw [← hinvS (u : S), ← hmulS ((u : S)⁻¹) (u : S),
          show (u : S)⁻¹ * (u : S) = 1 from inv_mul_cancel (u : S)]
        rfl
      calc m ((u : S)⁻¹ * (v : S) : S) *ᵥ v1
          = ((m (u : S))⁻¹ * m (v : S)) *ᵥ v1 := by rw [hmul]
        _ = (m (u : S))⁻¹ *ᵥ (m (v : S) *ᵥ v1) := by rw [← Matrix.mulVec_mulVec]
        _ = (m (u : S))⁻¹ *ᵥ (m (u : S) *ᵥ v1) := by rw [hsp]
        _ = ((m (u : S))⁻¹ * m (u : S)) *ᵥ v1 := by rw [Matrix.mulVec_mulVec]
        _ = 1 *ᵥ v1 := by rw [hinv]
        _ = v1 := Matrix.one_mulVec v1
    simpa [v0, v1, e0, e1, m] using hfix
  haveI : Finite T := by
    letI : Fintype K := Fintype.ofFinite K
    infer_instance
  change N.relIndex U ≤ Nat.card K
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  have hle : Nat.card (U ⧸ H) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
  rw [hTcard] at hle
  exact hle

end CFSG.LocalAnalysis.WeakClosure81

end
