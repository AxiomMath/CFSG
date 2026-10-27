module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpBasic
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

private theorem spUCited_eval_add_smul (hr : 2 ≤ r) (c : K) :
    ((Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) +
        c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
          Fin r ⊕ Fin r → K))
      (Sum.inl (⟨0, by omega⟩ : Fin r)) = c := by
  have hne : (Sum.inl (⟨1, by omega⟩ : Fin r) : Fin r ⊕ Fin r) ≠
      Sum.inl (⟨0, by omega⟩ : Fin r) := by
    intro h
    exact absurd (Sum.inl.inj h) (by simp)
  simp [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne,
    smul_eq_mul]

private theorem spUCited_isoFlag_one_eq (hr : 1 ≤ r) :
    isoFlag r K 1 =
      Submodule.span K {Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} := by
  unfold isoFlag
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = ⟨0, by omega⟩ := by
      apply Fin.ext
      simpa using Nat.lt_one_iff.mp hj
    rw [hj0]
  · rintro rfl
    exact ⟨⟨0, by omega⟩, by simp, rfl⟩

theorem spUCited_mem_rootGroupsIn (hr : 2 ≤ r) :
    spUCitedRoot r K ⟨1, by omega⟩ ∈
      rootGroupsIn (spUCitedRoot r K ⟨0, by omega⟩) (unipotent r K) := by
  refine ⟨⟨(weylRep K ⟨0, by omega⟩)⁻¹, ?_⟩, ?_⟩
  · rw [CFSG.Quasithin.conjSubgroup, inv_inv]
    exact (spUCited_conj_root_zero hr).symm
  · exact spUCited_root_le_unipotent ⟨1, by omega⟩

theorem spUCited_unipotent_apply_one (hr : 2 ≤ r) {u : ↥(StatedSp r K)} (hu : u ∈ unipotent r K) :
    ∃ c : K, spEnd u (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) =
      Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K) +
        c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : Fin r ⊕ Fin r → K) := by
  classical
  let e1 : Fin r := ⟨1, by omega⟩
  let e0 : Fin r := ⟨0, by omega⟩
  let v1 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl e1) 1
  let v0 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl e0) 1
  have hv1 : v1 ∈ flag r K 2 := by
    rw [mem_flag_iff]
    intro x hx
    rcases x with j | j
    · rw [flagOrder_inl] at hx
      by_cases hj : j = e1
      · rw [hj] at hx
        have h1 : (e1 : ℕ) = 1 := rfl
        rw [h1] at hx
        omega
      · have hne : (Sum.inl e1 : Fin r ⊕ Fin r) ≠ Sum.inl j := by
          intro h
          exact hj (Sum.inl.inj h).symm
        simp [v1, Pi.single_eq_of_ne' hne]
    · have hne : (Sum.inl e1 : Fin r ⊕ Fin r) ≠ Sum.inr j := by simp
      simp [v1, Pi.single_eq_of_ne' hne]
  have hsub := unipotent_sub_mulVec_mem_flag (r := r) (K := K) hu (i := 1) hv1
  have hsub' : spEnd u v1 - v1 ∈ flag r K 1 := by
    simpa [spEnd_apply] using hsub
  have hw : spEnd u v1 - v1 ∈ isoFlag r K 1 :=
    (mem_flag_of_le (by omega : 1 ≤ r)).mp hsub'
  have hflag : isoFlag r K 1 = Submodule.span K ({v0} : Set (Fin r ⊕ Fin r → K)) := by
    simpa [v0] using spUCited_isoFlag_one_eq (r := r) (K := K) (by omega : 1 ≤ r)
  have hspan : spEnd u v1 - v1 ∈ Submodule.span K ({v0} : Set (Fin r ⊕ Fin r → K)) := by
    rwa [← hflag]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  refine ⟨c, ?_⟩
  rw [hc]
  abel

theorem spUCited_index_le [Finite K] (hr : 2 ≤ r) :
    (Subgroup.normalizer (spUCitedRoot r K ⟨1, by omega⟩ : Set ↥(StatedSp r K))).relIndex
        (unipotent r K) ≤ Nat.card K := by
  classical
  let S := ↥(StatedSp r K)
  let U : Subgroup S := unipotent r K
  let X₂ : Subgroup S := spUCitedRoot r K ⟨1, by omega⟩
  let N : Subgroup S := Subgroup.normalizer (X₂ : Set S)
  let H : Subgroup U := N.subgroupOf U
  let e0 : Fin r := ⟨0, by omega⟩
  let e1 : Fin r := ⟨1, by omega⟩
  let v0 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl e0) 1
  let v1 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl e1) 1
  let T : Type _ := {w : Fin r ⊕ Fin r → K // ∃ c : K, w = v1 + c • v0}
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
        simpa [v0, v1, e0, e1] using spUCited_eval_add_smul hr c
      dsimp only
      rw [hcw]
      exact hc.symm
    · intro c
      simpa [v0, v1, e0, e1] using spUCited_eval_add_smul hr c
  let f : U ⧸ H → T := Quotient.lift
    (fun u : U => ⟨spEnd (u : S) v1, spUCited_unipotent_apply_one hr u.2⟩)
    (fun u v huv => by
      apply Subtype.ext
      have huvH : u⁻¹ * v ∈ H := QuotientGroup.leftRel_apply.mp huv
      have huvN : ((u : S)⁻¹ * (v : S)) ∈ N := by
        have h := (Subgroup.mem_subgroupOf).mp huvH
        simpa using h
      have hfix : spEnd ((u : S)⁻¹ * (v : S)) v1 = v1 := by
        obtain ⟨c, _hcne, hc⟩ :=
          (spUCited_mem_normalizer_root_iff ⟨1, by omega⟩ ((u : S)⁻¹ * (v : S))).mp huvN
        obtain ⟨c', hc'⟩ :=
          spUCited_unipotent_apply_one hr (u := ((u⁻¹ * v : U) : S)) (u⁻¹ * v).2
        have hc'' : spEnd ((u : S)⁻¹ * (v : S)) v1 = v1 + c' • v0 := by
          simpa [v0, v1, e0, e1] using hc'
        have heq : c • v1 = v1 + c' • v0 := hc.symm.trans hc''
        have hc1 : c = 1 := by
          have h := congrFun heq (Sum.inl (⟨1, by omega⟩ : Fin r))
          have h2 : (c • v1 : Fin r ⊕ Fin r → K)
              (Sum.inl (⟨1, by omega⟩ : Fin r)) = c := by
            simp [v1, e1, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
          have h3 : (v1 + c' • v0 : Fin r ⊕ Fin r → K)
              (Sum.inl (⟨1, by omega⟩ : Fin r)) = 1 := by
            simpa [v0, v1, e0, e1] using spUCited_eval_add_smul_one hr c'
          rw [h2, h3] at h
          exact h
        have hc2 : c' = 0 := by
          have h := congrFun heq (Sum.inl (⟨0, by omega⟩ : Fin r))
          have hne : (Sum.inl (⟨1, by omega⟩ : Fin r) : Fin r ⊕ Fin r) ≠
              Sum.inl (⟨0, by omega⟩ : Fin r) := by
            intro hh
            exact absurd (Sum.inl.inj hh) (by simp)
          have h2 : (c • v1 : Fin r ⊕ Fin r → K)
              (Sum.inl (⟨0, by omega⟩ : Fin r)) = 0 := by
            simp [v1, e1, Pi.smul_apply, Pi.single_eq_of_ne' hne]
          have h3 : (v1 + c' • v0 : Fin r ⊕ Fin r → K)
              (Sum.inl (⟨0, by omega⟩ : Fin r)) = c' := by
            simpa [v0, v1, e0, e1] using spUCited_eval_add_smul hr c'
          rw [h2, h3] at h
          exact h.symm
        rw [hc2] at hc''
        simpa using hc''
      have hcomp : spEnd ((u : S) * ((u : S)⁻¹ * (v : S))) v1 = spEnd (u : S) v1 := by
        rw [spEnd_mul]
        have h := congrArg (fun w => spEnd (u : S) w) hfix
        simpa only [Module.End.mul_apply] using h
      have hgroup : (u : S) * ((u : S)⁻¹ * (v : S)) = (v : S) := by
        calc (u : S) * ((u : S)⁻¹ * (v : S)) = ((u : S) * (u : S)⁻¹) * (v : S) := by
              rw [mul_assoc]
          _ = (v : S) := by rw [mul_inv_cancel, one_mul]
      rw [hgroup] at hcomp
      exact hcomp.symm)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | _ u => ?_
    induction y using Quotient.inductionOn with | _ v => ?_
    have hsp : spEnd (u : S) v1 = spEnd (v : S) v1 := congrArg Subtype.val hxy
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    rw [Subgroup.mem_subgroupOf, spUCited_mem_normalizer_root_iff]
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    have hfix : spEnd ((u : S)⁻¹ * (v : S)) v1 = v1 := by
      have hcomp : spEnd ((u : S)⁻¹ * (v : S)) v1 =
          spEnd ((u : S)⁻¹ * (u : S)) v1 := by
        rw [spEnd_mul, spEnd_mul]
        simp only [Module.End.mul_apply]
        rw [hsp]
      rw [hcomp, inv_mul_cancel, spEnd_one]
      rfl
    simpa using hfix
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
