module

public import CFSG.Sporadic.Schreier.Co3First
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms

theorem allInner_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ β : MulAut H, ∃ y : H, β = MulAut.conj y) :
    ∀ α : MulAut G, ∃ x : G, α = MulAut.conj x := by
  intro α
  obtain ⟨y, hy⟩ := h ((e.symm.trans α).trans e)
  refine ⟨e.symm y, MulEquiv.ext fun g => e.injective ?_⟩
  have h1 := congrArg (fun β : MulAut H => β (e g)) hy
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conjAut_eq_conj {A : gsp 3 (ZMod 2)} (hA : (A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) ∈
    StatedSp 3 (ZMod 2)) :
    conjAut 3 (ZMod 2) A = MulAut.conj (proj 3 (ZMod 2) ⟨A, hA⟩) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem sp3_two_allInner :
    ∀ α : MulAut (StatedProj (StatedSp 3 (ZMod 2))), ∃ y, α = MulAut.conj y := by
  intro α
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := 3) (K := ZMod 2) le_rfl).2 α
  have hσ : σ = 1 := Subsingleton.elim _ _
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hm : A ∈ (multiplier 3 (ZMod 2)).ker := MonoidHom.mem_ker.2 (Subsingleton.elim _ _)
  rw [ker_multiplier, Subgroup.mem_subgroupOf] at hm
  refine ⟨proj 3 (ZMod 2) ⟨A, hm⟩, ?_⟩
  rw [hα, hσ, map_one, mul_one, conjAut_eq_conj hm]

@[expose] def co3MQuotProj :
    co3M ⧸ Subgroup.center co3M ≃* StatedProj (StatedSp 3 (ZMod 2)) :=
  co3MQuotEquiv.trans (co3Sp6Equiv.symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.BinaryStabilizer.statedSpEquivProj 3))

theorem co3MQuot_allInner :
    ∀ α : MulAut (co3M ⧸ Subgroup.center co3M), ∃ q, α = MulAut.conj q :=
  allInner_of_mulEquiv co3MQuotProj sp3_two_allInner

theorem co3M_allInner :
    ∀ α : MulAut co3M, ∃ m : co3M, α = MulAut.conj m := by
  intro α
  obtain ⟨q, hq⟩ := co3MQuot_allInner (centerQuotientHom co3M α)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center co3M) q
  refine ⟨m, CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
    co3M ?_⟩
  rw [hq, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]

theorem inner_co3M :
    inner co3M = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨m, rfl⟩ := co3M_allInner α
  exact ⟨m, rfl⟩

theorem CTUC_Co3_first_centralizer_all_automorphisms_inner :
    (∀ α : MulAut co3M, ∃ m : co3M, α = MulAut.conj m) ∧ inner co3M = ⊤ :=
  ⟨co3M_allInner, inner_co3M⟩

end CFSG.Sporadic.Schreier.Co3
