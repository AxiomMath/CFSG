module

public import CFSG.Sporadic.Co2Schreier.QMod

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def qcChi :
    Subgroup.center (locQ.subgroupOf locC) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq card_center_qc (Nat.card_zmod 2)

theorem centralizer_qc :
    Subgroup.centralizer ((locQ.subgroupOf locC : Subgroup locC) : Set locC) =
      (Subgroup.center (locQ.subgroupOf locC)).map (locQ.subgroupOf locC).subtype := by
  ext x
  constructor
  · intro hx
    have hmem : (x : Equiv.Perm (Fin 2300)) ∈ CFSG.centerIn locQ := by
      rw [← locC_inf_centralizer_Q]
      refine ⟨x.2, fun g hg => ?_⟩
      have h := Subgroup.mem_centralizer_iff.1 hx (toQc g hg : locC) (toQc g hg).2
      exact congrArg Subtype.val h
    exact ⟨toQc x (Subgroup.mem_inf.1 hmem).1, (mem_center_qc_iff _).2 hmem, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subtype.ext ((Subgroup.mem_inf.1 ((mem_center_qc_iff y).1 hy)).2 _
      (Subgroup.mem_subgroupOf.1 hg))

theorem quotCQ_inner
    (φ : MulAut (locC ⧸ locQ.subgroupOf locC)) :
    ∃ g : locC ⧸ locQ.subgroupOf locC, φ = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_quotCQ_equiv_statedSp
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_statedSp
    ((e.symm.trans φ).trans e)
  refine ⟨e.symm s, MulEquiv.ext fun x => ?_⟩
  have h := congrArg (fun α : MulAut (StatedSp 3 (ZMod 2)) => α (e x)) hs
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem qmod_irr
    (W : Submodule (ZMod 2) QV)
    (hW : ∀ h : locC, ∀ w ∈ W, ((conjGL (Q := locQ.subgroupOf locC) h :
      LinearMap.GeneralLinearGroup (ZMod 2) QV) : Module.End (ZMod 2) QV) w ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  qmod_irreducible W (hW (cGen 0)) (hW (cGen 1))

theorem qmod_cent
    (φ : LinearMap.GeneralLinearGroup (ZMod 2) QV)
    (hφ : ∀ h : locC, φ * conjGL (Q := locQ.subgroupOf locC) h = conjGL h * φ) : φ = 1 := by
  have h0 := congrArg Units.val (hφ (cGen 0))
  have h1 := congrArg Units.val (hφ (cGen 1))
  rw [Units.val_mul, Units.val_mul] at h0 h1
  rcases qmod_commutant φ.val h0 h1 with h | h
  · exfalso
    have h2 := congrArg (fun m : Module.End (ZMod 2) QV => m kV) φ.inv_val
    simp only [Module.End.mul_apply, h, LinearMap.zero_apply, map_zero, Module.End.one_apply] at h2
    exact kV_ne_zero h2.symm
  · exact Units.ext h

theorem locC_perfect_and_inner :
    Group.IsPerfect locC ∧ ∀ α : MulAut locC, ∃ g : locC, α = MulAut.conj g :=
  CFSG.GroupTheory.extraspecial_centralizer_inner_automorphisms qc_extraspecial centralizer_qc
    qcChi.toMonoidHom qcChi.injective isSimpleGroup_quotCQ not_isMulCommutative_quotCQ
    quotCQ_inner qmod_irr (fun φ _ hφ => qmod_cent φ hφ)

theorem commForm_qc_isAlt :
    (commForm commutator_qc_le qcChi.toMonoidHom).IsAlt := by
  intro v
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  rw [commForm_apply]
  have h : commRight commutator_qc_le x x = 1 := Subtype.ext (commutatorElement_self x)
  rw [h, map_one, toAdd_one]

theorem commForm_qc_nondegenerate :
    (commForm commutator_qc_le qcChi.toMonoidHom).Nondegenerate :=
  commForm_nondegenerate commutator_qc_le commutator_qc.ge qcChi.injective

theorem CTUC_Co2_extraspecial_core_module_rigidity :
    CFSG.IsExtraspecialPGroup 2 (locQ.subgroupOf locC) ∧
    Nat.card (locQ.subgroupOf locC) = 2 ^ 9 ∧
    Subgroup.center (locQ.subgroupOf locC) = Subgroup.zpowers zQc ∧
    commutator (locQ.subgroupOf locC) = Subgroup.zpowers zQc ∧
    Module.finrank (ZMod 2) QV = 8 ∧
    (commForm commutator_qc_le qcChi.toMonoidHom).IsAlt ∧
    (commForm commutator_qc_le qcChi.toMonoidHom).Nondegenerate ∧
    (∀ X : Module.End (ZMod 2) QV,
      (∀ c : locC, X * conjEnd (Q := locQ.subgroupOf locC) c =
        conjEnd (Q := locQ.subgroupOf locC) c * X) ↔ X = 0 ∨ X = 1) ∧
    Submodule.span (ZMod 2) {w : QV | ∃ (c : locC) (v : QV),
      w = conjEnd (Q := locQ.subgroupOf locC) c v - v} = ⊤ ∧
    commutator locC = ⊤ := by
  refine ⟨qc_extraspecial, card_qc, center_qc, commutator_qc.trans center_qc, finrank_QV,
    commForm_qc_isAlt, commForm_qc_nondegenerate, fun X => ⟨fun h => ?_, ?_⟩,
    qmod_commutator_span, locC_perfect_and_inner.1.commutator_eq_top⟩
  · exact qmod_commutant X (h (cGen 0)) (h (cGen 1))
  · rintro (rfl | rfl) c
    · rw [zero_mul, mul_zero]
    · rw [one_mul, mul_one]

theorem CTUC_Co2_first_centralizer_automorphisms_inner :
    (∀ α : MulAut locC, ∃ g : locC, α = MulAut.conj g) ∧
    (MulAut.conj : locC →* MulAut locC).range = ⊤ := by
  refine ⟨locC_perfect_and_inner.2, eq_top_iff.2 fun α _ => ?_⟩
  obtain ⟨g, hg⟩ := locC_perfect_and_inner.2 α
  exact ⟨g, hg.symm⟩

end CFSG.Sporadic.Co2Schreier
