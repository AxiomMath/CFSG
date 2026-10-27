module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem autFix_inv {Y : Type} [Group Y] (α : MulAut Y) : Sec4.autFix α⁻¹ = Sec4.autFix α := by
  ext x
  rw [Sec4.mem_autFix, Sec4.mem_autFix]
  constructor
  · intro h
    have := congrArg α h
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

theorem hasType424_autFix_conj {Y : Type} [Group Y] [Finite Y] (β α : MulAut Y)
    (h : KS11Lie2Proof.HasType424 ↥(Sec4.autFix α)) :
    KS11Lie2Proof.HasType424 ↥(Sec4.autFix (β * α * β⁻¹)) := by
  have hc : β * α * β⁻¹ = MulAut.congr β α := by
    ext x
    rfl
  rw [hc]
  exact h.of_mulEquiv (Sec4.autFixCongrEquiv β α).symm

theorem hasType424_autFix_inv {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    (h : KS11Lie2Proof.HasType424 ↥(Sec4.autFix α)) :
    KS11Lie2Proof.HasType424 ↥(Sec4.autFix α⁻¹) := by
  rw [autFix_inv]
  exact h

section G2


theorem not_hasType424_g2 {k : Type} [Field k] [Finite k] (hk : 3 ≤ Nat.card k) :
    ¬ KS11Lie2Proof.HasType424
      ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 k) := by
  have : Finite (ModGL Tag.G2 k) := finite_modGL
  have : IsSimpleGroup (adjointGroup Tag.G2 k) := KS11Lie2Proof.isSimpleGroup_g2 hk
  have : IsSimpleGroup (⊤ : Subgroup (adjointGroup Tag.G2 k)) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := KS11Lie2Proof.g2_exists_e9 k
  have hc : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
  exact KS11Lie2Proof.not_hasType424_of_simple ⊤ (fun _ _ => Subgroup.mem_top _)
    (Subgroup.mem_top u) (Subgroup.mem_top v) hu1 hu3 hv3 (by rw [hc]; exact Commute.one_left _)
    (by rw [hc]; exact Commute.one_left _) hvu

end G2

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
