module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22Rep
import CFSG.Quasithin.Background.G9GolayM22
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

noncomputable def mulEquiv_of_center_eq_bot {L : Subgroup (GLV V)} (hZ : Subgroup.center ↥L = ⊥)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) : ↥L ≃* S :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e

theorem case1_M22_case_dimensionOnly
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) (hZ : Subgroup.center ↥L = ⊥)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)) :
    G93Case1DimensionOnly L m := by
  obtain ⟨e⟩ := hM
  let θ : ↥L ≃* NativeSporadic.Carrier .M22 := mulEquiv_of_center_eq_bot hZ e
  have hm : m ≤ 5 := m_le_of_autRank h θ m22_autRank
  have hb := h.bound
  have hd33 : Module.finrank (ZMod 2) V ≤ 33 := by omega
  obtain ⟨hd, hEnd, hSD⟩ := m22_repData (V := V) θ h.H_irr hd33
  exact ⟨Or.inl ⟨⟨θ⟩, hd, by omega, hm⟩, hEnd, hSD⟩

theorem case1_M22_case
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) (hZ : Subgroup.center ↥L = ⊥)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)) :
    G93Case1 L m := by
  obtain ⟨e⟩ := hM
  let θ : ↥L ≃* NativeSporadic.Carrier .M22 := mulEquiv_of_center_eq_bot hZ e
  have hm : m ≤ 5 := m_le_of_autRank h θ m22_autRank
  have hb := h.bound
  have hd33 : Module.finrank (ZMod 2) V ≤ 33 := by omega
  obtain ⟨hd, hEnd, hSD⟩ := m22_repData (V := V) θ h.H_irr hd33
  exact ⟨Or.inl ⟨⟨θ⟩, hd, by omega, hm, mathieu22_golay_realization h.H_irr ⟨θ⟩ hd⟩, hEnd, hSD⟩

theorem case1_M22
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m) (hZ : Subgroup.center ↥L = ⊥)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)) :
    G93Concl Γ L m :=
  Or.inr (Or.inl (case1_M22_case h hZ hM))

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
