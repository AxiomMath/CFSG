module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86_conj_q1_inf_q2_inf_q1_inf_conj_q2_eq_bot {L1 L2 S : Subgroup G}
    (hV : ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
      ((Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S) ⊓
        ((MulAut.conj g • Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S) =
          Z2 L1 L2 S)
    (hS1 : ∀ h ∈ L1 ⊔ bigB L1 L2 S, h ∉ bigB L1 L2 S →
      (Z2 L1 L2 S ⊓ Q1 L1 L2 S) ⊓ (Q1 L1 L2 S ⊓ (MulAut.conj h • Q2 L1 L2 S)) ≤
        Z1 L1 L2 S)
    (hS3 : ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
      Z1 L1 L2 S ⊓ (MulAut.conj g • Q1 L1 L2 S) = ⊥) :
    ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
      ∀ h ∈ L1 ⊔ bigB L1 L2 S, h ∉ bigB L1 L2 S →
        (MulAut.conj g • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊓ Q1 L1 L2 S ⊓
          (MulAut.conj h • Q2 L1 L2 S) = ⊥ := by
  intro g hg hgB h hh hhB
  set R : Subgroup G :=
    (MulAut.conj g • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊓ Q1 L1 L2 S ⊓
      (MulAut.conj h • Q2 L1 L2 S)
  have hRA : R ≤ MulAut.conj g • Q1 L1 L2 S :=
    (inf_le_left.trans inf_le_left).trans inf_le_left
  have hRB : R ≤ Q2 L1 L2 S :=
    (inf_le_left.trans inf_le_left).trans inf_le_right
  have hRC : R ≤ Q1 L1 L2 S := inf_le_left.trans inf_le_right
  have hRD : R ≤ MulAut.conj h • Q2 L1 L2 S := inf_le_right
  have hRZ2 : R ≤ Z2 L1 L2 S := by
    have h1 : R ≤ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S :=
      (le_inf hRC hRB).trans le_sup_left
    have h2 : R ≤ (MulAut.conj g • Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ Z2 L1 L2 S :=
      (le_inf hRA hRB).trans le_sup_left
    exact (le_inf h1 h2).trans (le_of_eq (hV g hg hgB))
  have hRZ1 : R ≤ Z1 L1 L2 S := by
    have h1 : R ≤ Z2 L1 L2 S ⊓ Q1 L1 L2 S := le_inf hRZ2 hRC
    have h2 : R ≤ Q1 L1 L2 S ⊓ (MulAut.conj h • Q2 L1 L2 S) := le_inf hRC hRD
    exact (le_inf h1 h2).trans (hS1 h hh hhB)
  have hRbot : R ≤ Z1 L1 L2 S ⊓ (MulAut.conj g • Q1 L1 L2 S) := le_inf hRZ1 hRA
  rw [hS3 g hg hgB] at hRbot
  exact eq_bot_iff.mpr hRbot

end CFSG.Quasithin.Stroth

end
