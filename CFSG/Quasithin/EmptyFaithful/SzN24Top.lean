module

public import CFSG.Quasithin.EmptyFaithful.SzN24Lin
public import CFSG.Quasithin.EmptyFaithful.SzN24Sp
public import CFSG.Quasithin.EmptyFaithful.SzN23Top

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C

namespace SzN24

@[expose] def LieRigidG2 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K : Subgroup Ω) (e : ℕ), 1 < e →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
        Nonempty (↥K ≃* ↥(CFSG.Open.quasithinG2 F))) → SzN22.KRig K

theorem lieRigidRankTwo_of_g2 (h : LieRigidG2) : SzN23.LieRigidRankTwo := by
  intro Ω _ _ K e he hfam
  rcases hfam with ⟨F, _, _, hF, ⟨iso⟩⟩ | ⟨F, _, _, hF, ⟨iso⟩⟩ | hg2
  · exact krig_of_sl3 hF iso
  · exact krig_of_sp4 hF iso
  · exact h Ω K e he hg2

end SzN24

end CFSG.Quasithin
