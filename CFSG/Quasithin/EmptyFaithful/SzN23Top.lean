module

public import CFSG.Quasithin.EmptyFaithful.SzN23Sl2
public import CFSG.Quasithin.EmptyFaithful.SzN22K

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C

namespace SzN23

@[expose] def LieRigidRankTwo : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (K : Subgroup Ω) (e : ℕ), 1 < e →
    ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
        Nonempty (↥K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
        Nonempty (↥K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ e ∧
        Nonempty (↥K ≃* ↥(CFSG.Open.quasithinG2 F)))) → SzN22.KRig K

theorem lieRigid_of_rankTwo (h : LieRigidRankTwo) : SzN22.LieRigid := by
  intro Ω _ _ K e he hlie
  rcases hlie with ⟨F, _, _, hF, ⟨iso⟩⟩ | hrest
  · exact krig_of_sl2 hF (by omega) iso
  · exact h Ω K e he hrest

end SzN23

end CFSG.Quasithin
