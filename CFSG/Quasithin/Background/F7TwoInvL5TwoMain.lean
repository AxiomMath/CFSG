module

public import CFSG.Quasithin.Background.F7TwoInvL5TwoAut
public import CFSG.Quasithin.Background.F7TwoInvL5TwoInner
public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.GH74.KGroups.PSLN

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GroupTheory.GL52 CFSG.Assembly.LowTwoRank

theorem invAutGen_G52 : ∀ φ : MulAut G52, φ * φ = 1 → φ ≠ 1 → InvAutGen G52 φ := by
  intro φ h2 h1
  rcases aut_involution_L5 φ h2 with ⟨A, rfl⟩ | ⟨H, rfl⟩
  · have hZ : Subgroup.center G52 = ⊥ :=
      center_eq_bot_of_isSimpleGroup isSimpleGroup_G52 (by
        by_contra hc
        push Not at hc
        exact not_commutative_G52 fun a b => hc a b)
    refine invAutGen_conj_of_involution (mul_self_eq_one_of_conj_mul_self hZ h2) ?_
    rintro rfl
    exact h1 (map_one _)
  · exact (InvAutGen.conj_iff (MulAut.conj H) dualG).1 invAutGen_dualG

theorem invAutGen_of_statedPSL5Two {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 5 2 1) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 2) 5 2 1 (by norm_num)
    (by rw [Nat.card_zmod, pow_one]) h
  exact invAutGen_of_mulEquiv_forall (e.trans G52EquivPSL.symm) invAutGen_G52

theorem invAutGenFamL5Two : InvAutGenFamL5Two :=
  fun _ _ _ h φ h2 h1 => invAutGen_of_statedPSL5Two h φ h2 h1

end CFSG.Quasithin.F7Two
