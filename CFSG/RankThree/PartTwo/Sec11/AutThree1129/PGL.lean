module

public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.Generic
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

@[expose] def IsPGL3PiFamily (X : Type) [Group X] : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
    Sec4.ModThree π (p ^ f) ∧ Nonempty (X ≃* projImage (Sec4.glPi π 3 (p ^ f) K))

theorem nonempty_commutator_mulEquiv_pgl {X X' : Type} [Group X] [Group X'] (e : X ≃* X') :
    Nonempty (_root_.commutator X ≃* _root_.commutator X') := by
  have h : (_root_.commutator X).map e.toMonoidHom = _root_.commutator X' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨((_root_.commutator X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

theorem autThree_pgl_of_l3 (h : AutThreeAut Sec13.IsLThreePi) : AutThreeAut IsPGL3PiFamily := by
  intro Z _ _ hZ α J hα3 hJ hJT hJ3 P hP
  obtain ⟨X, _, ⟨π, p, f, K, _, hK, hq, ⟨e⟩⟩, ⟨eZ⟩⟩ := hZ
  have hp := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  by_cases hq2 : 2 < p ^ f
  · have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi fun hπ => by subst hπ; exact hK.unitary)
    have hperf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      Sec13.isPerfect_projImage_slPi hK hq2
    obtain ⟨e₁⟩ := nonempty_commutator_mulEquiv_pgl e
    have e₂ : _root_.commutator (projImage (Sec4.glPi π 3 (p ^ f) K)) ≃*
        projImage (Sec4.slPi π 3 (p ^ f) K) :=
      (MulEquiv.subgroupCongr (Sec13.commutator_projImage_glPi hK hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP)
    have e₃ : projImage (Sec4.slPi π 3 (p ^ f) K) ≃*
        _root_.commutator (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv).symm
    exact h Z ⟨projImage (Sec4.slPi π 3 (p ^ f) K), inferInstance,
      Sec13.isLThreePi_projImage_slPi hK hq, ⟨eZ.trans (e₁.trans (e₂.trans e₃))⟩⟩
        α J hα3 hJ hJT hJ3 P hP
  · exfalso
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f :=
        le_trans hp.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
      omega
    cases π
    · have hsP : Group.IsSolvable (projImage (Sec4.glPi false 3 (p ^ f) K)) :=
        Sec13.isSolvable_projImage_glPi_two hK h2
      have hsX : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hsC : Group.IsSolvable (_root_.commutator X) := inferInstance
      have hsZ : Group.IsSolvable Z :=
        Group.isSolvable_of_isSolvable_injective (f := eZ.toMonoidHom) eZ.injective
      obtain ⟨K₀, ⟨-, -, hqs⟩, rfl⟩ := hJ
      have hinj : Function.Injective ((Item426.fixSub α).subtype.comp K₀.subtype) :=
        (Subgroup.subtype_injective (Item426.fixSub α)).comp K₀.subtype_injective
      have hsK₀ : Group.IsSolvable K₀ := Group.isSolvable_of_isSolvable_injective hinj
      obtain ⟨-, hsimple, u, v, huv⟩ := hqs
      have : Group.IsSolvable ((K₀ ⧸ aschbacherSolvableCore 3 K₀) ⧸
          Subgroup.center (K₀ ⧸ aschbacherSolvableCore 3 K₀)) := inferInstance
      exact huv ((IsSimpleGroup.comm_iff_isSolvable).mpr this u v)
    · change p ^ f % 3 = 1 at hq
      omega

end CFSG.RankThree.PartTwo.Sec11

end
