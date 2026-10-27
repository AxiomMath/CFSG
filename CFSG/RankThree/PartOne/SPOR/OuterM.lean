module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.Y443.Native.Hom
import CFSG.Sporadic.Schreier.Co1OddInner
import CFSG.Sporadic.Co2Schreier.FullAut
import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner
import CFSG.Monster.SteinbergMHmatInnerAut
import CFSG.Sporadic.Bridge.Y443Relabel
import CFSG.YGroups.Y443.Native.TerminalInputs
import CFSG.YGroups.Y443.Native.Surjective
import CFSG.RankThree.PartOne.SPOR.MonsterOrder
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.Generated.FiniteSimple
public import CFSG.YGroups.Y433.TwoCentral

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Monster.Generated (Gmat)

namespace CFSG.RankThree.PartOne.SPOR

theorem allInner_Gmat :
    ∀ α : MulAut Gmat, ∃ g : Gmat, α = MulAut.conj g :=
  CFSG.ComponentClassification.BMCase.gmat_automorphisms_inner
    (CFSG.Monster.Existence.Hmat_perfect_and_inner_of_Co1_inner
      (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)).2

theorem fM_terminal_order' :
    CFSG.YGroups.Q343N ≤ Nat.card (CFSG.YGroups.y443H.map CFSG.YGroups.Y443.fM) :=
  terminal_order' CFSG.YGroups.Y443.fM CFSG.YGroups.Y443.fM_C_ne_one
    ⟨CFSG.YGroups.Y443.fM (CFSG.YGroups.Y443.axElt CFSG.YGroups.Y443.y443U11),
      ⟨_, CFSG.YGroups.Y443.axElt_U11_mem_H, rfl⟩, CFSG.YGroups.Y443.orderOf_fM_b1⟩

theorem fM_surjective :
    Function.Surjective CFSG.YGroups.Y443.fM :=
  CFSG.YGroups.Y443.fM_surjective_of_order fM_terminal_order'

theorem mulEquiv_Gmat_of_simple
    {T : Type*} [Group T] [IsSimpleGroup T] (e : T ≃* NativeSporadic.Carrier .M) :
    Nonempty (T ≃* Gmat) := by
  have hGm : Nontrivial Gmat := CFSG.Monster.Generated.generated_rational_group_finite_simple.1
  let ε : T →* Gmat := CFSG.YGroups.Y443.fM.comp
    (CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toMonoidHom.comp e.toMonoidHom)
  have hs : Function.Surjective ε :=
    fM_surjective.comp (CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.surjective.comp e.surjective)
  have hne : ∃ x, ε x ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : Gmat)
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, hy⟩
  exact ⟨(MulEquiv.ofBijective ε
    (CFSG.ComponentClassification.BMCase.bijective_of_surjective_of_isSimpleGroup ε hs hne))⟩

theorem card_outer_M_of_simple
    {T : Type*} [Group T] [IsSimpleGroup T] (e : T ≃* NativeSporadic.Carrier .M) :
    Nat.card (Outer T) = 1 := by
  obtain ⟨ε⟩ := mulEquiv_Gmat_of_simple e
  have hsub := CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner
    (CFSG.ComponentClassification.BMCase.inner_of_equiv ε allInner_Gmat)
  exact Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩

theorem isSolvable_outer_of_simple_M
    {T : Type*} [Group T] [IsSimpleGroup T] (e : T ≃* NativeSporadic.Carrier .M) :
    Group.IsSolvable (Outer T) := by
  obtain ⟨ε⟩ := mulEquiv_Gmat_of_simple e
  exact CFSG.ComponentClassification.BMCase.isSolvable_outer_of_mulEquiv ε allInner_Gmat

@[expose] def MonsterPresentationIsNative : Prop :=
  Nonempty (NativeSporadic.Carrier .M ≃* Gmat)

theorem monsterPresentationIsNative_of_injective
    (hinj : Function.Injective CFSG.YGroups.Y443.fM) : MonsterPresentationIsNative :=
  ⟨CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.trans
    (MulEquiv.ofBijective CFSG.YGroups.Y443.fM ⟨hinj, fM_surjective⟩)⟩

theorem allInner_M_of_isNative
    (h : MonsterPresentationIsNative) :
    ∀ α : MulAut (NativeSporadic.Carrier .M), ∃ g : NativeSporadic.Carrier .M,
      α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  exact CFSG.ComponentClassification.BMCase.inner_of_equiv e allInner_Gmat

theorem card_outer_M_of_isNative
    (h : MonsterPresentationIsNative) :
    Nat.card (Outer (NativeSporadic.Carrier .M)) = 1 := by
  have hsub := CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner
    (allInner_M_of_isNative h)
  exact Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩

end CFSG.RankThree.PartOne.SPOR
