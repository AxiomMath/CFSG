module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7BaseCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountOfFusion
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # A₇ centralizer index  (source: refs/bender-dihedral-sylow.tex L785) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Ambient involutions lying in a subgroup `M` are the same, up to
cardinality, as involutions of the subtype group `↥M`. -/
private theorem involution_subtype_card_eq
    {G : Type u} [Group G] (M : Subgroup G) :
    Nat.card {x : M // IsInvolution x} =
      Nat.card {x : G // IsInvolution x ∧ x ∈ M} := by
  classical
  let e : {x : G // IsInvolution x ∧ x ∈ M} ≃ {x : M // IsInvolution x} :=
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, by
        constructor
        · intro h1
          exact x.2.1.1 (by simpa using congrArg Subtype.val h1)
        · apply Subtype.ext
          simpa using x.2.1.2⟩
      invFun := fun x => ⟨x.1.1, by
        constructor
        · intro h1
          exact x.2.1 (Subtype.ext h1)
        · simpa using congrArg Subtype.val x.2.2, x.1.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact (Nat.card_congr e).symm

/-- In the A₇ branch, `|M : H ∩ M| = 3·5·7 = 105` (source L785:
`|J ∩ M| = |M : H ∩ M| = 3·5·7`).  The `105` involutions of `M` (from
`secondCase_a7_base_involutions_card`) form one `M`-conjugacy class
(`secondCase_a7_involutions_in_component` plus
`secondCase_involutions_fused`), and the centralizer of `t` inside `M` is
`H ∩ M` (`c.H_eq_centralizer`), so the class size is the relative index. -/
public theorem secondCase_a7_centralizer_index
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    (c.H ⊓ w.M).relIndex w.M = 105 := by
  classical
  have htM : c.t ∈ w.M := d.E_component.1 d.t_mem_E
  let tM : w.M := ⟨c.t, htM⟩
  have htM' : IsInvolution tM := by
    constructor
    · intro h1
      apply c.t_involution.1
      simpa [tM] using congrArg Subtype.val h1
    · apply Subtype.ext
      simpa [tM] using c.t_involution.2
  have hfuseM : ∀ x : w.M, IsInvolution x → ∃ g : w.M, g * x * g⁻¹ = tM := by
    intro x hxI
    have hxI_amb : IsInvolution (x : G) := by
      constructor
      · intro h1
        apply hxI.1
        apply Subtype.ext
        exact h1
      · simpa using congrArg Subtype.val hxI.2
    have hxE : (x : G) ∈ d.E :=
      secondCase_a7_involutions_in_component hmin c w d hA7 hmodel
        (x : G) x.2 hxI_amb
    obtain ⟨g, hgE, hgzt⟩ := secondCase_involutions_fused w d (x : G) hxE hxI_amb
    let gM : w.M := ⟨g, d.E_component.1 hgE⟩
    refine ⟨gM, ?_⟩
    apply Subtype.ext
    simpa [tM, gM] using hgzt
  have hcountM := involutions_card_eq_centralizer_index_of_fusion
    (G := w.M) tM htM' hfuseM
  have hcent : Subgroup.centralizer ({tM} : Set (w.M)) =
      (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨?_, x.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [tM] using congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · rintro ⟨hxcent, _⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa [tM] using (Subgroup.mem_centralizer_singleton_iff.mp hxcent)
  have hLHS : Nat.card {x : w.M // IsInvolution x} = 105 := by
    exact (involution_subtype_card_eq w.M).trans
      (secondCase_a7_base_involutions_card hmin c w d hA7 hmodel)
  have hRHS : (Subgroup.centralizer ({tM} : Set (w.M))).index =
      (c.H ⊓ w.M).relIndex w.M := by
    calc
      (Subgroup.centralizer ({tM} : Set (w.M))).index
          = ((Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M).index := by
            rw [hcent]
      _ = (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).relIndex w.M := by
        rfl
      _ = (c.H ⊓ w.M).relIndex w.M := by rw [c.H_eq_centralizer]
  exact calc
    (c.H ⊓ w.M).relIndex w.M = (Subgroup.centralizer ({tM} : Set (w.M))).index := hRHS.symm
    _ = Nat.card {x : w.M // IsInvolution x} := hcountM.symm
    _ = 105 := hLHS

end CFSG.GorensteinWalter
