module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem exists_conj_mem_of_plane_of_cyclic_outer {P : Type} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (hcyc : IsCyclic (Outer P)) (E : Subgroup (MulAut P))
    [IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2) :
    ∃ g : P, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have : Finite (MulAut P) :=
    Finite.of_injective (fun f : MulAut P => (f : P → P)) DFunLike.coe_injective
  have : Finite (Outer P) := inferInstance
  have := Fintype.ofFinite (Outer P)
  let φ : E → {x : Outer P // x ^ p = 1} := fun e =>
    ⟨(QuotientGroup.mk (e : MulAut P) : Outer P), by
      rw [← QuotientGroup.mk_pow, elemPow_eq_one_of_isElementaryAbelian (A := E) (e : MulAut P) e.2,
        QuotientGroup.mk_one]⟩
  have hcard : Nat.card {x : Outer P // x ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have hlt : Nat.card {x : Outer P // x ^ p = 1} < Nat.card E := by
    rw [hEc]
    have := hp.two_le
    nlinarith
  have := Fintype.ofFinite E
  have hlt' : Fintype.card {x : Outer P // x ^ p = 1} < Fintype.card E := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  obtain ⟨x, y, hxy, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt'
  have h1 : (QuotientGroup.mk x.1 : Outer P) = QuotientGroup.mk y.1 := congrArg Subtype.val hφ
  have hmem : x.1⁻¹ * y.1 ∈ inner P := QuotientGroup.eq.mp h1
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hxy
    have h2 : x.1 = y.1 := by
      have := congrArg (fun z => x.1 * z) hg
      simpa using this
    exact Subtype.ext h2
  · rw [hg]
    exact E.mul_mem (E.inv_mem x.2) y.2

theorem isCyclic_outer_of_hom {P C : Type} [Group P] [Group C] [IsCyclic C]
    (Θ : MulAut P →* C) (hsurj : Function.Surjective Θ) (hker : Θ.ker = inner P) :
    IsCyclic (Outer P) := by
  let e : Outer P ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact (MulEquiv.isCyclic e).2 inferInstance

end CFSG.RankThree.PartOne.SEITZ2
