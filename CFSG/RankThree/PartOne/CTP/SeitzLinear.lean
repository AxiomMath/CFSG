module

public import CFSG.RankThree.PartOne.CTP.SeitzToral
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.KC.LinearPlaneCore
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.Adapters.LinearCatalog
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.RankThree.PartOne.CTP.SeitzToral

section Nonsplit

variable {n p : ℕ} {K : Type} [Field K] [Finite K]

theorem closure_centralizers_sl_nonsplit (hp : p.Prime) (hp3 : 3 < p) (hpK : (p : K) ≠ 0)
    (hpcard : ¬ p ∣ Nat.card K) (hpq : ¬ p ∣ Nat.card K - 1)
    (E0 : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) [CFSG.IsElementaryAbelian p E0]
    (hE0 : Nat.card E0 = p ^ 2) :
    Subgroup.closure {k : Matrix.SpecialLinearGroup (Fin n) K |
      ∃ x ∈ E0, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine KCLinPlane.eq_top_of_good_blocks_le hp hp3 hpK hpcard hpq E0 hE0 _ ?_
  intro a ha ha1 hsq h hgood g hg
  obtain ⟨s, hs⟩ := KCLinPlane.blockImage_le_range_toGL_of_good hsq h hgood hg
  refine ⟨s, Subgroup.subset_closure ⟨a, ha, ha1, ?_⟩, hs⟩
  have hgr : g ∈ (KCLinComm.commutantUnitsToGL
      (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))).range :=
    KCLinComm.blockImage_le_range hsq h hg
  have hrange := KCLinComm.range_commutantUnitsToGL_eq_centralizer
    (x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) (Matrix.SpecialLinearGroup.toGL a) rfl
  have hgc : g ∈ Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL a} :
      Set (GL (Fin n) K)) := by
    rw [← hrange]
    exact hgr
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, hs]
  exact hgc

end Nonsplit

section Field

variable {F : Type} [Field F] [Finite F]

theorem natCast_ne_zero_of_not_dvd_card {p : ℕ} (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F) :
    (p : F) ≠ 0 := by
  intro h0
  have := Fintype.ofFinite F
  obtain ⟨m, hq, hcard⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ p := (ringChar.spec F p).mp h0
  have hchar : ringChar F = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
  rw [← Nat.card_eq_fintype_card, hchar] at hcard
  exact hpF (hcard ▸ dvd_pow_self p m.ne_zero)

theorem exists_primitiveRoot_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ Nat.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨(x : F), IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)⟩

theorem closure_centralizers_psl_elementary {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) (hsplit : p ∣ Nat.card F - 1 → ¬ p ∣ n)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hnc : ¬ IsCyclic E := CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard
  have hZdvd := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd hn F
  by_cases hs : p ∣ Nat.card F - 1
  · have hZ : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) := fun h =>
      hsplit hs ((h.trans hZdvd).trans (Nat.gcd_dvd_left _ _))
    exact closure_centralizers_psl_eq_top hZ (exists_primitiveRoot_of_dvd hp hs) E hcomm hexp hnc
  · have hZ : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) := fun h =>
      hs ((h.trans hZdvd).trans (Nat.gcd_dvd_right _ _))
    refine closure_centralizers_psl_of_lift hZ E hcomm hexp ?_
    intro E' hc he hcd _
    have : CFSG.IsElementaryAbelian p E' :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (he x x.2) }
    exact closure_centralizers_sl_nonsplit hp (by omega) (natCast_ne_zero_of_not_dvd_card hp hpF)
      hpF hs E' (hcd.trans hcard)

end Field

theorem extSeitzAtInner_A {m : ℕ} {q : TauCeti.PrimePower} (hm : m ≤ 3 ∨ q.card = 2) :
    ExtSeitzAtInner (.A m q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpd' : p ≠ q.p := by simpa using hpd
  left
  have e := e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  refine closure_centralizers_psl_elementary (by omega) hp hp5 ?_ ?_ E₁ hcard₁
  · rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpd' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).mp (hp.dvd_of_dvd_pow hdvd))
  · intro hdvd hdvdm
    rcases hm with hm | hm
    · have := Nat.le_of_dvd (by omega) hdvdm
      omega
    · rw [hcardF, hm] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega

end CFSG.RankThree.PartOne.CTP
