module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZI
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.Quasithin.Vol2.Ch11SecS12ZH
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Sporadic.J4Base
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import Certificates.Certificate43
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.GroupWithZero.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import TauCeti.Algebra.Central.TensorProduct
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.SymplecticGroup
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_fitting {A L : Subgroup G} (hLA : L ≤ A) (hO2 : pCoreOf 2 A = ⊥)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → L ≤ Subgroup.centralizer (pCoreOf p A : Set G)) :
    L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf A : Set G) := by
  have hO2' : CFSG.pCore 2 ↥A = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp hO2
  have key : L.subgroupOf A ≤ Subgroup.centralizer (CFSG.fittingSubgroup ↥A : Set ↥A) := by
    apply CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    rintro ⟨⟨q, hq⟩, -⟩
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hq2 : q = 2
    · subst hq2
      rw [hO2', Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    · have hyG : (y : G) ∈ pCoreOf q A := ⟨y, by exact hy, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (hp q hqp hq2 (Subgroup.mem_subgroupOf.mp hx)) _ hyG)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp
    (key (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hLA hx⟩ : ↥A) ∈ L.subgroupOf A)) y hy)

omit [Finite G] in
theorem commutatorElement_mul_mul {a b z w : G} (hzb : Commute z b) (hzw : Commute z w)
    (hwa : Commute w a) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have k1 : z * (b * w) * z⁻¹ = b * w := by
    rw [(hzb.mul_right hzw).eq, mul_inv_cancel_right]
  have k2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    rw [hwa.inv_right.eq, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
        a * (z * (b * w) * z⁻¹) * (a⁻¹ * w⁻¹ * b⁻¹) := by group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [k1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [k2]

theorem le_componentLayerOf {A L : Subgroup G} (hLA : L ≤ A) (hL : ⁅L, L⁆ = L)
    (hF : L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf A : Set G))
    (hinn : ∀ J, CFSG.GorensteinWalter.IsComponentOf J A →
      ∀ ℓ ∈ L, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G)) :
    L ≤ CFSG.GorensteinWalter.componentLayerOf A := by
  classical
  set 𝒞 := {J : Subgroup G | CFSG.GorensteinWalter.IsComponentOf J A} with h𝒞
  set E := CFSG.GorensteinWalter.componentLayerOf A with hE
  set F := CFSG.fittingSubgroupOf A with hFdef
  set Fs := CFSG.GorensteinWalter.generalizedFittingSubgroupOf A with hFs
  have hfin : 𝒞.Finite := Set.toFinite _
  have hEA : E ≤ A := sSup_le fun J hJ => hJ.1
  have hFA : F ≤ A := Subgroup.map_subtype_le _
  have hEF : E ≤ Subgroup.centralizer (F : Set G) := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer A F hFA ?_ ?_)
    · have : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥A) := inferInstance
      have e : ↥(CFSG.fittingSubgroup ↥A) ≃* ↥F :=
        (CFSG.fittingSubgroup ↥A).equivMapOfInjective A.subtype A.subtype_injective
      have : Group.IsNilpotent ↥F := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
      infer_instance
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hxA : x ∈ A := hEA hx
      have hn : (CFSG.fittingSubgroup ↥A).Normal := inferInstance
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨⟨x, hxA⟩ * y' * ⟨x, hxA⟩⁻¹, hn.conj_mem y' hy' _, by simp⟩
      · rintro ⟨y', hy', hyy⟩
        refine ⟨⟨x, hxA⟩⁻¹ * y' * ⟨x, hxA⟩, ?_, ?_⟩
        · have := hn.conj_mem y' hy' (⟨x, hxA⟩⁻¹)
          simpa using this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyy ⊢
          rw [hyy]
          group
  have hdec : ∀ ℓ ∈ L, ∃ e ∈ E, e⁻¹ * ℓ ∈ Fs ∧
      e⁻¹ * ℓ ∈ Subgroup.centralizer (Fs : Set G) := by
    intro ℓ hℓ
    have H : ∀ S : Finset (Subgroup G), (↑S : Set (Subgroup G)) ⊆ 𝒞 →
        ∃ e ∈ sSup (↑S : Set (Subgroup G)),
          ∀ J ∈ S, e⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact fun _ => ⟨1, Subgroup.one_mem _, by simp⟩
      | insert J S hJS ih =>
        intro hS
        have hJ : J ∈ 𝒞 := hS (by simp)
        have hS' : (↑S : Set (Subgroup G)) ⊆ 𝒞 := fun K hK => hS (by simp [Finset.mem_coe.mp hK])
        obtain ⟨e, he, hz⟩ := ih hS'
        obtain ⟨j, hj, hjℓ⟩ := hinn J hJ ℓ hℓ
        have hJc : ∀ K ∈ S, J ≤ Subgroup.centralizer (K : Set G) := fun K hK =>
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (commutator_eq_bot_of_ne hJ (hS' hK) fun h => hJS (h ▸ hK))
        have heJ : e ∈ Subgroup.centralizer (J : Set G) := by
          refine (sSup_le fun K hK => ?_ : sSup (↑S : Set (Subgroup G)) ≤ _) he
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (commutator_eq_bot_of_ne (hS' hK) hJ fun h => hJS (h ▸ hK))
        have h1 : sSup (↑S : Set (Subgroup G)) ≤ sSup (↑(insert J S) : Set (Subgroup G)) :=
          sSup_le_sSup (by simp [Finset.coe_insert, Set.subset_insert])
        have h2 : J ≤ sSup (↑(insert J S) : Set (Subgroup G)) := le_sSup (by simp)
        refine ⟨e * j, Subgroup.mul_mem _ (h1 he) (h2 hj), fun K hK => ?_⟩
        rcases Finset.mem_insert.mp hK with rfl | hK
        · have hc : j * e = e * j := Subgroup.mem_centralizer_iff.mp heJ j hj
          have e1 : (e * j)⁻¹ * ℓ = e⁻¹ * (j⁻¹ * ℓ) := by
            rw [← hc, mul_inv_rev, mul_assoc]
          rw [e1]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ heJ) hjℓ
        · have e1 : (e * j)⁻¹ * ℓ = j⁻¹ * (e⁻¹ * ℓ) := by group
          rw [e1]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJc K hK hj)) (hz K hK)
    obtain ⟨e, he, hz⟩ := H hfin.toFinset (by simp)
    rw [Set.Finite.coe_toFinset] at he
    set z := e⁻¹ * ℓ with hzdef
    have hzE : E ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sSup_le fun J hJ x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hz J (hfin.mem_toFinset.mpr hJ)) x hx
    have hzF : F ≤ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_iff.mp (hF hℓ) x hx
      have h2 := Subgroup.mem_centralizer_iff.mp (hEF he) x hx
      have h3 : e⁻¹ * x = x * e⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2, mul_assoc, mul_inv_cancel, mul_one]
      calc x * z = x * e⁻¹ * ℓ := by rw [hzdef, mul_assoc]
        _ = e⁻¹ * x * ℓ := by rw [h3]
        _ = e⁻¹ * (ℓ * x) := by rw [mul_assoc, h1]
        _ = z * x := by rw [hzdef, mul_assoc]
    have hzc : z ∈ Subgroup.centralizer (Fs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := (sup_le hzF hzE : Fs ≤ _) hx
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    have hzA : z ∈ A := A.mul_mem (A.inv_mem (hEA he)) (hLA hℓ)
    exact ⟨e, he, CFSG.GorensteinWalter.centralizer_intersection_fstar_le_fstar A ⟨hzc, hzA⟩,
      hzc⟩
  have hEFs : E ≤ Fs := le_sup_right
  rw [← hL, Subgroup.commutator_le]
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂
  obtain ⟨e₁, he₁, hz₁, hc₁⟩ := hdec ℓ₁ hℓ₁
  obtain ⟨e₂, he₂, hz₂, hc₂⟩ := hdec ℓ₂ hℓ₂
  have hcomm : ∀ {u v : G}, u ∈ Subgroup.centralizer (Fs : Set G) → v ∈ Fs → Commute u v :=
    fun hu hv => (Subgroup.mem_centralizer_iff.mp hu _ hv).symm
  have e₁' : ℓ₁ = e₁ * (e₁⁻¹ * ℓ₁) := by group
  have e₂' : ℓ₂ = e₂ * (e₂⁻¹ * ℓ₂) := by group
  rw [e₁', e₂', commutatorElement_mul_mul (hcomm hc₁ (hEFs he₂)) (hcomm hc₁ hz₂)
    (hcomm hc₂ (hEFs he₁))]
  exact Subgroup.commutator_mem_commutator he₁ he₂ |> fun h => by
    simpa [commutatorElement_def] using E.mul_mem (E.mul_mem (E.mul_mem he₁ he₂)
      (E.inv_mem he₁)) (E.inv_mem he₂)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
