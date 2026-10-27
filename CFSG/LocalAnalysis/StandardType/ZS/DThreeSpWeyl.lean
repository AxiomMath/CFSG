module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal2.SpModel

import CFSG.LocalAnalysis.StandardType.ZS.DThreeChain
import CFSG.Fischer.Classification.Orthogonal2.SpRadical
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals
public import CFSG.LargeExtraspecial.S2Three
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Fischer.Classification.Orth2
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open Module

private def zsp4_spPair (n : ℕ) (x y : Fin n ⊕ Fin n → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i))

private def zsp4_spCoord (n k : ℕ) : Fin n ⊕ Fin n → ZMod 2 :=
  fun i => bitVec (n + n) k (finSumFinEquiv i)

private def zsp4_spPairBits (n : ℕ) (x y : Fin (n + n) → ZMod 2) : ZMod 2 :=
  ∑ i : Fin n, (x (finSumFinEquiv (Sum.inl i)) * y (finSumFinEquiv (Sum.inr i)) +
    x (finSumFinEquiv (Sum.inr i)) * y (finSumFinEquiv (Sum.inl i)))

private def zsp4_spNext (a b : ℕ) : ℕ := a ^^^ b

private def zsp4_spOk (n : ℕ) (a b : ℕ) : Bool :=
  decide (zsp4_spPairBits n (bitVec (n + n) a) (bitVec (n + n) b) = 1)

private theorem zsp4_spPair_coord (n a b : ℕ) :
    zsp4_spPair n (zsp4_spCoord n a) (zsp4_spCoord n b) =
      zsp4_spPairBits n (bitVec (n + n) a) (bitVec (n + n) b) := by
  simp only [zsp4_spPair, zsp4_spCoord, zsp4_spPairBits]

private theorem zsp4_spCoord_xor (n a b : ℕ) :
    zsp4_spCoord n (a ^^^ b) = zsp4_spCoord n a + zsp4_spCoord n b := by
  funext i
  simp [zsp4_spCoord, bitVec_xor, Pi.add_apply]

private theorem zsp4_spCoord_eq_zero_iff (n k : ℕ) :
    zsp4_spCoord n k = 0 ↔ bitVec (n + n) k = 0 := by
  constructor
  · intro h
    funext j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := n) (n := n)).surjective j
    have := congrFun h i
    simpa [zsp4_spCoord] using this
  · intro h
    funext i
    have := congrFun h (finSumFinEquiv (m := n) (n := n) i)
    simpa [zsp4_spCoord] using this

private theorem zsp4_apply_eq_spPair {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {b : LinearMap.BilinForm (ZMod 2) V}
    {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
    (he : IsSymplecticBasis b e) (x y : Fin n ⊕ Fin n → ZMod 2) :
    b (e.equivFun.symm x) (e.equivFun.symm y) = zsp4_spPair n x y := by
  have hneg : ∀ z : ZMod 2, -z = z := by decide
  have hnegmat : (-1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    ext i j
    simp [hneg]
  rw [← LinearMap.BilinForm.dotProduct_toMatrix_mulVec (b := e) (B := b) x y]
  have hmat : LinearMap.BilinForm.toMatrix e b = Matrix.fromBlocks 0 1 (-1) 0 := he
  rw [hmat, hnegmat, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, Matrix.one_mulVec, add_zero]
  rw [Matrix.dotProduct_block]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [zsp4_spPair, dotProduct, dotProduct, ← Finset.sum_add_distrib]
  rfl

private theorem zsp4_apply_spCoord {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}
    {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
    (he : IsSymplecticBasis f e) (a b : ℕ) :
    f (e.equivFun.symm (zsp4_spCoord n a)) (e.equivFun.symm (zsp4_spCoord n b)) =
      zsp4_spPairBits n (bitVec (n + n) a) (bitVec (n + n) b) := by
  rw [zsp4_apply_eq_spPair he, zsp4_spPair_coord]

private theorem zsp4_spCoord_ne_zero {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (e : Basis (Fin n ⊕ Fin n) (ZMod 2) V) (k : ℕ)
    (hk : bitVec (n + n) k ≠ 0) :
    e.equivFun.symm (zsp4_spCoord n k) ≠ 0 := by
  intro h
  exact hk ((zsp4_spCoord_eq_zero_iff n k).mp ((e.equivFun.symm).map_eq_zero_iff.mp h))

private theorem zsp4_spOk_pair {n a c : ℕ} (h : zsp4_spOk n a c = true) :
    zsp4_spPairBits n (bitVec (n + n) a) (bitVec (n + n) c) = 1 := by
  simpa [zsp4_spOk] using h

private theorem zsp4_spT_mem_closure_of_chain {n k : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V}
    (e : Basis (Fin n ⊕ Fin n) (ZMod 2) V)
    (he : IsSymplecticBasis b e) (halt : b.IsAlt)
    (codes : Fin k → ℕ) (d : Fin k → TauCeti.BilinForm.isometryGroup b)
    (hd : ∀ i, d i = spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n (codes i))))
    (steps : List (ℕ × ℕ))
    (hchain : chainOK zsp4_spNext (zsp4_spOk n) (List.ofFn codes) steps = true)
    (hcover : ∀ j < 2 ^ (n + n), bitVec (n + n) j ≠ 0 →
      j ∈ chainLabels zsp4_spNext (List.ofFn codes) steps)
    (v : V) (hv : v ≠ 0) :
    spT (f := b) halt v ∈ Subgroup.closure (Set.range d) := by
  set H := Subgroup.closure (Set.range d) with hH
  let τ : ℕ → TauCeti.BilinForm.isometryGroup b :=
    fun k => spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n k))
  have hknown : ∀ k ∈ List.ofFn codes, τ k ∈ H := by
    intro k hk
    rw [List.mem_ofFn] at hk
    obtain ⟨i, rfl⟩ := hk
    change spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n (codes i))) ∈ H
    rw [← hd i]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hstep : ∀ a c, τ a ∈ H → τ c ∈ H → zsp4_spOk n a c = true →
      τ (zsp4_spNext a c) ∈ H := by
    intro a c ha hc hab
    have hp : zsp4_spPairBits n (bitVec (n + n) a) (bitVec (n + n) c) = 1 :=
      zsp4_spOk_pair hab
    have hpair : b (e.equivFun.symm (zsp4_spCoord n a))
        (e.equivFun.symm (zsp4_spCoord n c)) = 1 := by
      rw [zsp4_apply_spCoord he]
      exact hp
    have hsum : e.equivFun.symm (zsp4_spCoord n (zsp4_spNext a c)) =
        e.equivFun.symm (zsp4_spCoord n a) + e.equivFun.symm (zsp4_spCoord n c) := by
      rw [zsp4_spNext, zsp4_spCoord_xor, map_add]
    have hgoal : τ (zsp4_spNext a c) =
        spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n a)) *
          spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n c)) *
            spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n a)) := by
      change spT (f := b) halt (e.equivFun.symm (zsp4_spCoord n (zsp4_spNext a c))) = _
      rw [hsum, ← spT_mul_spT_mul_spT (f := b) halt hpair]
    rw [hgoal]
    exact mul_mem (mul_mem ha hc) ha
  let c : Fin (n + n) → ZMod 2 := fun j => e.equivFun v (finSumFinEquiv.symm j)
  obtain ⟨k, hk, hkc⟩ := exists_lt_bitVec_eq c
  have hcoord : zsp4_spCoord n k = e.equivFun v := by
    funext i
    rw [zsp4_spCoord, hkc]
    simp [c, Module.Basis.equivFun_apply]
  have hvcode : v = e.equivFun.symm (zsp4_spCoord n k) := by
    rw [hcoord, LinearEquiv.symm_apply_apply]
  have hnonzero : bitVec (n + n) k ≠ 0 := by
    intro h0
    apply hv
    rw [hvcode, (zsp4_spCoord_eq_zero_iff n k).mpr h0, map_zero]
  rw [hvcode]
  exact mem_of_chainOK H τ zsp4_spNext (zsp4_spOk n) hstep steps (List.ofFn codes) hknown
    hchain k (hcover k hk hnonzero)

private def e₇Codes : Fin 7 → ℕ := ![32, 16, 4, 34, 24, 1, 8]

private def e₇Steps : List (ℕ × ℕ) :=
  [(1, 8), (1, 24), (4, 32), (4, 34), (8, 25), (16, 34), (4, 50), (17, 34), (4, 51), (8, 51),
    (1, 59), (4, 58), (1, 62), (16, 51), (4, 35), (8, 35), (1, 43), (4, 42), (1, 46), (32, 38),
    (6, 16), (6, 17), (6, 24), (1, 30), (6, 35), (4, 37), (6, 42), (1, 44), (4, 44), (1, 40),
    (16, 23), (7, 8), (1, 15), (7, 58), (1, 61), (4, 60), (1, 56), (8, 57), (4, 49), (32, 37),
    (5, 8), (1, 13), (5, 14), (1, 11), (5, 24), (1, 29), (5, 30), (1, 27), (5, 49), (4, 52),
    (8, 11), (3, 16), (3, 17), (3, 22), (3, 23), (16, 18)]

private theorem e₇Codes_ne_zero : ∀ i : Fin 7, bitVec (3 + 3) (e₇Codes i) ≠ 0 := by
  decide

private theorem e₇Codes_injective :
    ∀ p : Fin 7 × Fin 7, bitVec (3 + 3) (e₇Codes p.1) = bitVec (3 + 3) (e₇Codes p.2) →
      p.1 = p.2 := by
  decide

private theorem e₇Codes_pair_edge : ∀ p : Fin 7 × Fin 7, CoxeterMatrix.E₇ p.1 p.2 = 3 →
    zsp4_spPairBits 3 (bitVec (3 + 3) (e₇Codes p.1))
      (bitVec (3 + 3) (e₇Codes p.2)) = 1 := by
  decide

private theorem e₇Codes_pair_off : ∀ p : Fin 7 × Fin 7, p.1 ≠ p.2 →
    CoxeterMatrix.E₇ p.1 p.2 = 2 →
    zsp4_spPairBits 3 (bitVec (3 + 3) (e₇Codes p.1))
      (bitVec (3 + 3) (e₇Codes p.2)) = 0 := by
  decide

private theorem e₇_chainOK :
    chainOK zsp4_spNext (zsp4_spOk 3) (List.ofFn e₇Codes) e₇Steps = true := by
  decide

private theorem e₇_cover : ∀ k : Fin 64, bitVec (3 + 3) (k : ℕ) ≠ 0 →
    (k : ℕ) ∈ chainLabels zsp4_spNext (List.ofFn e₇Codes) e₇Steps := by
  decide

theorem exists_coxeterConfig_E₇_spT {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (htop : Subgroup.closure {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v} = ⊤) :
    ∃ d : Fin 7 → TauCeti.BilinForm.isometryGroup b,
      CoxeterConfig {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v} CoxeterMatrix.E₇ d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  have hbn : b.Nondegenerate := nondegenerate_of_isAlt halt hnd
  obtain ⟨e, he⟩ := exists_isSymplecticBasis (b := b) halt hbn (n := 3)
    (by rw [Module.finrank_fin_fun])
  let d : Fin 7 → TauCeti.BilinForm.isometryGroup b :=
    fun i => spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 3 (e₇Codes i)))
  refine ⟨d, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact ⟨e.equivFun.symm (zsp4_spCoord 3 (e₇Codes i)),
      zsp4_spCoord_ne_zero e _ (e₇Codes_ne_zero i), rfl⟩
  · intro i j hij
    have hcoord : zsp4_spCoord 3 (e₇Codes i) = zsp4_spCoord 3 (e₇Codes j) := by
      apply (e.equivFun.symm).injective
      exact eq_of_spT_eq (f := b) halt hbn
        (zsp4_spCoord_ne_zero e _ (e₇Codes_ne_zero i)) hij
    apply e₇Codes_injective (i, j)
    funext t
    obtain ⟨u, rfl⟩ := (finSumFinEquiv (m := 3) (n := 3)).surjective t
    have := congrFun hcoord u
    simpa [zsp4_spCoord] using this
  · intro i j hij
    refine orderOf_spT_mul_spT (f := b) halt hbn ?_
    rw [zsp4_apply_spCoord he]
    exact e₇Codes_pair_edge (i, j) hij
  · intro i j hne hij
    change spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 3 (e₇Codes i))) *
        spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 3 (e₇Codes j))) =
      spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 3 (e₇Codes j))) *
        spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 3 (e₇Codes i)))
    rw [spT_mul_comm_iff (f := b) halt hbn
      (zsp4_spCoord_ne_zero e _ (e₇Codes_ne_zero i))]
    rw [zsp4_apply_spCoord he]
    exact e₇Codes_pair_off (i, j) hne hij
  · apply le_antisymm le_top
    rw [← htop, Subgroup.closure_le]
    rintro g ⟨v, hv, rfl⟩
    exact zsp4_spT_mem_closure_of_chain e he halt e₇Codes d (fun _ => rfl) e₇Steps
      e₇_chainOK (fun j hj h => e₇_cover ⟨j, hj⟩ h) v hv

private def zsp4_a₅Codes : Fin 5 → ℕ := ![1, 4, 3, 8, 2]

private def zsp4_a₅Steps : List (ℕ × ℕ) :=
  [(1, 4), (4, 3), (3, 8), (3, 5), (8, 2), (8, 7), (8, 6), (2, 11), (2, 15), (2, 14)]

private theorem zsp4_a₅Codes_ne_zero : ∀ i : Fin 5, bitVec (2 + 2) (zsp4_a₅Codes i) ≠ 0 := by
  decide

private theorem zsp4_a₅Codes_injective :
    ∀ p : Fin 5 × Fin 5, bitVec (2 + 2) (zsp4_a₅Codes p.1) =
      bitVec (2 + 2) (zsp4_a₅Codes p.2) → p.1 = p.2 := by
  decide

private theorem zsp4_a₅Codes_pair_edge : ∀ p : Fin 5 × Fin 5, CoxeterMatrix.A 5 p.1 p.2 = 3 →
    zsp4_spPairBits 2 (bitVec (2 + 2) (zsp4_a₅Codes p.1))
      (bitVec (2 + 2) (zsp4_a₅Codes p.2)) = 1 := by
  decide

private theorem zsp4_a₅Codes_pair_off : ∀ p : Fin 5 × Fin 5, p.1 ≠ p.2 →
    CoxeterMatrix.A 5 p.1 p.2 = 2 →
    zsp4_spPairBits 2 (bitVec (2 + 2) (zsp4_a₅Codes p.1))
      (bitVec (2 + 2) (zsp4_a₅Codes p.2)) = 0 := by
  decide

private theorem zsp4_a₅_chainOK :
    chainOK zsp4_spNext (zsp4_spOk 2) (List.ofFn zsp4_a₅Codes) zsp4_a₅Steps = true := by
  decide

private theorem zsp4_a₅_cover : ∀ k : Fin 16, bitVec (2 + 2) (k : ℕ) ≠ 0 →
    (k : ℕ) ∈ chainLabels zsp4_spNext (List.ofFn zsp4_a₅Codes) zsp4_a₅Steps := by
  decide

theorem exists_coxeterConfig_A₅_spT {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (htop : Subgroup.closure {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v} = ⊤) :
    ∃ d : Fin 5 → TauCeti.BilinForm.isometryGroup b,
      CoxeterConfig {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v} (CoxeterMatrix.A 5) d ∧
        Subgroup.closure (Set.range d) = ⊤ := by
  have hbn : b.Nondegenerate := nondegenerate_of_isAlt halt hnd
  obtain ⟨e, he⟩ := exists_isSymplecticBasis (b := b) halt hbn (n := 2)
    (by rw [Module.finrank_fin_fun])
  let d : Fin 5 → TauCeti.BilinForm.isometryGroup b :=
    fun i => spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes i)))
  refine ⟨d, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact ⟨e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes i)),
      zsp4_spCoord_ne_zero e _ (zsp4_a₅Codes_ne_zero i), rfl⟩
  · intro i j hij
    have hcoord : zsp4_spCoord 2 (zsp4_a₅Codes i) = zsp4_spCoord 2 (zsp4_a₅Codes j) := by
      apply (e.equivFun.symm).injective
      exact eq_of_spT_eq (f := b) halt hbn
        (zsp4_spCoord_ne_zero e _ (zsp4_a₅Codes_ne_zero i)) hij
    apply zsp4_a₅Codes_injective (i, j)
    funext t
    obtain ⟨u, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective t
    have := congrFun hcoord u
    simpa [zsp4_spCoord] using this
  · intro i j hij
    refine orderOf_spT_mul_spT (f := b) halt hbn ?_
    rw [zsp4_apply_spCoord he]
    exact zsp4_a₅Codes_pair_edge (i, j) hij
  · intro i j hne hij
    change spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes i))) *
        spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes j))) =
      spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes j))) *
        spT (f := b) halt (e.equivFun.symm (zsp4_spCoord 2 (zsp4_a₅Codes i)))
    rw [spT_mul_comm_iff (f := b) halt hbn
      (zsp4_spCoord_ne_zero e _ (zsp4_a₅Codes_ne_zero i))]
    rw [zsp4_apply_spCoord he]
    exact zsp4_a₅Codes_pair_off (i, j) hne hij
  · apply le_antisymm le_top
    rw [← htop, Subgroup.closure_le]
    rintro g ⟨v, hv, rfl⟩
    exact zsp4_spT_mem_closure_of_chain e he halt zsp4_a₅Codes d (fun _ => rfl) zsp4_a₅Steps
      zsp4_a₅_chainOK (fun j hj h => zsp4_a₅_cover ⟨j, hj⟩ h) v hv

end CFSG.StandardType.ZS
