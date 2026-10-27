module

public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.GroupTheory.MulAutCongr
import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTorus
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (sl2EquivPSL2 mulAutToRingAut inner_eq_ker_mulAutToRingAut ringAut_card_and_cyclic)

variable {Y : Type*} [Group Y] {n : ℕ}

section Transport

variable {G : Type*} [Group G]

private theorem mem_centralizer_singleton_map (φ : Y ≃* G) (x y : Y) :
    y ∈ Subgroup.centralizer ({x} : Set Y) ↔ φ y ∈ Subgroup.centralizer ({φ x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul, φ.injective.eq_iff]

private theorem map_centralizer_singleton_eq (φ : Y ≃* G) (x : Y) :
    (Subgroup.centralizer ({x} : Set Y)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  have h := mem_centralizer_singleton_map φ x (φ.symm y)
  rwa [MulEquiv.apply_symm_apply] at h

end Transport

private theorem card_galoisField_two (hn : 2 ≤ n) : Nat.card (GaloisField 2 n) = 2 ^ n :=
  GaloisField.card 2 n (by omega)

private theorem exists_equiv_psl (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) :
    Nonempty (Y ≃* PSL(2, GaloisField 2 n)) :=
  ⟨e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n))⟩

private theorem psl_borel_commutator_mem (hn : 2 ≤ n) (U : Sylow 2 (PSL(2, GaloisField 2 n)))
    {a b : PSL(2, GaloisField 2 n)}
    (ha : a ∈ Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 n))) : Set _))
    (hb : b ∈ Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 n))) : Set _)) :
    a * b * a⁻¹ * b⁻¹ ∈ (U : Subgroup (PSL(2, GaloisField 2 n))) := by
  let N : Subgroup (PSL(2, GaloisField 2 n)) :=
    Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 n))) : Set _)
  have : (U.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hQcyc : IsCyclic (N ⧸ U.subgroupOf N) :=
    CFSG.Quasithin.St84.psl2_normalizer_quotient_cyclic hn U
  have hcomm : ∀ s t : N ⧸ U.subgroupOf N, s * t = t * s := fun s t =>
    (IsCyclic.commGroup (α := N ⧸ U.subgroupOf N)).mul_comm s t
  let π : N →* N ⧸ U.subgroupOf N := QuotientGroup.mk' _
  have hπ : π (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm (π ⟨a, ha⟩) (π ⟨b, hb⟩)]
    group
  have hmemN : (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : N) ∈ U.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    exact hπ
  exact Subgroup.mem_subgroupOf.mp hmemN

theorem l2_borel_commutator_mem (hn : 2 ≤ n)
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
    (U : Sylow 2 Y) {a b : Y} (ha : a ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y))
    (hb : b ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y)) :
    a * b * a⁻¹ * b⁻¹ ∈ (U : Subgroup Y) := by
  obtain ⟨φ⟩ := exists_equiv_psl e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_equiv _ φ.symm.toEquiv
  let U' : Sylow 2 (PSL(2, GaloisField 2 n)) :=
    Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective U
  have hU' : (U' : Subgroup (PSL(2, GaloisField 2 n))) =
      (U : Subgroup Y).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective U
  have hN : ∀ c ∈ Subgroup.normalizer ((U : Subgroup Y) : Set Y),
      φ c ∈ Subgroup.normalizer ((U' : Subgroup (PSL(2, GaloisField 2 n))) : Set _) := by
    intro c hc
    rw [hU', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hc
  have h := psl_borel_commutator_mem hn U' (hN a ha) (hN b hb)
  rw [hU'] at h
  have h2 := Subgroup.mem_map_equiv.mp (by simpa using h : φ (a * b * a⁻¹ * b⁻¹) ∈
    (U : Subgroup Y).map φ.toMonoidHom)
  simpa using h2

theorem l2_mulAut_commutator_inner (hn : 2 ≤ n)
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
    (α β : MulAut Y) : ∃ y : Y, α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  have hcard := card_galoisField_two hn
  obtain ⟨φ₀⟩ := exists_equiv_psl e
  let φ : Y ≃* SL(2, GaloisField 2 n) := φ₀.trans (sl2EquivPSL2 (F := GaloisField 2 n)).symm
  have : IsCyclic (RingAut (GaloisField 2 n)) := (ringAut_card_and_cyclic hcard).2
  have hcomm : ∀ a b : RingAut (GaloisField 2 n), a * b = b * a := fun a b =>
    (IsCyclic.commGroup (α := RingAut (GaloisField 2 n))).mul_comm a b
  have hker : MulAut.congr φ α * MulAut.congr φ β * (MulAut.congr φ α)⁻¹ *
      (MulAut.congr φ β)⁻¹ ∈ inner SL(2, GaloisField 2 n) := by
    rw [inner_eq_ker_mulAutToRingAut hcard, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm (mulAutToRingAut hcard (MulAut.congr φ α)) (mulAutToRingAut hcard (MulAut.congr φ β))]
    group
  obtain ⟨g, hg⟩ := hker
  refine ⟨φ.symm g, (MulAut.congr φ).injective ?_⟩
  simp only [map_mul, map_inv, CFSG.mulAut_congr_conj, MulEquiv.apply_symm_apply]
  exact hg.symm

theorem l2_centralizer_cyclic_odd (hn : 2 ≤ n)
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
    (x : Y) (hx : x ≠ 1) (hodd : Odd (orderOf x)) :
    IsCyclic (Subgroup.centralizer ({x} : Set Y)) ∧
      Odd (Nat.card (Subgroup.centralizer ({x} : Set Y))) := by
  have hcard := card_galoisField_two hn
  obtain ⟨φ⟩ := exists_equiv_psl e
  have hx' : φ x ≠ 1 := fun h => hx (φ.injective (by rw [h, map_one]))
  have hodd' : Odd (orderOf (φ x)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨hcyc, hcardC, -⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer n hn hcard
      (φ x) hx' hodd'
  have hmap := map_centralizer_singleton_eq φ x
  refine ⟨?_, ?_⟩
  · have : IsCyclic ↥((Subgroup.centralizer ({x} : Set Y)).map φ.toMonoidHom) := by
      rw [hmap]
      exact hcyc
    exact (MulEquiv.isCyclic
      (MulEquiv.subgroupMap φ (Subgroup.centralizer ({x} : Set Y)))).mpr this
  · have hc : Nat.card (Subgroup.centralizer ({x} : Set Y)) =
        Nat.card (Subgroup.centralizer ({φ x} : Set (PSL(2, GaloisField 2 n)))) := by
      rw [← hmap, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    have hKeven : Even (Nat.card (GaloisField 2 n)) := by
      rw [hcard]
      exact (Nat.even_pow' (by omega)).mpr even_two
    have hKpos : 1 ≤ Nat.card (GaloisField 2 n) := by
      rw [hcard]
      exact Nat.one_le_two_pow
    rw [hc]
    rcases hcardC with h | h
    · rw [h]
      exact Nat.Even.sub_odd hKpos hKeven odd_one
    · rw [h]
      exact hKeven.add_odd odd_one

theorem l2_normalizer_dichotomy (hn : 2 ≤ n)
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
    (x : Y) (hx : x ≠ 1) (hodd : Odd (orderOf x)) (R : Subgroup Y)
    (hR : R ≤ Subgroup.centralizer ({x} : Set Y)) (hR1 : R ≠ ⊥) {g : Y}
    (hg : g ∈ Subgroup.normalizer (R : Set Y)) :
    g ∈ Subgroup.centralizer ({x} : Set Y) ∨
      ∀ y ∈ Subgroup.centralizer ({x} : Set Y), g * y * g⁻¹ = y⁻¹ := by
  have hcard := card_galoisField_two hn
  obtain ⟨φ⟩ := exists_equiv_psl e
  have hx' : φ x ≠ 1 := fun h => hx (φ.injective (by rw [h, map_one]))
  have hodd' : Odd (orderOf (φ x)) := by rwa [MulEquiv.orderOf_eq]
  have hmap := map_centralizer_singleton_eq φ x
  have hRle : R.map φ.toMonoidHom ≤
      Subgroup.centralizer ({φ x} : Set (PSL(2, GaloisField 2 n))) := by
    rw [← hmap]
    exact Subgroup.map_mono hR
  have hRne : R.map φ.toMonoidHom ≠ ⊥ := fun hbot =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective R φ.injective).mp hbot)
  have hgN : φ g ∈ Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq R φ]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hg
  rcases CFSG.ShultStronglyClosedTI.LinearModel.psl2_even_odd_torus_normalizer_dichotomy n hn
      hcard (φ x) hx' hodd' _ hRle hRne hgN with h | h
  · exact Or.inl ((mem_centralizer_singleton_map φ x g).mpr h)
  · refine Or.inr fun y hy => φ.injective ?_
    have := h (φ y) ((mem_centralizer_singleton_map φ x y).mp hy)
    simpa using this

theorem l2_exists_inverter (hn : 2 ≤ n)
    (e : Y ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)))
    (x : Y) (hx : x ≠ 1) (hodd : Odd (orderOf x)) :
    ∃ w : Y, ∀ y ∈ Subgroup.centralizer ({x} : Set Y), w * y * w⁻¹ = y⁻¹ := by
  have hcard := card_galoisField_two hn
  obtain ⟨φ⟩ := exists_equiv_psl e
  have hx' : φ x ≠ 1 := fun h => hx (φ.injective (by rw [h, map_one]))
  have hodd' : Odd (orderOf (φ x)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨w, -, hwinv, -⟩ :=
    CFSG.ShultStronglyClosedTI.LinearModel.psl2_even_odd_element_torus_normalizer n hn hcard
      (φ x) hx' hodd'
  refine ⟨φ.symm w, fun y hy => φ.injective ?_⟩
  have := hwinv (φ y) ((mem_centralizer_singleton_map φ x y).mp hy)
  simpa using this

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
