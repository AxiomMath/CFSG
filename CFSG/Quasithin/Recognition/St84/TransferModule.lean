module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GroupTheory.AlternatingFive.NaturalModule
public import CFSG.GroupTheory.NormalizerInfCentralizer

import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner
import CFSG.Quasithin.Recognition.F112J2Act
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F1 CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem exists_mul_inv_commutator_mem_pCore
    {L T A : Subgroup G} [Finite ↥L] {c : G}
    (e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5))
    (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hT : IsSylowTwoOf T L) (hA : A ≤ T)
    (hAT : A ⊔ pCoreOf 2 L = T)
    (hcA : ∀ a ∈ A, c * a = a * c) :
    ∃ a ∈ A, ∀ l ∈ L, ⁅c * a⁻¹, l⁆ ∈ pCoreOf 2 L := by
  obtain ⟨e'⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  exact exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot ⟨e.trans e'.symm⟩ hT hA hAT hcL hcA

theorem centralizes_of_twoPow_of_natSec
    {L Q : Subgroup G} [Finite ↥L]
    (e : oTwoQuot ↥L ≃* alternatingGroup (Fin 5))
    (hQL : Q ≤ L)
    (hQn : L ≤ Subgroup.normalizer (Q : Set G))
    (hQab : IsMulCommutative ↥Q)
    (hQcomm : ⁅Q, L⁆ = Q)
    (hcard : (Q ⊓ Subgroup.centralizer (L : Set G)).relIndex Q = 16)
    (hnat : NatSec L (Q ⊓ Subgroup.centralizer (L : Set G)) Q)
    {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1)
    (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcLQ : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    ∀ q ∈ Q, ⁅c, q⁆ = 1 := by
  classical
  let C : Subgroup G := Q ⊓ Subgroup.centralizer (L : Set G)
  have hcardC : C.relIndex Q = 16 := by simpa [C] using hcard
  have hnatC : NatSec L C Q := by simpa [C] using hnat
  have hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQW : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ C := by
    intro x hx y hy
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hQc x hx y hy)]
    exact C.one_mem
  have hLnC : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    exact CFSG.GroupTheory.mem_normalizer_inf_centralizer
      (Subgroup.le_normalizer hl) (hQn hl)
  have hcC : c ∈ Subgroup.normalizer (C : Set G) :=
    CFSG.GroupTheory.mem_normalizer_inf_centralizer hcL hcQ
  have hmod : ∀ q ∈ Q, ⁅c, q⁆ ∈ C :=
    CFSG.GroupTheory.AlternatingFive.commutatorElement_mem_of_fixFree_of_twoPow e hQL hQn
      inf_le_left hLnC hQW hcardC hnatC hc2 hcQ hcC hcLQ
  have hmul : ∀ a ∈ Q, ∀ b ∈ Q, ⁅c, a * b⁆ = ⁅c, a⁆ * ⁅c, b⁆ := by
    intro a ha b hb
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅c, a⁆ a,
      hQc a ha _ (Subgroup.mem_inf.mp (hmod b hb)).1]
    group
  have hconj : ∀ l ∈ L, ∀ y ∈ Q, ⁅c, l * y * l⁻¹⁆ = ⁅c, y⁆ := by
    intro l hl y hy
    obtain ⟨hdQ, hdC⟩ := Subgroup.mem_inf.mp (hmod y hy)
    have hly : l * y * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hl) y).mp hy
    have hld : l * ⁅c, y⁆ = ⁅c, y⁆ * l := Subgroup.mem_centralizer_iff.mp hdC l hl
    have h1 : c * (l * y * l⁻¹) * c⁻¹ =
        ⁅c, l⁆ * (l * ⁅c, y⁆ * y * l⁻¹) * ⁅c, l⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    have h2 : l * ⁅c, y⁆ * y * l⁻¹ = ⁅c, y⁆ * (l * y * l⁻¹) := by
      rw [hld]
      group
    rw [commutatorElement_def, h1, h2, hQc _ (hcLQ l hl) _ (Q.mul_mem hdQ hly)]
    group
  have hLQ : ⁅L, Q⁆ ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.commutator_le]
    intro l hl y hy
    have hly : l * y * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hl) y).mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    calc ⁅c, ⁅l, y⁆⁆ = ⁅c, l * y * l⁻¹ * y⁻¹⁆ := rfl
      _ = ⁅c, y⁆ * ⁅c, y⁻¹⁆ := by
        rw [hmul _ hly _ (Q.inv_mem hy), hconj l hl y hy]
      _ = 1 := by
        rw [← hmul _ hy _ (Q.inv_mem hy), mul_inv_cancel, commutatorElement_one_right]
  rw [Subgroup.commutator_comm, hQcomm] at hLQ
  intro q hq
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hLQ hq)).symm

end CFSG.Quasithin.F112R.St84
