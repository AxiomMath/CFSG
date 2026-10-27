module

public import CFSG.RankThree.PartOne.S9.QD32.Basic

public section

namespace CFSG.RankThree.PartOne.QD32Facts

open CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY Subgroup
open scoped commutatorElement Pointwise

attribute [local instance] qdFintypeD

@[expose] def repQD : Fin 5 → QuaternionGroup 2 × QuaternionDihedralD := ![
  (1, ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩),
  (1, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩),
  (QuaternionGroup.a 1, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩),
  (QuaternionGroup.xa 0, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩),
  (QuaternionGroup.a 1 * QuaternionGroup.xa 0, ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 0⟩)]

@[expose] def invRep (k : Fin 5) : QD32 := (repQD k : QD32)

theorem invRep_ne_one (k : Fin 5) : invRep k ≠ 1 := by
  rw [invRep, ← QuotientGroup.mk_one, Ne, qd32_mk_eq_mk_iff]
  revert k
  decide +kernel

theorem invRep_sq (k : Fin 5) : invRep k ^ 2 = 1 := by
  rw [invRep, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff]
  revert k
  decide +kernel

theorem invRep_ne_qd32Z (k : Fin 5) : invRep k ≠ qd32Z := by
  rw [invRep, qd32Z_eq, Ne, qd32_mk_eq_mk_iff]
  revert k
  decide +kernel

theorem exists_invRep_of_involution {x : QD32} (hx : x ^ 2 = 1) (h1 : x ≠ 1) (hz : x ≠ qd32Z) :
    ∃ k : Fin 5, x = invRep k ∨ x = invRep k * qd32Z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have key : ∀ g : QuaternionGroup 2 × QuaternionDihedralD,
      qdSameImage (g ^ 2) 1 → ¬ qdSameImage g 1 →
      ¬ qdSameImage g (QuaternionGroup.a 2, 1) →
      ∃ k : Fin 5, qdSameImage g (repQD k) ∨
        qdSameImage g (repQD k * (QuaternionGroup.a 2, 1)) := by
    decide +kernel
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one, qd32_mk_eq_mk_iff] at hx
  rw [← QuotientGroup.mk_one, Ne, qd32_mk_eq_mk_iff] at h1
  rw [qd32Z_eq, Ne, qd32_mk_eq_mk_iff] at hz
  obtain ⟨k, hk⟩ := key g hx h1 hz
  refine ⟨k, ?_⟩
  rw [qd32Z_eq, invRep, ← QuotientGroup.mk_mul]
  rcases hk with hk | hk
  · left
    exact (qd32_mk_eq_mk_iff _ _).mpr hk
  · right
    exact (qd32_mk_eq_mk_iff _ _).mpr hk

@[expose] def clsSet (k : Fin 5) : Set QD32 := {invRep k, invRep k * qd32Z}

theorem exists_cls_of_aut (α : MulAut QD32) (k : Fin 5) :
    ∃ l : Fin 5, α (invRep k) ∈ clsSet l := by
  have hsq : (α (invRep k)) ^ 2 = 1 := by
    rw [← map_pow, invRep_sq, map_one]
  have h1 : α (invRep k) ≠ 1 := fun h => invRep_ne_one k (α.injective (h.trans (map_one α).symm))
  have hz : α (invRep k) ≠ qd32Z := fun h =>
    invRep_ne_qd32Z k (α.injective (h.trans (aut_qd32Z α).symm))
  obtain ⟨l, hl⟩ := exists_invRep_of_involution hsq h1 hz
  exact ⟨l, hl⟩

@[expose] def clsFamily : SubMulAction (MulAut QD32) (Set QD32) where
  carrier := Set.range clsSet
  smul_mem' := by
    rintro α _ ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := exists_cls_of_aut α k
    refine ⟨l, ?_⟩
    have hz2 : ∀ x : QD32, x * qd32Z * qd32Z = x := fun x => by
      rw [mul_assoc, qd32Z_mul_self, mul_one]
    have e : α • clsSet k = {α (invRep k), α (invRep k) * qd32Z} := by
      simp [clsSet, Set.smul_set_insert, Set.smul_set_singleton, MulAut.smul_def, aut_qd32Z]
    rw [e]
    ext x
    simp only [clsSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hl ⊢
    rcases hl with hl | hl
    · rw [hl]
    · rw [hl, hz2]
      exact or_comm

theorem card_clsFamily_le : Nat.card clsFamily ≤ 5 := by
  have h : Nat.card (Set.range clsSet) ≤ Nat.card (Fin 5) :=
    Nat.card_le_card_of_surjective (Set.rangeFactorization clsSet) Set.rangeFactorization_surjective
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h
  exact h

theorem qd32Gens_zero : qd32Gens 0 = invRep 2 := by
  show qd32I * qd32U = invRep 2
  rw [qd32I, qd32U, invRep, ← QuotientGroup.mk_mul, qd32_mk_eq_mk_iff]
  decide

theorem qd32Gens_one : qd32Gens 1 = invRep 3 := by
  show qd32J * qd32U = invRep 3
  rw [qd32J, qd32U, invRep, ← QuotientGroup.mk_mul, qd32_mk_eq_mk_iff]
  decide

theorem qd32Gens_two : qd32Gens 2 = invRep 4 := by
  show qd32I * qd32J * qd32U = invRep 4
  rw [qd32I, qd32J, qd32U, invRep, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    qd32_mk_eq_mk_iff]
  decide

theorem qd32Gens_three : qd32Gens 3 = invRep 0 := by
  show qd32V = invRep 0
  rw [qd32V, invRep, qd32_mk_eq_mk_iff]
  decide

theorem qd32Gens_eq (i : Fin 4) : qd32Gens i = invRep (![2, 3, 4, 0] i) := by
  fin_cases i
  exacts [qd32Gens_zero, qd32Gens_one, qd32Gens_two, qd32Gens_three]

@[expose] noncomputable def clsPerm : MulAut QD32 →* Equiv.Perm clsFamily :=
  MulAction.toPermHom (MulAut QD32) clsFamily

theorem mem_cls_of_mem_ker {α : MulAut QD32} (hα : α ∈ clsPerm.ker) (k : Fin 5) :
    α (invRep k) = invRep k ∨ α (invRep k) = invRep k * qd32Z := by
  have hk : clsSet k ∈ clsFamily := ⟨k, rfl⟩
  have h : α • (⟨clsSet k, hk⟩ : clsFamily) = ⟨clsSet k, hk⟩ := by
    have := congrArg (fun σ : Equiv.Perm clsFamily => σ ⟨clsSet k, hk⟩) (MonoidHom.mem_ker.mp hα)
    simpa [clsPerm, MulAction.toPermHom_apply] using this
  have h2 : α • clsSet k = clsSet k := congrArg Subtype.val h
  have h3 : α (invRep k) ∈ α • clsSet k := ⟨invRep k, Or.inl rfl, rfl⟩
  rw [h2] at h3
  exact h3

theorem card_ker_clsPerm_dvd : Nat.card clsPerm.ker ∣ 2 ^ 4 := by
  refine card_dvd_two_pow_of_displacement (z := qd32Z) orderOf_qd32Z qd32Gens
    closure_range_qd32Gens clsPerm.ker (fun α hα => ⟨aut_qd32Z α, fun i => ?_⟩)
  rw [qd32Gens_eq]
  rcases mem_cls_of_mem_ker hα (![2, 3, 4, 0] i) with h | h
  · rw [h, inv_mul_cancel]
    exact one_mem _
  · rw [h, inv_mul_cancel_left]
    exact mem_zpowers _

theorem card_mulAut_QD32_dvd : Nat.card (MulAut QD32) ∣ 2 ^ 7 * 3 * 5 := by
  have h := Subgroup.card_ker_mul_card_range clsPerm
  have hrange : Nat.card clsPerm.range ∣ 120 := by
    have h1 := Subgroup.card_subgroup_dvd_card clsPerm.range
    rw [Nat.card_perm] at h1
    exact h1.trans (Nat.factorial_dvd_factorial card_clsFamily_le)
  rw [← h, show 2 ^ 7 * 3 * 5 = 2 ^ 4 * 120 by norm_num]
  exact Nat.mul_dvd_mul card_ker_clsPerm_dvd hrange

end CFSG.RankThree.PartOne.QD32Facts
