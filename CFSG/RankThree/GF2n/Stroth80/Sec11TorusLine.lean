module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

namespace IsLBTorus

private theorem conj_pow_mem_LB {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B) {l : G}
    (hl : l ∈ LB M Q B) (i : ℕ) : y ^ i * l * (y ^ i)⁻¹ ∈ LB M Q B :=
  hc.conj_mem_LB_of_mem_normalizer (M.pow_mem hy.mem_M i) (Subgroup.pow_mem _ hy.normalizes_B i)
    hl

private noncomputable def torusLineElt {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (i : ℕ) : Mbar M Q :=
  QuotientGroup.mk' (Q.subgroupOf M)
    ⟨y ^ i * l * (y ^ i)⁻¹, hc.LB_le_M (hy.conj_pow_mem_LB hc hl i)⟩

omit [Finite G] in
private theorem mk_eq_mk_iff_mul_inv_mem {x x' : ↥M} :
    QuotientGroup.mk' (Q.subgroupOf M) x = QuotientGroup.mk' (Q.subgroupOf M) x' ↔
      (x : G) * (x' : G)⁻¹ ∈ Q := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
    Subgroup.mem_subgroupOf, Subgroup.coe_div, div_eq_mul_inv]

omit [Finite G] in
private theorem mk_eq_one_iff_mem {x : ↥M} :
    QuotientGroup.mk' (Q.subgroupOf M) x = 1 ↔ (x : G) ∈ Q := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem torusLineElt_ne_one {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (hlQ : l ∉ Q) (i : ℕ) : hy.torusLineElt hc hl i ≠ 1 := by
  intro h
  rw [torusLineElt, mk_eq_one_iff_mem] at h
  apply hlQ
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (hc.hyp.Q_normal.2 (M.inv_mem (M.pow_mem hy.mem_M i))) _).mp h
  have e : (y ^ i)⁻¹ * (y ^ i * l * (y ^ i)⁻¹) * ((y ^ i)⁻¹)⁻¹ = l := by group
  rwa [e] at h1

private theorem torusLineElt_eq_of_le {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (hlQ : l ∉ Q) {i j : ℕ} (hij : i ≤ j)
    (hj : j < Nat.card Z - 1) (h : hy.torusLineElt hc hl i = hy.torusLineElt hc hl j) :
    i = j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, add_zero]
  exfalso
  apply hlQ
  refine hy.fpf k hk (by omega) l hl ?_
  rw [torusLineElt, torusLineElt, mk_eq_mk_iff_mul_inv_mem] at h
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (hc.hyp.Q_normal.2 (M.inv_mem (M.pow_mem hy.mem_M i))) _).mp h
  have e : (y ^ i)⁻¹ * (y ^ i * l * (y ^ i)⁻¹ * (y ^ (i + k) * l * (y ^ (i + k))⁻¹)⁻¹) *
      ((y ^ i)⁻¹)⁻¹ = (y ^ k * l * (y ^ k)⁻¹ * l⁻¹)⁻¹ := by group
  rw [e] at h1
  simpa using Q.inv_mem h1

private theorem torusLineElt_injOn {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (hlQ : l ∉ Q) :
    Set.InjOn (hy.torusLineElt hc hl) ↑(Finset.range (Nat.card Z - 1)) := by
  intro i hi j hj h
  have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
  have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
  rcases le_total i j with hij | hji
  · exact hy.torusLineElt_eq_of_le hc hl hlQ hij hj' h
  · exact (hy.torusLineElt_eq_of_le hc hl hlQ hji hi' h.symm).symm

private theorem torusLineElt_mul {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B) {l : G}
    (hl : l ∈ LB M Q B) (i j : ℕ) :
    hy.torusLineElt hc hl i * hy.torusLineElt hc hl j = 1 ∨ ∃ k < Nat.card Z - 1,
      hy.torusLineElt hc hl k = hy.torusLineElt hc hl i * hy.torusLineElt hc hl j := by
  rcases hy.line_closed l hl i j with h | ⟨k, hk, h⟩
  · left
    rw [torusLineElt, torusLineElt, ← map_mul, mk_eq_one_iff_mem]
    exact h
  · right
    refine ⟨k, hk, ?_⟩
    rw [torusLineElt, torusLineElt, torusLineElt, ← map_mul, eq_comm, mk_eq_mk_iff_mul_inv_mem]
    exact h

private theorem torusLineElt_inv {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B) {l : G}
    (hl : l ∈ LB M Q B) (i : ℕ) : (hy.torusLineElt hc hl i)⁻¹ = hy.torusLineElt hc hl i := by
  rw [inv_eq_iff_mul_eq_one, torusLineElt, ← map_mul, mk_eq_one_iff_mem]
  have h := hc.sq_mem_Q_of_mem_LB (hy.conj_pow_mem_LB hc hl i)
  rwa [pow_two] at h

open _root_.Classical in
private noncomputable def torusLineFinset {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) : Finset (Mbar M Q) :=
  insert 1 ((Finset.range (Nat.card Z - 1)).image (hy.torusLineElt hc hl))

private theorem mem_torusLineFinset {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (u : Mbar M Q) :
    u ∈ hy.torusLineFinset hc hl ↔ u = 1 ∨ ∃ i < Nat.card Z - 1, hy.torusLineElt hc hl i = u := by
  classical
  simp only [torusLineFinset, Finset.mem_insert, Finset.mem_image, Finset.mem_range]

private theorem torusLineFinset_mul_mem {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) {a b : Mbar M Q} (ha : a ∈ hy.torusLineFinset hc hl)
    (hb : b ∈ hy.torusLineFinset hc hl) : a * b ∈ hy.torusLineFinset hc hl := by
  rw [mem_torusLineFinset] at ha hb ⊢
  rcases ha with rfl | ⟨i, hi, rfl⟩
  · rwa [one_mul]
  rcases hb with rfl | ⟨j, -, rfl⟩
  · rw [mul_one]
    exact Or.inr ⟨i, hi, rfl⟩
  rcases hy.torusLineElt_mul hc hl i j with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk, h⟩

private noncomputable def torusLine {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) : Subgroup (Mbar M Q) where
  carrier := ↑(hy.torusLineFinset hc hl)
  mul_mem' ha hb := hy.torusLineFinset_mul_mem hc hl ha hb
  one_mem' := (hy.mem_torusLineFinset hc hl 1).mpr (Or.inl rfl)
  inv_mem' {a} ha := by
    have ha' : a ∈ hy.torusLineFinset hc hl := ha
    rcases (hy.mem_torusLineFinset hc hl a).mp ha' with rfl | ⟨i, -, rfl⟩
    · rw [inv_one]
      exact ha
    · rw [hy.torusLineElt_inv hc hl i]
      exact ha

private theorem natCard_torusLine {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B)
    {l : G} (hl : l ∈ LB M Q B) (hlQ : l ∉ Q) : Nat.card (hy.torusLine hc hl) = Nat.card Z := by
  classical
  have hq := hc.hyp.q4
  have h1 : (1 : Mbar M Q) ∉ (Finset.range (Nat.card Z - 1)).image (hy.torusLineElt hc hl) := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun i _ h => hy.torusLineElt_ne_one hc hl hlQ i h
  rw [show Nat.card (hy.torusLine hc hl) = (hy.torusLineFinset hc hl).card from
    Nat.card_eq_finsetCard (hy.torusLineFinset hc hl), torusLineFinset,
    Finset.card_insert_of_notMem h1, Finset.card_image_of_injOn (hy.torusLineElt_injOn hc hl hlQ),
    Finset.card_range]
  omega

theorem exists_lbLine {y : G} (hy : IsLBTorus M Q Z B y) (hc : Ctx M Q Z B) {l : G}
    (hl : l ∈ LB M Q B) (hlQ : l ∉ Q) :
    ∃ U : Subgroup (Mbar M Q), U ≤ bar M Q (LB M Q B) ∧ Nat.card U = Nat.card Z ∧
      (∀ m : ↥M, (m : G) = l → QuotientGroup.mk' (Q.subgroupOf M) m ∈ U) ∧
      ∀ u ∈ U, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M,
        (m : G) = y ^ i * l * (y ^ i)⁻¹ ∧ u = QuotientGroup.mk' (Q.subgroupOf M) m := by
  have hn : 0 < Nat.card Z - 1 := by
    have := hc.hyp.q4
    omega
  refine ⟨hy.torusLine hc hl, fun u hu => ?_, hy.natCard_torusLine hc hl hlQ, fun m hm => ?_,
    fun u hu hu1 => ?_⟩
  · rcases (hy.mem_torusLineFinset hc hl u).mp hu with rfl | ⟨i, -, rfl⟩
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr (hy.conj_pow_mem_LB hc hl i), rfl⟩
  · refine (hy.mem_torusLineFinset hc hl _).mpr (Or.inr ⟨0, hn, ?_⟩)
    rw [torusLineElt]
    congr 1
    exact Subtype.ext (by simp [hm])
  · rcases (hy.mem_torusLineFinset hc hl u).mp hu with rfl | ⟨i, hi, rfl⟩
    · exact absurd rfl hu1
    · exact ⟨i, hi, _, rfl, rfl⟩

end IsLBTorus

end CFSG.RankThree.GF2n.Stroth80
