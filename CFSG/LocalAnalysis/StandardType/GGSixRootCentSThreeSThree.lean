module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.StandardType

theorem ggSThree_pow_three_mem {X : Type*} [Group X] [Finite X] {S Q : Subgroup X}
    (hQS : Q ≤ S) (hQn : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hcard : Nat.card S = 3 * Nat.card Q) {s : X} (hs : s ∈ S) : s ^ 3 ∈ Q := by
  haveI hQn' : (Q.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff hQS).mpr fun q s' hq hs' => hQn s' hs' q hq
  have hcardQ' : Nat.card (Q.subgroupOf S) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  have hquot : Nat.card (↥S ⧸ Q.subgroupOf S) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S)
    rw [hcard, hcardQ'] at h
    have hQpos : 0 < Nat.card Q := by
      haveI : Nonempty Q := ⟨1⟩
      exact Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hQpos h).symm
  have hs3 : (QuotientGroup.mk ⟨s, hs⟩ : ↥S ⧸ Q.subgroupOf S) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥S ⧸ Q.subgroupOf S) (x := QuotientGroup.mk ⟨s, hs⟩)
    rwa [hquot] at h
  have hmem : (⟨s, hs⟩ : ↥S) ^ 3 ∈ Q.subgroupOf S := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs3
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem ggSThree_conj_mem {X : Type*} [Group X] [Finite X] {H S R₀ Q : Subgroup X}
    (hSR₀ : S ≤ R₀) (hR₀H : R₀ ≤ H) (hR₀n : (R₀.subgroupOf H).Normal) (hQS : Q ≤ S)
    (hQn : (Q.subgroupOf H).Normal) (hcard : Nat.card S = 3 * Nat.card Q)
    (hiso : ∀ [(Q.subgroupOf R₀).Normal],
      Nonempty (↥R₀ ⧸ Q.subgroupOf R₀ ≃* Equiv.Perm (Fin 3))) :
    ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
  have hSH : S ≤ H := hSR₀.trans hR₀H
  have hQH : Q ≤ H := hQS.trans hSH
  have hQR₀ : Q ≤ R₀ := hQS.trans hSR₀
  haveI hQR₀n : (Q.subgroupOf R₀).Normal :=
    (Subgroup.normal_subgroupOf_iff hQR₀).mpr fun q r hq hr =>
      (Subgroup.normal_subgroupOf_iff hQH).mp hQn q r hq (hR₀H hr)
  obtain ⟨φ⟩ := hiso
  have hcardPerm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hcardQuot : Nat.card (↥R₀ ⧸ Q.subgroupOf R₀) = 6 := by
    rw [Nat.card_congr φ.toEquiv, hcardPerm]
  have hcardR₀ : Nat.card R₀ = 6 * Nat.card Q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf R₀)
    rw [hcardQuot, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR₀).toEquiv] at h
    exact h
  have hcardS' : Nat.card (S.subgroupOf R₀) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR₀).toEquiv
  have hQpos : 0 < Nat.card Q := by
    haveI : Nonempty Q := ⟨1⟩
    exact Nat.card_pos
  have hindex : (S.subgroupOf R₀).index = 2 := by
    have h := Subgroup.card_mul_index (S.subgroupOf R₀)
    rw [hcardS', hcard, hcardR₀] at h
    rw [show 6 * Nat.card Q = (3 * Nat.card Q) * 2 by ring] at h
    exact Nat.mul_left_cancel (Nat.mul_pos (by decide) hQpos) h
  have hQn_point : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q :=
    fun s hs q hq => (Subgroup.normal_subgroupOf_iff hQH).mp hQn q s hq (hSH hs)
  intro h hh s hs
  have hs3 : s ^ 3 ∈ Q := ggSThree_pow_three_mem hQS hQn_point hcard hs
  have hconjR₀ : h * s * h⁻¹ ∈ R₀ :=
    (Subgroup.normal_subgroupOf_iff hR₀H).mp hR₀n s h (hSR₀ hs) hh
  let x : ↥R₀ := ⟨h * s * h⁻¹, hconjR₀⟩
  have hx3 : x ^ 3 ∈ Q.subgroupOf R₀ := by
    rw [Subgroup.mem_subgroupOf]
    have hconjQ : h * s ^ 3 * h⁻¹ ∈ Q :=
      (Subgroup.normal_subgroupOf_iff hQH).mp hQn (s ^ 3) h hs3 hh
    convert hconjQ using 1
    change (h * s * h⁻¹) ^ 3 = h * s ^ 3 * h⁻¹
    exact conj_pow
  have hxS : x ∈ S.subgroupOf R₀ := by
    have hx2 : x ^ 2 ∈ S.subgroupOf R₀ := Subgroup.sq_mem_of_index_two hindex x
    have hx3S : x ^ 3 ∈ S.subgroupOf R₀ := (Subgroup.subgroupOf_mono R₀ hQS) hx3
    have hx : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [hx]
    exact mul_mem hx3S (inv_mem hx2)
  simpa [x] using (Subgroup.mem_subgroupOf.mp hxS)

theorem ggSThree_card_map_dvd {X Z : Type*} [Group X] [Finite X] [Group Z] (π : X →* Z)
    {S Q : Subgroup X} (hQS : Q ≤ S) (hQπ : ∀ q ∈ Q, π q = 1)
    (hcard : Nat.card S = 3 * Nat.card Q) : Nat.card (S.map π) ∣ 3 := by
  let f : ↥S →* Z := π.comp S.subtype
  have hrange : f.range = S.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Q.subgroupOf S ≤ f.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    change π (q : X) = 1
    exact hQπ (q : X) (Subgroup.mem_subgroupOf.mp hq)
  have hcardK : Nat.card (Q.subgroupOf S) ∣ Nat.card f.ker := Subgroup.card_dvd_of_le hker
  have hcardQ' : Nat.card (Q.subgroupOf S) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  have hQpos : 0 < Nat.card Q := by
    haveI : Nonempty Q := ⟨1⟩
    exact Nat.card_pos
  obtain ⟨k, hk⟩ := hcardK
  have h3 : k * Nat.card f.range = 3 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hk, hcardQ', hcard, mul_assoc, mul_comm 3 (Nat.card Q)] at h
    exact Nat.mul_left_cancel hQpos h
  rw [← hrange]
  exact ⟨k, by rw [mul_comm]; exact h3.symm⟩

theorem ggSThree_isSolvable_of_card_dvd_three {Z : Type*} [Group Z] [Finite Z] (A : Subgroup Z)
    (h : Nat.card A ∣ 3) : Group.IsSolvable A := by
  haveI : IsCyclic A := isCyclic_of_card_dvd_prime h
  infer_instance

end CFSG.StandardType
