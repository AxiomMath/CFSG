module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN1
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ] [Finite Δ]

theorem exists_mem_cos {B P : Subgroup Δ} (hB : B ≤ P) (us : List Δ) (r : Δ) (hr : r ∈ P)
    (hU : ∀ u ∈ us, u ∈ B) (hrB : r ∉ B) (hidx : B.relIndex P = us.length + 1)
    (hpw : us.Pairwise fun u u' => r⁻¹ * (u * u'⁻¹) * r ∉ B) :
    ∀ x ∈ P, x ∈ B ∨ ∃ v ∈ us, ∃ b ∈ B, v * x = r * b := by
  classical
  have hmem : ∀ i : Fin us.length, (us.get i)⁻¹ * r ∈ P := fun i =>
    P.mul_mem (P.inv_mem (hB (hU _ (List.get_mem us i)))) hr
  let g : Fin (us.length + 1) → P ⧸ B.subgroupOf P :=
    Fin.cases (QuotientGroup.mk 1) (fun i => QuotientGroup.mk ⟨(us.get i)⁻¹ * r, hmem i⟩)
  have hcard : Nat.card (P ⧸ B.subgroupOf P) = us.length + 1 := hidx
  have hinj : Function.Injective g := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        exfalso
        have h := QuotientGroup.eq.1 hij
        rw [Subgroup.mem_subgroupOf] at h
        have h' : (us.get j)⁻¹ * r ∈ B := by simpa using h
        have : r ∈ B := by simpa using B.mul_mem (hU _ (List.get_mem us j)) h'
        exact hrB this
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        exfalso
        have h := QuotientGroup.eq.1 hij
        rw [Subgroup.mem_subgroupOf] at h
        have h' : (us.get i)⁻¹ * r ∈ B := by simpa using B.inv_mem h
        have : r ∈ B := by simpa using B.mul_mem (hU _ (List.get_mem us i)) h'
        exact hrB this
      | succ j =>
        by_contra hne
        have hne' : i ≠ j := fun h => hne (by rw [h])
        have h := QuotientGroup.eq.1 hij
        rw [Subgroup.mem_subgroupOf] at h
        have hpw' := List.pairwise_iff_get.1 hpw
        have hval : ((us.get i)⁻¹ * r)⁻¹ * ((us.get j)⁻¹ * r) =
            r⁻¹ * (us.get i * (us.get j)⁻¹) * r := by group
        have h1 : ((us.get i)⁻¹ * r)⁻¹ * ((us.get j)⁻¹ * r) ∈ B := h
        rcases lt_or_gt_of_ne hne' with hlt | hgt
        · exact hpw' i j hlt (by rw [← hval]; exact h1)
        · refine hpw' j i hgt ?_
          have h2 := B.inv_mem h1
          have : (((us.get i)⁻¹ * r)⁻¹ * ((us.get j)⁻¹ * r))⁻¹ =
              r⁻¹ * (us.get j * (us.get i)⁻¹) * r := by group
          rw [← this]
          exact h2
  have hsurj := (hinj.bijective_of_nat_card_le (by simp [hcard])).2
  intro x hx
  obtain ⟨i, hi⟩ := hsurj (QuotientGroup.mk ⟨x, hx⟩)
  induction i using Fin.cases with
  | zero =>
    left
    have h := QuotientGroup.eq.1 hi
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  | succ j =>
    right
    have h := QuotientGroup.eq.1 hi
    rw [Subgroup.mem_subgroupOf] at h
    have h' : ((us.get j)⁻¹ * r)⁻¹ * x ∈ B := h
    refine ⟨us.get j, List.get_mem us j, r⁻¹ * (us.get j * x), ?_, ?_⟩
    · simpa [mul_assoc] using h'
    · group

end CFSG.Quasithin.H13.F431.U42Aut
