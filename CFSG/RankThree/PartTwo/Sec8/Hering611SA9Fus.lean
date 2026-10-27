module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Perf
public import CFSG.RankThree.PartTwo.Sec8.Hering611SA9Syl

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

theorem a9fW0_facts :
    (∀ y ∈ Subgroup.zpowers a9fT0 ⊔ a9fE0, a9fW0 * y * a9fW0⁻¹ ∈ Subgroup.zpowers a9fT0 ⊔ a9fE0) ∧
      a9fW0 * a9fT0 * a9fW0⁻¹ ∈ a9fE0 ∧ a9fW0 * a9fT0 * a9fW0⁻¹ ≠ 1 := by
  have h1 : a9fW0 * a9fT0 * a9fW0⁻¹ = a9fT1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    decide
  have h2 : a9fW0 * a9fT1 * a9fW0⁻¹ = a9fT0 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    decide
  have h3 : a9fW0 * a9fT2 * a9fW0⁻¹ = a9fT2⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    decide
  have hT1 : a9fT1 ≠ 1 := by decide
  have ha9T1 : a9fT1 ∈ a9fE0 := by
    show a9fT1 ∈ Subgroup.zpowers a9fT1 ⊔ Subgroup.zpowers a9fT2
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a9fT1)
  have ha9T2 : a9fT2 ∈ a9fE0 := by
    show a9fT2 ∈ Subgroup.zpowers a9fT1 ⊔ Subgroup.zpowers a9fT2
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a9fT2)
  have hD0 : Subgroup.zpowers a9fT0 ⊔ a9fE0 ≤
      (Subgroup.zpowers a9fT0 ⊔ a9fE0).comap (MulAut.conj a9fW0).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_comap]
      show a9fW0 * a9fT0 * a9fW0⁻¹ ∈ _
      rw [h1]
      exact Subgroup.mem_sup_right ha9T1
    · show Subgroup.zpowers a9fT1 ⊔ Subgroup.zpowers a9fT2 ≤ _
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        show a9fW0 * a9fT1 * a9fW0⁻¹ ∈ _
        rw [h2]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a9fT0)
      · rw [Subgroup.mem_comap]
        show a9fW0 * a9fT2 * a9fW0⁻¹ ∈ _
        rw [h3]
        exact Subgroup.inv_mem _ (Subgroup.mem_sup_right ha9T2)
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · have hy' := hD0 hy
    rw [Subgroup.mem_comap] at hy'
    exact hy'
  · rw [h1]
    exact ha9T1
  · rw [h1]
    exact hT1

theorem a9_fusion_std {P E : Subgroup (alternatingGroup (Fin 9))} (hP : Group.IsPerfect P)
    (hPc : ∀ p ∈ P, p * a9fT0 = a9fT0 * p) (hEP : E ≤ P) (hE9 : Nat.card E = 9) :
    ∃ w : alternatingGroup (Fin 9),
      (∀ y ∈ Subgroup.zpowers a9fT0 ⊔ E, w * y * w⁻¹ ∈ Subgroup.zpowers a9fT0 ⊔ E) ∧
        w * a9fT0 * w⁻¹ ∈ E ∧ w * a9fT0 * w⁻¹ ≠ 1 := by
  have hEA : E ≤ a9fAlt6 := hEP.trans (mem_a9Alt6_of_perfect hP hPc)
  obtain ⟨g, hgA, hEg⟩ := exists_conj_a9E0 hE9 hEA
  have hgsupp : (g : Perm (Fin 9)).support ⊆ a9fS :=
    (alternatingGroup.mem_range_ofSubtype_iff a9fS g).mp hgA
  have key2 : ∀ x : Fin 9, x ∈ a9fS → (a9fT0 : Perm (Fin 9)) x = x := by decide
  have hdisj : Equiv.Perm.Disjoint (g : Perm (Fin 9)) (a9fT0 : Perm (Fin 9)) := by
    intro x
    by_cases hx : x ∈ a9fS
    · exact Or.inr (key2 x hx)
    · refine Or.inl ?_
      by_contra hne
      exact hx (hgsupp (Equiv.Perm.mem_support.mpr hne))
  have hcomm : (g : Perm (Fin 9)) * (a9fT0 : Perm (Fin 9)) = (a9fT0 : Perm (Fin 9)) * g :=
    (Equiv.Perm.Disjoint.commute hdisj).eq
  have hgt : g * a9fT0 = a9fT0 * g := Subtype.ext (by simp only [Subgroup.coe_mul]; exact hcomm)
  have hgt' : g⁻¹ * a9fT0 * g = a9fT0 := by
    calc g⁻¹ * a9fT0 * g = g⁻¹ * (a9fT0 * g) := by group
      _ = g⁻¹ * (g * a9fT0) := by rw [hgt]
      _ = a9fT0 := by group
  have hfix : (MulAut.conj g).toMonoidHom a9fT0 = a9fT0 := by
    show g * a9fT0 * g⁻¹ = a9fT0
    calc g * a9fT0 * g⁻¹ = a9fT0 * g * g⁻¹ := by rw [hgt]
      _ = a9fT0 := by group
  have hD : Subgroup.zpowers a9fT0 ⊔ E =
      (Subgroup.zpowers a9fT0 ⊔ a9fE0).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfix, hEg]
  have hconjW : g * a9fW0 * g⁻¹ * a9fT0 * (g * a9fW0 * g⁻¹)⁻¹ =
      g * (a9fW0 * a9fT0 * a9fW0⁻¹) * g⁻¹ := by
    calc g * a9fW0 * g⁻¹ * a9fT0 * (g * a9fW0 * g⁻¹)⁻¹
        = g * a9fW0 * (g⁻¹ * a9fT0 * g) * a9fW0⁻¹ * g⁻¹ := by group
      _ = g * (a9fW0 * a9fT0 * a9fW0⁻¹) * g⁻¹ := by rw [hgt']; group
  have hmemE : g * a9fW0 * g⁻¹ * a9fT0 * (g * a9fW0 * g⁻¹)⁻¹ ∈ E := by
    rw [hEg, hconjW]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom a9fW0_facts.2.1
  refine ⟨g * a9fW0 * g⁻¹, ?_, hmemE, ?_⟩
  · intro y hy
    rw [hD] at hy ⊢
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨a9fW0 * y₀ * a9fW0⁻¹, a9fW0_facts.1 y₀ hy₀, ?_⟩
    show g * (a9fW0 * y₀ * a9fW0⁻¹) * g⁻¹ = g * a9fW0 * g⁻¹ * (g * y₀ * g⁻¹) * (g * a9fW0 * g⁻¹)⁻¹
    group
  · rw [hconjW]
    intro h
    apply a9fW0_facts.2.2
    calc a9fW0 * a9fT0 * a9fW0⁻¹ = g⁻¹ * (g * (a9fW0 * a9fT0 * a9fW0⁻¹) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

end CFSG.RankThree.PartTwo.Sec8.Hering611
