module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne.StrongP

open CFSG.RankThree.PartOne (IsSylowOf omegaOne)

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem exists_conj_le_sylow {P Q : Subgroup H} (hP : IsSylowOf p P ⊤) (hQ : IsPGroup p Q) :
    ∃ g : H, conjSub g Q ≤ P := by
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  let P' : Sylow p H := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q' P'
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have hmem : MulAut.conj g • y ∈ ((g • Q' : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q' : Subgroup H) (hQQ' hy)
  rw [hg] at hmem
  simpa [P', MulAut.smul_def] using hmem

omit [Finite H] [Fact p.Prime] in
theorem conj_mem_omegaOne {P Q : Subgroup H} {g : H} (hgQ : conjSub g Q ≤ P) {x : H} (hxQ : x ∈ Q)
    (hx : x ^ p = 1) : g * x * g⁻¹ ∈ omegaOne p P := by
  refine Subgroup.subset_closure ⟨hgQ ⟨x, hxQ, rfl⟩, ?_⟩
  calc (g * x * g⁻¹) ^ p = g * x ^ p * g⁻¹ := by rw [conj_pow]
    _ = 1 := by rw [hx]; simp

theorem card_le_card_omegaOne {P Q : Subgroup H} (hP : IsSylowOf p P ⊤) (hQ : IsPGroup p Q)
    (hexp : ∀ x ∈ Q, x ^ p = 1) : Nat.card Q ≤ Nat.card (omegaOne p P) := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hP hQ
  have hle : conjSub g Q ≤ omegaOne p P := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_omegaOne hg hx (hexp x hx)
  calc Nat.card Q = Nat.card (conjSub g Q) := card_conjSub.symm
    _ ≤ Nat.card (omegaOne p P) := Subgroup.card_le_of_le hle

theorem not_isMulCommutative_omegaOne {P : Subgroup H} (hP : IsSylowOf p P ⊤) {x y : H}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y ≠ y * x)
    (hQ : IsPGroup p (Subgroup.closure ({x, y} : Set H))) :
    ¬ IsMulCommutative (omegaOne p P) := by
  intro hcomm
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hP hQ
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set H) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set H) := Subgroup.subset_closure (by simp)
  have h1 := conj_mem_omegaOne hg hxQ hx
  have h2 := conj_mem_omegaOne hg hyQ hy
  have h3 := hcomm.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩
  have h4 : g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := congrArg Subtype.val h3
  apply hxy
  have h5 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h4
      _ = g * (y * x) * g⁻¹ := by group
  simpa using h5

end CFSG.RankThree.PartOne.StrongP
