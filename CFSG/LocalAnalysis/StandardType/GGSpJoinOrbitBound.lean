module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open

theorem ncard_orbit_le_of_stabilizer {M α : Type*} [Group M] [MulAction M α] [Finite M]
    {A H : Subgroup M} (hHA : H ≤ A) (y : α) (hH : ∀ h ∈ H, h • y = y) {c k : ℕ} (hc : 0 < c)
    (hcH : c ≤ Nat.card H) (hA : Nat.card A ≤ c * k) :
    Set.ncard ((fun a : M => a • y) '' (A : Set M)) ≤ k := by
  classical
  have horbit : (fun a : M => a • y) '' (A : Set M) = MulAction.orbit A y := by
    ext z
    rw [Set.mem_image, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, by rw [Subgroup.smul_def]⟩
    · rintro ⟨a, hz⟩
      refine ⟨(a : M), a.2, ?_⟩
      rw [← Subgroup.smul_def]
      exact hz
  rw [horbit, ← Nat.card_coe_set_eq]
  have hstab : c ≤ Nat.card (MulAction.stabilizer A y) := by
    have hsub : H.subgroupOf A ≤ MulAction.stabilizer A y := by
      intro h hh
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      exact hH (h : M) (Subgroup.mem_subgroupOf.mp hh)
    calc c ≤ Nat.card H := hcH
      _ = Nat.card (H.subgroupOf A) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv).symm
      _ ≤ Nat.card (MulAction.stabilizer A y) := Subgroup.card_le_of_le hsub
  have hos : Nat.card (MulAction.orbit A y) * Nat.card (MulAction.stabilizer A y) =
      Nat.card A := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A y)
  have hchain : c * Nat.card (MulAction.orbit A y) ≤ c * k := by
    calc c * Nat.card (MulAction.orbit A y)
        = Nat.card (MulAction.orbit A y) * c := Nat.mul_comm _ _
      _ ≤ Nat.card (MulAction.orbit A y) * Nat.card (MulAction.stabilizer A y) :=
          Nat.mul_le_mul_left _ hstab
      _ = Nat.card A := hos
      _ ≤ c * k := hA
  exact Nat.le_of_mul_le_mul_left hchain hc

theorem ncard_automizer_orbit_le {G : Type} [Group G] [Finite G] {p n : ℕ} {Bs : Subgroup G}
    {A H : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p (CoxeterMatrix.B (n + 1)) A) (hHA : H ≤ A)
    {y : G} (hy : y ∈ Bs) (hfix : ∀ ψ ∈ H, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y)
    (hH : 2 ^ n * n.factorial ≤ Nat.card H) :
    Set.ncard {z : G | ∃ ψ ∈ A, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = z} ≤ 2 * n + 2 := by
  obtain ⟨e, -⟩ := hA
  have hcardA : Nat.card A ≤ 2 ^ n * n.factorial * (2 * n + 2) := by
    calc Nat.card A = Nat.card (CoxeterMatrix.B (n + 1)).Group :=
          (Nat.card_congr e.toEquiv).symm
      _ ≤ 2 ^ (n + 1) * (n + 1).factorial := card_coxeterB_le (n + 1)
      _ = 2 ^ n * n.factorial * (2 * n + 2) := by
          rw [pow_succ, Nat.factorial_succ]
          ring
  have hfix' : ∀ h ∈ H, h • (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ := by
    intro ψ hψ
    rw [MulAut.smul_def]
    exact Subtype.ext (hfix ψ hψ)
  have hbound : Set.ncard ((fun a : MulAut ↥Bs => a • (⟨y, hy⟩ : ↥Bs)) ''
      (A : Set (MulAut ↥Bs))) ≤ 2 * n + 2 :=
    ncard_orbit_le_of_stabilizer (M := MulAut ↥Bs) (α := ↥Bs) hHA (⟨y, hy⟩ : ↥Bs) hfix'
      (Nat.mul_pos (pow_pos (by norm_num) n) (Nat.factorial_pos n)) hH hcardA
  set S : Set ↥Bs :=
    (fun a : MulAut ↥Bs => a • (⟨y, hy⟩ : ↥Bs)) '' (A : Set (MulAut ↥Bs)) with hS
  have hT : {z : G | ∃ ψ ∈ A, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = z} = Subtype.val '' S := by
    ext z
    constructor
    · rintro ⟨ψ, hψ, hz⟩
      exact ⟨ψ • (⟨y, hy⟩ : ↥Bs), ⟨ψ, hψ, rfl⟩, by simpa [MulAut.smul_def] using hz⟩
    · rintro ⟨w, ⟨ψ, hψ, rfl⟩, hz⟩
      exact ⟨ψ, hψ, by simpa [MulAut.smul_def] using hz⟩
  calc Set.ncard {z : G | ∃ ψ ∈ A, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = z}
      = Set.ncard (Subtype.val '' S) := by rw [hT]
    _ ≤ Set.ncard S := Set.ncard_image_le
    _ ≤ 2 * n + 2 := hbound

theorem ggAutomizer_fixes_of_mem_centralizer {G : Type} [Group G] {K Bs : Subgroup G} {y : G}
    (hy : y ∈ Bs) (hyK : y ∈ Subgroup.centralizer (K : Set G)) :
    ∀ ψ ∈ ggAutomizer K Bs, ((ψ ⟨y, hy⟩ : ↥Bs) : G) = y := by
  intro ψ hψ
  have hmem : ψ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs) := by
    rw [ggAutomizer] at hψ
    refine (Subgroup.closure_le (K :=
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs))).mpr ?_ hψ
    intro φ hφ
    change φ ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    apply Subtype.ext
    change ((φ ⟨y, hy⟩ : ↥Bs) : G) = y
    obtain ⟨g, hgK, _hgnorm, hφg⟩ := hφ
    rw [hφg]
    change g * y * g⁻¹ = y
    rw [Subgroup.mem_centralizer_iff.mp hyK g hgK]
    group
  rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
  exact congrArg (fun w : ↥Bs => (w : G)) hmem

end CFSG.StandardType.SpJoin
