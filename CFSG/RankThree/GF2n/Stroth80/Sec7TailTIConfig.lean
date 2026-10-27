module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

variable {X : Type*} [Group X]

@[expose] def NormIn (H V : Subgroup X) : Subgroup X := H ⊓ normalizer (V : Set X)

theorem mem_NormIn {H V : Subgroup X} {x : X} :
    x ∈ NormIn H V ↔ x ∈ H ∧ x ∈ normalizer (V : Set X) := Iff.rfl

structure TIConfig (H V N : Subgroup X) : Prop where
  V_le : V ≤ H
  V_ne_bot : V ≠ ⊥
  V_pgroup : IsPGroup 2 V
  V_comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  ti : ∀ g : X, ∀ x ∈ V, x ≠ 1 → g * x * g⁻¹ ∈ V → g ∈ normalizer (V : Set X)
  N_le : N ≤ NormIn H V
  N_normal : ∀ k ∈ NormIn H V, k ∈ normalizer (N : Set X)
  N_pgroup : IsPGroup 2 N
  pcore_le : ∀ P : Subgroup X, P ≤ NormIn H V → (∀ k ∈ NormIn H V, k ∈ normalizer (P : Set X)) →
    IsPGroup 2 P → P ≤ N
  cent_le : ∀ k ∈ NormIn H V, (∀ n ∈ N, k * n = n * k) → k ∈ N
  VN_comm : ∀ x ∈ V, ∀ n ∈ N, x * n = n * x
  maxAb : ∀ A : Subgroup X, V ≤ A → A ≤ NormIn H V →
    (∀ k ∈ NormIn H V, k ∈ normalizer (A : Set X)) → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → A = V

namespace TIConfig

variable [Finite X] {H V N : Subgroup X}

@[expose] def cenIn (P : Subgroup X) : Subgroup X := (Subgroup.center P).map P.subtype

theorem mem_cenIn {P : Subgroup X} {z : X} :
    z ∈ cenIn P ↔ z ∈ P ∧ ∀ s ∈ P, z * s = s * z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hzP, hz⟩
    refine ⟨⟨z, hzP⟩, Subgroup.mem_center_iff.mpr fun s => ?_, rfl⟩
    exact Subtype.ext (hz s s.2).symm

theorem V_le_N (h : TIConfig H V N) : V ≤ N :=
  h.pcore_le V (fun x hx => ⟨h.V_le hx, Subgroup.le_normalizer hx⟩)
    (fun k hk => hk.2) h.V_pgroup

theorem conj_mem_of_mem_normalizer {A : Subgroup X} {k z : X} (hk : k ∈ normalizer (A : Set X))
    (hz : z ∈ A) : k * z * k⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hk z).mp hz

theorem mem_normalizer_of_conj_mem {A : Subgroup X} {k : X}
    (h : ∀ z ∈ A, k * z * k⁻¹ ∈ A) : k ∈ normalizer (A : Set X) :=
  Subgroup.mem_normalizer_fintype h


theorem conj_mem_cenIn {P : Subgroup X} {k z : X} (hk : k ∈ normalizer (P : Set X))
    (hz : z ∈ cenIn P) : k * z * k⁻¹ ∈ cenIn P := by
  obtain ⟨hzN, hzc⟩ := mem_cenIn.1 hz
  refine mem_cenIn.2 ⟨conj_mem_of_mem_normalizer hk hzN, fun s hs => ?_⟩
  have hs' : k⁻¹ * s * k ∈ P := by
    have := conj_mem_of_mem_normalizer ((normalizer (P : Set X)).inv_mem hk) hs
    simpa using this
  have h1 := hzc _ hs'
  calc k * z * k⁻¹ * s = k * (z * (k⁻¹ * s * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * s * k) * z) * k⁻¹ := by rw [h1]
    _ = s * (k * z * k⁻¹) := by group

theorem conj_sup_mem {A B : Subgroup X} {k : X} (hA : k ∈ normalizer (A : Set X))
    (hB : k ∈ normalizer (B : Set X)) : k ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem fun z hz => ?_
  rw [Subgroup.sup_eq_closure] at hz ⊢
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl (conj_mem_of_mem_normalizer hA hx))
    · exact Subgroup.subset_closure (Or.inr (conj_mem_of_mem_normalizer hB hx))
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {P N : Subgroup X}
    (hP : IsPGroup p P) (hNP : N ≤ P) (hne : ¬ P ≤ N) :
    ∃ x ∈ P, x ∈ normalizer (N : Set X) ∧ x ∉ N := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hlt : N.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact hne
  have h2 := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨y, hy1, hy2⟩ := SetLike.exists_of_lt h2
  refine ⟨y, y.2, ?_, hy2⟩
  have h3 : y ∈ (normalizer (N : Set X)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hNP]; exact hy1
  exact h3

theorem exists_ne_one_mem_cenIn {p : ℕ} [Fact p.Prime] {S : Subgroup X} (hS : IsPGroup p S)
    (hne : S ≠ ⊥) : ∃ z ∈ cenIn S, z ≠ 1 := by
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  haveI := hS.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center S)
  refine ⟨(c : S), ⟨c, c.2, rfl⟩, ?_⟩
  intro h
  apply hc
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem cenIn_N_eq (h : TIConfig H V N) : cenIn N = V := by
  have hVN := h.V_le_N
  have hVc : V ≤ cenIn N := fun x hx => mem_cenIn.2 ⟨hVN hx, fun s hs => h.VN_comm x hx s hs⟩
  refine le_antisymm ?_ hVc
  refine (h.maxAb (cenIn N) hVc (fun x hx => h.N_le (mem_cenIn.1 hx).1) ?_ ?_).le
  · intro k hk
    exact mem_normalizer_of_conj_mem fun z hz => conj_mem_cenIn (h.N_normal k hk) hz
  · intro x hx y hy
    exact (mem_cenIn.1 hx).2 y (mem_cenIn.1 hy).1

theorem N_le_of_maximal (h : TIConfig H V N) {Y S : Subgroup X} (hNY : N ≤ Y)
    (hYK : Y ≤ NormIn H V) (hSY : S ≤ Y) (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup X, T ≤ Y → IsPGroup 2 T → S ≤ T → T = S) : N ≤ S := by
  have hNS : IsPGroup 2 (N ⊔ S : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' h.N_pgroup hSp (fun s hs => h.N_normal s (hYK (hSY hs)))
  have h1 := hS (N ⊔ S) (sup_le hNY hSY) hNS le_sup_right
  exact le_sup_left.trans h1.le

theorem cenIn_le_V (h : TIConfig H V N) {Y S : Subgroup X} (hNY : N ≤ Y)
    (hYK : Y ≤ NormIn H V) (hSY : S ≤ Y) (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup X, T ≤ Y → IsPGroup 2 T → S ≤ T → T = S) : cenIn S ≤ V := by
  have hNS := h.N_le_of_maximal hNY hYK hSY hSp hS
  intro z hz
  obtain ⟨hzS, hzc⟩ := mem_cenIn.1 hz
  have hzN : z ∈ N := h.cent_le z (hYK (hSY hzS)) (fun n hn => hzc n (hNS hn))
  have : z ∈ cenIn N := mem_cenIn.2 ⟨hzN, fun n hn => hzc n (hNS hn)⟩
  rwa [h.cenIn_N_eq] at this

end TIConfig

end CFSG.RankThree.GF2n.Stroth80
