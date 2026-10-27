module

public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.E1Sec7

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_closure_diff_of_lt {X C : Subgroup G} (hCX : C < X) :
    X ≤ Subgroup.closure ((X : Set G) \ (C : Set G)) := by
  obtain ⟨y, hyX, hyC⟩ := IsConcreteLE.exists_of_lt hCX
  intro x hx
  by_cases hxC : x ∈ C
  · have hxy : x * y ∈ Subgroup.closure ((X : Set G) \ (C : Set G)) :=
      Subgroup.subset_closure ⟨X.mul_mem hx hyX, fun h => hyC (by
        simpa using C.mul_mem (C.inv_mem hxC) h)⟩
    have hy : y⁻¹ ∈ Subgroup.closure ((X : Set G) \ (C : Set G)) :=
      Subgroup.inv_mem _ (Subgroup.subset_closure ⟨hyX, hyC⟩)
    simpa using Subgroup.mul_mem _ hxy hy
  · exact Subgroup.subset_closure ⟨hx, hxC⟩

@[expose] def commSub (X A O : Subgroup G) (hXO : X ≤ Subgroup.normalizer (O : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ a ∈ A, x⁻¹ * a * x * a⁻¹ ∈ O}
  one_mem' := ⟨X.one_mem, fun a _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxX, hx⟩ ⟨hyX, hy⟩
    refine ⟨X.mul_mem hxX hyX, fun a ha => ?_⟩
    have e : (x * y)⁻¹ * a * (x * y) * a⁻¹ =
        y⁻¹ * (x⁻¹ * a * x * a⁻¹) * y⁻¹⁻¹ * (y⁻¹ * a * y * a⁻¹) := by group
    rw [e]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hyX)) _).mp (hx a ha))
      (hy a ha)
  inv_mem' := by
    rintro x ⟨hxX, hx⟩
    refine ⟨X.inv_mem hxX, fun a ha => ?_⟩
    have e : x⁻¹⁻¹ * a * x⁻¹ * a⁻¹ = x * (x⁻¹ * a * x * a⁻¹)⁻¹ * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXO hxX) _).mp (O.inv_mem (hx a ha))

theorem commSub_le {X A O : Subgroup G} {hXO : X ≤ Subgroup.normalizer (O : Set G)} :
    commSub X A O hXO ≤ X := fun _ hx => hx.1

theorem exists_pow_eq_one_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {c : G} (hc : c ∈ P) :
    ∃ k : ℕ, c ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨c, hc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem twoResidual_le_closure_nonTwoConj_of_eOne [Finite G] {H A : Subgroup G} (hAH : A ≤ H)
    (h : E1.EOne ↥H (A.subgroupOf H)) :
    twoResidual H ≤ Subgroup.closure (nonTwoConj A H) := by
  obtain ⟨-, -, -, hnot, -, h2el, hcomm, -⟩ :=
    E1.eOneAmb_facts hAH ((E1.eOne_iff_amb hAH).mp h)
  have hXH : twoResidual H ≤ H := twoResidual_le H
  have hHX : H ≤ Subgroup.normalizer (twoResidual H : Set G) := le_normalizer_twoResidual H
  have hXO : twoResidual H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hx)
  set C := commSub (twoResidual H) A (pCoreOf 2 H) hXO with hC
  have hdiff : ((twoResidual H : Set G) \ (C : Set G)) ⊆ nonTwoConj A H := by
    rintro x ⟨hxX, hxC⟩
    refine ⟨hXH hxX, fun hP => hxC ⟨hxX, fun a ha => ?_⟩⟩
    by_contra hcO
    have hc : x⁻¹ * a * x * a⁻¹ ∈ twoResidual H := by
      have e : x⁻¹ * a * x * a⁻¹ = x⁻¹ * (a * x * a⁻¹) := by group
      rw [e]
      exact (twoResidual H).mul_mem ((twoResidual H).inv_mem hxX)
        ((Subgroup.mem_normalizer_iff.mp (hHX (hAH ha)) x).mp hxX)
    have hcP : x⁻¹ * a * x * a⁻¹ ∈ A ⊔ conjSubgroup A x := by
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
        (Subgroup.mem_sup_left (A.inv_mem ha))
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using ha
    exact hcO (h2el _ hc (exists_pow_eq_one_of_mem hP hcP))
  have hlt : C < twoResidual H := by
    refine lt_of_le_of_ne commSub_le fun hCX => hnot ?_
    have hX : twoResidual H ≤ C := hCX ▸ le_rfl
    have hcomO : ⁅twoResidual H, A⁆ ≤ pCoreOf 2 H := by
      refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
      have := (hX ((twoResidual H).inv_mem hx)).2 a ha
      rw [commutatorElement_def]
      simpa using this
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le
      ((hcomm).trans (sup_le hcomO le_rfl))
  exact (le_closure_diff_of_lt hlt).trans (Subgroup.closure_mono hdiff)

end CFSG.Quasithin.F7Two
