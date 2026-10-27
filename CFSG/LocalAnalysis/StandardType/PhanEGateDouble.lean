module

public import Mathlib.GroupTheory.DoubleCoset
public import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W}

theorem dist_mul_simple_left (hB : IsWeylDistanceBuilding cs δ) {x y z : C} {i : ι}
    (h : δ x y = cs.simple i) : δ y z = δ x z ∨ δ y z = cs.simple i * δ x z := by
  rcases (hB.mul_simple z x y i h).1 with he | he
  · left
    rw [dist_inv hB z y, he, dist_inv hB z x]
  · right
    rw [dist_inv hB z y, he, mul_inv_rev, cs.inv_simple, dist_inv hB z x]

private theorem p9uGD_exists_residue_dist_eq_wordProd (hB : IsWeylDistanceBuilding cs δ)
    (E : C) {K : Set ι} :
    ∀ (ω : List ι), (∀ i ∈ ω, i ∈ K) →
      ∀ D₀ : C, ∃ D ∈ residue cs δ K D₀, δ E D = δ E D₀ * cs.wordProd ω := by
  intro ω
  induction ω with
  | nil =>
    intro _ D₀
    exact ⟨D₀, self_mem_residue K D₀, by simp⟩
  | cons k ω ih =>
    intro hω D₀
    have hk : k ∈ K := hω k (by simp)
    obtain ⟨D₁, hD₁D₀, hED₁⟩ := hB.exists_simple E D₀ k
    have hD₁ : D₁ ∈ residue cs δ K D₀ :=
      Relation.ReflTransGen.single ⟨k, hk, hD₁D₀⟩
    have hω' : ∀ i ∈ ω, i ∈ K := fun i hi => hω i (by simp [hi])
    obtain ⟨D, hDD₁, hED⟩ := ih hω' D₁
    refine ⟨D, mem_residue_trans hD₁ hDD₁, ?_⟩
    rw [hED, hED₁, cs.wordProd_cons, mul_assoc]

theorem exists_mem_residue_dist_eq_mul (hB : IsWeylDistanceBuilding cs δ) (E D₀ : C) {K : Set ι}
    {v : W} (hv : v ∈ cs.parabolic K) :
    ∃ D ∈ residue cs δ K D₀, δ E D = δ E D₀ * v := by
  obtain ⟨ω, _, hωK, hω⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hv
  obtain ⟨D, hD, hED⟩ := p9uGD_exists_residue_dist_eq_wordProd hB E ω hωK D₀
  exact ⟨D, hD, by rw [hED, hω]⟩

theorem exists_mem_residue_dist_eq_mul_left (hB : IsWeylDistanceBuilding cs δ) (C₀ F : C)
    {J : Set ι} {u : W} (hu : u ∈ cs.parabolic J) :
    ∃ C' ∈ residue cs δ J C₀, δ C' F = u * δ C₀ F := by
  obtain ⟨C', hC', hFC'⟩ :=
    exists_mem_residue_dist_eq_mul hB F C₀ (K := J) (v := u⁻¹) (inv_mem hu)
  refine ⟨C', hC', ?_⟩
  calc δ C' F = (δ F C')⁻¹ := dist_inv hB F C'
    _ = (δ F C₀ * u⁻¹)⁻¹ := by rw [hFC']
    _ = u * (δ F C₀)⁻¹ := by rw [mul_inv_rev, inv_inv]
    _ = u * δ C₀ F := by rw [dist_inv hB C₀ F, inv_inv]

theorem dist_mem_mul_parabolic (hB : IsWeylDistanceBuilding cs δ) {E D₀ D : C} {K : Set ι}
    (hD : D ∈ residue cs δ K D₀) : ∃ v ∈ cs.parabolic K, δ E D = δ E D₀ * v := by
  induction hD with
  | refl => exact ⟨1, one_mem _, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨i, hi, hbc⟩ := hbc
    obtain ⟨v, hv, hEb⟩ := ih
    rcases (hB.mul_simple E b c i hbc).1 with he | he
    · exact ⟨v, hv, by rw [he, hEb]⟩
    · exact ⟨v * cs.simple i, mul_mem hv (cs.simple_mem_parabolic hi),
        by rw [he, hEb, mul_assoc]⟩

theorem dist_mem_parabolic_mul (hB : IsWeylDistanceBuilding cs δ) {C₀ C' F : C} {J : Set ι}
    (hC : C' ∈ residue cs δ J C₀) : ∃ u ∈ cs.parabolic J, δ C' F = u * δ C₀ F := by
  obtain ⟨v, hv, hFC'⟩ :=
    dist_mem_mul_parabolic hB (E := F) (D₀ := C₀) (D := C') (K := J) hC
  refine ⟨v⁻¹, inv_mem hv, ?_⟩
  calc δ C' F = (δ F C')⁻¹ := dist_inv hB F C'
    _ = (δ F C₀ * v)⁻¹ := by rw [hFC']
    _ = v⁻¹ * (δ F C₀)⁻¹ := by rw [mul_inv_rev]
    _ = v⁻¹ * δ C₀ F := by rw [dist_inv hB C₀ F, inv_inv]

theorem dist_mem_doubleCoset (hB : IsWeylDistanceBuilding cs δ) {J K : Set ι} {C₀ D₀ C' D : C}
    (hC : C' ∈ residue cs δ J C₀) (hD : D ∈ residue cs δ K D₀) :
    δ C' D ∈ DoubleCoset.doubleCoset (δ C₀ D₀) (cs.parabolic J) (cs.parabolic K) := by
  obtain ⟨u, hu, hC'D⟩ :=
    dist_mem_parabolic_mul hB (C₀ := C₀) (C' := C') (F := D) (J := J) hC
  obtain ⟨v, hv, hC₀D⟩ :=
    dist_mem_mul_parabolic hB (E := C₀) (D₀ := D₀) (D := D) (K := K) hD
  exact DoubleCoset.mem_doubleCoset.mpr ⟨u, hu, v, hv, by rw [hC'D, hC₀D, mul_assoc]⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
