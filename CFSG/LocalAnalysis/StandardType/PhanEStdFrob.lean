module

public import CFSG.LocalAnalysis.StandardType.PhanEStdBuilding

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (D n H) in
structure FrobData (w₀ : W) where
  φ : K →* K
  invol : ∀ g, φ (φ g) = g
  op : Fin D.rank → Fin D.rank
  hop : ∀ i, w₀ * (cs).simple i * w₀ = (cs).simple (op i)
  pos : (posUnipotent D).map φ ≤ posUnipotent D
  torus : (⨆ i, H i).map φ ≤ ⨆ i, H i
  n_map : ∀ i, φ (n i) = n (op i)

namespace FrobData

variable {w₀ : W} (F : FrobData D n H w₀)

theorem borel_map : (borel D H).map F.φ ≤ borel D H := by
  show ((⨆ i, H i) ⊔ posUnipotent D).map F.φ ≤ (⨆ i, H i) ⊔ posUnipotent D
  rw [Subgroup.map_sup]
  exact sup_le_sup F.torus F.pos

theorem mem_borel_iff (g : K) : F.φ g ∈ borel D H ↔ g ∈ borel D H := by
  refine ⟨fun hg => ?_, fun hg => borel_map F (Subgroup.mem_map_of_mem F.φ hg)⟩
  have h := borel_map F (Subgroup.mem_map_of_mem F.φ hg)
  rwa [F.invol g] at h

theorem phi_rel {a b : K} (h : a⁻¹ * b ∈ borel D H) : (F.φ a)⁻¹ * F.φ b ∈ borel D H := by
  have h' : F.φ (a⁻¹ * b) ∈ (borel D H).map F.φ := Subgroup.mem_map_of_mem F.φ h
  rw [map_mul, map_inv] at h'
  exact borel_map F h'

theorem length_conj (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
    (w : W) : (cs).length (w₀ * w * w₀) = (cs).length w := by
  have hx : w ∈ (cs).parabolic (Set.univ : Set (Fin D.rank)) := by
    rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top w
  have hx' : w * w₀ ∈ (cs).parabolic (Set.univ : Set (Fin D.rank)) := by
    rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top _
  have h1 : (cs).length (w₀ * (w * w₀)) + (cs).length (w * w₀) = (cs).length w₀ :=
    hw₀.length_mul hx'
  have h2 : (cs).length w + (cs).length (w * w₀) = (cs).length w₀ := by
    rw [add_comm]; exact hw₀.length_mul_left hx
  rw [mul_assoc]
  exact Nat.add_right_cancel (h1.trans h2.symm)

private theorem q2nPE_wordProd_conj
    (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
    (ω : List (Fin D.rank)) :
    w₀ * (cs).wordProd ω * w₀ = (cs).wordProd (ω.map F.op) := by
  have hinv : w₀⁻¹ = w₀ := hw₀.inv_eq
  have hconj : ∀ i : Fin D.rank, MulAut.conj w₀ ((cs).simple i) = (cs).simple (F.op i) := by
    intro i
    rw [MulAut.conj_apply, hinv, F.hop i]
  have hc : MulAut.conj w₀ ((cs).wordProd ω) = (cs).wordProd (ω.map F.op) := by
    induction ω with
    | nil => simp [CoxeterSystem.wordProd_nil]
    | cons i ω ih =>
      rw [List.map_cons, CoxeterSystem.wordProd_cons, map_mul, ih, hconj i]
      rw [CoxeterSystem.wordProd_cons]
  simpa [MulAut.conj_apply, hinv] using hc

private theorem q2nPE_isReduced_map_op
    (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
    {ω : List (Fin D.rank)} (hω : (cs).IsReduced ω) : (cs).IsReduced (ω.map F.op) := by
  change (cs).length ((cs).wordProd (ω.map F.op)) = (ω.map F.op).length
  rw [← q2nPE_wordProd_conj F hw₀ ω, length_conj hw₀, hω.eq, List.length_map]

theorem nrep_map (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀) (w : W) :
    F.φ (nrep hct w) = nrep hct (w₀ * w * w₀) := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced w
  have hred : (cs).IsReduced (ω.map F.op) := q2nPE_isReduced_map_op F hw₀ hω
  have hconj := q2nPE_wordProd_conj F hw₀ ω
  have hmap : ω.map (F.φ ∘ n) = (ω.map F.op).map n := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => F.n_map i
  rw [nrep_wordProd hct hω, map_list_prod, List.map_map, hmap, hconj, nrep_wordProd hct hred]

theorem mem_cell_iff (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀) (w : W)
    (g : K) : F.φ g ∈ bruhatCell hct (w₀ * w * w₀) ↔ g ∈ bruhatCell hct w := by
  have hconj : w₀ * (w₀ * w * w₀) * w₀ = w := by
    rw [show w₀ * (w₀ * w * w₀) * w₀ = (w₀ * w₀) * w * (w₀ * w₀) by group,
      hw₀.mul_self, one_mul, mul_one]
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hg
    refine ⟨F.φ b₁, borel_map F (Subgroup.mem_map_of_mem F.φ hb₁),
      F.φ b₂, borel_map F (Subgroup.mem_map_of_mem F.φ hb₂), ?_⟩
    calc g = F.φ (F.φ g) := (F.invol g).symm
      _ = F.φ (b₁ * nrep hct (w₀ * w * w₀) * b₂) := by rw [he]
      _ = F.φ b₁ * F.φ (nrep hct (w₀ * w * w₀)) * F.φ b₂ := by rw [map_mul, map_mul]
      _ = F.φ b₁ * nrep hct (w₀ * (w₀ * w * w₀) * w₀) * F.φ b₂ := by rw [nrep_map F hct hw₀]
      _ = F.φ b₁ * nrep hct w * F.φ b₂ := by rw [hconj]
  · obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hg
    refine ⟨F.φ b₁, borel_map F (Subgroup.mem_map_of_mem F.φ hb₁),
      F.φ b₂, borel_map F (Subgroup.mem_map_of_mem F.φ hb₂), ?_⟩
    rw [he, map_mul, map_mul, nrep_map F hct hw₀]

end FrobData

end CFSG.ClassicalInvolution.Phan.PhanE
