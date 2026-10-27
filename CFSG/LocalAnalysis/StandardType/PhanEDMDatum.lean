module

public import CFSG.LocalAnalysis.StandardType.PhanEDMPush
public import CFSG.LocalAnalysis.StandardType.PhanEDMFilt

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
open Classical

variable {I C : Type*} {X : ChamberSystem I C} {lev : C → ℕ}

theorem exists_retraction (hres : IsResidual X lev) {J : Set I} (hJ : J.Nonempty) (c : C)
    {m : ℕ} (hm : ∃ x ∈ X.residue J c, lev x ≤ m) :
    ∃ i ∈ J, ∃ π : C → C,
      (∀ x ∈ X.residue J c ∩ levelSet lev (m + 1),
        π x ∈ X.residue J c ∩ levelSet lev m ∧ X.adj i x (π x)) ∧
      ∀ x ∈ X.residue J c ∩ levelSet lev m, π x = x := by
  classical
  obtain ⟨i, hiJ, hi⟩ := hres J c hJ m hm
  let π : C → C := fun x =>
    if lev x ≤ m then x
    else if h : ∃ x' ∈ X.residue J c, lev x' ≤ m ∧ X.adj i x x' then h.choose else x
  refine ⟨i, hiJ, π, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxA, hxm⟩ := hx
    by_cases hle : lev x ≤ m
    · dsimp only [π]
      rw [if_pos hle]
      exact ⟨⟨hxA, hle⟩, X.adj_refl i x⟩
    · dsimp only [π]
      rw [if_neg hle]
      have hex : ∃ x' ∈ X.residue J c, lev x' ≤ m ∧ X.adj i x x' := hi x hxA hxm
      rw [dif_pos hex]
      exact ⟨⟨hex.choose_spec.1, hex.choose_spec.2.1⟩, hex.choose_spec.2.2⟩
  · intro x hx
    obtain ⟨_, hxm⟩ := hx
    dsimp only [π]
    exact if_pos hxm

theorem exists_step_gallery (hres : IsResidual X lev) (hlco : Lco X lev) {J : Set I} (c : C)
    {m : ℕ} {i : I} (hi : i ∈ J) {π : C → C}
    (hπ : ∀ x ∈ X.residue J c ∩ levelSet lev (m + 1),
        π x ∈ X.residue J c ∩ levelSet lev m ∧ X.adj i x (π x))
    {j : I} (hj : j ∈ J) {x y : C} (hx : x ∈ X.residue J c ∩ levelSet lev (m + 1))
    (hy : y ∈ X.residue J c ∩ levelSet lev (m + 1)) (hxy : X.adj j x y) :
    ∃ γ : List (I × C), GalleryIn X {i, j} (X.residue J c ∩ levelSet lev m) (π x) γ ∧
      galleryEnd (π x) γ = π y := by
  classical
  by_cases hij : j = i
  · rw [hij] at hxy ⊢
    refine ⟨[(i, π y)], ?_, by simp⟩
    rw [galleryIn_cons, galleryIn_nil]
    exact ⟨(hπ x hx).1, adj_trans (adj_symm (hπ x hx).2) (adj_trans hxy (hπ y hy).2),
      by simp, (hπ y hy).1, (hπ y hy).1⟩
  · let R' := X.residue {i, j} x
    have hsub : ({i, j} : Set I) ⊆ J := by
      intro k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    have hR'sub : R' ⊆ X.residue J c := by
      intro z hz
      have hzJ : z ∈ X.residue J x := residue_mono hsub x hz
      rwa [residue_eq_of_mem hx.1] at hzJ
    have hD : Descends X lev {i, j} R' := hres {i, j} x ⟨i, by simp⟩
    have hc : ConnectedIn X {i, j} (aff lev R') := hlco {i, j} x (Set.encard_pair (Ne.symm hij))
    have hconn := connectedIn_levelSet_inter hD hc m
    have hi_mem : i ∈ ({i, j} : Set I) := by simp
    have hj_mem : j ∈ ({i, j} : Set I) := by simp
    have hpxR' : π x ∈ R' :=
      residue_mono (Set.singleton_subset_iff.mpr hi_mem) x
        (mem_residue_singleton.mpr (hπ x hx).2)
    have hyR' : y ∈ R' :=
      residue_mono (Set.singleton_subset_iff.mpr hj_mem) x (mem_residue_singleton.mpr hxy)
    have hpyR' : π y ∈ R' := by
      have h1 : π y ∈ X.residue {i, j} y :=
        residue_mono (Set.singleton_subset_iff.mpr hi_mem) y
          (mem_residue_singleton.mpr (hπ y hy).2)
      rwa [residue_eq_of_mem hyR'] at h1
    obtain ⟨γ, hγ, hend⟩ :=
      hconn (π x) ⟨hpxR', (hπ x hx).1.2⟩ (π y) ⟨hpyR', (hπ y hy).1.2⟩
    exact ⟨γ, GalleryIn.mono (fun _ hz => hz) (fun z hz => ⟨hR'sub hz.1, hz.2⟩) hγ, hend⟩

private noncomputable def q2cDMd_pushEps (X : ChamberSystem I C) (J : Set I) (Q P : Set C)
    (i : I) (π : C → C)
    (step : ∀ j ∈ J, ∀ x ∈ Q, ∀ y ∈ Q, X.adj j x y →
      ∃ γ : List (I × C), GalleryIn X {i, j} P (π x) γ ∧ galleryEnd (π x) γ = π y)
    (j : I) (x y : C) : List (I × C) :=
  if x ∈ P ∧ y ∈ P then [(j, y)]
  else if h : j ∈ J ∧ x ∈ Q ∧ y ∈ Q ∧ X.adj j x y then
    (step j h.1 x h.2.1 y h.2.2.1 h.2.2.2).choose
  else []

private theorem q2cDMd_pushEps_of_mem (X : ChamberSystem I C) (J : Set I) (Q P : Set C)
    (i : I) (π : C → C)
    (step : ∀ j ∈ J, ∀ x ∈ Q, ∀ y ∈ Q, X.adj j x y →
      ∃ γ : List (I × C), GalleryIn X {i, j} P (π x) γ ∧ galleryEnd (π x) γ = π y)
    {j : I} {x y : C} (hx : x ∈ P) (hy : y ∈ P) :
    q2cDMd_pushEps X J Q P i π step j x y = [(j, y)] := by
  unfold q2cDMd_pushEps
  rw [if_pos ⟨hx, hy⟩]

private theorem q2cDMd_pushEps_of_adj (X : ChamberSystem I C) (J : Set I) (Q P : Set C)
    (i : I) (π : C → C)
    (step : ∀ j ∈ J, ∀ x ∈ Q, ∀ y ∈ Q, X.adj j x y →
      ∃ γ : List (I × C), GalleryIn X {i, j} P (π x) γ ∧ galleryEnd (π x) γ = π y)
    {j : I} {x y : C} (hP : ¬ (x ∈ P ∧ y ∈ P)) (hj : j ∈ J) (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : X.adj j x y) :
    q2cDMd_pushEps X J Q P i π step j x y = (step j hj x hx y hy hxy).choose := by
  unfold q2cDMd_pushEps
  rw [if_neg hP,
    dif_pos (show j ∈ J ∧ x ∈ Q ∧ y ∈ Q ∧ X.adj j x y from ⟨hj, hx, hy, hxy⟩)]

theorem exists_pushData (hres : IsResidual X lev) (hlco : Lco X lev) {J : Set I}
    (hJ : J.Nonempty) (c : C) {m : ℕ} (hm : ∃ x ∈ X.residue J c, lev x ≤ m) :
    ∃ i ∈ J, ∃ (π : C → C) (ε : I → C → C → List (I × C)),
      PushData X J (X.residue J c ∩ levelSet lev (m + 1)) (X.residue J c ∩ levelSet lev m)
        i π ε := by
  classical
  obtain ⟨i, hiJ, π, hπmem, hπfix⟩ := exists_retraction hres hJ c hm
  let A := X.residue J c
  let P := A ∩ levelSet lev m
  let Q := A ∩ levelSet lev (m + 1)
  have step : ∀ j ∈ J, ∀ x ∈ Q, ∀ y ∈ Q, X.adj j x y →
      ∃ γ : List (I × C), GalleryIn X {i, j} P (π x) γ ∧ galleryEnd (π x) γ = π y :=
    fun j hj x hx y hy hxy => exists_step_gallery hres hlco c hiJ hπmem hj hx hy hxy
  refine ⟨i, hiJ, π, q2cDMd_pushEps X J Q P i π step, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hπmem
  · exact hπfix
  · intro j hj x hx y hy hxy
    by_cases hP : x ∈ P ∧ y ∈ P
    · have heps : q2cDMd_pushEps X J Q P i π step j x y = [(j, y)] :=
        q2cDMd_pushEps_of_mem X J Q P i π step hP.1 hP.2
      rw [heps]
      refine ⟨?_, ?_⟩
      · rw [galleryIn_cons, galleryIn_nil]
        refine ⟨(hπmem x hx).1, ?_, by simp, hP.2, hP.2⟩
        rw [hπfix x hP.1]
        exact hxy
      · simp [hπfix y hP.2]
    · have heps : q2cDMd_pushEps X J Q P i π step j x y =
          (step j hj x hx y hy hxy).choose :=
        q2cDMd_pushEps_of_adj X J Q P i π step hP hj hx hy hxy
      rw [heps]
      exact (step j hj x hx y hy hxy).choose_spec
  · intro j hj x hx y hy _
    exact q2cDMd_pushEps_of_mem X J Q P i π step hx hy

end CFSG.ClassicalInvolution.Phan.PhanE.DM
