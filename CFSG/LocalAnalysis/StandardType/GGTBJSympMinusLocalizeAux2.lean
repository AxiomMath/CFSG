module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalizeAux1
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram ofSymplecticMat mat_ofSymplecticMat
  mat_transpose_mul_gram_mul)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open Matrix Multiplicative

@[expose] def sympMinusLocCls {m : ℕ} {p : ℕ} (f₀ : Fin m → Multiplicative (ZMod p))
    (a : Multiplicative (ZMod p)) : Finset (Fin m) :=
  Finset.univ.filter fun x => f₀ x = a ∨ f₀ x = a⁻¹

theorem sympMinusLocCls_mem {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {a : Multiplicative (ZMod p)} {x : Fin m} :
    x ∈ sympMinusLocCls f₀ a ↔ f₀ x = a ∨ f₀ x = a⁻¹ := by
  simp [sympMinusLocCls]

theorem sympMinusLocCls_self {m : ℕ} {p : ℕ} (f₀ : Fin m → Multiplicative (ZMod p)) (x : Fin m) :
    x ∈ sympMinusLocCls f₀ (f₀ x) :=
  sympMinusLocCls_mem.mpr (Or.inl rfl)

theorem sympMinusLocCls_eq_of_mem {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {a b : Multiplicative (ZMod p)} {z : Fin m}
    (hza : z ∈ sympMinusLocCls f₀ a) (hzb : z ∈ sympMinusLocCls f₀ b) :
    sympMinusLocCls f₀ a = sympMinusLocCls f₀ b := by
  have hab : a = b ∨ a = b⁻¹ := by
    rcases sympMinusLocCls_mem.mp hza with h | h <;> rcases sympMinusLocCls_mem.mp hzb with h' | h'
    · exact Or.inl (h.symm.trans h')
    · exact Or.inr (h.symm.trans h')
    · exact Or.inr (inv_injective (by rw [inv_inv]; exact h.symm.trans h'))
    · exact Or.inl (inv_injective (h.symm.trans h'))
  rcases hab with rfl | hab
  · rfl
  · rw [hab]
    ext x
    simp [sympMinusLocCls, inv_inv, or_comm]

theorem sympMinusLocCls_disjoint {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {a b : Multiplicative (ZMod p)} (h : sympMinusLocCls f₀ a ≠ sympMinusLocCls f₀ b) :
    Disjoint (sympMinusLocCls f₀ a) (sympMinusLocCls f₀ b) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  exact h (sympMinusLocCls_eq_of_mem hza hzb)

theorem sympMinusLocCoordSet_disjoint {m : ℕ} {S T : Finset (Fin m)} (h : Disjoint S T) :
    Disjoint (sympMinusLocCoordSet S) (sympMinusLocCoordSet T) := by
  rw [Set.disjoint_left]
  intro a ha hb
  exact (Finset.disjoint_left.mp h ha) hb

@[expose] def sympMinusLocClasses {m : ℕ} {p : ℕ} (f₀ : Fin m → Multiplicative (ZMod p)) :
    Finset (Finset (Fin m)) :=
  Finset.univ.image fun x => sympMinusLocCls f₀ (f₀ x)

@[expose] def sympMinusLocUnionCls {m : ℕ} {p : ℕ} (f₀ : Fin m → Multiplicative (ZMod p))
    (Q : Finset (Finset (Fin m))) : Finset (Fin m) :=
  Finset.univ.filter fun x => sympMinusLocCls f₀ (f₀ x) ∈ Q

theorem sympMinusLocUnionCls_mem {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {Q : Finset (Finset (Fin m))} {x : Fin m} :
    x ∈ sympMinusLocUnionCls f₀ Q ↔ sympMinusLocCls f₀ (f₀ x) ∈ Q := by
  simp [sympMinusLocUnionCls]

theorem sympMinusLoc_projSet_mul {K : Type} [Field K] {m : ℕ} {A B : Set (Fin m ⊕ Fin m)}
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (hdisj : Disjoint A B)
    (hcross : ∀ x y, ¬(x ∈ A ∧ y ∈ A) → ¬(x ∈ B ∧ y ∈ B) →
      H x y = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y) :
    sympMinusLocProjSet (K := K) (m := m) A H * sympMinusLocProjSet B H =
      sympMinusLocProjSet (A ∪ B) H := by
  have hA := sympMinusLocProjSet_isSupp A H
  have hB := sympMinusLocProjSet_isSupp B H
  ext x y
  by_cases hxA : x ∈ A
  · rw [IsSupp.mul_apply_of_mem hA hB hdisj hxA]
    by_cases hyA : y ∈ A
    · rw [sympMinusLocProjSet_pos hxA hyA, sympMinusLocProjSet_pos (Or.inl hxA) (Or.inl hyA)]
    · rw [sympMinusLocProjSet_neg fun hc => hyA hc.2]
      by_cases hyB : y ∈ B
      · rw [sympMinusLocProjSet_pos (Or.inl hxA) (Or.inr hyB),
          hcross x y (fun hc => hyA hc.2) (fun hc => (Set.disjoint_left.mp hdisj hxA) hc.1)]
      · rw [sympMinusLocProjSet_neg fun hc => hc.2.elim hyA hyB]
  · rw [IsSupp.mul_apply_of_notMem hA hxA]
    by_cases hxB : x ∈ B
    · by_cases hyB : y ∈ B
      · rw [sympMinusLocProjSet_pos hxB hyB, sympMinusLocProjSet_pos (Or.inr hxB) (Or.inr hyB)]
      · rw [sympMinusLocProjSet_neg fun hc => hyB hc.2]
        by_cases hyA : y ∈ A
        · rw [sympMinusLocProjSet_pos (Or.inr hxB) (Or.inl hyA),
            hcross x y (fun hc => (Set.disjoint_left.mp hdisj hc.1) hxB) (fun hc => hyB hc.2)]
        · rw [sympMinusLocProjSet_neg fun hc => hc.2.elim hyA hyB]
    · rw [sympMinusLocProjSet_neg fun hc => hxB hc.1,
        sympMinusLocProjSet_neg fun hc => hc.1.elim hxA hxB]

theorem sympMinusLoc_coord_side_plane {m : ℕ} (u : Fin m ⊕ Fin m) :
    WitSpNs.coord (WitSpNs.side u) (WitSpNs.plane u) = u :=
  WitSpNs.eq_of_plane_side (by simp) (by simp)

theorem sympMinusLoc_hcross {K : Type} [Field K] {m : ℕ} [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) {h : StatedSp m K}
    (hh : h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))) :
    ∀ u v : Fin m ⊕ Fin m,
      (∀ S ∈ sympMinusLocClasses f₀, ¬(WitSpNs.plane u ∈ S ∧ WitSpNs.plane v ∈ S)) →
      mat m K h u v = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) u v := by
  have hh' : h * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * h :=
    Subgroup.mem_centralizer_singleton_iff.mp hh
  intro u v huv
  by_cases huv0 : mat m K h u v = 0
  · rw [huv0, Matrix.one_apply]
    by_cases huv_eq : u = v
    · exfalso
      refine huv (sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)))
        (Finset.mem_image.mpr ⟨WitSpNs.plane u, Finset.mem_univ _, rfl⟩) ⟨?_, ?_⟩
      · exact sympMinusLocCls_self f₀ _
      · rw [huv_eq]; exact sympMinusLocCls_self f₀ _
    · rw [if_neg huv_eq]
  · exfalso
    have hcl : f₀ (WitSpNs.plane v) = f₀ (WitSpNs.plane u) ∨
        f₀ (WitSpNs.plane v) = (f₀ (WitSpNs.plane u))⁻¹ := by
      by_contra hcon
      push Not at hcon
      have hblk := sympMinusLoc_blk_eq_zero_of_mem_centralizer hp hp2 hζ f₀ hh'
        (WitSpNs.plane v) (WitSpNs.plane u) hcon.1.symm
        (fun hh2 => hcon.2 (by rw [hh2]; simp))
      exact huv0 (by
        have h := congrFun (congrFun hblk (WitSpNs.side u)) (WitSpNs.side v)
        rw [← sympMinusLoc_coord_side_plane u, ← sympMinusLoc_coord_side_plane v]
        simpa only [blk, Matrix.of_apply, Matrix.zero_apply] using h)
    refine huv (sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)))
      (Finset.mem_image.mpr ⟨WitSpNs.plane u, Finset.mem_univ _, rfl⟩) ⟨?_, ?_⟩
    · exact sympMinusLocCls_self f₀ _
    · exact sympMinusLocCls_mem.mpr hcl

theorem sympMinusLocMat_eq_zero_of_not_same {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) {h : StatedSp m K}
    (hh : h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))
    {u v : Fin m ⊕ Fin m}
    (huv : ∀ S ∈ sympMinusLocClasses f₀, ¬(WitSpNs.plane u ∈ S ∧ WitSpNs.plane v ∈ S)) :
    mat m K h u v = 0 := by
  have h1 := sympMinusLoc_hcross hp hp2 hζ f₀ hh u v huv
  rw [Matrix.one_apply] at h1
  by_cases huv_eq : u = v
  · exfalso
    exact huv (sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)))
      (Finset.mem_image.mpr ⟨WitSpNs.plane u, Finset.mem_univ _, rfl⟩)
      ⟨sympMinusLocCls_self f₀ _, by rw [huv_eq]; exact sympMinusLocCls_self f₀ _⟩
  · rwa [if_neg huv_eq] at h1

@[expose] def sympMinusLocIsUnionCls {m : ℕ} {p : ℕ} (f₀ : Fin m → Multiplicative (ZMod p))
    (S : Finset (Fin m)) : Prop :=
  ∀ x ∈ S, sympMinusLocCls f₀ (f₀ x) ⊆ S

theorem sympMinusLocProjSp_cross_of_union {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) {h : StatedSp m K}
    (hh : h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))
    {S : Finset (Fin m)} (hS : sympMinusLocIsUnionCls f₀ S) :
    (∀ u v, WitSpNs.plane u ∉ S → WitSpNs.plane v ∈ S → mat m K h u v = 0) ∧
    (∀ u v, WitSpNs.plane u ∈ S → WitSpNs.plane v ∉ S → mat m K h u v = 0) := by
  constructor
  · intro u v hu hv
    refine sympMinusLocMat_eq_zero_of_not_same hp hp2 hζ f₀ hh fun T hT => ?_
    rintro ⟨huT, hvT⟩
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hT
    rw [← hy] at huT hvT
    have hsub : sympMinusLocCls f₀ (f₀ y) ⊆ S := by
      rw [sympMinusLocCls_eq_of_mem hvT (sympMinusLocCls_self f₀ (WitSpNs.plane v))]
      exact hS _ hv
    exact hu (hsub huT)
  · intro u v hu hv
    refine sympMinusLocMat_eq_zero_of_not_same hp hp2 hζ f₀ hh fun T hT => ?_
    rintro ⟨huT, hvT⟩
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hT
    rw [← hy] at huT hvT
    have hsub : sympMinusLocCls f₀ (f₀ y) ⊆ S := by
      rw [sympMinusLocCls_eq_of_mem huT (sympMinusLocCls_self f₀ (WitSpNs.plane u))]
      exact hS _ hu
    exact hv (hsub hvT)

theorem sympMinusLocIsUnionCls_of_mem_classes {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {S : Finset (Fin m)} (hS : S ∈ sympMinusLocClasses f₀) :
    sympMinusLocIsUnionCls f₀ S := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hS
  intro y hy
  rw [sympMinusLocCls_eq_of_mem (sympMinusLocCls_self f₀ y) hy]

theorem sympMinusLocIsUnionCls_unionCls {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {Q : Finset (Finset (Fin m))} (hQ : ∀ S ∈ Q, S ∈ sympMinusLocClasses f₀) :
    sympMinusLocIsUnionCls f₀ (sympMinusLocUnionCls f₀ Q) := by
  intro x hx
  rw [sympMinusLocUnionCls_mem] at hx
  intro y hy
  rw [sympMinusLocUnionCls_mem, sympMinusLocCls_eq_of_mem (sympMinusLocCls_self f₀ y) hy]
  exact hx

theorem sympMinusLocCoordSet_unionCls {m : ℕ} {p : ℕ} {f₀ : Fin m → Multiplicative (ZMod p)}
    {Q : Finset (Finset (Fin m))} (hQ : ∀ S ∈ Q, S ∈ sympMinusLocClasses f₀) :
    sympMinusLocCoordSet (sympMinusLocUnionCls f₀ Q) = ⋃ S ∈ Q, sympMinusLocCoordSet S := by
  ext u
  simp only [sympMinusLocCoordSet, Set.mem_setOf_eq, Set.mem_iUnion, sympMinusLocUnionCls_mem]
  constructor
  · intro h
    exact ⟨sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)), h, sympMinusLocCls_self f₀ _⟩
  · rintro ⟨T, hT, hu⟩
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp (hQ T hT)
    have hTeq : sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)) = T := by
      rw [← hy]
      exact (sympMinusLocCls_eq_of_mem (by rwa [← hy] at hu) (sympMinusLocCls_self f₀ _)).symm
    rw [hTeq]
    exact hT

theorem sympMinusLoc_iUnion_insert {m : ℕ} (S : Finset (Fin m)) (Q' : Finset (Finset (Fin m))) :
    (⋃ T ∈ insert S Q', sympMinusLocCoordSet T) =
      sympMinusLocCoordSet S ∪ ⋃ T ∈ Q', sympMinusLocCoordSet T := by
  ext u
  simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨T, rfl | hT, hu⟩
    · exact Or.inl hu
    · exact Or.inr ⟨T, hT, hu⟩
  · rintro (hu | ⟨T, hT, hu⟩)
    · exact ⟨S, Or.inl rfl, hu⟩
    · exact ⟨T, Or.inr hT, hu⟩

theorem sympMinusLoc_eq_proj_mul {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) {h : StatedSp m K}
    (hh : h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)))
    {A B : Finset (Fin m)} (hA : sympMinusLocIsUnionCls f₀ A) (hB : sympMinusLocIsUnionCls f₀ B)
    (hdisj : Disjoint A B)
    (hsup : IsSupp (sympMinusLocCoordSet A ∪ sympMinusLocCoordSet B) (mat m K h)) :
    sympMinusLocProjSp A h (sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hA).1
        (sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hA).2 *
      sympMinusLocProjSp B h (sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hB).1
        (sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hB).2 = h := by
  have hcrossA := sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hA
  have hcrossB := sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hB
  have hcrossAB : ∀ x y, ¬(x ∈ sympMinusLocCoordSet A ∧ y ∈ sympMinusLocCoordSet A) →
      ¬(x ∈ sympMinusLocCoordSet B ∧ y ∈ sympMinusLocCoordSet B) →
      mat m K h x y = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := by
    intro x y hxA hyB
    by_cases hmem : x ∈ sympMinusLocCoordSet A ∪ sympMinusLocCoordSet B ∧
        y ∈ sympMinusLocCoordSet A ∪ sympMinusLocCoordSet B
    · have hnotsame : ∀ T ∈ sympMinusLocClasses f₀,
          ¬(WitSpNs.plane x ∈ T ∧ WitSpNs.plane y ∈ T) := by
        intro T hT
        rintro ⟨hxT, hyT⟩
        obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp hT
        rw [← hx₀] at hxT hyT
        have hTeq : T = sympMinusLocCls f₀ (f₀ (WitSpNs.plane x)) := by
          rw [← hx₀]
          exact sympMinusLocCls_eq_of_mem hxT (sympMinusLocCls_self f₀ (WitSpNs.plane x))
        have hxA' : x ∈ sympMinusLocCoordSet A ∨ x ∈ sympMinusLocCoordSet B := by
          simpa only [Set.mem_union] using hmem.1
        rcases hxA' with hxA' | hxB'
        · have hTA : T ⊆ A := by rw [hTeq]; exact hA _ hxA'
          exact hxA ⟨hxA', hTA (hx₀ ▸ hyT)⟩
        · have hTB : T ⊆ B := by rw [hTeq]; exact hB _ hxB'
          exact hyB ⟨hxB', hTB (hx₀ ▸ hyT)⟩
      rw [sympMinusLocMat_eq_zero_of_not_same hp hp2 hζ f₀ hh hnotsame, Matrix.one_apply, if_neg]
      intro hxy
      exact hnotsame (sympMinusLocCls f₀ (f₀ (WitSpNs.plane x)))
        (Finset.mem_image.mpr ⟨WitSpNs.plane x, Finset.mem_univ _, rfl⟩)
        ⟨sympMinusLocCls_self f₀ _, by rw [hxy]; exact sympMinusLocCls_self f₀ _⟩
    · rw [hsup x y (not_and_or.mp hmem)]
  apply mat_injective
  rw [map_mul, sympMinusLocProjSp_mat, sympMinusLocProjSp_mat,
    sympMinusLocProjMat_eq_projSet hcrossA.1, sympMinusLocProjMat_eq_projSet hcrossB.1,
    sympMinusLoc_projSet_mul (mat m K h) (sympMinusLocCoordSet_disjoint hdisj) hcrossAB]
  ext x y
  by_cases hxy : x ∈ sympMinusLocCoordSet A ∪ sympMinusLocCoordSet B ∧
      y ∈ sympMinusLocCoordSet A ∪ sympMinusLocCoordSet B
  · rw [sympMinusLocProjSet_pos hxy.1 hxy.2]
  · rw [sympMinusLocProjSet_neg hxy, hsup x y (not_and_or.mp hxy)]

theorem sympMinusLoc_iSup_MS {K : Type} [Field K] {m : ℕ} [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p)) :
    (⨆ S ∈ sympMinusLocClasses f₀, sympMinusLocMS ζ f₀ S) =
      Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K)) := by
  classical
  refine le_antisymm (iSup₂_le fun S _ => inf_le_left) ?_
  intro h hh
  have key : ∀ (Q : Finset (Finset (Fin m))), (∀ S ∈ Q, S ∈ sympMinusLocClasses f₀) →
      ∀ h : StatedSp m K, h ∈ Subgroup.centralizer ({spPlaneTorus m ζ f₀} :
        Set (StatedSp m K)) →
      IsSupp (sympMinusLocCoordSet (sympMinusLocUnionCls f₀ Q)) (mat m K h) →
        h ∈ ⨆ T ∈ Q, sympMinusLocMS ζ f₀ T := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
        intro _ h hh hsup
        have hmat : mat m K h = 1 := by
          ext u v
          exact hsup u v (by simp [sympMinusLocUnionCls, sympMinusLocCoordSet])
        have h1 : h = 1 := mat_injective (by rw [hmat, map_one])
        rw [h1]
        exact one_mem _
    | insert S Q' hS ih =>
        intro hQ h hh hsup
        have hSP : S ∈ sympMinusLocClasses f₀ := hQ S (Finset.mem_insert_self S Q')
        have hQ' : ∀ T ∈ Q', T ∈ sympMinusLocClasses f₀ :=
          fun T hT => hQ T (Finset.mem_insert_of_mem hT)
        have hSUnion : sympMinusLocIsUnionCls f₀ S := sympMinusLocIsUnionCls_of_mem_classes hSP
        have hBunion : sympMinusLocIsUnionCls f₀ (sympMinusLocUnionCls f₀ Q') :=
          sympMinusLocIsUnionCls_unionCls hQ'
        have hcoord : sympMinusLocCoordSet (sympMinusLocUnionCls f₀ (insert S Q')) =
            sympMinusLocCoordSet S ∪ sympMinusLocCoordSet (sympMinusLocUnionCls f₀ Q') := by
          rw [sympMinusLocCoordSet_unionCls hQ, sympMinusLocCoordSet_unionCls hQ',
            sympMinusLoc_iUnion_insert]
        rw [hcoord] at hsup
        have hdisjS : Disjoint S (sympMinusLocUnionCls f₀ Q') := by
          rw [Finset.disjoint_left]
          intro x hxS hxB
          rw [sympMinusLocUnionCls_mem] at hxB
          obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.mp hSP
          have hxS' : x ∈ sympMinusLocCls f₀ (f₀ x₀) := by rwa [← hx₀] at hxS
          have hSx : sympMinusLocCls f₀ (f₀ x) = S := by
            rw [← hx₀]
            exact (sympMinusLocCls_eq_of_mem hxS' (sympMinusLocCls_self f₀ x)).symm
          rw [hSx] at hxB
          exact hS hxB
        have hkh := sympMinusLoc_eq_proj_mul hp hp2 hζ f₀ hh hSUnion hBunion hdisjS hsup
        rw [← hkh]
        refine mul_mem ?_ ?_
        · exact le_iSup₂ (f := fun T (_ : T ∈ insert S Q') => sympMinusLocMS ζ f₀ T) S
            (Finset.mem_insert_self S Q') (Subgroup.mem_inf.mpr
            ⟨sympMinusLocProjSp_mem_centralizer ζ f₀ _ _ hh, sympMinusLocProjSp_mem_supp S h _ _⟩)
        · have hle : (⨆ T ∈ Q', sympMinusLocMS ζ f₀ T) ≤
              (⨆ T ∈ insert S Q', sympMinusLocMS ζ f₀ T) := by
            refine iSup₂_le fun T hT => ?_
            exact le_iSup₂ (f := fun U (_ : U ∈ insert S Q') => sympMinusLocMS ζ f₀ U) T
              (Finset.mem_insert_of_mem hT)
          refine hle ?_
          refine ih hQ' _ (sympMinusLocProjSp_mem_centralizer ζ f₀ _ _ hh) ?_
          rw [sympMinusLocProjSp_mat, sympMinusLocProjMat_eq_projSet
            (sympMinusLocProjSp_cross_of_union hp hp2 hζ f₀ hh hBunion).1,
            sympMinusLocCoordSet_unionCls hQ']
          exact sympMinusLocProjSet_isSupp _ _
  have hfull : sympMinusLocCoordSet (sympMinusLocUnionCls f₀ (sympMinusLocClasses f₀)) =
      Set.univ := by
    rw [sympMinusLocCoordSet_unionCls (fun S hS => hS)]
    ext u
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨sympMinusLocCls f₀ (f₀ (WitSpNs.plane u)),
      Finset.mem_image.mpr ⟨WitSpNs.plane u, Finset.mem_univ _, rfl⟩, sympMinusLocCls_self f₀ _⟩
  refine key (sympMinusLocClasses f₀) (fun S hS => hS) h hh ?_
  rw [hfull]
  intro u v huv
  rcases huv with h | h
  · exact absurd (Set.mem_univ u) h
  · exact absurd (Set.mem_univ v) h

theorem sympMinusLocBlk_eq_of_isSupp {K : Type} [Field K] {m : ℕ} {S : Finset (Fin m)}
    {j : StatedSp m K}
    (hj : IsSupp (sympMinusLocCoordSet S) (mat m K j)) {x : Fin m} (hx : x ∉ S) (y : Fin m) :
    blk (mat m K j) y x = if y = x then 1 else 0 := by
  ext a b
  change mat m K j (WitSpNs.coord a y) (WitSpNs.coord b x) =
    (if y = x then (1 : Matrix (Fin 2) (Fin 2) K) else 0) a b
  have hmem : WitSpNs.coord b x ∉ sympMinusLocCoordSet S := by
    simp only [sympMinusLocCoordSet, Set.mem_setOf_eq]
    rwa [WitSpNs.plane_coord]
  rw [hj _ _ (Or.inr hmem)]
  by_cases hyx : y = x
  · subst hyx
    rw [if_pos rfl, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · have hne : WitSpNs.coord a y ≠ WitSpNs.coord b y := fun h =>
        hab (by have := congrArg WitSpNs.side h; simpa using this)
      rw [if_neg hne, if_neg hab]
  · rw [if_neg hyx, Matrix.one_apply]
    have hne : WitSpNs.coord a y ≠ WitSpNs.coord b x := fun h =>
      hyx (by have := congrArg WitSpNs.plane h; simpa using this)
    rw [if_neg hne]
    rfl

end CFSG.StandardType.SympMinus

end
