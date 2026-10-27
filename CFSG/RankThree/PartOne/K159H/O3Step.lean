module

public import CFSG.RankThree.PartOne.K159H.O3Elim
public import CFSG.RankThree.PartOne.K159H.O3Group

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin Matrix Matrix.Pivot

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} (qA : QuadraticForm K A)

@[expose] def gL (I : Finset (Fin r ⊕ Fin r)) (L : List (TransvectionStruct I K)) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  (L.map fun t => rEl qA t.c t.i.1 t.j.1).prod

variable {qA}

theorem ActsOn_gL {I : Finset (Fin r ⊕ Fin r)} (hfst : ∀ x y : I, x ≠ y → coordIdx x.1 ≠ coordIdx y.1)
    (hswap : ∀ x i : I, x.1.swap ≠ i.1) (L : List (TransvectionStruct I K)) :
    ActsOn I (gL qA I L) ((L.map TransvectionStruct.toMatrix).prod) := by
  induction L with
  | nil => simpa [gL] using ActsOn.one I
  | cons t L ih =>
    simp only [gL, List.map_cons, List.prod_cons] at ih ⊢
    exact ActsOn.mul (ActsOn_rEl qA (hfst t.i t.j t.hij) (hswap t.i) t.c) ih

theorem gL_mem_Rts {S : Subgroup (Fin r → Kˣ)} {I : Finset (Fin r ⊕ Fin r)}
    (hfst : ∀ x y : I, x ≠ y → coordIdx x.1 ≠ coordIdx y.1) (hsim : ∀ x y : I, SimOn S x.1 y.1)
    (L : List (TransvectionStruct I K)) : gL qA I L ∈ Rts qA S := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hg
  exact rEl_mem_Rts (hfst t.i t.j t.hij) (hsim t.i t.j)

theorem gL_fix {I : Finset (Fin r ⊕ Fin r)} {j : Fin r ⊕ Fin r} (hj : ∀ x : I, j ≠ x.1 ∧ j ≠ x.1.swap)
    (hfst : ∀ x y : I, x ≠ y → coordIdx x.1 ≠ coordIdx y.1) (L : List (TransvectionStruct I K)) :
    gL qA I L (hypVec K A j) = hypVec K A j := by
  induction L with
  | nil => simp [gL]
  | cons t L ih =>
    simp only [gL, List.map_cons, List.prod_cons] at ih ⊢
    rw [LinearEquiv.mul_apply, ih, rEl_apply_hypVec qA (hfst t.i t.j t.hij)]
    have h1 : (if j = t.j.1 then t.c else 0) = 0 := by
      rw [ite_eq_right_iff]; intro h; exact absurd h (hj t.j).1
    have h2 : (if j = t.i.1.swap then t.c else 0) = 0 := by
      rw [ite_eq_right_iff]; intro h; exact absurd h (hj t.i).2
    rw [h1, h2]
    simp

theorem step [CharP K 2] {S : Subgroup (Fin r → Kˣ)} {j₀ : Fin r ⊕ Fin r} (hj₀ : ¬ TrivOn S j₀)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ CO qA S) :
    ∃ h ∈ Rts qA S ⊔ Tor K A r, ∃ g' ∈ CO qA S, g = h * g' ∧
      (∀ i, SimOn S i j₀ → g' (hypVec K A i) = hypVec K A i ∧
        g' (hypVec K A i.swap) = hypVec K A i.swap) ∧
      (∀ j, g (hypVec K A j) = hypVec K A j → g' (hypVec K A j) = hypVec K A j) := by
  classical
  set I := cls S j₀ with hI
  obtain ⟨hgo, hgc⟩ := mem_CO.1 hg
  have hfst : ∀ x y : I, x ≠ y → coordIdx x.1 ≠ coordIdx y.1 := fun x y hxy =>
    cls_coordIdx_ne hj₀ x.2 y.2 fun h => hxy (Subtype.ext h)
  have hswap : ∀ x i : I, x.1.swap ≠ i.1 := fun x i h => cls_swap_not_mem hj₀ x.2 (h ▸ i.2)
  have hsim : ∀ x y : I, SimOn S x.1 y.1 := fun x y => cls_sim x.2 y.2
  have hM : ActsOn I g (matOf g I) := actsOn_matOf hgc hj₀
  have hginv : g⁻¹ ∈ CO qA S := inv_mem hg
  have hMinv : ActsOn I g⁻¹ (matOf g⁻¹ I) := actsOn_matOf (mem_CO.1 hginv).2 hj₀
  have hMM : matOf g I * matOf g⁻¹ I = 1 := by
    have h1 := ActsOn.mul hM hMinv
    rw [mul_inv_cancel] at h1
    exact h1.unique (ActsOn.one I)
  have hdet : (matOf g I).det ≠ 0 := by
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  obtain ⟨L, L', D, hMD⟩ := exists_list_transvec_mul_diagonal_mul_list_transvec (matOf g I)
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hMD, Matrix.det_mul, Matrix.det_mul, TransvectionStruct.det_toMatrix_prod, TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal,
      one_mul, mul_one]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let Du : Fin r ⊕ Fin r → Kˣ := fun j => if h : j ∈ I then Units.mk0 (D ⟨j, h⟩) (hD _) else 1
  have hDu : ∀ i : I, ((Du i.1 : Kˣ) : K) = D i := by
    intro i
    simp [Du, i.2]
  let d : Fin r → Kˣ := fun k =>
    if Sum.inl k ∈ I then Du (Sum.inl k) else if Sum.inr k ∈ I then (Du (Sum.inr k))⁻¹ else 1
  have hd_mem : ∀ i : I, wt d i.1 = Du i.1 := by
    rintro ⟨i | i, hi⟩
    · have : d i = Du (Sum.inl i) := by simp [d, hi]
      rw [wt_inl, this]
    · have hl : Sum.inl i ∉ I := fun hl =>
        hfst ⟨Sum.inl i, hl⟩ ⟨Sum.inr i, hi⟩ (fun h => by cases h) rfl
      have : d i = (Du (Sum.inr i))⁻¹ := by simp [d, hl, hi]
      rw [wt_inr, this, inv_inv]
  have hd_one : ∀ j, j ∉ I → j.swap ∉ I → wt d j = 1 := by
    rintro (k | k) hj hjs
    · have hr : Sum.inr k ∉ I := hjs
      have : d k = 1 := by simp [d, hj, hr]
      rw [wt_inl, this]
    · have hl : Sum.inl k ∉ I := hjs
      have : d k = 1 := by simp [d, hl, hj]
      rw [wt_inr, this, inv_one]
  have hT : ActsOn I (torH K A r d) (Matrix.diagonal D) :=
    ActsOn_tor (fun i => by rw [hd_mem i, hDu i])
  have hL : ActsOn I (gL qA I L) (L.map TransvectionStruct.toMatrix).prod := ActsOn_gL hfst hswap L
  have hL' : ActsOn I (gL qA I L') (L'.map TransvectionStruct.toMatrix).prod := ActsOn_gL hfst hswap L'
  set h := gL qA I L * torH K A r d * gL qA I L' with hh
  have hAct : ActsOn I h (matOf g I) := by
    rw [hMD]
    exact (hL.mul hT).mul hL'
  have hgh : ∀ i : I, g (hypVec K A i.1) = h (hypVec K A i.1) := fun i => (hM.apply i).trans (hAct.apply i).symm
  have hh_mem : h ∈ Rts qA S ⊔ Tor K A r :=
    mul_mem (mul_mem (Subgroup.mem_sup_left (gL_mem_Rts hfst hsim L))
      (Subgroup.mem_sup_right ⟨d, rfl⟩)) (Subgroup.mem_sup_left (gL_mem_Rts hfst hsim L'))
  have hh_CO : h ∈ CO qA S :=
    mul_mem (mul_mem (Rts_le_CO (gL_mem_Rts hfst hsim L)) (torH_mem_CO d)) (Rts_le_CO (gL_mem_Rts hfst hsim L'))
  have hg0_CO : h⁻¹ * g ∈ CO qA S := mul_mem (inv_mem hh_CO) hg
  obtain ⟨hg0o, hg0c⟩ := mem_CO.1 hg0_CO
  have hg0_I : ∀ i : I, (h⁻¹ * g) (hypVec K A i.1) = hypVec K A i.1 := by
    intro i
    rw [LinearEquiv.mul_apply, hgh i, LinearEquiv.inv_apply_apply']
  have hg0_swap : ∀ i : I, (h⁻¹ * g) (hypVec K A i.1.swap) = hypVec K A i.1.swap := by
    intro i
    refine Prod.ext (funext fun c => ?_) ?_
    · by_cases hc : SimOn S c i.1.swap
      · have hcs : c.swap ∈ I := mem_cls.2 (((simOn_swap_iff S i.1 c).1 hc).trans S (mem_cls.1 i.2))
        have h1 := polar_map_of_mem hg0o (hypVec K A i.1.swap) (hypVec K A c.swap)
        rw [hg0_I ⟨c.swap, hcs⟩, polar_hypVec, polar_hypVec, Sum.swap_swap] at h1
        exact h1
      · have hne : c ≠ i.1.swap := by
          rintro rfl
          exact hc (SimOn.refl S _)
        rw [entry_coord_eq_zero hg0c hc, hypVec_fst]
        simp [hne]
    · exact entry_snd_eq_zero hg0c (fun hs => cls_nontriv hj₀ i.2 ((trivOn_swap_iff S _).1 hs))
  refine ⟨h, hh_mem, h⁻¹ * g, hg0_CO, (mul_inv_cancel_left h g).symm, ?_, ?_⟩
  · intro i hi
    exact ⟨hg0_I ⟨i, mem_cls.2 hi⟩, hg0_swap ⟨i, mem_cls.2 hi⟩⟩
  · intro j hj
    by_cases hjI : j ∈ I
    · exact hg0_I ⟨j, hjI⟩
    by_cases hjs : j.swap ∈ I
    · have := hg0_swap ⟨j.swap, hjs⟩
      rwa [Sum.swap_swap] at this
    have hjx : ∀ x : I, j ≠ x.1 ∧ j ≠ x.1.swap := fun x =>
      ⟨fun e => hjI (e ▸ x.2), fun e => hjs (by rw [e, Sum.swap_swap]; exact x.2)⟩
    have hhj : h (hypVec K A j) = hypVec K A j := by
      rw [hh, LinearEquiv.mul_apply, LinearEquiv.mul_apply, gL_fix hjx hfst, torH_hypVec, hd_one j hjI hjs,
        Units.val_one, one_smul, gL_fix hjx hfst]
    rw [LinearEquiv.mul_apply, hj]
    conv_lhs => rw [← hhj]
    exact LinearEquiv.inv_apply_apply' h _

end CFSG.RankThree.PartOne.K159H
