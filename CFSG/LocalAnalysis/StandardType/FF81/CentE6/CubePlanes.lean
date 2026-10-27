module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatSStruct
public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

private def e6 (i : Fin 6) : Fin 6 → ZMod 2 := A5Cube.e (ZMod 2) i

private noncomputable def w3v (a b c : Fin 6 → ZMod 2) : A5Cube.Cube (ZMod 2) :=
  exteriorPower.ιMulti (ZMod 2) 3 ![a, b, c]

private noncomputable def w3 (x y z : Fin 6) : A5Cube.Cube (ZMod 2) :=
  w3v (e6 x) (e6 y) (e6 z)

private lemma cubeBasis_eq_w3 (I : Set.powersetCard (Fin 6) 3) :
    A5Cube.cubeBasis (ZMod 2) I = w3 (A5Cube.enum I 0) (A5Cube.enum I 1) (A5Cube.enum I 2) := by
  unfold w3 w3v A5Cube.cubeBasis
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  congr 1
  funext t
  fin_cases t <;> simp [Pi.basisFun_apply, e6]

private lemma charTwo_add_self (v : A5Cube.Cube (ZMod 2)) : v + v = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rw [← one_smul (ZMod 2) v, ← add_smul, h, zero_smul]

private lemma w3_swap12 (x y z : Fin 6) : w3 y x z = w3 x y z := by
  have h0 : w3v (e6 x + e6 y) (e6 x + e6 y) (e6 z) = 0 :=
    A5Cube.ι3_eq_fst_snd (e6 x + e6 y) (e6 z)
  have h1 : w3v (e6 x + e6 y) (e6 x + e6 y) (e6 z) =
      w3v (e6 x) (e6 x + e6 y) (e6 z) + w3v (e6 y) (e6 x + e6 y) (e6 z) :=
    A5Cube.ι3_add_fst (K := ZMod 2) (e6 x) (e6 y) (e6 x + e6 y) (e6 z)
  have h2 : w3v (e6 x) (e6 x + e6 y) (e6 z) =
      w3v (e6 x) (e6 x) (e6 z) + w3v (e6 x) (e6 y) (e6 z) :=
    A5Cube.ι3_add_snd (K := ZMod 2) (e6 x) (e6 x) (e6 y) (e6 z)
  have h3 : w3v (e6 y) (e6 x + e6 y) (e6 z) =
      w3v (e6 y) (e6 x) (e6 z) + w3v (e6 y) (e6 y) (e6 z) :=
    A5Cube.ι3_add_snd (K := ZMod 2) (e6 y) (e6 x) (e6 y) (e6 z)
  have e1 : w3v (e6 x) (e6 x) (e6 z) = 0 := A5Cube.ι3_eq_fst_snd (e6 x) (e6 z)
  have e2 : w3v (e6 y) (e6 y) (e6 z) = 0 := A5Cube.ι3_eq_fst_snd (e6 y) (e6 z)
  have key : w3 x y z + w3 y x z = 0 := by
    have hA : w3v (e6 x) (e6 x + e6 y) (e6 z) = w3 x y z := by
      rw [h2, e1, zero_add]
      rfl
    have hB : w3v (e6 y) (e6 x + e6 y) (e6 z) = w3 y x z := by
      rw [h3, e2, add_zero]
      rfl
    have hsum : w3v (e6 x + e6 y) (e6 x + e6 y) (e6 z) = w3 x y z + w3 y x z := by
      rw [h1, hA, hB]
    rw [← hsum, h0]
  have hA : w3 x y z = -w3 y x z := eq_neg_of_add_eq_zero_left key
  have hB : w3 y x z = -w3 y x z := eq_neg_of_add_eq_zero_left (charTwo_add_self _)
  exact hB.trans hA.symm

private lemma w3_swap23 (x y z : Fin 6) : w3 x z y = w3 x y z := by
  have h0 : w3v (e6 x) (e6 y + e6 z) (e6 y + e6 z) = 0 :=
    A5Cube.ι3_eq_snd_thd (e6 y + e6 z) (e6 x)
  have h1 : w3v (e6 x) (e6 y + e6 z) (e6 y + e6 z) =
      w3v (e6 x) (e6 y) (e6 y + e6 z) + w3v (e6 x) (e6 z) (e6 y + e6 z) :=
    A5Cube.ι3_add_snd (K := ZMod 2) (e6 x) (e6 y) (e6 z) (e6 y + e6 z)
  have h2 : w3v (e6 x) (e6 y) (e6 y + e6 z) =
      w3v (e6 x) (e6 y) (e6 y) + w3v (e6 x) (e6 y) (e6 z) :=
    A5Cube.ι3_add_thd (K := ZMod 2) (e6 x) (e6 y) (e6 y) (e6 z)
  have h3 : w3v (e6 x) (e6 z) (e6 y + e6 z) =
      w3v (e6 x) (e6 z) (e6 y) + w3v (e6 x) (e6 z) (e6 z) :=
    A5Cube.ι3_add_thd (K := ZMod 2) (e6 x) (e6 z) (e6 y) (e6 z)
  have e1 : w3v (e6 x) (e6 y) (e6 y) = 0 := A5Cube.ι3_eq_snd_thd (e6 y) (e6 x)
  have e2 : w3v (e6 x) (e6 z) (e6 z) = 0 := A5Cube.ι3_eq_snd_thd (e6 z) (e6 x)
  have key : w3 x y z + w3 x z y = 0 := by
    have hA : w3v (e6 x) (e6 y) (e6 y + e6 z) = w3 x y z := by
      rw [h2, e1, zero_add]
      rfl
    have hB : w3v (e6 x) (e6 z) (e6 y + e6 z) = w3 x z y := by
      rw [h3, e2, add_zero]
      rfl
    have hsum : w3v (e6 x) (e6 y + e6 z) (e6 y + e6 z) = w3 x y z + w3 x z y := by
      rw [h1, hA, hB]
    rw [← hsum, h0]
  have hA : w3 x y z = -w3 x z y := eq_neg_of_add_eq_zero_left key
  have hB : w3 x z y = -w3 x z y := eq_neg_of_add_eq_zero_left (charTwo_add_self _)
  exact hB.trans hA.symm

private lemma w3_self12 (x z : Fin 6) : w3 x x z = 0 := A5Cube.ι3_eq_fst_snd (e6 x) (e6 z)
private lemma w3_self13 (x y : Fin 6) : w3 x y x = 0 := A5Cube.ι3_eq_fst_thd (e6 x) (e6 y)
private lemma w3_self23 (x y : Fin 6) : w3 x y y = 0 := A5Cube.ι3_eq_snd_thd (e6 y) (e6 x)

private lemma transvection_mulVec_e6 (a b m : Fin 6) :
    (Matrix.transvection a b (1 : ZMod 2)).mulVec (e6 m) =
      e6 m + (if m = b then e6 a else 0) := by
  rw [← Matrix.toLin'_apply]
  change CFSG.LieType.Chevalley.ExteriorCube.transvLin a b (1 : ZMod 2) (Pi.single m 1) =
    Pi.single m 1 + (if m = b then Pi.single a 1 else 0)
  rw [CFSG.LieType.Chevalley.ExteriorCube.transvLin_single]
  by_cases hm : m = b
  · subst hm
    simp
  · simp [hm]

private lemma wedge_add_three (u u' v v' w w' : Fin 6 → ZMod 2) :
    w3v (u + u') (v + v') (w + w') =
      w3v u v w + w3v u' v w + w3v u v' w + w3v u' v' w
        + w3v u v w' + w3v u' v w' + w3v u v' w' + w3v u' v' w' := by
  simp only [w3v, A5Cube.ι3_add_fst, A5Cube.ι3_add_snd, A5Cube.ι3_add_thd]
  abel

private lemma w3v_zero_fst (v w : Fin 6 → ZMod 2) : w3v 0 v w = 0 := by
  simpa [w3v] using A5Cube.ι3_smul_fst (K := ZMod 2) (0 : ZMod 2) (0 : Fin 6 → ZMod 2) v w

private lemma w3v_zero_snd (u w : Fin 6 → ZMod 2) : w3v u 0 w = 0 := by
  simpa [w3v] using A5Cube.ι3_smul_snd (K := ZMod 2) (0 : ZMod 2) u (0 : Fin 6 → ZMod 2) w

private lemma w3v_zero_thd (u v : Fin 6 → ZMod 2) : w3v u v 0 = 0 := by
  simpa [w3v] using A5Cube.ι3_smul_thd (K := ZMod 2) (0 : ZMod 2) u v (0 : Fin 6 → ZMod 2)

private lemma w3v_self12 (x z : Fin 6 → ZMod 2) : w3v x x z = 0 := by
  simpa [w3v] using A5Cube.ι3_eq_fst_snd x z

private lemma w3v_self13 (x y : Fin 6 → ZMod 2) : w3v x y x = 0 := by
  simpa [w3v] using A5Cube.ι3_eq_fst_thd x y

private lemma w3v_self23 (x y : Fin 6 → ZMod 2) : w3v x y y = 0 := by
  simpa [w3v] using A5Cube.ι3_eq_snd_thd y x

private lemma cubeAct_elem_w3 (a b : Fin 6) (hab : a ≠ b) (x y z : Fin 6) :
    cubeAct (elem a b) (w3 x y z) =
      w3 x y z + (if x = b then w3 a y z else 0) + (if y = b then w3 x a z else 0)
        + (if z = b then w3 x y a else 0) := by
  have hM : ((elem a b : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      Matrix.transvection a b 1 := by
    rw [elem, dif_neg hab]
    exact Matrix.SpecialLinearGroup.transvection_coe _ _
  change A5Cube.rho (ZMod 2) (Matrix.SpecialLinearGroup.toGL (elem a b))
      (exteriorPower.ιMulti (ZMod 2) 3 ![e6 x, e6 y, e6 z]) = _
  rw [A5Cube.rho_ιMulti]
  have hfun : (fun i => (((elem a b : SL(6, ZMod 2)) : GL (Fin 6) (ZMod 2)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (![e6 x, e6 y, e6 z] i)) =
      ![e6 x + (if x = b then e6 a else 0), e6 y + (if y = b then e6 a else 0),
        e6 z + (if z = b then e6 a else 0)] := by
    funext i
    fin_cases i
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hM]
      exact transvection_mulVec_e6 a b x
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hM]
      exact transvection_mulVec_e6 a b y
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hM]
      exact transvection_mulVec_e6 a b z
  rw [hfun]
  change w3v (e6 x + (if x = b then e6 a else 0)) (e6 y + (if y = b then e6 a else 0))
      (e6 z + (if z = b then e6 a else 0)) = _
  rw [wedge_add_three]
  by_cases hx : x = b <;> by_cases hy : y = b <;> by_cases hz : z = b <;>
    simp [hx, hy, hz, w3, w3v_zero_fst, w3v_zero_snd, w3v_zero_thd,
      w3v_self12, w3v_self13, w3v_self23]



private lemma coord_w3_0 (i k : Fin 6) (h0i : (0 : Fin 6) ≠ i) (h0k : (0 : Fin 6) ≠ k)
    (hik : i ≠ k) (J : Set.powersetCard (Fin 6) 3) :
    A5Cube.coord (ZMod 2) (w3 0 i k) J =
      if J.val = ({0, i, k} : Finset (Fin 6)) then 1 else 0 := by
  have h0i' : (0 : Fin 6) < i := Fin.pos_iff_ne_zero.mpr (Ne.symm h0i)
  by_cases hik' : i < k
  · have h := A5Cube.coord_ιMulti_e_sorted (K := ZMod 2) (i := 0) (j := i) (k := k) h0i' hik' J
    simpa only [w3, w3v, e6, A5Cube.e] using h
  · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hik') (Ne.symm hik)
    have h0k' : (0 : Fin 6) < k := Fin.pos_iff_ne_zero.mpr (Ne.symm h0k)
    have h := A5Cube.coord_ιMulti_e_sorted (K := ZMod 2) (i := 0) (j := k) (k := i) h0k' hki J
    have hset : ({0, i, k} : Finset (Fin 6)) = {0, k, i} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hset, show w3 0 i k = w3 0 k i from (w3_swap23 0 i k).symm]
    simpa only [w3, w3v, e6, A5Cube.e] using h

private def mid : Finset (Fin 6) := {1, 2, 3, 4}

private lemma mid_ne_five {i : Fin 6} (hi : i ∈ mid) : i ≠ 5 := by
  revert hi; fin_cases i <;> simp_all [mid]

private lemma mid_ne_zero {i : Fin 6} (hi : i ∈ mid) : i ≠ 0 := by
  revert hi; fin_cases i <;> simp_all [mid]


private def Plane (i j : Fin 6) : Submodule (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  Submodule.span (ZMod 2) {v | ∃ m : Fin 6, m ∈ mid ∧ m ≠ i ∧ m ≠ j ∧ v = w3 0 i m}

private lemma w3_0_mem_Plane (i j m : Fin 6) (hm : m ∈ mid) (hmi : m ≠ i) (hmj : m ≠ j) :
    w3 0 i m ∈ Plane i j :=
  Submodule.subset_span ⟨m, hm, hmi, hmj, rfl⟩


private lemma Plane_eq_pair (i j k l : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) (hk : k ∈ mid)
    (hl : l ∈ mid) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) (hmid : mid = {i, j, k, l}) :
    Plane i j = Submodule.span (ZMod 2) ({w3 0 i k, w3 0 i l} : Set (A5Cube.Cube (ZMod 2))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨m, hm, hmi, hmj, rfl⟩
    have hm' : m ∈ ({i, j, k, l} : Finset (Fin 6)) := by rw [← hmid]; exact hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
    rcases hm' with rfl | rfl | rfl | rfl
    · exact absurd rfl hmi
    · exact absurd rfl hmj
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    · exact w3_0_mem_Plane i j k hk (Ne.symm hik) (Ne.symm hjk)
    · exact w3_0_mem_Plane i j l hl (Ne.symm hil) (Ne.symm hjl)


private lemma Plane_inter_le (i j k l : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) (hk : k ∈ mid)
    (hl : l ∈ mid) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) (hmid : mid = {i, j, k, l}) :
    Plane i j ⊓ Plane i l ≤ Submodule.span (ZMod 2) ({w3 0 i k} : Set (A5Cube.Cube (ZMod 2))) := by
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxj, hxl⟩ := hx
  have hmid_l : mid = {i, l, j, k} := by
    rw [hmid]; ext m; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [Plane_eq_pair i j k l hi hj hk hl hij hik hil hjk hjl hkl hmid] at hxj
  rw [Plane_eq_pair i l j k hi hl hj hk hil hij hik (Ne.symm hjl) (Ne.symm hkl) hjk hmid_l] at hxl
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxj
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hxl
  have h0i : (0 : Fin 6) ≠ i := Ne.symm (mid_ne_zero hi)
  have h0l : (0 : Fin 6) ≠ l := Ne.symm (mid_ne_zero hl)
  have h0k : (0 : Fin 6) ≠ k := Ne.symm (mid_ne_zero hk)
  have h0j : (0 : Fin 6) ≠ j := Ne.symm (mid_ne_zero hj)
  let S : Set.powersetCard (Fin 6) 3 := A5Cube.tripleSet 0 i l h0i h0l hil
  have hSv : S.val = ({0, i, l} : Finset (Fin 6)) := rfl
  have hgk : A5Cube.coord (ZMod 2) (w3 0 i k) S = 0 := by
    rw [coord_w3_0 i k h0i h0k hik S]
    have hne : S.val ≠ ({0, i, k} : Finset (Fin 6)) := by
      intro h
      have hmem : l ∈ ({0, i, k} : Finset (Fin 6)) := by
        rw [← h, hSv]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h0 | hi' | hk'
      · exact (mid_ne_zero hl) h0
      · exact (Ne.symm hil) hi'
      · exact (Ne.symm hkl) hk'
    rw [if_neg hne]
  have hgl : A5Cube.coord (ZMod 2) (w3 0 i l) S = 1 := by
    rw [coord_w3_0 i l h0i h0l hil S, if_pos hSv]
  have hgj : A5Cube.coord (ZMod 2) (w3 0 i j) S = 0 := by
    rw [coord_w3_0 i j h0i h0j hij S]
    have hne : S.val ≠ ({0, i, j} : Finset (Fin 6)) := by
      intro h
      have hmem : l ∈ ({0, i, j} : Finset (Fin 6)) := by
        rw [← h, hSv]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h0 | hi' | hj'
      · exact (mid_ne_zero hl) h0
      · exact (Ne.symm hil) hi'
      · exact (Ne.symm hjl) hj'
    rw [if_neg hne]
  have hphi : A5Cube.coord (ZMod 2) x S = 0 := by
    rw [← hcd, A5Cube.coord_add, A5Cube.coord_smul, A5Cube.coord_smul, hgj, hgk]
    ring
  have hbx : b = 0 := by
    have h := congrArg (fun z => A5Cube.coord (ZMod 2) z S) hab
    rw [A5Cube.coord_add, A5Cube.coord_smul, A5Cube.coord_smul, hgk, hgl, hphi] at h
    simpa using h
  rw [hbx, zero_smul, add_zero] at hab
  rw [← hab]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private noncomputable def Tij (i j : Fin 6) :
    A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2) :=
  (cubeAct (elem 0 j) - 1).comp (cubeAct (elem i 5) - 1)

private lemma Tij_apply_5 (i j u v : Fin 6) (hij : i ≠ j) (hi5 : i ≠ 5) (h0j : j ≠ 0)
    (hu5 : u ≠ 5) (hv5 : v ≠ 5) (huv : u ≠ v) :
    Tij i j (w3 5 u v) =
      (if u = j then w3 0 i v else 0) + (if v = j then w3 0 i u else 0) := by
  have hB : (cubeAct (elem i 5) - 1) (w3 5 u v) = w3 i u v := by
    rw [LinearMap.sub_apply, cubeAct_elem_w3 i 5 hi5 5 u v]
    simp only [if_true, if_neg hu5, if_neg hv5, add_zero]
    simp
  rw [Tij, LinearMap.comp_apply, hB, LinearMap.sub_apply,
    cubeAct_elem_w3 0 j (Ne.symm h0j) i u v, if_neg hij]
  by_cases hu : u = j
  · subst hu
    simp [Ne.symm huv, w3_swap12]
  · by_cases hv : v = j
    · subst hv
      simp [if_neg hu, w3_swap12, w3_swap23]
    · simp [if_neg hu, if_neg hv]

private lemma Tij_apply_5_mem (i j u v : Fin 6) (hij : i ≠ j) (hi5 : i ≠ 5) (h0j : j ≠ 0)
    (hu5 : u ≠ 5) (hv5 : v ≠ 5) (huv : u ≠ v) :
    Tij i j (w3 5 u v) ∈ Plane i j := by
  rw [Tij_apply_5 i j u v hij hi5 h0j hu5 hv5 huv]
  by_cases hu : u = j
  · rw [if_pos hu, if_neg (Ne.symm (hu ▸ huv)), add_zero]
    by_cases hv0 : v = 0
    · rw [hv0, w3_self13]; exact Submodule.zero_mem (Plane i j)
    · by_cases hvi : v = i
      · rw [hvi, w3_self23]; exact Submodule.zero_mem (Plane i j)
      · exact w3_0_mem_Plane i j v (by revert hv0 hv5; fin_cases v <;> simp_all [mid]) hvi
          (Ne.symm (hu ▸ huv))
  · rw [if_neg hu]
    by_cases hv : v = j
    · rw [if_pos hv, zero_add]
      by_cases hu0 : u = 0
      · rw [hu0, w3_self13]; exact Submodule.zero_mem (Plane i j)
      · by_cases hui : u = i
        · rw [hui, w3_self23]; exact Submodule.zero_mem (Plane i j)
        · exact w3_0_mem_Plane i j u (by revert hu0 hu5; fin_cases u <;> simp_all [mid]) hui hu
    · rw [if_neg hv]; simp


private lemma Tij_apply_w3_mem (i j x y z : Fin 6) (hij : i ≠ j) (hi : i ∈ mid) (hj : j ∈ mid)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Tij i j (w3 x y z) ∈ Plane i j := by
  have hi5 : i ≠ 5 := by revert hi; fin_cases i <;> simp_all [mid]
  have h0j : j ≠ 0 := by revert hj; fin_cases j <;> simp_all [mid]
  by_cases h5 : (5 : Fin 6) ∈ ({x, y, z} : Finset (Fin 6))
  · rw [Finset.mem_insert] at h5
    rcases h5 with rfl | h5
    · exact Tij_apply_5_mem i j y z hij hi5 h0j (Ne.symm hxy)
        (by intro h; exact hxz (by rw [h])) hyz
    · rw [Finset.mem_insert] at h5
      rcases h5 with rfl | h5
      · rw [← w3_swap12 x 5 z]
        exact Tij_apply_5_mem i j x z hij hi5 h0j hxy (by intro h; exact hyz (by rw [h])) hxz
      · rw [Finset.mem_singleton] at h5
        subst h5
        rw [← w3_swap23 x y 5, ← w3_swap12 x 5 y]
        exact Tij_apply_5_mem i j x y hij hi5 h0j hxz hyz hxy
  · have hx5 : x ≠ 5 := by intro h; exact h5 (by rw [h]; simp)
    have hy5 : y ≠ 5 := by intro h; exact h5 (by rw [h]; simp)
    have hz5 : z ≠ 5 := by intro h; exact h5 (by rw [h]; simp)
    have hB : (cubeAct (elem i 5) - 1) (w3 x y z) = 0 := by
      rw [LinearMap.sub_apply, cubeAct_elem_w3 i 5 hi5 x y z]
      simp only [if_neg hx5, if_neg hy5, if_neg hz5, add_zero]
      simp
    rw [Tij, LinearMap.comp_apply, hB, map_zero]
    exact Submodule.zero_mem _


private lemma range_Tij_le (i j : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) (hij : i ≠ j) :
    LinearMap.range (Tij i j) ≤ Plane i j := by
  rw [LinearMap.range_eq_map, ← (A5Cube.cubeBasis (ZMod 2)).span_eq, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, ⟨I, rfl⟩, rfl⟩
  rw [cubeBasis_eq_w3]
  exact Tij_apply_w3_mem i j _ _ _ hij hi hj
    ((A5Cube.enum I).injective.ne (by decide : (0 : Fin 3) ≠ 1))
    ((A5Cube.enum I).injective.ne (by decide : (1 : Fin 3) ≠ 2))
    ((A5Cube.enum I).injective.ne (by decide : (0 : Fin 3) ≠ 2))

private lemma Tij_gen_mem (i j k : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) (hk : k ∈ mid)
    (hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k) :
    w3 0 i k ∈ LinearMap.range (Tij i j) := by
  refine ⟨w3 5 j k, ?_⟩
  have hB : (cubeAct (elem i 5) - 1) (w3 5 j k) = w3 i j k := by
    rw [LinearMap.sub_apply, cubeAct_elem_w3 i 5 (mid_ne_five hi) 5 j k]
    simp only [if_true, if_neg (mid_ne_five hj), if_neg (mid_ne_five hk), add_zero]
    simp
  rw [Tij, LinearMap.comp_apply, hB, LinearMap.sub_apply,
    cubeAct_elem_w3 0 j (Ne.symm (mid_ne_zero hj)) i j k, if_neg hij, if_pos rfl,
    if_neg (Ne.symm hjk)]
  simp only [add_zero]
  rw [show w3 i 0 k = w3 0 i k from (w3_swap12 i 0 k).symm]
  simp


private lemma f_comm_Tij (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
    (hc : ∀ s ∈ Sgrp, f ∘ₗ cubeAct s = cubeAct s ∘ₗ f)
    (i j : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) :
    f ∘ₗ Tij i j = Tij i j ∘ₗ f := by
  have hmemA : elem 0 j ∈ Sgrp := by
    have h1 : 1 ≤ j.val := by revert hj; fin_cases j <;> simp_all [mid]
    exact (le_sup_left : Sone ≤ Sgrp) (Subgroup.subset_closure ⟨j, h1, rfl⟩)
  have hmemB : elem i 5 ∈ Sgrp := by
    have h4 : i.val ≤ 4 := by revert hi; fin_cases i <;> simp_all [mid]
    exact (le_sup_right : Ssix ≤ Sgrp) (Subgroup.subset_closure ⟨i, h4, rfl⟩)
  have hA := hc (elem 0 j) hmemA
  have hB := hc (elem i 5) hmemB
  have hA' : f ∘ₗ (cubeAct (elem 0 j) - 1) = (cubeAct (elem 0 j) - 1) ∘ₗ f := by
    refine LinearMap.ext fun x => ?_
    change f ((cubeAct (elem 0 j) - 1) x) = (cubeAct (elem 0 j) - 1) (f x)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have hx := congrFun (congrArg DFunLike.coe hA) x
    simp only [LinearMap.comp_apply] at hx
    rw [hx]
  have hB' : f ∘ₗ (cubeAct (elem i 5) - 1) = (cubeAct (elem i 5) - 1) ∘ₗ f := by
    refine LinearMap.ext fun x => ?_
    change f ((cubeAct (elem i 5) - 1) x) = (cubeAct (elem i 5) - 1) (f x)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have hx := congrFun (congrArg DFunLike.coe hB) x
    simp only [LinearMap.comp_apply] at hx
    rw [hx]
  rw [Tij]
  calc f ∘ₗ ((cubeAct (elem 0 j) - 1) ∘ₗ (cubeAct (elem i 5) - 1))
      = (f ∘ₗ (cubeAct (elem 0 j) - 1)) ∘ₗ (cubeAct (elem i 5) - 1) := by
          rw [LinearMap.comp_assoc]
    _ = ((cubeAct (elem 0 j) - 1) ∘ₗ f) ∘ₗ (cubeAct (elem i 5) - 1) := by rw [hA']
    _ = (cubeAct (elem 0 j) - 1) ∘ₗ (f ∘ₗ (cubeAct (elem i 5) - 1)) := by
          rw [LinearMap.comp_assoc]
    _ = (cubeAct (elem 0 j) - 1) ∘ₗ ((cubeAct (elem i 5) - 1) ∘ₗ f) := by rw [hB']
    _ = ((cubeAct (elem 0 j) - 1) ∘ₗ (cubeAct (elem i 5) - 1)) ∘ₗ f := by
          rw [LinearMap.comp_assoc]

private lemma f_mem_range_Tij (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
    (hc : ∀ s ∈ Sgrp, f ∘ₗ cubeAct s = cubeAct s ∘ₗ f)
    (i j : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) {y : A5Cube.Cube (ZMod 2)}
    (hy : y ∈ LinearMap.range (Tij i j)) : f y ∈ LinearMap.range (Tij i j) := by
  obtain ⟨x, rfl⟩ := hy
  have hcomm := congrFun (congrArg DFunLike.coe (f_comm_Tij f hc i j hi hj)) x
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm]
  exact ⟨f x, rfl⟩

private lemma f_fix_line (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
    (hf : Function.Injective f)
    (hc : ∀ s ∈ Sgrp, f ∘ₗ cubeAct s = cubeAct s ∘ₗ f)
    (i j k l : Fin 6) (hi : i ∈ mid) (hj : j ∈ mid) (hk : k ∈ mid) (hl : l ∈ mid)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hmid : mid = {i, j, k, l}) :
    f (w3 0 i k) = w3 0 i k := by
  have hg : w3 0 i k ∈ LinearMap.range (Tij i j) := Tij_gen_mem i j k hi hj hk hij hik hjk
  have hg' : w3 0 i k ∈ LinearMap.range (Tij i l) :=
    Tij_gen_mem i l k hi hl hk hil hik (Ne.symm hkl)
  have hyj := f_mem_range_Tij f hc i j hi hj hg
  have hyl := f_mem_range_Tij f hc i l hi hl hg'
  have hy := Plane_inter_le i j k l hi hj hk hl hij hik hil hjk hjl hkl hmid
      ⟨range_Tij_le i j hi hj hij hyj, range_Tij_le i l hi hl hil hyl⟩
  have h0i : (0 : Fin 6) ≠ i := Ne.symm (mid_ne_zero hi)
  have h0k : (0 : Fin 6) ≠ k := Ne.symm (mid_ne_zero hk)
  have hne : w3 0 i k ≠ 0 := by
    intro hzero
    have h := coord_w3_0 i k h0i h0k hik (A5Cube.tripleSet 0 i k h0i h0k hik)
    rw [hzero, A5Cube.coord_zero] at h
    simp at h
    exact h rfl
  have hfne : f (w3 0 i k) ≠ 0 := by
    intro h
    exact hne (hf (by rw [h, map_zero]))
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc'⟩ := hy
  have hc01 : c = 0 ∨ c = 1 := by
    have hlt : c.val < 2 := ZMod.val_lt c
    have h : c.val = 0 ∨ c.val = 1 := by omega
    rcases h with h | h
    · exact Or.inl ((ZMod.val_eq_zero c).mp h)
    · exact Or.inr ((ZMod.val_eq_one (by norm_num) c).mp h)
  rcases hc01 with rfl | rfl
  · rw [zero_smul] at hc'
    exact absurd hc'.symm hfne
  · rw [one_smul] at hc'
    exact hc'.symm


private noncomputable def lineGens : Set (A5Cube.Cube (ZMod 2)) :=
  {w3 0 1 2, w3 0 1 3, w3 0 1 4, w3 0 2 3, w3 0 2 4, w3 0 3 4}

private noncomputable def spanLines : Submodule (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  Submodule.span (ZMod 2) lineGens

private lemma w3_0_in_spanLines (u v : Fin 6) (hu5 : u ≠ 5) (hv5 : v ≠ 5) :
    w3 0 u v ∈ spanLines := by
  have hu : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by
    have h := u.isLt
    have h5 : u.val ≠ 5 := by intro hh; exact hu5 (Fin.ext hh)
    have : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 ∨ u.val = 4 := by omega
    rcases this with h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by
    have h := v.isLt
    have h5 : v.val ≠ 5 := by intro hh; exact hv5 (Fin.ext hh)
    have : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4 := by omega
    rcases this with h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [w3_self12]; exact Submodule.zero_mem spanLines
    · rw [w3_self12]; exact Submodule.zero_mem spanLines
    · rw [w3_self12]; exact Submodule.zero_mem spanLines
    · rw [w3_self12]; exact Submodule.zero_mem spanLines
    · rw [w3_self12]; exact Submodule.zero_mem spanLines
  · rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [w3_self13]; exact Submodule.zero_mem spanLines
    · rw [w3_self23]; exact Submodule.zero_mem spanLines
    · exact Submodule.subset_span (by simp [lineGens])
    · exact Submodule.subset_span (by simp [lineGens])
    · exact Submodule.subset_span (by simp [lineGens])
  · rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [w3_self13]; exact Submodule.zero_mem spanLines
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_self23]; exact Submodule.zero_mem spanLines
    · exact Submodule.subset_span (by simp [lineGens])
    · exact Submodule.subset_span (by simp [lineGens])
  · rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [w3_self13]; exact Submodule.zero_mem spanLines
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_self23]; exact Submodule.zero_mem spanLines
    · exact Submodule.subset_span (by simp [lineGens])
  · rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [w3_self13]; exact Submodule.zero_mem spanLines
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_swap23]; exact Submodule.subset_span (by simp [lineGens])
    · rw [w3_self23]; exact Submodule.zero_mem spanLines

private lemma elem_0_5 : elem 0 5 = CFSG.Holt.SL6.stdTransvection := by
  rw [elem, dif_neg (by decide)]
  rfl

private lemma transvection_W_mem (x y z : Fin 6) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (cubeAct CFSG.Holt.SL6.stdTransvection - 1) (w3 x y z) ∈ spanLines := by
  rw [show CFSG.Holt.SL6.stdTransvection = elem 0 5 from elem_0_5.symm]
  rw [LinearMap.sub_apply, cubeAct_elem_w3 0 5 (by decide) x y z]
  by_cases hx : x = 5
  · rw [if_pos hx, if_neg (Ne.symm (hx ▸ hxy)), if_neg (Ne.symm (hx ▸ hxz))]
    simp only [add_zero, Module.End.one_apply]
    rw [add_sub_cancel_left]
    exact w3_0_in_spanLines y z (Ne.symm (hx ▸ hxy)) (Ne.symm (hx ▸ hxz))
  · rw [if_neg hx]
    by_cases hy : y = 5
    · rw [if_pos hy, if_neg (Ne.symm (hy ▸ hyz))]
      simp only [add_zero, Module.End.one_apply]
      rw [add_sub_cancel_left, ← w3_swap12]
      exact w3_0_in_spanLines x z (hy ▸ hxy) (Ne.symm (hy ▸ hyz))
    · rw [if_neg hy]
      by_cases hz : z = 5
      · rw [if_pos hz]
        simp only [add_zero, Module.End.one_apply]
        rw [add_sub_cancel_left, ← w3_swap23, ← w3_swap12]
        exact w3_0_in_spanLines x y (hz ▸ hxz) (hz ▸ hyz)
      · rw [if_neg hz]
        simp

private lemma Wsp_le_spanLines : Wsp ≤ spanLines := by
  rw [Wsp, LinearMap.range_eq_map, ← (A5Cube.cubeBasis (ZMod 2)).span_eq, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, ⟨I, rfl⟩, rfl⟩
  rw [cubeBasis_eq_w3]
  exact transvection_W_mem _ _ _
    ((A5Cube.enum I).injective.ne (by decide : (0 : Fin 3) ≠ 1))
    ((A5Cube.enum I).injective.ne (by decide : (1 : Fin 3) ≠ 2))
    ((A5Cube.enum I).injective.ne (by decide : (0 : Fin 3) ≠ 2))

private lemma f_fix_gens (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
    (hf : Function.Injective f)
    (hc : ∀ s ∈ Sgrp, f ∘ₗ cubeAct s = cubeAct s ∘ₗ f) :
    ∀ v ∈ spanLines, f v = v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    simp only [lineGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact f_fix_line f hf hc 1 3 2 4 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact f_fix_line f hf hc 1 2 3 4 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact f_fix_line f hf hc 1 2 4 3 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact f_fix_line f hf hc 2 1 3 4 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact f_fix_line f hf hc 2 1 4 3 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact f_fix_line f hf hc 3 1 4 2 (by simp [mid]) (by simp [mid]) (by simp [mid])
        (by simp [mid]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem fix_of_commute_cubeAct
    (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2)) (hf : Function.Injective f)
    (hc : ∀ s ∈ Sgrp, f ∘ₗ cubeAct s = cubeAct s ∘ₗ f) : ∀ w ∈ Wsp, f w = w := by
  intro w hw
  exact f_fix_gens f hf hc w (Wsp_le_spanLines hw)

end CFSG.StandardType.FF81.CentE6
