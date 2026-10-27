module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatSMem

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open Matrix

private noncomputable def soneA (f : Fin 5 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ∑ k : Fin 5, f k • Matrix.single (0 : Fin 6) k.succ 1

private theorem det_one_add_soneA (f : Fin 5 → ZMod 2) : (1 + soneA f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · have hdiag : ∀ i : Fin 6, (1 + soneA f) i i = 1 := by
      intro i
      fin_cases i <;> simp [soneA,   Fin.sum_univ_five]
    simp [hdiag]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.add_apply,  soneA,  
        smul_eq_mul,  Fin.sum_univ_five]

private noncomputable def soneElem (f : Fin 5 → ZMod 2) : SL(6, ZMod 2) :=
  ⟨1 + soneA f, det_one_add_soneA f⟩

private theorem soneElem_apply (f : Fin 5 → ZMod 2) (k : Fin 5) :
    (soneElem f).1 0 k.succ = f k := by
  fin_cases k <;>
    simp only [soneElem, Subtype.coe_mk, Matrix.add_apply, Matrix.one_apply, soneA,
      Matrix.sum_apply]
  all_goals simp [Fin.sum_univ_five]

private theorem soneElem_mem (f : Fin 5 → ZMod 2) : soneElem f ∈ Sone := by
  rw [mem_Sone_iff]
  constructor
  · simp [soneElem, soneA, Matrix.add_apply,  
      Fin.sum_univ_five]
  · intro i j hi
    fin_cases i <;> fin_cases j <;>
      simp_all [soneElem, soneA, Matrix.add_apply,  
         Fin.sum_univ_five]

private noncomputable def ssixA (f : Fin 5 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ∑ k : Fin 5, f k • Matrix.single k.castSucc (5 : Fin 6) 1

private theorem det_one_add_ssixA (f : Fin 5 → ZMod 2) : (1 + ssixA f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · have hdiag : ∀ i : Fin 6, (1 + ssixA f) i i = 1 := by
      intro i
      fin_cases i <;> simp [ssixA,   Fin.sum_univ_five]
    simp [hdiag]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.add_apply,  ssixA,  
        smul_eq_mul,  Fin.sum_univ_five]

private noncomputable def ssixElem (f : Fin 5 → ZMod 2) : SL(6, ZMod 2) :=
  ⟨1 + ssixA f, det_one_add_ssixA f⟩

private theorem ssixElem_apply (f : Fin 5 → ZMod 2) (k : Fin 5) :
    (ssixElem f).1 k.castSucc 5 = f k := by
  fin_cases k <;>
    simp only [ssixElem, Subtype.coe_mk, Matrix.add_apply, Matrix.one_apply, ssixA,
      Matrix.sum_apply]
  all_goals simp [Fin.sum_univ_five]

private theorem ssixElem_mem (f : Fin 5 → ZMod 2) : ssixElem f ∈ Ssix := by
  rw [mem_Ssix_iff]
  constructor
  · simp [ssixElem, ssixA, Matrix.add_apply,  
      Fin.sum_univ_five]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      simp_all [ssixElem, ssixA, Matrix.add_apply,  
         Fin.sum_univ_five]

private theorem eq_soneElem_of_mem_Sone (g : SL(6, ZMod 2)) (hg : g ∈ Sone) :
    g = soneElem (fun k : Fin 5 => g.1 0 k.succ) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hg' := (mem_Sone_iff g).1 hg
  have hmem := soneElem_mem (fun k : Fin 5 => g.1 0 k.succ)
  have hs' := (mem_Sone_iff (soneElem (fun k : Fin 5 => g.1 0 k.succ))).1 hmem
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · subst hj; rw [hg'.1, hs'.1]
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
      rw [soneElem_apply]
  · rw [hg'.2 i j hi, hs'.2 i j hi]

private theorem eq_ssixElem_of_mem_Ssix (g : SL(6, ZMod 2)) (hg : g ∈ Ssix) :
    g = ssixElem (fun k : Fin 5 => g.1 k.castSucc 5) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hg' := (mem_Ssix_iff g).1 hg
  have hmem := ssixElem_mem (fun k : Fin 5 => g.1 k.castSucc 5)
  have hs' := (mem_Ssix_iff (ssixElem (fun k : Fin 5 => g.1 k.castSucc 5))).1 hmem
  by_cases hj : j = 5
  · subst hj
    by_cases hi : i = 5
    · subst hi; rw [hg'.1, hs'.1]
    · obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last (n := 5) (by simpa using hi)
      rw [← hk, ssixElem_apply]
  · rw [hg'.2 i j hj, hs'.2 i j hj]

private noncomputable def soneEquiv : Sone ≃ (Fin 5 → ZMod 2) where
  toFun g := fun k => (g : SL(6, ZMod 2)).1 0 k.succ
  invFun f := ⟨soneElem f, soneElem_mem f⟩
  left_inv g := by
    apply Subtype.ext
    exact (eq_soneElem_of_mem_Sone g g.2).symm
  right_inv f := by
    funext k
    exact soneElem_apply f k

private noncomputable def ssixEquiv : Ssix ≃ (Fin 5 → ZMod 2) where
  toFun g := fun k => (g : SL(6, ZMod 2)).1 k.castSucc 5
  invFun f := ⟨ssixElem f, ssixElem_mem f⟩
  left_inv g := by
    apply Subtype.ext
    exact (eq_ssixElem_of_mem_Ssix g g.2).symm
  right_inv f := by
    funext k
    exact ssixElem_apply f k

private noncomputable def sgrpA (u v : Fin 4 → ZMod 2) (c : ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (∑ k : Fin 4, u k • Matrix.single (0 : Fin 6) k.castSucc.succ 1)
    + (∑ k : Fin 4, v k • Matrix.single k.castSucc.succ (5 : Fin 6) 1)
    + c • Matrix.single (0 : Fin 6) 5 1

private theorem sgrpA_add (u v u' v' : Fin 4 → ZMod 2) (c c' : ZMod 2) :
    sgrpA u v c + sgrpA u' v' c' = sgrpA (u+u') (v+v') (c+c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgrpA, Matrix.add_apply,   Pi.add_apply, smul_eq_mul,
       Fin.sum_univ_four]

private theorem sgrpA_mul_sgrpA (u v u' v' : Fin 4 → ZMod 2) (c c' : ZMod 2) :
    sgrpA u v c * sgrpA u' v' c' = (∑ k, u k * v' k) • Matrix.single (0:Fin 6) 5 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgrpA, Matrix.add_apply, Matrix.mul_apply,  
      smul_eq_mul, Matrix.single_apply, Fin.sum_univ_four, Fin.sum_univ_six]

private theorem sgrpA_zero_zero (d : ZMod 2) :
    sgrpA (0 : Fin 4 → ZMod 2) 0 d = d • Matrix.single (0:Fin 6) 5 1 := by
  simp [sgrpA]

private noncomputable def sgrpElem (u v : Fin 4 → ZMod 2) (c : ZMod 2) : SL(6, ZMod 2) :=
  ⟨1 + sgrpA u v c, by
    rw [Matrix.det_of_isUpperTriangular]
    · have hdiag : ∀ i : Fin 6, (1 + sgrpA u v c) i i = 1 := by
        intro i
        fin_cases i <;> simp [sgrpA,   Fin.sum_univ_four]
      simp [hdiag]
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.add_apply,  sgrpA,  
          smul_eq_mul,  Fin.sum_univ_four]⟩

private theorem sgrpElem_row (u v : Fin 4 → ZMod 2) (c : ZMod 2) (k : Fin 4) :
    (sgrpElem u v c).1 0 k.castSucc.succ = u k := by
  fin_cases k <;>
    simp [sgrpElem, sgrpA, Matrix.add_apply,  
       smul_eq_mul,  Fin.sum_univ_four]

private theorem sgrpElem_col (u v : Fin 4 → ZMod 2) (c : ZMod 2) (k : Fin 4) :
    (sgrpElem u v c).1 k.castSucc.succ 5 = v k := by
  fin_cases k <;>
    simp [sgrpElem, sgrpA, Matrix.add_apply,  
       smul_eq_mul,  Fin.sum_univ_four]

private theorem sgrpElem_corner (u v : Fin 4 → ZMod 2) (c : ZMod 2) :
    (sgrpElem u v c).1 0 5 = c := by
  simp [sgrpElem, sgrpA, Matrix.add_apply,  
     smul_eq_mul,  Fin.sum_univ_four]

private theorem sgrpElem_mem (u v : Fin 4 → ZMod 2) (c : ZMod 2) : sgrpElem u v c ∈ Sgrp := by
  rw [mem_Sgrp_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [sgrpElem, sgrpA, Matrix.add_apply,  
      Fin.sum_univ_four]
  · simp [sgrpElem, sgrpA, Matrix.add_apply,  
      Fin.sum_univ_four]
  · intro i j hi1 hi4 hj1 hj4
    fin_cases i <;> fin_cases j <;>
      simp_all [sgrpElem, sgrpA, Matrix.add_apply,  
         Fin.sum_univ_four]
  · intro i hi
    fin_cases i <;>
      simp_all [sgrpElem, sgrpA, Matrix.add_apply,  
         Fin.sum_univ_four]
  · intro j hj
    fin_cases j <;>
      simp_all [sgrpElem, sgrpA, Matrix.add_apply,  
         Fin.sum_univ_four]

private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h := ZMod.val_lt x
  rcases (by omega : x.val = 0 ∨ x.val = 1) with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val x, h0]; simp
  · right; rw [← ZMod.natCast_zmod_val x, h1]; simp

private theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

private theorem sgrpElem_mul' (u v u' v' : Fin 4 → ZMod 2) (c c' : ZMod 2) :
    sgrpElem u v c * sgrpElem u' v' c' =
      sgrpElem (u + u') (v + v') (c + c' + ∑ k, u k * v' k) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h : (1 + sgrpA u v c : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (1 + sgrpA u' v' c') =
      1 + sgrpA (u + u') (v + v') (c + c' + ∑ k, u k * v' k) := by
    calc (1 + sgrpA u v c) * (1 + sgrpA u' v' c')
        = 1 + sgrpA u v c + sgrpA u' v' c' + sgrpA u v c * sgrpA u' v' c' := by
          noncomm_ring
      _ = 1 + (sgrpA u v c + sgrpA u' v' c') + sgrpA u v c * sgrpA u' v' c' := by abel
      _ = 1 + sgrpA (u + u') (v + v') (c + c') + sgrpA u v c * sgrpA u' v' c' := by
          rw [sgrpA_add]
      _ = 1 + sgrpA (u + u') (v + v') (c + c') +
            (∑ k, u k * v' k) • Matrix.single (0:Fin 6) 5 1 := by
          rw [sgrpA_mul_sgrpA]
      _ = 1 + (sgrpA (u + u') (v + v') (c + c') +
            (∑ k, u k * v' k) • Matrix.single (0:Fin 6) 5 1) := by abel
      _ = 1 + sgrpA (u + u') (v + v') (c + c' + ∑ k, u k * v' k) := by
          rw [← sgrpA_zero_zero (∑ k, u k * v' k),
            sgrpA_add (u + u') (v + v') 0 0 (c + c') (∑ k, u k * v' k)]
          simp
  change ((1 + sgrpA u v c : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (1 + sgrpA u' v' c')) i j =
    (1 + sgrpA (u + u') (v + v') (c + c' + ∑ k, u k * v' k)) i j
  exact congrFun (congrFun h i) j

private theorem sgrpElem_inv (u v : Fin 4 → ZMod 2) (c : ZMod 2) :
    (sgrpElem u v c)⁻¹ = sgrpElem u v (c + ∑ k, u k * v k) := by
  apply inv_eq_of_mul_eq_one_right
  rw [sgrpElem_mul']
  have huu : u + u = 0 := by funext k; exact zmod_two_add_self (u k)
  have hvv : v + v = 0 := by funext k; exact zmod_two_add_self (v k)
  have hcorner : c + (c + ∑ k, u k * v k) + ∑ k, u k * v k = 0 := by
    rw [show c + (c + ∑ k, u k * v k) + ∑ k, u k * v k =
      (c + c) + ((∑ k, u k * v k) + ∑ k, u k * v k) by abel,
      zmod_two_add_self c, zmod_two_add_self (∑ k, u k * v k), add_zero]
  rw [huu, hvv, hcorner]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [sgrpElem, sgrpA]

private theorem mem_zpowers_sgrpElem_zero_zero (e : ZMod 2) :
    sgrpElem (0 : Fin 4 → ZMod 2) 0 e ∈
      Subgroup.zpowers CFSG.Holt.SL6.stdTransvection := by
  rcases zmod_two_eq_zero_or_one e with h | h
  · subst h
    have : sgrpElem (0 : Fin 4 → ZMod 2) 0 0 = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simp [sgrpElem, sgrpA]
    rw [this]; exact Subgroup.one_mem _
  · subst h
    have : sgrpElem (0 : Fin 4 → ZMod 2) 0 1 = CFSG.Holt.SL6.stdTransvection := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [sgrpElem, Subtype.coe_mk, sgrpA, CFSG.Holt.SL6.coe_stdTransvection]
      simp
    rw [this]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩

private def sgrpCoord (g : Sgrp) :
    (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × ZMod 2 :=
  (fun k => (g : SL(6, ZMod 2)).1 0 k.castSucc.succ,
   fun k => (g : SL(6, ZMod 2)).1 k.castSucc.succ 5,
   (g : SL(6, ZMod 2)).1 0 5)

private theorem sgrpCoord_injective : Function.Injective sgrpCoord := by
  intro g g' h
  have h1 : (fun k : Fin 4 => (g : SL(6, ZMod 2)).1 0 k.castSucc.succ) =
      (fun k : Fin 4 => (g' : SL(6, ZMod 2)).1 0 k.castSucc.succ) :=
    congrArg Prod.fst h
  have h2 : (fun k : Fin 4 => (g : SL(6, ZMod 2)).1 k.castSucc.succ 5) =
      (fun k : Fin 4 => (g' : SL(6, ZMod 2)).1 k.castSucc.succ 5) :=
    congrArg Prod.fst (congrArg Prod.snd h)
  have h3 : (g : SL(6, ZMod 2)).1 0 5 = (g' : SL(6, ZMod 2)).1 0 5 :=
    congrArg Prod.snd (congrArg Prod.snd h)
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hg := (mem_Sgrp_iff (g : SL(6, ZMod 2))).1 g.2
  have hg' := (mem_Sgrp_iff (g' : SL(6, ZMod 2))).1 g'.2
  by_cases hi0 : i = 0
  · rw [hi0]
    by_cases hj0 : j = 0
    · rw [hj0, hg.1, hg'.1]
    · by_cases hj5 : j = 5
      · rw [hj5]; exact h3
      · let k : Fin 4 := ⟨j.val - 1, by omega⟩
        have hk : k.castSucc.succ = j := by
          apply Fin.ext; simp [k]; omega
        have := congrFun h1 k
        rw [hk] at this
        exact this
  · by_cases hi5 : i = 5
    · rw [hi5]
      by_cases hj5 : j = 5
      · rw [hj5, hg.2.1, hg'.2.1]
      · rw [hg.2.2.2.2 j hj5, hg'.2.2.2.2 j hj5]
    · by_cases hj0 : j = 0
      · rw [hj0, hg.2.2.2.1 i hi0, hg'.2.2.2.1 i hi0]
      · by_cases hj5 : j = 5
        · rw [hj5]
          let k : Fin 4 := ⟨i.val - 1, by omega⟩
          have hk : k.castSucc.succ = i := by
            apply Fin.ext; simp [k]; omega
          have := congrFun h2 k
          rw [hk] at this
          exact this
        · have hi1 : 1 ≤ i.val := by have := i.isLt; omega
          have hi4 : i.val ≤ 4 := by have := i.isLt; omega
          have hj1 : 1 ≤ j.val := by have := j.isLt; omega
          have hj4 : j.val ≤ 4 := by have := j.isLt; omega
          rw [hg.2.2.1 i j hi1 hi4 hj1 hj4, hg'.2.2.1 i j hi1 hi4 hj1 hj4]

private theorem sgrpCoord_sgrpElem (u v : Fin 4 → ZMod 2) (c : ZMod 2) :
    sgrpCoord ⟨sgrpElem u v c, sgrpElem_mem u v c⟩ = (u, v, c) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext k; exact sgrpElem_row u v c k
  · funext k; exact sgrpElem_col u v c k
  · exact sgrpElem_corner u v c

private noncomputable def sgrpEquiv :
    Sgrp ≃ ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × ZMod 2) where
  toFun := sgrpCoord
  invFun d := ⟨sgrpElem d.1 d.2.1 d.2.2, sgrpElem_mem d.1 d.2.1 d.2.2⟩
  left_inv g := sgrpCoord_injective (by
    obtain ⟨u, v, c⟩ := sgrpCoord g
    exact sgrpCoord_sgrpElem u v c)
  right_inv d := by
    obtain ⟨u, v, c⟩ := d
    exact sgrpCoord_sgrpElem u v c

private theorem eq_sgrpElem_of_mem_Sgrp (g : SL(6, ZMod 2)) (hg : g ∈ Sgrp) :
    g = sgrpElem (fun k : Fin 4 => g.1 0 k.castSucc.succ)
        (fun k : Fin 4 => g.1 k.castSucc.succ 5) (g.1 0 5) := by
  have h := sgrpEquiv.left_inv ⟨g, hg⟩
  exact (Subtype.ext_iff.mp h).symm

private theorem sgrpElem_eq_iff {a b c a' b' c' : _} :
    sgrpElem a b c = sgrpElem a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h2 : (a, b, c) = (a', b', c') := by
      rw [← sgrpCoord_sgrpElem a b c, ← sgrpCoord_sgrpElem a' b' c']
      exact congrArg sgrpCoord (Subtype.ext h)
    exact ⟨congrArg Prod.fst h2, congrArg Prod.fst (congrArg Prod.snd h2),
      congrArg Prod.snd (congrArg Prod.snd h2)⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

private theorem sgrpElem_commutator (u v u' v' : Fin 4 → ZMod 2) (c c' : ZMod 2) :
    sgrpElem u v c * sgrpElem u' v' c' * (sgrpElem u v c)⁻¹ * (sgrpElem u' v' c')⁻¹ =
      sgrpElem 0 0 ((∑ k, u k * v' k) + ∑ k, u' k * v k) := by
  rw [sgrpElem_inv, sgrpElem_inv, sgrpElem_mul', sgrpElem_mul', sgrpElem_mul']
  rw [sgrpElem_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  · funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl]

private theorem elem_zero_five : elem (0 : Fin 6) 5 = CFSG.Holt.SL6.stdTransvection := rfl

private theorem mem_zpowers_of_shape (g : SL(6, ZMod 2))
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + (g.1 0 5) • Matrix.single (0 : Fin 6) 5 1) :
    g ∈ Subgroup.zpowers CFSG.Holt.SL6.stdTransvection := by
  rcases zmod_two_eq_zero_or_one (g.1 0 5) with h0 | h1
  · have : g = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      rw [h, h0, zero_smul, add_zero]
      intro i j; simp [Matrix.one_apply]
    rw [this]; exact Subgroup.one_mem _
  · have : g = CFSG.Holt.SL6.stdTransvection := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [h, h1, one_smul, CFSG.Holt.SL6.coe_stdTransvection]
    rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩

private theorem sgrpElem_zero_zero_one :
    sgrpElem (0 : Fin 4 → ZMod 2) 0 1 = CFSG.Holt.SL6.stdTransvection := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [sgrpElem, Subtype.coe_mk, sgrpA, CFSG.Holt.SL6.coe_stdTransvection]
  simp [Matrix.add_apply, Matrix.single_apply]

theorem stdTransvection_mem_Sone : CFSG.Holt.SL6.stdTransvection ∈ Sone := by
  rw [← elem_zero_five]
  exact Subgroup.subset_closure ⟨(5 : Fin 6), by decide, rfl⟩

theorem stdTransvection_mem_Ssix : CFSG.Holt.SL6.stdTransvection ∈ Ssix := by
  rw [← elem_zero_five]
  exact Subgroup.subset_closure ⟨(0 : Fin 6), by decide, rfl⟩

theorem Sone_inf_Ssix :
    Sone ⊓ Ssix = Subgroup.zpowers CFSG.Holt.SL6.stdTransvection := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    apply mem_zpowers_of_shape g
    have h1 := (mem_Sone_iff g).1 hg.1
    have h6 := (mem_Ssix_iff g).1 hg.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.add_apply]
  · rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    exact ⟨stdTransvection_mem_Sone, stdTransvection_mem_Ssix⟩

theorem card_Sone : Nat.card Sone = 32 := by
  rw [Nat.card_congr soneEquiv]
  simp [Nat.card_eq_fintype_card,  ZMod.card]

theorem card_Ssix : Nat.card Ssix = 32 := by
  rw [Nat.card_congr ssixEquiv]
  simp [Nat.card_eq_fintype_card,  ZMod.card]

theorem card_Sgrp : Nat.card Sgrp = 512 := by
  rw [Nat.card_congr sgrpEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod,  ZMod.card]

theorem isPGroup_Sgrp : IsPGroup 2 Sgrp :=
  IsPGroup.of_card (n := 9) (by rw [card_Sgrp]; norm_num)

theorem Sone_comm_and_sq (x y : SL(6, ZMod 2)) (hx : x ∈ Sone) (hy : y ∈ Sone) :
    x * y = y * x ∧ x * x = 1 := by
  have hx' := (mem_Sone_iff x).1 hx
  have hy' := (mem_Sone_iff y).1 hy
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_six] <;>
      ring_nf
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_six] <;>
      ring_nf <;> simp [show (2 : ZMod 2) = 0 from rfl]

theorem commutator_mem_zpowers_of_mem_Sgrp (x y : SL(6, ZMod 2)) (hx : x ∈ Sgrp)
    (hy : y ∈ Sgrp) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers CFSG.Holt.SL6.stdTransvection := by
  rw [eq_sgrpElem_of_mem_Sgrp x hx, eq_sgrpElem_of_mem_Sgrp y hy, sgrpElem_commutator]
  exact mem_zpowers_sgrpElem_zero_zero _

theorem comm_stdTransvection_of_mem_Sgrp (x : SL(6, ZMod 2)) (hx : x ∈ Sgrp) :
    x * CFSG.Holt.SL6.stdTransvection = CFSG.Holt.SL6.stdTransvection * x := by
  rw [eq_sgrpElem_of_mem_Sgrp x hx, ← sgrpElem_zero_zero_one, sgrpElem_mul', sgrpElem_mul',
    sgrpElem_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp []
  · simp []
  · simp only [ Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero]
    exact add_comm (x.1 0 5) (1 : ZMod 2)

end CFSG.StandardType.FF81.CentE6

