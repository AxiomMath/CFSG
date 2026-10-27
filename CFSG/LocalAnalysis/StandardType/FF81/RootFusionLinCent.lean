module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

variable (r m : ℕ)

theorem uSub_le_cent : uSub r m ≤ Cent r m := by
  rintro _ ⟨a, b, c, rfl⟩
  rw [Cent, Subgroup.mem_centralizer_singleton_iff, jGL, uGL_mul, uGL_mul]
  simp [add_comm]

theorem levi_mem_cent (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)) :
    levi P R ∈ Cent r m := by
  rw [Cent, Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  simp only [Units.val_mul, jGL, coe_uGL, coe_levi, uMat]
  rw [blk_mul, blk_mul]
  simp

theorem levi_conj_uGL (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
    (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
    (c : Matrix (Fin r) (Fin r) (ZMod 2)) :
    levi P R * uGL a b c * (levi P R)⁻¹ =
      uGL ((P : Matrix (Fin r) (Fin r) (ZMod 2)) * a * ((R⁻¹ : GL (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)))
        ((R : Matrix (Fin m) (Fin m) (ZMod 2)) * b * ((P⁻¹ : GL (Fin r) (ZMod 2)) :
          Matrix (Fin r) (Fin r) (ZMod 2)))
        ((P : Matrix (Fin r) (Fin r) (ZMod 2)) * c * ((P⁻¹ : GL (Fin r) (ZMod 2)) :
          Matrix (Fin r) (Fin r) (ZMod 2))) := by
  apply Units.ext
  have h1 : ((levi P R)⁻¹ : GL (BlkIdx r m) (ZMod 2)).val =
      blk (↑P⁻¹ : Matrix (Fin r) (Fin r) (ZMod 2)) 0 0 (↑R⁻¹ : Matrix (Fin m) (Fin m) (ZMod 2))
        0 ↑P⁻¹ := rfl
  simp only [Units.val_mul, h1, coe_levi, coe_uGL, uMat]
  rw [blk_mul, blk_mul]
  simp [Matrix.mul_assoc]

theorem uGL_commutator (a a' : Matrix (Fin r) (Fin m) (ZMod 2))
    (b b' : Matrix (Fin m) (Fin r) (ZMod 2)) (c c' : Matrix (Fin r) (Fin r) (ZMod 2)) :
    uGL a b c * uGL a' b' c' * (uGL a b c)⁻¹ * (uGL a' b' c')⁻¹ = uGL 0 0 (a * b' + a' * b) := by
  have h2 : ∀ x : Matrix (Fin r) (Fin r) (ZMod 2), x + x = 0 := fun x => by
    ext i j
    simpa using CharTwo.add_self_eq_zero (x i j)
  have hzc : ∀ (x : Matrix (Fin r) (Fin m) (ZMod 2)) (y : Matrix (Fin m) (Fin r) (ZMod 2))
      (w : Matrix (Fin r) (Fin r) (ZMod 2)),
      uGL (0 : Matrix (Fin r) (Fin m) (ZMod 2)) (0 : Matrix (Fin m) (Fin r) (ZMod 2))
          (a * b' + a' * b) * uGL x y w =
        uGL x y w * uGL 0 0 (a * b' + a' * b) := fun x y w => by
    rw [uGL_mul, uGL_mul]
    simp [add_comm]
  have key : uGL a b c * uGL a' b' c' =
      uGL a' b' c' * uGL a b c * uGL 0 0 (a * b' + a' * b) := by
    rw [uGL_mul, uGL_mul, uGL_mul]
    have e1 : a + a' = a' + a + 0 := by rw [add_zero, add_comm]
    have e2 : b + b' = b' + b + 0 := by rw [add_zero, add_comm]
    have e3 : c + c' + a * b' =
        c' + c + a' * b + (a * b' + a' * b) + (a' + a) * (0 : Matrix (Fin m) (Fin r) (ZMod 2)) := by
      rw [Matrix.mul_zero, add_zero]
      calc c + c' + a * b' = (c + c') + a * b' + (a' * b + a' * b) := by rw [h2, add_zero]
        _ = _ := by abel
    rw [e1, e2, e3]
  rw [key]
  calc uGL a' b' c' * uGL a b c * uGL 0 0 (a * b' + a' * b) * (uGL a b c)⁻¹ * (uGL a' b' c')⁻¹
      = uGL a' b' c' * (uGL a b c * uGL 0 0 (a * b' + a' * b)) * (uGL a b c)⁻¹ *
          (uGL a' b' c')⁻¹ := by rw [mul_assoc (uGL a' b' c')]
    _ = uGL a' b' c' * (uGL 0 0 (a * b' + a' * b) * uGL a b c) * (uGL a b c)⁻¹ *
          (uGL a' b' c')⁻¹ := by rw [← hzc]
    _ = uGL a' b' c' * uGL 0 0 (a * b' + a' * b) * (uGL a' b' c')⁻¹ := by group
    _ = uGL 0 0 (a * b' + a' * b) * uGL a' b' c' * (uGL a' b' c')⁻¹ := by rw [← hzc a' b' c']
    _ = uGL 0 0 (a * b' + a' * b) := by group

theorem uSub_le_zSub_of_eq_zero : uSub r 0 ≤ zSub r 0 := by
  rintro _ ⟨a, b, c, rfl⟩
  refine ⟨c, ?_⟩
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  rw [ha, hb]

theorem zSub_comm {x y : GL (BlkIdx r m) (ZMod 2)} (hx : x ∈ zSub r m) (hy : y ∈ zSub r m) :
    x * y = y * x := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨c', rfl⟩ := hy
  rw [uGL_mul, uGL_mul]
  simp [add_comm]

private abbrev centMat (r m : ℕ) : Type := Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)

private theorem cent_E (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) :
    (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        (blk 0 0 1 0 0 0 : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      (blk 0 0 1 0 0 0 : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
  have hJ : (jGL r m : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      1 + (blk 0 0 1 0 0 0 : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
    ext x y
    rcases x with i | i | i <;> rcases y with j | j | j <;>
      simp [jGL, uGL, uMat, blk, Matrix.one_apply, Matrix.add_apply]
  have hm : (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        (jGL r m : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      (jGL r m : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
        (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
    have := congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hk)
    simpa using this
  rw [hJ, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hm
  exact add_left_cancel hm

private theorem cent_BA (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) (i : Fin m)
    (j : Fin r) :
    (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := by
  have hm := cent_E r m k hk
  have h := congrFun₂ hm (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j))
  simpa [blk, Matrix.mul_apply, Matrix.one_apply] using h

private theorem cent_CA (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) (i : Fin r)
    (j : Fin r) :
    (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
  have hm := cent_E r m k hk
  have h := congrFun₂ hm (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))
  simpa [blk, Matrix.mul_apply, Matrix.one_apply] using h

private theorem cent_CB (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) (i : Fin r)
    (j : Fin m) :
    (k : centMat r m) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := by
  have hm := cent_E r m k hk
  have h := congrFun₂ hm (Sum.inl i) (Sum.inr (Sum.inl j))
  simpa [blk, Matrix.mul_apply, Matrix.one_apply] using h.symm

private theorem cent_AA (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) (i : Fin r)
    (j : Fin r) :
    (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inl j) =
      (k : centMat r m) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) := by
  have hm := cent_E r m k hk
  have h := congrFun₂ hm (Sum.inl i) (Sum.inr (Sum.inr j))
  simpa [blk, Matrix.mul_apply, Matrix.one_apply] using h

private theorem cent_eq_blk_AA (k : GL (BlkIdx r m) (ZMod 2)) (hk : k ∈ Cent r m) :
    (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      blk (fun i j => (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inl j))
          (fun i j => (k : centMat r m) (Sum.inl i) (Sum.inr (Sum.inl j)))
          (fun i j => (k : centMat r m) (Sum.inl i) (Sum.inr (Sum.inr j)))
          (fun i j => (k : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)))
          (fun i j => (k : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)))
          (fun i j => (k : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inl j)) := by
  ext x y
  rcases x with i | i | i <;> rcases y with j | j | j
  · rfl
  · rfl
  · rfl
  · exact cent_BA r m k hk i j
  · rfl
  · rfl
  · exact cent_CA r m k hk i j
  · exact cent_CB r m k hk i j
  · exact (cent_AA r m k hk i j).symm

private theorem cent_coe_eq_blk (g : GL (BlkIdx r m) (ZMod 2)) (hg : g ∈ Cent r m) :
    ∃ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
      (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
      (c : Matrix (Fin r) (Fin r) (ZMod 2)),
      (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
        blk (P : Matrix (Fin r) (Fin r) (ZMod 2)) a c (R : Matrix (Fin m) (Fin m) (ZMod 2)) b
          P := by
  set AA : Matrix (Fin r) (Fin r) (ZMod 2) := fun i j =>
    (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inl j) with hAA
  set AB : Matrix (Fin r) (Fin m) (ZMod 2) := fun i j =>
    (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inr (Sum.inl j)) with hAB
  set AC : Matrix (Fin r) (Fin r) (ZMod 2) := fun i j =>
    (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inr (Sum.inr j)) with hAC
  set BB : Matrix (Fin m) (Fin m) (ZMod 2) := fun i j =>
    (g : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) with hBB
  set BC : Matrix (Fin m) (Fin r) (ZMod 2) := fun i j =>
    (g : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) with hBC
  set AA' : Matrix (Fin r) (Fin r) (ZMod 2) := fun i j =>
    (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inl j) with hAA'
  set AB' : Matrix (Fin r) (Fin m) (ZMod 2) := fun i j =>
    (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inr (Sum.inl j)) with hAB'
  set AC' : Matrix (Fin r) (Fin r) (ZMod 2) := fun i j =>
    (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) (Sum.inl i) (Sum.inr (Sum.inr j)) with hAC'
  set BB' : Matrix (Fin m) (Fin m) (ZMod 2) := fun i j =>
    (↑(g⁻¹) : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) with hBB'
  set BC' : Matrix (Fin m) (Fin r) (ZMod 2) := fun i j =>
    (↑(g⁻¹) : centMat r m) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) with hBC'
  have hG : (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = blk AA AB AC BB BC AA := by
    rw [cent_eq_blk_AA r m g hg]
  have hGi : (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      blk AA' AB' AC' BB' BC' AA' := by
    rw [cent_eq_blk_AA r m g⁻¹ ((Cent r m).inv_mem hg)]
  have hmul1 : (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
      (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
    simp
  have hmul2 : (↑(g⁻¹) : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
      (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
    simp
  have hmul1' : (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
      blk AA' AB' AC' BB' BC' AA' = 1 := by
    rw [← hGi]
    exact hmul1
  have hmul2' : blk AA' AB' AC' BB' BC' AA' *
      (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
    rw [← hGi]
    exact hmul2
  have key1 : (blk (AA * AA') (AA * AB' + AB * BB') (AA * AC' + AB * BC' + AC * AA')
      (BB * BB') (BB * BC' + BC * AA') (AA * AA') :
        Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
    calc blk (AA * AA') (AA * AB' + AB * BB') (AA * AC' + AB * BC' + AC * AA')
          (BB * BB') (BB * BC' + BC * AA') (AA * AA')
        = (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) *
            blk AA' AB' AC' BB' BC' AA' := by
          rw [hG, blk_mul]
      _ = 1 := hmul1'
  have key2 : (blk (AA' * AA) (AA' * AB + AB' * BB) (AA' * AC + AB' * BC + AC' * AA)
      (BB' * BB) (BB' * BC + BC' * AA) (AA' * AA) :
        Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) = 1 := by
    calc blk (AA' * AA) (AA' * AB + AB' * BB) (AA' * AC + AB' * BC + AC' * AA)
          (BB' * BB) (BB' * BC + BC' * AA) (AA' * AA)
        = blk AA' AB' AC' BB' BC' AA' *
            (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := by
          rw [hG, blk_mul]
      _ = 1 := hmul2'
  have hAA1 : AA * AA' = 1 := by
    ext i j
    have h := congrFun₂ key1 (Sum.inl i) (Sum.inl j)
    simpa [blk, Matrix.one_apply] using h
  have hAA2 : AA' * AA = 1 := by
    ext i j
    have h := congrFun₂ key2 (Sum.inl i) (Sum.inl j)
    simpa [blk, Matrix.one_apply] using h
  have hBB1 : BB * BB' = 1 := by
    ext i j
    have h := congrFun₂ key1 (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
    simpa [blk, Matrix.one_apply] using h
  have hBB2 : BB' * BB = 1 := by
    ext i j
    have h := congrFun₂ key2 (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
    simpa [blk, Matrix.one_apply] using h
  refine ⟨⟨AA, AA', hAA1, hAA2⟩, ⟨BB, BB', hBB1, hBB2⟩, AB, BC, AC, ?_⟩
  rw [hG]

theorem mem_cent_iff {g : GL (BlkIdx r m) (ZMod 2)} :
    g ∈ Cent r m ↔ ∃ (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
      (c : Matrix (Fin r) (Fin r) (ZMod 2)) (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)),
      g = uGL a b c * levi P R := by
  constructor
  · intro hg
    obtain ⟨P, R, a, b, c, hblk⟩ := cent_coe_eq_blk r m g hg
    refine ⟨a * ((R⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)),
      b * ((P⁻¹ : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)),
      c * ((P⁻¹ : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)), P, R, ?_⟩
    have hRinv : ((R⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *
        (R : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
      simp
    have hPinv : ((P⁻¹ : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)) *
        (P : Matrix (Fin r) (Fin r) (ZMod 2)) = 1 := by
      simp
    apply Units.ext
    rw [hblk, Units.val_mul, coe_uGL, uMat, coe_levi, blk_mul]
    simp only [Matrix.one_mul, Matrix.mul_zero, zero_add, add_zero]
    congr 1
    · simp only [Matrix.mul_assoc, hRinv, Matrix.mul_one]
    · simp only [Matrix.mul_assoc, hPinv, Matrix.mul_one]
    · simp only [Matrix.mul_assoc, hPinv, Matrix.mul_one]
  · rintro ⟨a, b, c, P, R, rfl⟩
    exact (Cent r m).mul_mem (uSub_le_cent r m ⟨a, b, c, rfl⟩) (levi_mem_cent r m P R)

theorem coe_eq_blk_of_mem_cent {g : GL (BlkIdx r m) (ZMod 2)} (hg : g ∈ Cent r m) :
    ∃ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
      (a : Matrix (Fin r) (Fin m) (ZMod 2)) (b : Matrix (Fin m) (Fin r) (ZMod 2))
      (c : Matrix (Fin r) (Fin r) (ZMod 2)),
      (g : Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
        blk (P : Matrix (Fin r) (Fin r) (ZMod 2)) a c (R : Matrix (Fin m) (Fin m) (ZMod 2)) b
          P :=
  cent_coe_eq_blk r m g hg

private theorem cent_uGL_conj_mem (a : Matrix (Fin r) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin r) (ZMod 2)) (c : Matrix (Fin r) (Fin r) (ZMod 2))
    (x : Matrix (Fin r) (Fin m) (ZMod 2)) (y : Matrix (Fin m) (Fin r) (ZMod 2))
    (z : Matrix (Fin r) (Fin r) (ZMod 2)) :
    uGL a b c * uGL x y z * (uGL a b c)⁻¹ ∈ uSub r m := by
  have h : uGL a b c * uGL x y z * (uGL a b c)⁻¹ =
      uGL ((a + x) + -a) ((b + y) + -b)
        (((c + z + a * y) + (a * b - c)) + (a + x) * (-b)) := by
    rw [uGL_mul, uGL_inv, uGL_mul]
  exact ⟨_, _, _, h⟩

theorem normal_uSub : ∀ g ∈ Cent r m, ∀ u ∈ uSub r m, g * u * g⁻¹ ∈ uSub r m := by
  intro g hg u hu
  obtain ⟨a, b, c, P, R, rfl⟩ := (mem_cent_iff r m).mp hg
  obtain ⟨a', b', c', rfl⟩ := hu
  have hconj : (uGL a b c * levi P R) * uGL a' b' c' * (uGL a b c * levi P R)⁻¹ =
      uGL a b c * (levi P R * uGL a' b' c' * (levi P R)⁻¹) * (uGL a b c)⁻¹ := by group
  rw [hconj, levi_conj_uGL]
  exact cent_uGL_conj_mem r m a b c _ _ _

private theorem cent_cancel_right_mat {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (x y : Matrix ι κ (ZMod 2)) (R : GL κ (ZMod 2))
    (h : x * (R : Matrix κ κ (ZMod 2)) = y * (R : Matrix κ κ (ZMod 2))) : x = y := by
  have hRi : (R : Matrix κ κ (ZMod 2)) * ((R⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) = 1 := by
    simp
  calc x = (x * (R : Matrix κ κ (ZMod 2))) * ((R⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) := by
        simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    _ = (y * (R : Matrix κ κ (ZMod 2))) * ((R⁻¹ : GL κ (ZMod 2)) : Matrix κ κ (ZMod 2)) := by
        rw [h]
    _ = y := by simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]

private theorem cent_prod_blk (a : Matrix (Fin r) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin r) (ZMod 2)) (c : Matrix (Fin r) (Fin r) (ZMod 2))
    (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)) :
    ((uGL a b c * levi P R : GL (BlkIdx r m) (ZMod 2)) :
        Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
      blk (P : Matrix (Fin r) (Fin r) (ZMod 2)) (a * (R : Matrix (Fin m) (Fin m) (ZMod 2)))
        (c * (P : Matrix (Fin r) (Fin r) (ZMod 2))) (R : Matrix (Fin m) (Fin m) (ZMod 2))
        (b * (P : Matrix (Fin r) (Fin r) (ZMod 2))) P := by
  rw [Units.val_mul, coe_uGL, uMat, coe_levi, blk_mul]
  simp

private theorem cent_two_pow (r m : ℕ) :
    (2 : ℕ) ^ (m * r) * 2 ^ (r * m) * 2 ^ (r * r) = 2 ^ (r * r + 2 * r * m) := by
  rw [← pow_add, ← pow_add]
  congr 1
  ring

theorem card_uSub : Nat.card (uSub r m) = 2 ^ (r * r + 2 * r * m) := by
  let f : (Matrix (Fin r) (Fin m) (ZMod 2)) × (Matrix (Fin m) (Fin r) (ZMod 2)) ×
      (Matrix (Fin r) (Fin r) (ZMod 2)) → uSub r m :=
    fun x => ⟨uGL x.1 x.2.1 x.2.2, ⟨x.1, x.2.1, x.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, ⟨b, c⟩⟩ ⟨a', ⟨b', c'⟩⟩ h
      have h2 : uGL a b c = uGL a' b' c' := congrArg Subtype.val h
      obtain ⟨h1, h2', h3⟩ := uGL_injective h2
      simp [h1, h2', h3]
    · rintro ⟨g, a, b, c, rfl⟩
      exact ⟨⟨a, ⟨b, c⟩⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm]
  simp only [Nat.card_prod, Matrix.card_matrix, Nat.card_fin, Nat.card_zmod]
  rw [← pow_add, ← pow_add]
  congr 1
  ring

theorem card_cent :
    Nat.card (Cent r m) = 2 ^ (r * r + 2 * r * m) * Nat.card (GL (Fin r) (ZMod 2)) *
      Nat.card (GL (Fin m) (ZMod 2)) := by
  let f : ((Matrix (Fin r) (Fin m) (ZMod 2)) × (Matrix (Fin m) (Fin r) (ZMod 2)) ×
      (Matrix (Fin r) (Fin r) (ZMod 2))) × (GL (Fin r) (ZMod 2) × GL (Fin m) (ZMod 2)) → Cent r m :=
    fun x => ⟨uGL x.1.1 x.1.2.1 x.1.2.2 * levi x.2.1 x.2.2,
      (mem_cent_iff r m).mpr ⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1, x.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ⟨b, c⟩⟩, P, R⟩ ⟨⟨a', ⟨b', c'⟩⟩, P', R'⟩ h
      have hm : (uGL a b c * levi P R : GL (BlkIdx r m) (ZMod 2)) =
          uGL a' b' c' * levi P' R' := congrArg Subtype.val h
      have hm' : ((uGL a b c * levi P R : GL (BlkIdx r m) (ZMod 2)) :
          Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) =
          ((uGL a' b' c' * levi P' R' : GL (BlkIdx r m) (ZMod 2)) :
            Matrix (BlkIdx r m) (BlkIdx r m) (ZMod 2)) := congrArg Units.val hm
      rw [cent_prod_blk r m a b c P R, cent_prod_blk r m a' b' c' P' R'] at hm'
      have hP : P = P' := by
        apply Units.ext
        ext i j
        have := congrFun₂ hm' (Sum.inl i) (Sum.inl j)
        simpa [blk] using this
      have hR : R = R' := by
        apply Units.ext
        ext i j
        have := congrFun₂ hm' (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
        simpa [blk] using this
      subst hP
      subst hR
      have ha : a = a' := by
        apply cent_cancel_right_mat (κ := Fin m) (R := R)
        ext i j
        have := congrFun₂ hm' (Sum.inl i) (Sum.inr (Sum.inl j))
        simpa [blk] using this
      have hb : b = b' := by
        apply cent_cancel_right_mat (ι := Fin m) (κ := Fin r) (R := P)
        ext i j
        have := congrFun₂ hm' (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j))
        simpa [blk] using this
      have hc : c = c' := by
        apply cent_cancel_right_mat (ι := Fin r) (κ := Fin r) (R := P)
        ext i j
        have := congrFun₂ hm' (Sum.inl i) (Sum.inr (Sum.inr j))
        simpa [blk] using this
      subst ha; subst hb; subst hc; rfl
    · rintro ⟨g, hg⟩
      obtain ⟨a, b, c, P, R, rfl⟩ := (mem_cent_iff r m).mp hg
      exact ⟨⟨⟨a, ⟨b, c⟩⟩, P, R⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm]
  simp only [Nat.card_prod, Matrix.card_matrix, Nat.card_fin, Nat.card_zmod]
  rw [← mul_assoc (2 ^ (m * r)) (2 ^ (r * m)) (2 ^ (r * r)), cent_two_pow r m]
  ring

theorem padicValNat_card_GL (d : ℕ) :
    padicValNat 2 (Nat.card (GL (Fin d) (ZMod 2))) = d.choose 2 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq]
  simp only [Nat.card_zmod]
  have hodd : ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 d, (2 ^ j - 1) := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨j, hj, hdvd⟩
    rw [Finset.mem_Icc] at hj
    have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    have hle : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hsub : 2 ∣ 2 ^ j - (2 ^ j - 1) := Nat.dvd_sub h2j hdvd
    rw [Nat.sub_sub_self hle] at hsub
    exact absurd hsub (by decide)
  have hprod : (∏ j ∈ Finset.Icc 1 d, (2 ^ j - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj.1
    omega
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hprod, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd, add_zero]
  exact (Nat.choose_two_right d).symm

private theorem cent_choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have := Nat.choose_succ_succ n 1
  simpa [Nat.choose_one_right, Nat.add_comm] using this

private theorem cent_choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, cent_choose_two_succ (a + b), ih, cent_choose_two_succ b]
      ring

private theorem cent_choose_two_two_mul (r : ℕ) :
    (2 * r).choose 2 = r * r + 2 * r.choose 2 := by
  have h := cent_choose_two_add r r
  rw [← two_mul] at h
  rw [h]; ring

private theorem cent_choose_arith (r m : ℕ) :
    (2 * r + m).choose 2 - r.choose 2 =
      r * r + 2 * r * m + r.choose 2 + m.choose 2 := by
  rw [cent_choose_two_add (2 * r) m, cent_choose_two_two_mul r]
  omega

theorem padicValNat_card_cent :
    padicValNat 2 (Nat.card (Cent r m)) = (2 * r + m).choose 2 - r.choose 2 := by
  rw [card_cent]
  have hGLr : Nat.card (GL (Fin r) (ZMod 2)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hGLm : Nat.card (GL (Fin m) (ZMod 2)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hGLr) hGLm,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hGLr, padicValNat.prime_pow,
    padicValNat_card_GL, padicValNat_card_GL]
  rw [cent_choose_arith]

end CFSG.StandardType.FF81.RootFusionLin

end
