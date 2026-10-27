module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4A

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Fischer
open scoped IsMulCommutative

@[expose] def matOf (B : B6) : Matrix (Fin 3) (Fin 3) F4 := (⟨B.c0, B.c2, B.c4⟩ : Mc).toMat

theorem matOf_toB6 (A : Mc) : matOf A.toB6 = A.toMat := rfl

theorem matOf_id : matOf B6.id = 1 := Mc.toMat_one

theorem matOf_comp {B D : B6} (hB : B ∈ gm6) (hD : D ∈ gm6) :
    matOf (B.comp D) = matOf B * matOf D := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  obtain ⟨A', hA', rfl⟩ := List.mem_map.1 hD
  have hv := (cert_gmList_mem A hA).1
  have hv' := (cert_gmList_mem A' hA').1
  rw [← toB6_mul hv hv', matOf_toB6, matOf_toB6, matOf_toB6, Mc.toMat_mul A A' hv hv']

theorem matOf_mulVec {B : B6} (hB : B ∈ gm6) {c : ℕ}
    (hc : c < 64) : (matOf B).mulVec (decV c) = decV (B.app c) := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  rw [matOf_toB6, Mc.toMat_mulVec A (cert_gmList_mem A hA).1, toB6_app A hc]

theorem matOf_apply (B : B6) (i j : Fin 3) :
    matOf B i j = decV (![B.c0, B.c2, B.c4] j) i := rfl

theorem matOf_col0 {B : B6} (h : B.c0 < 4) : matOf B 1 0 = 0 ∧ matOf B 2 0 = 0 := by
  have e1 : B.c0 >>> 2 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have e2 : B.c0 >>> 4 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · show decF (B.c0 >>> (2 * 1)) = 0
    rw [show 2 * 1 = 2 from rfl, e1, decF_zero]
  · show decF (B.c0 >>> (2 * 2)) = 0
    rw [show 2 * 2 = 4 from rfl, e2, decF_zero]

theorem c0_lt_of_presv {B : B6} (h : presv pt1 B = true) : B.c0 < 4 := by
  rw [← B6.app_c0]
  have := (presv_iff pt1 B).1 h 1 (by decide)
  have h4 := pt1_lt _ this
  rcases (mem_pt1_iff _ h4).1 this with e | e | e | e <;> omega

@[expose] def blk (M : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 2) (Fin 2) F4 :=
  fun i j => M i.succ j.succ

theorem blk_mul {M N : Matrix (Fin 3) (Fin 3) F4} (h1 : M 1 0 = 0) (h2 : M 2 0 = 0) :
    blk (M * N) = blk M * blk N := by
  ext i j
  simp only [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> simp [h1, h2]

theorem blk_one : blk 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blk_mulVec {M : Matrix (Fin 3) (Fin 3) F4} (h1 : M 1 0 = 0) (h2 : M 2 0 = 0)
    (x : Fin 3 → F4) : (fun i : Fin 2 => M.mulVec x i.succ) = (blk M).mulVec fun i => x i.succ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, blk]
  fin_cases i <;> simp [h1, h2]

theorem blkC_of_blk_eq_one {B : B6} (h : blk (matOf B) = 1) : blkC B = [1, 0, 0, 1] := by
  have e : ∀ i j : Fin 2, blk (matOf B) i j = (1 : Matrix (Fin 2) (Fin 2) F4) i j := fun i j => by
    rw [h]
  have e00 : decF (B.c2 >>> 2) = 1 := e 0 0
  have e01 : decF (B.c4 >>> 2) = 0 := e 0 1
  have e10 : decF (B.c2 >>> 4) = 0 := e 1 0
  have e11 : decF (B.c4 >>> 4) = 1 := e 1 1
  have c00 : (B.c2 >>> 2) % 4 = 1 := congrArg (fun x : F4 => (x.code : ℕ)) e00
  have c01 : (B.c4 >>> 2) % 4 = 0 := congrArg (fun x : F4 => (x.code : ℕ)) e01
  have c10 : (B.c2 >>> 4) % 4 = 0 := congrArg (fun x : F4 => (x.code : ℕ)) e10
  have c11 : (B.c4 >>> 4) % 4 = 1 := congrArg (fun x : F4 => (x.code : ℕ)) e11
  show [(B.c2 >>> 2) % 4, (B.c4 >>> 2) % 4, (B.c2 >>> 4) % 4, (B.c4 >>> 4) % 4] = [1, 0, 0, 1]
  rw [c00, c01, c10, c11]

section BlkHom

variable {W : Type} [CommGroup W]

theorem blk_cB_mul (C : Coding W) {a b : MulAut W}
    (ha : C.cB a ∈ gm6 ∧ presv pt1 (C.cB a) = true) (hb : C.cB b ∈ gm6) :
    blk (matOf (C.cB (a * b))) = blk (matOf (C.cB a)) * blk (matOf (C.cB b)) := by
  obtain ⟨h1, h2⟩ := matOf_col0 (c0_lt_of_presv ha.2)
  rw [C.cB_mul, matOf_comp ha.1 hb, blk_mul h1 h2]

@[expose] noncomputable def blkHom (C : Coding W)
    {H : Subgroup (MulAut W)} (hH : ∀ a ∈ H, C.cB a ∈ gm6 ∧ presv pt1 (C.cB a) = true) :
    ↥H →* Matrix.GeneralLinearGroup (Fin 2) F4 where
  toFun a :=
    { val := blk (matOf (C.cB a))
      inv := blk (matOf (C.cB ((a⁻¹ : ↥H) : MulAut W)))
      val_inv := by
        rw [← blk_cB_mul C (hH a a.2) (hH _ (a⁻¹).2).1, Subgroup.coe_inv, mul_inv_cancel,
          C.cB_one, matOf_id, blk_one]
      inv_val := by
        rw [← blk_cB_mul C (hH _ (a⁻¹).2) (hH a a.2).1, Subgroup.coe_inv, inv_mul_cancel,
          C.cB_one, matOf_id, blk_one] }
  map_one' := by
    apply Units.ext
    show blk (matOf (C.cB 1)) = 1
    rw [C.cB_one, matOf_id, blk_one]
  map_mul' a b := by
    apply Units.ext
    show blk (matOf (C.cB ((a : MulAut W) * b))) = blk (matOf (C.cB a)) * blk (matOf (C.cB b))
    exact blk_cB_mul C (hH a a.2) (hH b b.2).1

theorem coe_blkHom (C : Coding W) {H : Subgroup (MulAut W)}
    (hH : ∀ a ∈ H, C.cB a ∈ gm6 ∧ presv pt1 (C.cB a) = true) (a : ↥H) :
    ((blkHom C hH a : Matrix.GeneralLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) =
      blk (matOf (C.cB a)) := rfl

theorem blkHom_injective
    (C : Coding W) {H : Subgroup (MulAut W)}
    (hH : ∀ a ∈ H, C.cB a ∈ gm6 ∧ presv pt1 (C.cB a) = true) :
    Function.Injective (blkHom C hH) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : blk (matOf (C.cB a)) = 1 := by
    rw [← coe_blkHom C hH a, ha]
    rfl
  have hid := cert4_blk_ker _ (hH a a.2).1 (hH a a.2).2 (blkC_of_blk_eq_one h1)
  exact Subtype.ext (C.cB_eq_one.1 hid)

end BlkHom

theorem card_F4 : Fintype.card F4 = 4 := F4.card

theorem card_GL2_F4 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F4) = 180 := by
  rw [Matrix.card_GL_field, card_F4]
  decide

theorem gm6_nodup : gm6.Nodup :=
  cert_gmList_nodup.map_on fun _ _ _ _ h => toB6_injective h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mem_N_iff {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.normalizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V ↔
      C.cB a ∈ gm6.filter (presv pt1) := by
  rw [mem_autOn_inf_normalizer hC pt1_lt, List.mem_filter]

theorem card_N
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    Nat.card ↥(autOn (L ⊓ Subgroup.normalizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V) = 180 := by
  classical
  set H := autOn (L ⊓ Subgroup.normalizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V with hHd
  have e : ↥H ≃ {B : B6 // B ∈ gm6.filter (presv pt1)} :=
    Equiv.ofBijective (fun a => ⟨C.cB a, (mem_N_iff hC a).1 a.2⟩)
      ⟨fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab)), fun B => by
        obtain ⟨a, ha⟩ := hC.2 B.1 (List.mem_filter.1 B.2).1
        exact ⟨⟨a, (mem_N_iff hC a).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e]
  have e2 : {B : B6 // B ∈ gm6.filter (presv pt1)} ≃ ↥(gm6.filter (presv pt1)).toFinset :=
    Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard,
    List.toFinset_card_of_nodup (gm6_nodup.filter _), cert4_card_pt1]

theorem normalizer_Vt_equiv
    {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    Nonempty (↥(autOn (L ⊓ Subgroup.normalizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V) ≃*
      Matrix.GeneralLinearGroup (Fin 2) F4) := by
  have hH : ∀ a ∈ autOn (L ⊓ Subgroup.normalizer (C.subG pt1 pt1_zero pt1_xor : Set G)) V,
      C.cB a ∈ gm6 ∧ presv pt1 (C.cB a) = true := fun a ha =>
    (mem_autOn_inf_normalizer hC pt1_lt a).1 ha
  have hinj := blkHom_injective C hH
  have hbij := hinj.bijective_of_nat_card_le (by rw [card_GL2_F4, card_N hC])
  exact ⟨MulEquiv.ofBijective (blkHom C hH) hbij⟩

end CFSG.Quasithin.H13.S127.Mod

end
