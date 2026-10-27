module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFGF4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open Matrix
open scoped Matrix commutatorElement MatrixGroups

namespace L7

@[expose] def r1M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0,1,0,0,0,0,0; 1,1,0,0,0,0,0; 0,0,1,0,0,0,0; 0,0,0,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]

@[expose] def r2M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0,1,0,0,0,0,0; 1,1,0,0,0,0,0; 0,0,0,1,0,0,0; 0,0,1,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]

@[expose] def r3M : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0,1,0,0,0,0,0; 1,1,0,0,0,0,0; 0,0,0,1,0,0,0; 0,0,1,1,0,0,0; 0,0,0,0,0,1,0; 0,0,0,0,1,1,0; 0,0,0,0,0,0,1]

@[expose] def rep2M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def e25 : Fin 7 ≃ Fin 2 ⊕ Fin 5 := (finSumFinEquiv : Fin 2 ⊕ Fin 5 ≃ Fin 7).symm

@[expose] def e42 : Fin 7 ≃ Fin 4 ⊕ Fin 3 := (finSumFinEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7).symm

@[expose] def e61 : Fin 7 ≃ Fin 6 ⊕ Fin 1 := (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm

@[expose] def t5a : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def t5b : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem bl_r1 : bl e25 r1M = fromBlocks rhoM 0 0 (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  decide +kernel

theorem bl_r2 : bl e42 r2M = fromBlocks rep2M 0 0 (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide +kernel

theorem bl_r3 : bl e61 r3M = fromBlocks rep3M 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) := by
  decide +kernel

theorem bl_P1 : bl e25 ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r1M + r1M * r1M) =
    fromBlocks 0 0 0 1 := by
  decide +kernel

theorem bl_P2 : bl e42 ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r2M + r2M * r2M) =
    fromBlocks 0 0 0 1 := by
  decide +kernel

theorem bl_P3 : bl e61 ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r3M + r3M * r3M) =
    fromBlocks 0 0 0 1 := by
  decide +kernel

theorem comm_rho : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * rhoM = rhoM * A →
    B * rhoM = rhoM * B → A * B = B * A := by
  decide +kernel

theorem isBlockDiag_r1 {X : Matrix (Fin 7) (Fin 7) (ZMod 2)} (h : X * r1M = r1M * X) :
    IsBlockDiag (bl e25 X) ∧ (bl e25 X).toBlocks₁₁ * rhoM = rhoM * (bl e25 X).toBlocks₁₁ := by
  have hc : Commute X r1M := h
  have hP : Commute X ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r1M + r1M * r1M) :=
    ((Commute.one_right X).add_right hc).add_right (hc.mul_right hc)
  have hbd : IsBlockDiag (bl e25 X) := by
    apply isBlockDiag_of_commute
    rw [← bl_P1, ← bl_mul, ← bl_mul, hP.eq]
  refine ⟨hbd, ?_⟩
  have h' := bl_commute e25 h
  rw [eq_fromBlocks_of_isBlockDiag hbd, bl_r1, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  exact (fromBlocks_inj.mp h').1

theorem isBlockDiag_r2 {X : Matrix (Fin 7) (Fin 7) (ZMod 2)} (h : X * r2M = r2M * X) :
    IsBlockDiag (bl e42 X) ∧ (bl e42 X).toBlocks₁₁ * rep2M = rep2M * (bl e42 X).toBlocks₁₁ := by
  have hc : Commute X r2M := h
  have hP : Commute X ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r2M + r2M * r2M) :=
    ((Commute.one_right X).add_right hc).add_right (hc.mul_right hc)
  have hbd : IsBlockDiag (bl e42 X) := by
    apply isBlockDiag_of_commute
    rw [← bl_P2, ← bl_mul, ← bl_mul, hP.eq]
  refine ⟨hbd, ?_⟩
  have h' := bl_commute e42 h
  rw [eq_fromBlocks_of_isBlockDiag hbd, bl_r2, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  exact (fromBlocks_inj.mp h').1

theorem isBlockDiag_r3 {X : Matrix (Fin 7) (Fin 7) (ZMod 2)} (h : X * r3M = r3M * X) :
    IsBlockDiag (bl e61 X) ∧ (bl e61 X).toBlocks₁₁ * rep3M = rep3M * (bl e61 X).toBlocks₁₁ := by
  have hc : Commute X r3M := h
  have hP : Commute X ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + r3M + r3M * r3M) :=
    ((Commute.one_right X).add_right hc).add_right (hc.mul_right hc)
  have hbd : IsBlockDiag (bl e61 X) := by
    apply isBlockDiag_of_commute
    rw [← bl_P3, ← bl_mul, ← bl_mul, hP.eq]
  refine ⟨hbd, ?_⟩
  have h' := bl_commute e61 h
  rw [eq_fromBlocks_of_isBlockDiag hbd, bl_r3, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  exact (fromBlocks_inj.mp h').1

theorem mat_comm_of_mem {s : SL(7, ZMod 2)} {r : Matrix (Fin 7) (Fin 7) (ZMod 2)}
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r) {g : SL(7, ZMod 2)}
    (hg : g ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) :
    (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * r = r * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
  have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2)))
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  rw [hs] at h
  exact h

@[expose] def blkL {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : Fin 7 ≃ α ⊕ β) (g : SL(7, ZMod 2)) : Matrix α α (ZMod 2) :=
  (bl e (g : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁

@[expose] def blkR {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : Fin 7 ≃ α ⊕ β) (g : SL(7, ZMod 2)) : Matrix β β (ZMod 2) :=
  (bl e (g : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂

theorem blkL_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {g h : SL(7, ZMod 2)}
    (hg : IsBlockDiag (bl e (g : Matrix (Fin 7) (Fin 7) (ZMod 2))))
    (hh : IsBlockDiag (bl e (h : Matrix (Fin 7) (Fin 7) (ZMod 2)))) :
    blkL e (g * h) = blkL e g * blkL e h := by
  unfold blkL
  rw [Matrix.SpecialLinearGroup.coe_mul, bl_mul, IsBlockDiag.toBlocks₁₁_mul hg hh]

theorem blkL_one {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : Fin 7 ≃ α ⊕ β) : blkL e 1 = 1 := by
  unfold blkL
  rw [Matrix.SpecialLinearGroup.coe_one, bl_one, toBlocks₁₁_one]

theorem blkL_mul_inv {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {C : Subgroup SL(7, ZMod 2)}
    (hbd : ∀ x ∈ C, IsBlockDiag (bl e (x : Matrix (Fin 7) (Fin 7) (ZMod 2)))) {x : SL(7, ZMod 2)}
    (hx : x ∈ C) : blkL e x * blkL e x⁻¹ = 1 := by
  rw [← blkL_mul (hbd x hx) (hbd x⁻¹ (C.inv_mem hx)), mul_inv_cancel, blkL_one]

theorem blkL_inv_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {C : Subgroup SL(7, ZMod 2)}
    (hbd : ∀ x ∈ C, IsBlockDiag (bl e (x : Matrix (Fin 7) (Fin 7) (ZMod 2)))) {x : SL(7, ZMod 2)}
    (hx : x ∈ C) : blkL e x⁻¹ * blkL e x = 1 := by
  rw [← blkL_mul (hbd x⁻¹ (C.inv_mem hx)) (hbd x hx), inv_mul_cancel, blkL_one]

theorem blkR_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {g h : SL(7, ZMod 2)}
    (hg : IsBlockDiag (bl e (g : Matrix (Fin 7) (Fin 7) (ZMod 2))))
    (hh : IsBlockDiag (bl e (h : Matrix (Fin 7) (Fin 7) (ZMod 2)))) :
    blkR e (g * h) = blkR e g * blkR e h := by
  unfold blkR
  rw [Matrix.SpecialLinearGroup.coe_mul, bl_mul, IsBlockDiag.toBlocks₂₂_mul hg hh]

theorem blkR_one {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : Fin 7 ≃ α ⊕ β) : blkR e 1 = 1 := by
  unfold blkR
  rw [Matrix.SpecialLinearGroup.coe_one, bl_one, toBlocks₂₂_one]

theorem blkR_mul_inv {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {C : Subgroup SL(7, ZMod 2)}
    (hbd : ∀ x ∈ C, IsBlockDiag (bl e (x : Matrix (Fin 7) (Fin 7) (ZMod 2)))) {x : SL(7, ZMod 2)}
    (hx : x ∈ C) : blkR e x * blkR e x⁻¹ = 1 := by
  rw [← blkR_mul (hbd x hx) (hbd x⁻¹ (C.inv_mem hx)), mul_inv_cancel, blkR_one]

theorem blkR_inv_mul {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {e : Fin 7 ≃ α ⊕ β} {C : Subgroup SL(7, ZMod 2)}
    (hbd : ∀ x ∈ C, IsBlockDiag (bl e (x : Matrix (Fin 7) (Fin 7) (ZMod 2)))) {x : SL(7, ZMod 2)}
    (hx : x ∈ C) : blkR e x⁻¹ * blkR e x = 1 := by
  rw [← blkR_mul (hbd x⁻¹ (C.inv_mem hx)) (hbd x hx), inv_mul_cancel, blkR_one]

theorem one_block_eq : ∀ a b : Matrix (Fin 1) (Fin 1) (ZMod 2), a * b = 1 → a = 1 := by
  decide +kernel

@[expose] def emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 A).submatrix e25 e25

theorem bl_emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    bl e25 (emb5 A) = fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 A :=
  bl_submatrix e25 _

theorem emb5_mul (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : emb5 (A * B) = emb5 A * emb5 B := by
  apply bl_injective e25
  rw [bl_mul, bl_emb5, bl_emb5, bl_emb5, fromBlocks_diag_mul, Matrix.mul_one]

theorem emb5_one : emb5 1 = 1 := by
  apply bl_injective e25
  rw [bl_emb5, bl_one, fromBlocks_one]

theorem det_emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : (emb5 A).det = A.det := by
  rw [emb5, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    _root_.one_mul]

@[expose] noncomputable def iota5 : SL(5, ZMod 2) →* SL(7, ZMod 2) where
  toFun A := ⟨emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)),
    (det_emb5 _).trans (Matrix.SpecialLinearGroup.det_coe A)⟩
  map_one' := Subtype.ext (by simp [emb5_one])
  map_mul' A B := Subtype.ext
    (emb5_mul (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (B : Matrix (Fin 5) (Fin 5) (ZMod 2)))

theorem iota5_injective : Function.Injective iota5 := by
  intro A B h
  apply Subtype.ext
  have h' : emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      emb5 (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) := congrArg Subtype.val h
  have h2 := congrArg (bl e25) h'
  rw [bl_emb5, bl_emb5] at h2
  exact (fromBlocks_inj.mp h2).2.2.2

theorem mem_range_iota5 (z : SL(7, ZMod 2))
    (hz : IsBlockDiag (bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))))
    (h11 : (bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁ = 1) :
    z ∈ iota5.range := by
  have hX := eq_fromBlocks_of_isBlockDiag hz
  rw [h11] at hX
  have hdet : ((bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂).det = 1 := by
    have h1 : (bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).det = 1 :=
      (Matrix.det_submatrix_equiv_self e25.symm (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).trans
        (Matrix.SpecialLinearGroup.det_coe z)
    rw [hX, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, _root_.one_mul] at h1
    exact h1
  rw [MonoidHom.mem_range]
  refine ⟨⟨(bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂, hdet⟩, ?_⟩
  apply Subtype.ext
  change emb5 ((bl e25 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂) =
    (z : Matrix (Fin 7) (Fin 7) (ZMod 2))
  unfold emb5
  rw [← hX, submatrix_bl]

@[expose] def emb6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  (fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))).submatrix e61 e61

theorem bl_emb6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    bl e61 (emb6 A) = fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) :=
  bl_submatrix e61 _

theorem emb6_mul (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) : emb6 (A * B) = emb6 A * emb6 B := by
  apply bl_injective e61
  rw [bl_mul, bl_emb6, bl_emb6, bl_emb6, fromBlocks_diag_mul, Matrix.mul_one]

theorem emb6_one : emb6 1 = 1 := by
  apply bl_injective e61
  rw [bl_emb6, bl_one, fromBlocks_one]

theorem det_emb6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : (emb6 A).det = A.det := by
  rw [emb6, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    _root_.mul_one]

@[expose] noncomputable def iota6 : SL(6, ZMod 2) →* SL(7, ZMod 2) where
  toFun A := ⟨emb6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)),
    (det_emb6 _).trans (Matrix.SpecialLinearGroup.det_coe A)⟩
  map_one' := Subtype.ext (by simp [emb6_one])
  map_mul' A B := Subtype.ext
    (emb6_mul (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) (B : Matrix (Fin 6) (Fin 6) (ZMod 2)))

theorem iota6_injective : Function.Injective iota6 := by
  intro A B h
  apply Subtype.ext
  have h' : emb6 (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      emb6 (B : Matrix (Fin 6) (Fin 6) (ZMod 2)) := congrArg Subtype.val h
  have h2 := congrArg (bl e61) h'
  rw [bl_emb6, bl_emb6] at h2
  exact (fromBlocks_inj.mp h2).1

theorem exists_not_comm_SL5 : ∃ a b : SL(5, ZMod 2), a * b ≠ b * a := by
  refine ⟨mkSL t5a t5a (by decide +kernel), mkSL t5b t5b (by decide +kernel), fun h => ?_⟩
  have h' := congrArg (fun z : SL(5, ZMod 2) => (z : Matrix (Fin 5) (Fin 5) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL] at h'
  exact absurd h' (by decide +kernel)

theorem commutator_blkL_one {C : Subgroup SL(7, ZMod 2)} {e : Fin 7 ≃ Fin 2 ⊕ Fin 5}
    (hbd : ∀ w ∈ C, IsBlockDiag (bl e (w : Matrix (Fin 7) (Fin 7) (ZMod 2))))
    (hrho : ∀ w ∈ C, blkL e w * rhoM = rhoM * blkL e w) {x y : SL(7, ZMod 2)}
    (hx : x ∈ C) (hy : y ∈ C) : blkL e ⁅x, y⁆ = 1 := by
  have hxy : x * y ∈ C := C.mul_mem hx hy
  have hxi : x⁻¹ ∈ C := C.inv_mem hx
  have hyi : y⁻¹ ∈ C := C.inv_mem hy
  have hxyx : x * y * x⁻¹ ∈ C := C.mul_mem hxy hxi
  have hcomm : blkL e x * blkL e y = blkL e y * blkL e x :=
    comm_rho _ _ (hrho x hx) (hrho y hy)
  have hxxi : blkL e x * blkL e x⁻¹ = 1 := blkL_mul_inv hbd hx
  have hyyi : blkL e y * blkL e y⁻¹ = 1 := blkL_mul_inv hbd hy
  rw [commutatorElement_def, blkL_mul (hbd _ hxyx) (hbd _ hyi), blkL_mul (hbd _ hxy) (hbd _ hxi),
    blkL_mul (hbd _ hx) (hbd _ hy)]
  calc blkL e x * blkL e y * blkL e x⁻¹ * blkL e y⁻¹
      = blkL e y * blkL e x * blkL e x⁻¹ * blkL e y⁻¹ := by rw [hcomm]
    _ = blkL e y * (blkL e x * blkL e x⁻¹) * blkL e y⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = blkL e y * blkL e y⁻¹ := by rw [hxxi, Matrix.mul_one]
    _ = 1 := hyyi

theorem commutator_mem_range_iota5 (s : SL(7, ZMod 2))
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r1M) (x y : SL(7, ZMod 2))
    (hx : x ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)))
    (hy : y ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) :
    ⁅x, y⁆ ∈ iota5.range := by
  have hbd : ∀ w ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)),
      IsBlockDiag (bl e25 (w : Matrix (Fin 7) (Fin 7) (ZMod 2))) :=
    fun w hw => (isBlockDiag_r1 (mat_comm_of_mem hs hw)).1
  have hrho : ∀ w ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)),
      blkL e25 w * rhoM = rhoM * blkL e25 w :=
    fun w hw => (isBlockDiag_r1 (mat_comm_of_mem hs hw)).2
  have hc : ⁅x, y⁆ ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  exact mem_range_iota5 ⁅x, y⁆ (hbd _ hc) (commutator_blkL_one hbd hrho hx hy)

theorem good429_r1 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r1M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) := by
  haveI : IsSimpleGroup SL(5, ZMod 2) := isSimpleGroup_SL_zmod_two (by norm_num)
  haveI : Group.IsPerfect SL(5, ZMod 2) := isPerfect_of_simple exists_not_comm_SL5
  haveI : Group.IsPerfect iota5.range :=
    Group.IsPerfect.ofSurjective (f := iota5.rangeRestrict) iota5.rangeRestrict_surjective
  have hcard : Nat.card iota5.range = 9999360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective iota5_injective).toEquiv, card_SL5_zmod_two]
  have hDC : iota5.range ≤ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) * emb5 (A : Matrix (Fin 5) (Fin 5) (ZMod 2))
    rw [hs]
    apply bl_injective e25
    rw [bl_mul, bl_mul, bl_emb5, bl_r1, fromBlocks_diag_mul, fromBlocks_diag_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
  refine Good429.of_perfect_le hDC
    (fun K hKC hKp => le_of_commutator_mem
      (fun a ha b hb => commutator_mem_range_iota5 s hs a b ha hb) hKC hKp) ?_
  exact good429_self hcard (B := 216) (by norm_num) (by norm_num) (by decide +kernel)
    (not_isType429_quot_of_noEqOK hcard (B := 216) (by norm_num) (by norm_num) (by decide +kernel))

theorem rosSL_comm_rep3M (A : SL(3, GaloisField 2 2)) :
    ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * rep3M =
      rep3M * ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have hc : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) *
      Matrix.diagonal (fun _ : Fin 3 => omega4) =
      Matrix.diagonal (fun _ : Fin 3 => omega4) *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact mul_comm _ _
  rw [coe_rosSL, ← ros_scalar_omega, ← map_mul, ← map_mul, hc]

theorem commutator_mem_range_r3 (s : SL(7, ZMod 2))
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r3M) (x y : SL(7, ZMod 2))
    (hx : x ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)))
    (hy : y ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) :
    ⁅x, y⁆ ∈ (iota6.comp rosSL).range := by
  have hbd : ∀ w ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)),
      IsBlockDiag (bl e61 (w : Matrix (Fin 7) (Fin 7) (ZMod 2))) :=
    fun w hw => (isBlockDiag_r3 (mat_comm_of_mem hs hw)).1
  have hrep : ∀ w ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)),
      blkL e61 w * rep3M = rep3M * blkL e61 w :=
    fun w hw => (isBlockDiag_r3 (mat_comm_of_mem hs hw)).2
  have hone : ∀ w ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)), blkR e61 w = 1 :=
    fun w hw => one_block_eq _ _ (blkR_mul_inv hbd hw)
  have hc : ⁅x, y⁆ ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  have hxy : x * y ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) :=
    Subgroup.mul_mem _ hx hy
  have hxyx : x * y * x⁻¹ ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) :=
    Subgroup.mul_mem _ hxy (Subgroup.inv_mem _ hx)
  have h6 : blkL e61 ⁅x, y⁆ = blkL e61 x * blkL e61 y * blkL e61 x⁻¹ * blkL e61 y⁻¹ := by
    rw [commutatorElement_def, blkL_mul (hbd _ hxyx) (hbd _ (Subgroup.inv_mem _ hy)),
      blkL_mul (hbd _ hxy) (hbd _ (Subgroup.inv_mem _ hx)), blkL_mul (hbd _ hx) (hbd _ hy)]
  obtain ⟨A, hA⟩ := exists_rosSL_of_commute (blkL_mul_inv hbd hx) (blkL_inv_mul hbd hx)
    (blkL_mul_inv hbd hy) (blkL_inv_mul hbd hy) (hrep x hx) (hrep y hy)
  have e6 : (bl e61 ((⁅x, y⁆ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁ =
      ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := h6.trans hA.symm
  have e1 : (bl e61 ((⁅x, y⁆ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂ = 1 :=
    hone _ hc
  rw [MonoidHom.mem_range]
  refine ⟨A, ?_⟩
  apply Subtype.ext
  change emb6 ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    ((⁅x, y⁆ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))
  apply bl_injective e61
  rw [bl_emb6, eq_fromBlocks_of_isBlockDiag (hbd _ hc), e6, e1]

theorem good429_r3 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r3M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) := by
  haveI : Group.IsPerfect SL(3, GaloisField 2 2) := isPerfect_SL3_gf4
  have hinj : Function.Injective (iota6.comp rosSL) := iota6_injective.comp rosSL_injective
  haveI : Group.IsPerfect (iota6.comp rosSL).range :=
    Group.IsPerfect.ofSurjective (f := (iota6.comp rosSL).rangeRestrict)
      (iota6.comp rosSL).rangeRestrict_surjective
  have hcard : Nat.card (iota6.comp rosSL).range = 60480 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_SL3_gf4]
  have hDC : (iota6.comp rosSL).range ≤ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change emb6 ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        emb6 ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))
    rw [hs]
    apply bl_injective e61
    rw [bl_mul, bl_mul, bl_emb6, bl_r3, fromBlocks_diag_mul, fromBlocks_diag_mul,
      rosSL_comm_rep3M A]
  refine Good429.of_perfect_le hDC
    (fun K hKC hKp => le_of_commutator_mem
      (fun a ha b hb => commutator_mem_range_r3 s hs a b ha hb) hKC hKp) ?_
  exact good429_self hcard (B := 40) (by norm_num) (by norm_num) (by decide +kernel)
    (not_isType429_quot_of_noEqOK hcard (B := 40) (by norm_num) (by norm_num) (by decide +kernel))

theorem hbd2 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    ∀ x ∈ Subgroup.centralizer ({s} : Set SL(7, ZMod 2)),
      IsBlockDiag (bl e42 (x : Matrix (Fin 7) (Fin 7) (ZMod 2))) :=
  fun x hx => (isBlockDiag_r2 (mat_comm_of_mem hs hx)).1

@[expose] noncomputable def hom4 (s : SL(7, ZMod 2))
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) →* GL (Fin 4) (ZMod 2) where
  toFun x := Units.mk (blkL e42 (x : SL(7, ZMod 2))) (blkL e42 (x : SL(7, ZMod 2))⁻¹)
    (blkL_mul_inv (hbd2 s hs) x.2) (blkL_inv_mul (hbd2 s hs) x.2)
  map_one' := Units.ext (blkL_one e42)
  map_mul' x y := Units.ext (blkL_mul (hbd2 s hs _ x.2) (hbd2 s hs _ y.2))

@[expose] noncomputable def hom3 (s : SL(7, ZMod 2))
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    Subgroup.centralizer ({s} : Set SL(7, ZMod 2)) →* GL (Fin 3) (ZMod 2) where
  toFun x := Units.mk (blkR e42 (x : SL(7, ZMod 2))) (blkR e42 (x : SL(7, ZMod 2))⁻¹)
    (blkR_mul_inv (hbd2 s hs) x.2) (blkR_inv_mul (hbd2 s hs) x.2)
  map_one' := Units.ext (blkR_one e42)
  map_mul' x y := Units.ext (blkR_mul (hbd2 s hs _ x.2) (hbd2 s hs _ y.2))

theorem inj_rep2 (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M * rep2M = rep2M * M)
    (hN : N * rep2M = rep2M * N) (h0 : M *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2) =
      N *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2))
    (h2 : M *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2) = N *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2)) :
    M = N := by
  have e1 : rep2M *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2) = Pi.single (1 : Fin 4) (1 : ZMod 2) := by
    decide +kernel
  have e3 : rep2M *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2) = Pi.single (3 : Fin 4) (1 : ZMod 2) := by
    decide +kernel
  have h1 : M *ᵥ Pi.single (1 : Fin 4) (1 : ZMod 2) = N *ᵥ Pi.single (1 : Fin 4) (1 : ZMod 2) := by
    calc M *ᵥ Pi.single (1 : Fin 4) (1 : ZMod 2)
        = M *ᵥ (rep2M *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2)) := by rw [e1]
      _ = rep2M *ᵥ (M *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
      _ = rep2M *ᵥ (N *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2)) := by rw [h0]
      _ = N *ᵥ (rep2M *ᵥ Pi.single (0 : Fin 4) (1 : ZMod 2)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN]
      _ = N *ᵥ Pi.single (1 : Fin 4) (1 : ZMod 2) := by rw [e1]
  have h3 : M *ᵥ Pi.single (3 : Fin 4) (1 : ZMod 2) = N *ᵥ Pi.single (3 : Fin 4) (1 : ZMod 2) := by
    calc M *ᵥ Pi.single (3 : Fin 4) (1 : ZMod 2)
        = M *ᵥ (rep2M *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2)) := by rw [e3]
      _ = rep2M *ᵥ (M *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
      _ = rep2M *ᵥ (N *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2)) := by rw [h2]
      _ = N *ᵥ (rep2M *ᵥ Pi.single (2 : Fin 4) (1 : ZMod 2)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN]
      _ = N *ᵥ Pi.single (3 : Fin 4) (1 : ZMod 2) := by rw [e3]
  ext i j
  have hc : ∀ k : Fin 4, M *ᵥ Pi.single k (1 : ZMod 2) = N *ᵥ Pi.single k (1 : ZMod 2) := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have := congrFun (hc j) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this

theorem card_range_hom4 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    Nat.card (hom4 s hs).range ≤ 256 := by
  have hφ : Function.Injective (fun u : (hom4 s hs).range =>
      ((((u : GL (Fin 4) (ZMod 2))) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Pi.single (0 : Fin 4) (1 : ZMod 2),
        ((u : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          Pi.single (2 : Fin 4) (1 : ZMod 2))) := by
    rintro ⟨u, x, rfl⟩ ⟨v, y, rfl⟩ h
    dsimp only at h
    obtain ⟨h0, h2⟩ := Prod.mk.inj h
    have hM : blkL e42 (x : SL(7, ZMod 2)) * rep2M = rep2M * blkL e42 (x : SL(7, ZMod 2)) :=
      (isBlockDiag_r2 (mat_comm_of_mem hs x.2)).2
    have hN : blkL e42 (y : SL(7, ZMod 2)) * rep2M = rep2M * blkL e42 (y : SL(7, ZMod 2)) :=
      (isBlockDiag_r2 (mat_comm_of_mem hs y.2)).2
    have hMN : blkL e42 (x : SL(7, ZMod 2)) = blkL e42 (y : SL(7, ZMod 2)) :=
      inj_rep2 _ _ hM hN h0 h2
    exact Subtype.ext (Units.ext hMN)
  have h : Nat.card (hom4 s hs).range ≤
      Nat.card ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
    Nat.card_le_card_of_injective _ hφ
  have hc : Nat.card ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) = 256 := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin] <;> norm_num
  rw [hc] at h
  exact h

theorem card_range_hom3 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    Nat.card (hom3 s hs).range ≤ 512 := by
  have hφ : Function.Injective (fun u : (hom3 s hs).range =>
      ((u : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
    fun u v h => Subtype.ext (Units.ext h)
  have h : Nat.card (hom3 s hs).range ≤ Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    Nat.card_le_card_of_injective _ hφ
  have hc : Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 512 := by
    rw [Matrix.card_matrix, Nat.card_zmod, Nat.card_fin] <;> norm_num
  rw [hc] at h
  exact h

theorem eq_one_of_blocks42 {g : SL(7, ZMod 2)}
    (hg : IsBlockDiag (bl e42 (g : Matrix (Fin 7) (Fin 7) (ZMod 2))))
    (h4 : blkL e42 g = 1) (h3 : blkR e42 g = 1) : g = 1 := by
  apply Subtype.ext
  apply bl_injective e42
  have h4' : (bl e42 (g : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁ = 1 := h4
  have h3' : (bl e42 (g : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂ = 1 := h3
  rw [Matrix.SpecialLinearGroup.coe_one, bl_one, eq_fromBlocks_of_isBlockDiag hg, h4', h3',
    fromBlocks_one]

theorem hinj_r2 (s : SL(7, ZMod 2)) (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M)
    (x : Subgroup.centralizer ({s} : Set SL(7, ZMod 2)))
    (hf : hom4 s hs x = 1) (hg : hom3 s hs x = 1) : x = 1 := by
  have h4 : blkL e42 (x : SL(7, ZMod 2)) = 1 := congrArg Units.val hf
  have h3 : blkR e42 (x : SL(7, ZMod 2)) = 1 := congrArg Units.val hg
  exact Subtype.ext (eq_one_of_blocks42 (hbd2 s hs _ x.2) h4 h3)

theorem good429_r2
    (s : SL(7, ZMod 2))
    (hs : (s : Matrix (Fin 7) (Fin 7) (ZMod 2)) = r2M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(7, ZMod 2))) :=
  good429_of_prod (hom4 s hs) (hom3 s hs) (fun x hf hg => hinj_r2 s hs x hf hg)
    (lt_of_le_of_lt (card_range_hom4 s hs) (by norm_num))
    (lt_of_le_of_lt (card_range_hom3 s hs) (by norm_num))

end L7

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
