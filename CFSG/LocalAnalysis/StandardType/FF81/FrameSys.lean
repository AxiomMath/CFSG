module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.FrameMat
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
import CFSG.ClassicalInvolution.WeakCT.AutExtend
import CFSG.ClassicalInvolution.WeakCT.Standard
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
import CFSG.ClassicalInvolution.Q3.AE.Twins
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.ClassicalInvolution.WeakCT.TorusAgree

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped MatrixGroups

theorem A2System.map {G H : Type} [Group G] [Group H] {m : ℕ} {adj : Fin m → Fin m → Prop}
    {U : Fin m → Subgroup G} {X : Subgroup G} (h : A2System adj U X) (f : G →* H)
    (hf : Function.Injective f) : A2System adj (fun i => (U i).map f) (X.map f) := by
  obtain ⟨hiso, hgen, hcomm, hpair⟩ := h
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := hiso i
    exact ⟨e.trans (Subgroup.equivMapOfInjective (U i) f hf)⟩
  · rw [← hgen, Subgroup.map_iSup]
  · intro i j hij hnot a ha c hc
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    rw [← map_mul, hcomm i j hij hnot a' ha' c' hc', map_mul]
  · intro i j hadj
    obtain ⟨W, θ, c, hrange, hker, hUV⟩ := hpair i j hadj
    refine ⟨W.map f, f.comp θ, c, ?_, ?_, ?_⟩
    · rw [MonoidHom.range_comp, hrange]
    · rw [MonoidHom.ker_comp_of_injective θ f hf]
      exact hker
    · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp only; rw [← h1]; simp only [Subgroup.map_map, MonoidHom.comp_assoc],
            by dsimp only; rw [← h2]; simp only [Subgroup.map_map, MonoidHom.comp_assoc]⟩
      · exact Or.inr ⟨by dsimp only; rw [← h1]; simp only [Subgroup.map_map, MonoidHom.comp_assoc],
            by dsimp only; rw [← h2]; simp only [Subgroup.map_map, MonoidHom.comp_assoc]⟩

private theorem linearBlockStandardPair_symm {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair (ZMod 2) W U V) :
    LinearBlockStandardPair (ZMod 2) W V U := by
  obtain ⟨θ, c, hrange, hker, h | h⟩ := h
  · exact ⟨θ, c, hrange, hker, Or.inr h⟩
  · exact ⟨θ, c, hrange, hker, Or.inl h⟩

theorem a2System_blockSL2 (n : ℕ) :
    A2System adjA (fun i : Fin n => (blockSL2 (ZMod 2) n i).range) ⊤ := by
  have w := weakCTSystem_standard (K := ZMod 2) n
  refine ⟨w.iso, w.gen, ?_, ?_⟩
  · intro i j hij hnot a ha c hc
    have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hne : (i : ℕ) + 1 ≠ (j : ℕ) := fun h => hnot (Or.inl h)
    have hne' : (j : ℕ) + 1 ≠ (i : ℕ) := fun h => hnot (Or.inr h)
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · exact w.comm i j (by omega) a ha c hc
    · exact (w.comm j i (by omega) c hc a ha).symm
  · intro i j hadj
    rcases hadj with h | h
    · have h' : (j : ℕ) = (i : ℕ) + 1 := by omega
      refine ⟨(blockSL2 (ZMod 2) n i).range ⊔ (blockSL2 (ZMod 2) n j).range, ?_⟩
      rw [← w.join i j (by omega)]
      exact w.pair i j h'
    · have h' : (i : ℕ) = (j : ℕ) + 1 := by omega
      have hp := w.pair j i h'
      rw [← w.join j i (by omega)] at hp
      refine ⟨(blockSL2 (ZMod 2) n i).range ⊔ (blockSL2 (ZMod 2) n j).range, ?_⟩
      have hs := linearBlockStandardPair_symm hp
      rwa [sup_comm] at hs

private theorem adjA_rev {n : ℕ} (i j : Fin n) : adjA i.rev j.rev ↔ adjA i j := by
  unfold adjA
  simp only [Fin.val_rev]
  constructor <;> intro h <;> omega

private theorem a2System_reindex {G : Type} [Group G] {m m' : ℕ} {adj : Fin m → Fin m → Prop}
    {adj' : Fin m' → Fin m' → Prop} {U : Fin m → Subgroup G} {X : Subgroup G}
    (h : A2System adj U X) (e : Fin m' ≃ Fin m)
    (hadj : ∀ i j, adj' i j ↔ adj (e i) (e j)) :
    A2System adj' (fun i => U (e i)) X := by
  obtain ⟨hiso, hgen, hcomm, hpair⟩ := h
  refine ⟨fun i => hiso (e i), ?_, ?_, ?_⟩
  · rw [show (⨆ i, U (e i)) = ⨆ k, U k from Equiv.iSup_comp e, hgen]
  · intro i j hij hnot a ha c hc
    exact hcomm (e i) (e j) (fun h => hij (e.injective h)) (fun h => hnot ((hadj i j).mpr h))
      a ha c hc
  · intro i j hadj'
    exact hpair (e i) (e j) ((hadj i j).mp hadj')

theorem a2System_blockSL2_rev (n : ℕ) :
    A2System adjA (fun i : Fin n => (blockSL2 (ZMod 2) n i.rev).range) ⊤ := by
  have h := a2System_reindex (a2System_blockSL2 n) (Fin.revPerm (n := n))
    (fun i j => (adjA_rev i j).symm)
  simpa only [Fin.revPerm_apply] using h

@[expose] def framePermFun (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : (k : ℕ) < 2 then k else ⟨n + 2 - k, by have := k.isLt; omega⟩

theorem framePermFun_involutive (n : ℕ) : Function.Involutive (framePermFun n) := by
  intro k
  by_cases hk : (k : ℕ) < 2
  · rw [show framePermFun n k = k from by rw [framePermFun, dif_pos hk]]
    rw [framePermFun, dif_pos hk]
  · have h1 : ¬ ((n + 2 - (k : ℕ) : ℕ) < 2) := by have := k.isLt; omega
    rw [show framePermFun n k = ⟨n + 2 - k, by have := k.isLt; omega⟩ from
      by rw [framePermFun, dif_neg hk]]
    rw [framePermFun, dif_neg h1]
    exact Fin.ext (by simp only; omega)

@[expose] def framePerm (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  Function.Involutive.toPerm (framePermFun n) (framePermFun_involutive n)

@[expose] def frameSys (n : ℕ) (i : Fin n) : Subgroup SL(n + 1, ZMod 2) :=
  (blockSL2 (ZMod 2) n i).range.map
    (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom

theorem a2System_frameSys (n : ℕ) : A2System adjA (frameSys n) ⊤ := by
  have hinj : Function.Injective (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom :=
    (MulAut.conj _).injective
  have hsurj : Function.Surjective
      (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom :=
    (MulAut.conj _).surjective
  have h := A2System.map (a2System_blockSL2 n)
    (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom hinj
  rw [Subgroup.map_top_of_surjective _ hsurj] at h
  change A2System adjA (fun i => (blockSL2 (ZMod 2) n i).range.map
    (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom) ⊤
  exact h

private theorem blockSL2_mem_iff_of_maps {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin n)
    (τ : Equiv.Perm (Fin 2))
    (h : ∀ x : Fin 2, σ ⟨i'.val + x.val, by have := i'.isLt; omega⟩ =
      ⟨i.val + (τ x).val, by have := i.isLt; omega⟩) (a : Fin (n + 1)) :
    (i' ≤ (a : ℕ) ∧ (a : ℕ) < i' + 2) ↔ (i ≤ (σ a : ℕ) ∧ (σ a : ℕ) < i + 2) := by
  constructor
  · rintro ⟨ha1, ha2⟩
    obtain ⟨x, hx⟩ : ∃ x : Fin 2, a = ⟨i'.val + x.val, by have := i'.isLt; omega⟩ :=
      ⟨⟨a.val - i', by omega⟩, Fin.ext (by simp only; omega)⟩
    rw [hx, h x]
    dsimp only
    have := (τ x).isLt
    omega
  · rintro ⟨ha1, ha2⟩
    obtain ⟨y, hy⟩ : ∃ y : Fin 2, σ a = ⟨i.val + y.val, by have := i.isLt; omega⟩ :=
      ⟨⟨(σ a).val - i, by omega⟩, Fin.ext (by simp only; omega)⟩
    have hae : a = ⟨i'.val + (τ.symm y).val, by have := i'.isLt; omega⟩ := by
      apply σ.injective
      rw [hy, h (τ.symm y)]
      congr 1
      simp only [Equiv.apply_symm_apply]
    rw [hae]
    dsimp only
    have := (τ.symm y).isLt
    omega

private theorem conj_blockSL2_of_maps {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin n)
    (τ : Equiv.Perm (Fin 2)) (A B : SL(2, ZMod 2))
    (h : ∀ x : Fin 2, σ ⟨i'.val + x.val, by have := i'.isLt; omega⟩ =
      ⟨i.val + (τ x).val, by have := i.isLt; omega⟩)
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).submatrix τ τ) :
    ggPermSL (F := ZMod 2) σ * blockSL2 (ZMod 2) n i A * (ggPermSL (F := ZMod 2) σ)⁻¹ =
      blockSL2 (ZMod 2) n i' B := by
  apply Subtype.ext
  rw [coe_ggPermSL_conj]
  change (blockMat (n + 1) i.val (A : Matrix (Fin 2) (Fin 2) (ZMod 2))).submatrix σ σ =
    blockMat (n + 1) i'.val (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
  ext a b
  rw [Matrix.submatrix_apply]
  by_cases ha : i' ≤ (a : ℕ) ∧ (a : ℕ) < i' + 2
  · by_cases hb : i' ≤ (b : ℕ) ∧ (b : ℕ) < i' + 2
    · obtain ⟨x, hx⟩ : ∃ x : Fin 2, a = ⟨i'.val + x.val, by have := i'.isLt; omega⟩ :=
        ⟨⟨a.val - i', by omega⟩, Fin.ext (by simp only; omega)⟩
      obtain ⟨y, hy⟩ : ∃ y : Fin 2, b = ⟨i'.val + y.val, by have := i'.isLt; omega⟩ :=
        ⟨⟨b.val - i', by omega⟩, Fin.ext (by simp only; omega)⟩
      rw [hx, hy, h x, h y]
      change blockMat (n + 1) i.val (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
          (blockIdx i.val (by omega) (τ x)) (blockIdx i.val (by omega) (τ y)) =
        blockMat (n + 1) i'.val (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
          (blockIdx i'.val (by omega) x) (blockIdx i'.val (by omega) y)
      rw [blockMat_apply_blockIdx (by omega) (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (τ x) (τ y),
        blockMat_apply_blockIdx (by omega) (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) x y, hB]
      rfl
    · have hs : ¬ (i ≤ (σ b : ℕ) ∧ (σ b : ℕ) < i + 2) :=
        fun h' => hb ((blockSL2_mem_iff_of_maps σ i i' τ h b).mpr h')
      rw [blockMat_apply_of_not_mem_right (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (σ a) hs,
        blockMat_apply_of_not_mem_right (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) a hb]
      simp only [Matrix.one_apply, σ.injective.eq_iff]
  · have hs : ¬ (i ≤ (σ a : ℕ) ∧ (σ a : ℕ) < i + 2) :=
      fun h' => ha ((blockSL2_mem_iff_of_maps σ i i' τ h a).mpr h')
    by_cases hb : i' ≤ (b : ℕ) ∧ (b : ℕ) < i' + 2
    · rw [blockMat_apply_of_not_mem_left (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) hs,
        blockMat_apply_of_not_mem_left (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) ha]
      simp only [Matrix.one_apply, σ.injective.eq_iff]
    · rw [blockMat_apply_of_not_mem_left (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) hs,
        blockMat_apply_of_not_mem_left (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) ha]
      simp only [Matrix.one_apply, σ.injective.eq_iff]

private theorem conj_blockSL2_of_maps_id {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin n)
    (A : SL(2, ZMod 2))
    (h0 : σ ⟨i'.val, by have := i'.isLt; omega⟩ = ⟨i.val, by have := i.isLt; omega⟩)
    (h1 : σ ⟨i'.val + 1, by have := i'.isLt; omega⟩ =
      ⟨i.val + 1, by have := i.isLt; omega⟩) :
    ggPermSL (F := ZMod 2) σ * blockSL2 (ZMod 2) n i A * (ggPermSL (F := ZMod 2) σ)⁻¹ =
      blockSL2 (ZMod 2) n i' A := by
  have h : ∀ x : Fin 2, σ ⟨i'.val + x.val, by have := i'.isLt; omega⟩ =
      ⟨i.val + (Equiv.refl (Fin 2) x).val, by have := i.isLt; omega⟩ := by
    intro x
    fin_cases x
    · simpa using h0
    · simpa using h1
  refine conj_blockSL2_of_maps σ i i' (Equiv.refl (Fin 2)) A A h ?_
  simp

private theorem framePerm_apply (n : ℕ) (k : Fin (n + 1)) :
    framePerm n k = framePermFun n k := by
  rw [framePerm]
  exact congrFun (Function.Involutive.coe_toPerm (framePermFun_involutive n)) k

private theorem framePerm_zero (n : ℕ) : framePerm n 0 = 0 := by
  rw [framePerm_apply, framePermFun, dif_pos (by simp)]

private theorem framePerm_one (n : ℕ) [NeZero n] :
    framePerm n ⟨1, by have := NeZero.pos n; omega⟩ =
      ⟨1, by have := NeZero.pos n; omega⟩ := by
  rw [framePerm_apply, framePermFun, dif_pos (by simp)]

private theorem framePerm_of_two_le {n : ℕ} {k : Fin (n + 1)} (hk : 2 ≤ (k : ℕ)) :
    framePerm n k = ⟨n + 2 - k, by have := k.isLt; omega⟩ := by
  rw [framePerm_apply, framePermFun, dif_neg (by omega)]

theorem frameSys_zero (n : ℕ) [NeZero n] : frameSys n 0 = (blockSL2 (ZMod 2) n 0).range := by
  have hfix : ∀ A : SL(2, ZMod 2), ggPermSL (F := ZMod 2) (framePerm n) * blockSL2 (ZMod 2) n 0 A *
      (ggPermSL (F := ZMod 2) (framePerm n))⁻¹ = blockSL2 (ZMod 2) n 0 A :=
    fun A => conj_blockSL2_of_maps_id (framePerm n) 0 0 A (framePerm_zero n)
      (framePerm_one n)
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨A, rfl⟩ := hy
    change (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) (blockSL2 (ZMod 2) n 0 A) ∈
      (blockSL2 (ZMod 2) n 0).range
    rw [MulAut.conj_apply, hfix A]
    exact ⟨A, rfl⟩
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    obtain ⟨A, rfl⟩ := hx
    change (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) (blockSL2 (ZMod 2) n 0 A) =
      blockSL2 (ZMod 2) n 0 A
    rw [MulAut.conj_apply]
    exact hfix A

private theorem conj_blockSL2_of_maps_rev {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin n)
    (A : SL(2, ZMod 2))
    (h0 : σ ⟨i'.val + 1, by have := i'.isLt; omega⟩ = ⟨i.val, by have := i.isLt; omega⟩)
    (h1 : σ ⟨i'.val, by have := i'.isLt; omega⟩ = ⟨i.val + 1, by have := i.isLt; omega⟩) :
    ggPermSL (F := ZMod 2) σ * blockSL2 (ZMod 2) n i A * (ggPermSL (F := ZMod 2) σ)⁻¹ =
      blockSL2 (ZMod 2) n i'
        (ggPermSL (F := ZMod 2) (Equiv.swap 0 1) * A *
          (ggPermSL (F := ZMod 2) (Equiv.swap 0 1))⁻¹) := by
  have h : ∀ x : Fin 2, σ ⟨i'.val + x.val, by have := i'.isLt; omega⟩ =
      ⟨i.val + (Equiv.swap 0 1 x).val, by have := i.isLt; omega⟩ := by
    intro x
    fin_cases x
    · simpa using h1
    · simpa using h0
  exact conj_blockSL2_of_maps σ i i' (Equiv.swap 0 1) A _
    h (coe_ggPermSL_conj (Equiv.swap 0 1) A)

private theorem framePerm_rev_block {n : ℕ} (i i' : Fin n) (hi' : (i' : ℕ) = n + 1 - (i : ℕ)) :
    framePerm n ⟨i'.val + 1, by have := i'.isLt; omega⟩ =
        ⟨i.val, by have := i.isLt; omega⟩ ∧
      framePerm n ⟨i'.val, by have := i'.isLt; omega⟩ =
        ⟨i.val + 1, by have := i.isLt; omega⟩ ∧
      framePerm n ⟨i.val + 1, by have := i.isLt; omega⟩ =
        ⟨i'.val, by have := i'.isLt; omega⟩ ∧
      framePerm n ⟨i.val, by have := i.isLt; omega⟩ =
        ⟨i'.val + 1, by have := i'.isLt; omega⟩ := by
  have hfframe : ∀ x : Fin (n + 1), framePerm n (framePerm n x) = x := by
    intro x
    rw [framePerm_apply, framePerm_apply]
    exact framePermFun_involutive n x
  have h0 : framePerm n ⟨i'.val + 1, by have := i'.isLt; omega⟩ =
      ⟨i.val, by have := i.isLt; omega⟩ := by
    rw [framePerm_of_two_le (by dsimp only; omega)]
    exact Fin.ext (by simp only; omega)
  have h1 : framePerm n ⟨i'.val, by have := i'.isLt; omega⟩ =
      ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    rw [framePerm_of_two_le (by dsimp only; omega)]
    exact Fin.ext (by simp only; omega)
  have h0' : framePerm n ⟨i.val + 1, by have := i.isLt; omega⟩ =
      ⟨i'.val, by have := i'.isLt; omega⟩ := by
    have h := congrArg (framePerm n) h1
    rw [hfframe] at h
    exact h.symm
  have h1' : framePerm n ⟨i.val, by have := i.isLt; omega⟩ =
      ⟨i'.val + 1, by have := i'.isLt; omega⟩ := by
    have h := congrArg (framePerm n) h0
    rw [hfframe] at h
    exact h.symm
  exact ⟨h0, h1, h0', h1'⟩

private theorem conj_framePerm_involutive (n : ℕ) :
    ∀ x : SL(n + 1, ZMod 2),
      (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n)))
        ((MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) x) = x := by
  have hfframe : ∀ x : Fin (n + 1), framePerm n (framePerm n x) = x := by
    intro x
    rw [framePerm_apply, framePerm_apply]
    exact framePermFun_involutive n x
  have hsym : (framePerm n)⁻¹ = framePerm n :=
    Function.Involutive.symm_eq_self_of_involutive (framePerm n) hfframe
  have hPin : (ggPermSL (F := ZMod 2) (framePerm n))⁻¹ =
      ggPermSL (F := ZMod 2) (framePerm n) := by
    rw [ggPermSL_inv, hsym]
  have hPP : ggPermSL (F := ZMod 2) (framePerm n) * ggPermSL (F := ZMod 2) (framePerm n) = 1 := by
    nth_rewrite 2 [← hPin]
    exact mul_inv_cancel _
  have hcomp : (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) *
      (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) = 1 := by
    rw [← map_mul, hPP, map_one]
  intro x
  change ((MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) *
    (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n)))) x = x
  rw [hcomp]
  rfl

theorem frameSys_of_two_le {n : ℕ} (i : Fin n) (hi : 2 ≤ (i : ℕ)) :
    frameSys n i = (blockSL2 (ZMod 2) n ⟨n + 1 - i, by have := i.isLt; omega⟩).range := by
  let i' : Fin n := ⟨n + 1 - i, by have := i.isLt; omega⟩
  have hi'v : (i' : ℕ) = n + 1 - (i : ℕ) := rfl
  obtain ⟨h0, h1, h0', h1'⟩ := framePerm_rev_block i i' hi'v
  change (blockSL2 (ZMod 2) n i).range.map
    (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom =
    (blockSL2 (ZMod 2) n i').range
  have hKL : (blockSL2 (ZMod 2) n i).range.map
      (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom ≤
      (blockSL2 (ZMod 2) n i').range := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨A, rfl⟩ := hy
    change (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) (blockSL2 (ZMod 2) n i A) ∈
      (blockSL2 (ZMod 2) n i').range
    rw [MulAut.conj_apply, conj_blockSL2_of_maps_rev (framePerm n) i i' A h0 h1]
    exact ⟨_, rfl⟩
  have hLK : (blockSL2 (ZMod 2) n i').range.map
      (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))).toMonoidHom ≤
      (blockSL2 (ZMod 2) n i).range := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨A, rfl⟩ := hy
    change (MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) (blockSL2 (ZMod 2) n i' A) ∈
      (blockSL2 (ZMod 2) n i).range
    rw [MulAut.conj_apply, conj_blockSL2_of_maps_rev (framePerm n) i' i A h0' h1']
    exact ⟨_, rfl⟩
  have hff := conj_framePerm_involutive n
  apply le_antisymm hKL
  intro x hx
  exact Subgroup.mem_map.mpr ⟨(MulAut.conj (ggPermSL (F := ZMod 2) (framePerm n))) x,
    hLK ⟨x, hx, rfl⟩, hff x⟩

theorem exists_conj_tOne_mem_range (n : ℕ) [NeZero n] (i : Fin n) :
    ∃ c : SL(n + 1, ZMod 2), c * tOne n * c⁻¹ ∈ (blockSL2 (ZMod 2) n i).range := by
  let i' : Fin (n + 1) := ⟨i.val, by have := i.isLt; omega⟩
  let j0 : Fin (n + 1) := ⟨1, by have := NeZero.pos n; omega⟩
  let j : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j0 j * Equiv.swap 0 i'
  have hσ0 : σ i' = 0 := by
    show Equiv.swap j0 j (Equiv.swap 0 i' i') = 0
    rw [Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (a := j0) (b := j) (x := (0 : Fin (n + 1)))
        (by simp [j0]) (by simp [j])]
  have hσ1 : σ j = j0 := by
    show Equiv.swap j0 j (Equiv.swap 0 i' j) = j0
    rw [Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (n + 1))) (b := i') (x := j)
      (by simp [j]) (by
        have hji : (j : ℕ) = (i : ℕ) + 1 := rfl
        have hii : (i' : ℕ) = (i : ℕ) := rfl
        omega)]
    exact Equiv.swap_apply_right j0 j
  have h0 : σ ⟨i.val, by have := i.isLt; omega⟩ = ⟨0, by have := NeZero.pos n; omega⟩ := hσ0
  have h1 : σ ⟨i.val + 1, by have := i.isLt; omega⟩ =
      ⟨0 + 1, by have := NeZero.pos n; omega⟩ := hσ1
  refine ⟨ggPermSL (F := ZMod 2) σ, ?_⟩
  change ggPermSL (F := ZMod 2) σ * blockSL2 (ZMod 2) n 0 rhoTwo *
    (ggPermSL (F := ZMod 2) σ)⁻¹ ∈ (blockSL2 (ZMod 2) n i).range
  rw [conj_blockSL2_of_maps_id σ 0 i rhoTwo h0 h1]
  exact ⟨rhoTwo, rfl⟩

theorem range_blockSL2_eq (n : ℕ) (i : Fin n) :
    (blockSL2 (ZMod 2) n i).range = Subgroup.zpowers (blockSL2 (ZMod 2) n i rhoTwo) ⊔
      Subgroup.zpowers (blockSL2 (ZMod 2) n i sTwo) := by
  rw [MonoidHom.range_eq_map, ← zpowers_rhoTwo_sup_zpowers_sTwo, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]

theorem map_slGraphAut_range_blockSL (m i : ℕ) (h : i + 2 ≤ m) :
    (blockSL (ZMod 2) m 2 i h).range.map (slGraphAut m (ZMod 2)).toMonoidHom =
      (blockSL (ZMod 2) m 2 i h).range := by
  have hcomp : (slGraphAut m (ZMod 2)).toMonoidHom.comp (blockSL (ZMod 2) m 2 i h) =
      (blockSL (ZMod 2) m 2 i h).comp (invTransposeSL 2).toMonoidHom :=
    MonoidHom.ext fun A => invTransposeSL_blockSL h A
  rw [← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (invTransposeSL 2).surjective, Subgroup.map_top]

private theorem blockSL_congr {K : Type} [Field K] {m k a b : ℕ} (hab : a = b)
    (ha : a + k ≤ m) (hb : b + k ≤ m) :
    blockSL K m k a ha = blockSL K m k b hb := by
  subst hab
  rfl

theorem jBlock_blockSL (n : ℕ) [NeZero n] (i : ℕ) (h : i + 2 ≤ n - 1) (A : SL(2, ZMod 2)) :
    jBlock n (blockSL (ZMod 2) (n - 1) 2 i h A) = blockSL2 (ZMod 2) n ⟨i + 2, by omega⟩ A := by
  rw [jBlock, blockSL2, blockSL_comp_apply, blockSL_congr (Nat.add_comm 2 i)]

theorem tOne_mem_range_blockSL_three (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    tOne n ∈ (blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range := by
  refine ⟨blockSL (ZMod 2) 3 2 0 (by omega) rhoTwo, ?_⟩
  rw [tOne, blockSL2, blockSL_comp_apply]
  exact congrArg (fun f : SL(2, ZMod 2) →* SL(n + 1, ZMod 2) => f rhoTwo)
    (blockSL_congr (by simp) (by omega) (by rw [Fin.val_zero]; omega))

private noncomputable def blockSLThreeEquiv (n : ℕ) (h : 2 ≤ n) :
    SL(3, ZMod 2) ≃* ↥(blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range :=
  MonoidHom.ofInjective (blockSL_injective (K := ZMod 2) (m := n + 1) (k := 3) (i := 0)
    (by omega))

theorem isSimpleGroup_range_blockSL_three (n : ℕ) (h : 2 ≤ n) :
    IsSimpleGroup ↥(blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range :=
  (MulEquiv.isSimpleGroup_congr (blockSLThreeEquiv n h)).mp
    CFSG.ClassicalInvolution.Q3.TL4.isSimpleGroup_sl3Two

theorem card_range_blockSL_three (n : ℕ) (h : 2 ≤ n) :
    Nat.card ↥(blockSL (ZMod 2) (n + 1) 3 0 (by omega)).range = 168 := by
  rw [← Nat.card_congr (blockSLThreeEquiv n h).toEquiv, Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

end CFSG.StandardType.FF81
