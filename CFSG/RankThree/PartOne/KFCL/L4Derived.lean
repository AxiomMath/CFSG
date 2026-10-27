module

public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

section Centralizer

variable {p : ℕ} (S : Subgroup (SL(4, K)))

@[expose] def cls (a : Fin 4) : ↥S → K := fun s => s.1.1 a a

variable {S}

theorem bd_of_mem_centralizer (hST : S ≤ torus p K) {c : SL(4, K)}
    (hc : c ∈ Subgroup.centralizer (S : Set (SL(4, K)))) {i j : Fin 4} (hij : cls S i ≠ cls S j) :
    c.1 i j = 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hij
  have hcomm := Subgroup.mem_centralizer_iff.1 hc t.1 t.2
  obtain ⟨d, hd, -⟩ := hST t.2
  have h1 := congrArg (fun z : SL(4, K) => z.1 i j) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul, hd, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
  have hti : d i = t.1.1 i i := by rw [hd, diagonal_apply_eq]
  have htj : d j = t.1.1 j j := by rw [hd, diagonal_apply_eq]
  have h2 : c.1 i j * (d i - d j) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exfalso
    apply ht
    show t.1.1 i i = t.1.1 j j
    rw [← hti, ← htj]
    exact sub_eq_zero.1 h

open _root_.Classical in
@[expose] noncomputable def detBlk (k : ↥S → K) (g : SL(4, K)) : K :=
  (g.1.submatrix (Subtype.val : {i // cls S i = k} → Fin 4) Subtype.val).det

theorem detBlk_one (k : ↥S → K) : detBlk k (1 : SL(4, K)) = 1 := by
  classical
  unfold detBlk
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

theorem detBlk_mul (hST : S ≤ torus p K) (k : ↥S → K) {g : SL(4, K)}
    (hg : g ∈ Subgroup.centralizer (S : Set (SL(4, K)))) (h : SL(4, K)) :
    detBlk k (g * h) = detBlk k g * detBlk k h := by
  classical
  unfold detBlk
  rw [← Matrix.det_mul]
  congr 1
  have := blk1_mul (fun i => cls S i = k) g.1 h.1 (fun a b ha hb =>
    bd_of_mem_centralizer hST hg (fun hab => hb (hab.symm.trans ha)))
  exact this

theorem detBlk_mul_inv (hST : S ≤ torus p K) (k : ↥S → K) {g : SL(4, K)}
    (hg : g ∈ Subgroup.centralizer (S : Set (SL(4, K)))) : detBlk k g * detBlk k g⁻¹ = 1 := by
  rw [← detBlk_mul hST k hg, mul_inv_cancel, detBlk_one]

theorem detBlk_commutator (hST : S ≤ torus p K) (k : ↥S → K) {x y : SL(4, K)}
    (hx : x ∈ Subgroup.centralizer (S : Set (SL(4, K))))
    (hy : y ∈ Subgroup.centralizer (S : Set (SL(4, K)))) : detBlk k ⁅x, y⁆ = 1 := by
  have hxy : x * y ∈ Subgroup.centralizer (S : Set (SL(4, K))) := Subgroup.mul_mem _ hx hy
  have hxyx : x * y * x⁻¹ ∈ Subgroup.centralizer (S : Set (SL(4, K))) :=
    Subgroup.mul_mem _ hxy (Subgroup.inv_mem _ hx)
  rw [commutatorElement_def, detBlk_mul hST k hxyx, detBlk_mul hST k hxy, detBlk_mul hST k hx]
  have h1 := detBlk_mul_inv hST k hx
  have h2 := detBlk_mul_inv hST k hy
  calc detBlk k x * detBlk k y * detBlk k x⁻¹ * detBlk k y⁻¹ =
      (detBlk k x * detBlk k x⁻¹) * (detBlk k y * detBlk k y⁻¹) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

end Centralizer

variable {p : ℕ}

theorem derived_le_std (S : Subgroup (SL(4, K))) (hST : S ≤ torus p K) :
    ⁅Subgroup.centralizer (S : Set (SL(4, K))), Subgroup.centralizer (S : Set (SL(4, K)))⁆ ≤
      ⨆ r : {r : {s : Finset (Fin 4) // s.card = 2} // S ≤ hypSub p K r.1}, pairBlock K r.1.1 := by
  classical
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hc : ⁅x, y⁆ ∈ Subgroup.centralizer (S : Set (SL(4, K))) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  have hmem := bd_mem_closure (cls S) ⁅x, y⁆ (fun i j hij => bd_of_mem_centralizer hST hc hij)
    (fun k => detBlk_commutator hST k hx hy)
  refine ((Subgroup.closure_le _).2 ?_) hmem
  rintro _ ⟨i, j, hij, a, hcl, rfl⟩
  have hs2 : ({i, j} : Finset (Fin 4)).card = 2 := Finset.card_pair hij
  have hS : S ≤ hypSub p K {i, j} := by
    intro t ht
    refine ⟨hST ht, fun a ha b hb => ?_⟩
    have hij' : t.1 i i = t.1 j j := congrFun hcl ⟨t, ht⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> simp [hij']
  exact le_iSup (fun r : {r : {s : Finset (Fin 4) // s.card = 2} // S ≤ hypSub p K r.1} =>
    pairBlock K r.1.1) ⟨⟨{i, j}, hs2⟩, hS⟩ (transvection_mem_pairBlock hij a)

end CFSG.RankThree.PartOne.KFCL.L4
