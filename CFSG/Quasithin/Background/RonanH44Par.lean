module

public import CFSG.Quasithin.Background.RonanH44Fix
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def hermBlk (X : HMod n K) : Matrix (Fin 2) (Fin 2) K :=
  fun row col => mat X (Fin.castLE (by decide) row) (Fin.castLE (by decide) col)

private def blk (g : SL(3, K)) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => (g : Matrix (Fin 3) (Fin 3) K) (Fin.castLE (by decide) i) (Fin.castLE (by decide) j)

private theorem blk_mul {g h : SL(3, K)} (hg : g ∈ stabW K) (hh : h ∈ stabW K) :
    blk (g * h) = blk g * blk h := by
  obtain ⟨hg0, hg1⟩ := hg
  obtain ⟨hh0, hh1⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, hg0, hg1, hh0, hh1]

private theorem blk_one : blk (1 : SL(3, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

private def blkUnit (g : ↥(stabW K)) : GL (Fin 2) K :=
  ⟨blk (g : SL(3, K)), blk ((g : SL(3, K))⁻¹),
    by rw [← blk_mul g.2 (inv_mem g.2), mul_inv_cancel, blk_one],
    by rw [← blk_mul (inv_mem g.2) g.2, inv_mul_cancel, blk_one]⟩

private def blkHom : ↥(stabW K) →* GL (Fin 2) K :=
  MonoidHom.mk' blkUnit fun g h => Units.ext (blk_mul g.2 h.2)

theorem herm_parabolic_action {P Q : Subgroup SL(3, K)} {S : Subgroup (HMod n K)}
    (hP : P = stabW K) (hQ : Q = QWs K) (hS : S = blkW n K) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ action : ↥P →* GL (Fin 2) K,
      Function.Surjective action ∧
      (∀ groupElement : ↥P, action groupElement = 1 ↔ (groupElement : SL(3, K)) ∈ Q) ∧
      (∀ groupElement : ↥P, ∀ row col : Fin 2,
          (action groupElement : Matrix (Fin 2) (Fin 2) K) row col =
            ((groupElement : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)
              (Fin.castLE (by decide) row) (Fin.castLE (by decide) col)) ∧
      (∀ block : Matrix (Fin 2) (Fin 2) K,
        (block.map (bar n))ᵀ = block →
        ∃ vector ∈ S, hermBlk vector = block) ∧
      (∀ (groupElement : ↥P) (vector : HMod n K),
        vector ∈ S →
        rho hK (groupElement : SL(3, K)) vector ∈ S ∧
        hermBlk (rho hK (groupElement : SL(3, K)) vector) =
          (action groupElement : Matrix (Fin 2) (Fin 2) K) * hermBlk vector *
            ((action groupElement : Matrix (Fin 2) (Fin 2) K).map (bar n))ᵀ ∧
        (hermBlk (rho hK (groupElement : SL(3, K)) vector)).det =
          ((action groupElement : Matrix (Fin 2) (Fin 2) K).det *
            bar n ((action groupElement : Matrix (Fin 2) (Fin 2) K).det)) *
              (hermBlk vector).det) := by
  subst hP hQ hS
  rw [QWs_eq_Q2]
  obtain ⟨action, hact⟩ : ∃ action : ↥(stabW K) →* GL (Fin 2) K,
      ∀ (g : ↥(stabW K)) (row col : Fin 2), (action g : Matrix (Fin 2) (Fin 2) K) row col =
        ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) (Fin.castLE (by decide) row)
          (Fin.castLE (by decide) col) :=
    ⟨blkHom, fun _ _ _ => rfl⟩
  refine ⟨action, ?_, ?_, fun g row col => hact g row col, ?_, ?_⟩
  ·
    intro A
    obtain ⟨e, he⟩ : ∃ e : K, (A : Matrix (Fin 2) (Fin 2) K).det * e = 1 :=
      ⟨((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det, by
        rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]⟩
    rw [Matrix.det_fin_two] at he
    obtain ⟨g3, hg3⟩ : ∃ g3 : Matrix (Fin 3) (Fin 3) K,
        g3 = !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0;
          (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1, 0;
          0, 0, e] := ⟨_, rfl⟩
    have hdet : g3.det = 1 := by
      rw [hg3, Matrix.det_fin_three]
      simp
      linear_combination he
    have hmem : (⟨g3, hdet⟩ : SL(3, K)) ∈ stabW K := by
      constructor <;> simp [hg3]
    refine ⟨⟨⟨g3, hdet⟩, hmem⟩, Units.ext ?_⟩
    ext r c
    rw [hact]
    fin_cases r <;> fin_cases c <;> simp [hg3]
  ·
    intro g
    have hkey : action g = 1 ↔ (action g : Matrix (Fin 2) (Fin 2) K) = 1 :=
      ⟨fun h => by rw [h, Units.val_one], fun h => Units.ext (by rw [h, Units.val_one])⟩
    rw [hkey, mem_Q2, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular]
    obtain ⟨hg20, hg21⟩ := g.2
    constructor
    · intro h
      have hent : ∀ r c : Fin 2,
          ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) (Fin.castLE (by decide) r)
            (Fin.castLE (by decide) c) = (1 : Matrix (Fin 2) (Fin 2) K) r c := by
        intro r c
        rw [← hact, h]
      have h00 := hent 0 0
      have h01 := hent 0 1
      have h10 := hent 1 0
      have h11 := hent 1 1
      simp at h00 h01 h10 h11
      have hdet : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).det = 1 := (g : SL(3, K)).2
      rw [Matrix.det_fin_three, hg20, hg21, h00, h11, h01, h10] at hdet
      have h22 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
        linear_combination hdet
      refine ⟨⟨fun i j hji => ?_, fun i => ?_⟩, h01⟩
      · fin_cases i <;> fin_cases j
        all_goals first
          | exact absurd hji (by decide)
          | exact h10
          | exact hg20
          | exact hg21
      · fin_cases i
        · exact h00
        · exact h11
        · exact h22
    · rintro ⟨hU, h01⟩
      have hlow := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.1 hU).1
      have hdiag := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular.1 hU).2
      ext r c
      rw [hact]
      fin_cases r <;> fin_cases c
      · exact hdiag 0
      · exact h01
      · exact hlow 1 0 (by decide)
      · exact hdiag 1
  ·
    intro block hblock
    have hb : ∀ r c : Fin 2, bar n (block c r) = block r c := fun r c => by
      have := congrFun (congrFun hblock r) c
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    have hM : (conjM n (!![block 0 0, block 0 1, 0; block 1 0, block 1 1, 0; 0, 0, 0] :
        Matrix (Fin 3) (Fin 3) K))ᵀ =
        !![block 0 0, block 0 1, 0; block 1 0, block 1 1, 0; 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, hb]
    refine ⟨mkH _ hM, ?_, ?_⟩
    · rw [mem_blkW]
      simp [mat_mkH]
    · ext r c
      fin_cases r <;> fin_cases c <;> simp [hermBlk, mat_mkH]
  ·
    intro g X hX
    obtain ⟨hg20, hg21⟩ := g.2
    obtain ⟨hX02, hX12, hX22⟩ := hX
    have hX20 : mat X 2 0 = 0 := by rw [← herm_apply, hX02, map_zero]
    have hX21 : mat X 2 1 = 0 := by rw [← herm_apply, hX12, map_zero]
    have hmem : rho hK ((g : SL(3, K))) X ∈ blkW n K := by
      rw [mem_blkW]
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [mat_rho, tw, Matrix.mul_apply, Fin.sum_univ_three, conjM, hX02, hX12, hX22,
          hX20, hX21, hg20, hg21]
    have hblk : hermBlk (rho hK ((g : SL(3, K))) X) =
        (action g : Matrix (Fin 2) (Fin 2) K) * hermBlk X *
          ((action g : Matrix (Fin 2) (Fin 2) K).map (bar n))ᵀ := by
      ext r c
      simp [hermBlk, mat_rho, tw, conjM, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
        hact, hX02, hX12, hX22, hX20, hX21, hg20, hg21]
    refine ⟨hmem, hblk, ?_⟩
    have hdetmap : ∀ A : Matrix (Fin 2) (Fin 2) K, (A.map (bar n)).det = bar n A.det :=
      fun A => (RingHom.map_det (bar n).toRingHom A).symm
    rw [hblk, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetmap]
    ring

end CFSG.Quasithin.RonanH44
