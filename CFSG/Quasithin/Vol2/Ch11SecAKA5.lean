module

public import CFSG.Quasithin.Vol2.KGNatSp4N13
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4I
public import CFSG.Quasithin.Vol2.Ch11SecQ9aSp4P

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ blkQ_apply blkIdx sigma2 spLevi spMat spMat_lam
  spMat_col_zero_of_mem_Q2_zero spMat_inr_zero_of_mem_Q2_zero spLevi_mem_perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (usp_le_perfectCore mem_pCoreOf_Q0_iff pCoreOf_Q0_eq)

namespace KA

variable {K : Type} [Field K]

theorem spLevi0_mulVec (A : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (spLevi 0 A) *ᵥ v = vec4 (v (.inl 0))
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * v (.inl 1) + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
        v (.inr 1)) (v (.inr 0))
      ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * v (.inl 1) + (A : Matrix (Fin 2) (Fin 2) K) 1 1 *
        v (.inr 1)) := by
  rw [show mat 2 K (spLevi 0 A) = spMat (spLevi 0 A) from rfl, spMat_lam]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat, vec4]

variable [Finite K] [CharP K 2]

theorem pCore_mulVec (hK4 : ∃ s : Finset K, s.card = 4) {N : StatedSp 2 K}
    (hN : N ∈ pCoreOf 2 (perfectCore (Q2 K 0))) {v : Fin 2 ⊕ Fin 2 → K} (hv : v (.inr 0) = 0) :
    (mat 2 K N *ᵥ v) (.inl 1) = v (.inl 1) ∧ (mat 2 K N *ᵥ v) (.inr 0) = 0 ∧
      (mat 2 K N *ᵥ v) (.inr 1) = v (.inr 1) := by
  rw [← pCoreOf_Q0_eq hK4] at hN
  obtain ⟨hNQ, -, hB⟩ := (mem_pCoreOf_Q0_iff hK4).mp hN
  have hblk : ∀ i k : Fin 2, spMat N (sigma2 0 i) (sigma2 0 k) =
      (1 : Matrix (Fin 2) (Fin 2) K) i k := fun i k => by
    have := congrFun₂ hB i k
    rwa [blkQ_apply] at this
  have e11 : spMat N (.inl 1) (.inl 1) = 1 := by simpa [sigma2] using hblk 0 0
  have e13 : spMat N (.inl 1) (.inr 1) = 0 := by simpa [sigma2] using hblk 0 1
  have e31 : spMat N (.inr 1) (.inl 1) = 0 := by simpa [sigma2] using hblk 1 0
  have e33 : spMat N (.inr 1) (.inr 1) = 1 := by simpa [sigma2] using hblk 1 1
  have c1 := spMat_col_zero_of_mem_Q2_zero hNQ (Sum.inl 1) (by simp)
  have c3 := spMat_col_zero_of_mem_Q2_zero hNQ (Sum.inr 1) (by simp)
  have c2 := spMat_col_zero_of_mem_Q2_zero hNQ (Sum.inr 0) (by simp)
  have r1 := spMat_inr_zero_of_mem_Q2_zero hNQ (c := Sum.inl 1) (by simp)
  have r3 := spMat_inr_zero_of_mem_Q2_zero hNQ (c := Sum.inr 1) (by simp)
  simp only [spMat] at e11 e13 e31 e33 c1 c2 c3 r1 r3
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mat_apply, hv, e11,
      e13, e31, e33, c1, c2, c3, r1, r3]

theorem shape_of_levi (hK4 : ∃ s : Finset K, s.card = 4)
    {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x)
    (hinj : Function.Injective T) (hline : T (vec4 1 0 0 0) ∈ spLine K)
    (hlevi : ∀ M ∈ perfectCore (Q2 K 0), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v,
      T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ T v)) :
    (∀ c, σ c = c) ∧ T (vec4 0 1 0 0) (.inr 0) = 0 ∧ T (vec4 0 1 0 0) (.inr 1) = 0 ∧
      T (vec4 0 0 0 1) (.inr 0) = 0 ∧ T (vec4 0 0 0 1) (.inl 1) = 0 ∧
      T (vec4 0 0 0 1) (.inr 1) = T (vec4 0 1 0 0) (.inl 1) ∧
      T (vec4 0 1 0 0) (.inl 1) ≠ 0 := by
  have horth := orth_of_semilinear_normalizing hσ hL
  obtain ⟨l1, l2, l3⟩ := hline
  obtain ⟨lam, hlam⟩ : ∃ lam, T (vec4 1 0 0 0) (.inl 0) = lam := ⟨_, rfl⟩
  have he0 : T (vec4 1 0 0 0) = lam • vec4 1 0 0 0 :=
    vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one, hlam])
      (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_zero, l1])
      (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, l2])
      (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, l3])
  have hl0 : lam ≠ 0 := by
    intro h
    have h1 : T (vec4 1 0 0 0) = T 0 := by rw [he0, h, zero_smul, map_zero]
    simpa [vec4] using congrFun (hinj h1) (.inl 0)
  have hperp : ∀ x : Fin 2 ⊕ Fin 2 → K, x (.inr 0) = 0 → T x (.inr 0) = 0 := by
    intro x hx
    have h1 := horth _ _ ((spB_e0 x).trans hx)
    rw [he0, LinearMap.map_smul₂, spB_e0, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hl0
  have ha2 : T (vec4 0 1 0 0) (.inr 0) = 0 := hperp _ rfl
  have hb2 : T (vec4 0 0 0 1) (.inr 0) = 0 := hperp _ rfl
  have hMt : ∀ t : K, qSp 0 0 t ∈ perfectCore (Q2 K 0) := fun t =>
    usp_le_perfectCore hK4 (qSp_mem_Usp 0 0 t)
  have key : ∀ t : K, T (vec4 0 1 0 0) (.inl 1) =
      T (vec4 0 1 0 0) (.inl 1) + t * T (vec4 0 1 0 0) (.inr 1) ∧
      T (vec4 0 0 0 1) (.inl 1) + σ t * T (vec4 0 1 0 0) (.inl 1) =
        T (vec4 0 0 0 1) (.inl 1) + t * T (vec4 0 0 0 1) (.inr 1) := by
    intro t
    obtain ⟨N, hN, hTN⟩ := hlevi _ (hMt t)
    have hq1 : mat 2 K (qSp 0 0 t) *ᵥ vec4 0 1 0 0 = vec4 0 1 0 0 := by
      rw [qSp_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
    have hq2 : mat 2 K (qSp 0 0 t) *ᵥ vec4 0 0 0 1 = vec4 0 0 0 1 + t • vec4 0 1 0 0 := by
      rw [qSp_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
    have e1 := hTN (vec4 0 1 0 0)
    have e2 := hTN (vec4 0 0 0 1)
    rw [hq1] at e1
    rw [hq2, map_add, hσ] at e2
    have m1 := (pCore_mulVec hK4 hN (v := mat 2 K (qSp 0 0 t) *ᵥ T (vec4 0 1 0 0))
      (by rw [qSp_mulVec]; simpa [vec4] using ha2)).1
    have m2 := (pCore_mulVec hK4 hN (v := mat 2 K (qSp 0 0 t) *ᵥ T (vec4 0 0 0 1))
      (by rw [qSp_mulVec]; simpa [vec4] using hb2)).1
    rw [← e1, qSp_mulVec] at m1
    rw [← e2, qSp_mulVec] at m2
    simp only [vec4_apply_inl1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha2, hb2,
      zero_mul, add_zero] at m1 m2
    exact ⟨m1, m2⟩
  have ha3 : T (vec4 0 1 0 0) (.inr 1) = 0 := by
    have := (key 1).1
    rw [one_mul, left_eq_add] at this
    exact this
  have hab : T (vec4 0 0 0 1) (.inr 1) = T (vec4 0 1 0 0) (.inl 1) := by
    have := (key 1).2
    rw [map_one, one_mul, one_mul, add_left_cancel_iff] at this
    exact this.symm
  have ha1 : T (vec4 0 1 0 0) (.inl 1) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := Finite.surjective_of_injective σ.injective
      (T (vec4 0 1 0 0) (.inl 0) / lam)
    have h1 : T (c • vec4 1 0 0 0) = T (vec4 0 1 0 0) := by
      rw [hσ, hc, he0, smul_smul, div_mul_cancel₀ _ hl0]
      exact vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one])
        (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_zero, h0])
        (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, ha2])
        (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, ha3])
    simpa [vec4] using congrFun (hinj h1) (.inl 1)
  refine ⟨fun c => ?_, ha2, ha3, hb2, ?_, hab, ha1⟩
  · have := (key c).2
    rw [add_left_cancel_iff, hab] at this
    exact mul_right_cancel₀ ha1 this
  ·
    let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
    obtain ⟨N, hN, hTN⟩ := hlevi _ (spLevi_mem_perfectCore hK4 0 A)
    have hA : mat 2 K (spLevi 0 A) *ᵥ vec4 0 0 0 1 = vec4 0 0 0 1 := by
      rw [spLevi0_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4, A]) (by simp [vec4]) (by simp [vec4, A])
    have e := hTN (vec4 0 0 0 1)
    rw [hA] at e
    have m := (pCore_mulVec hK4 hN (v := mat 2 K (spLevi 0 A) *ᵥ T (vec4 0 0 0 1))
      (by rw [spLevi0_mulVec]; simpa [vec4] using hb2)).2.2
    rw [← e, spLevi0_mulVec] at m
    simpa [vec4, A] using m

end KA

end CFSG.Quasithin.Vol2.KGNat
