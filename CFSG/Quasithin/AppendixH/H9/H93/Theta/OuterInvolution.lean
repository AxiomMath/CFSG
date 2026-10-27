module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

theorem mem_zpowers_involution {G : Type*} [Group G] {t : G} (ht : t * t = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℕ) = 1 := by rw [pow_two]; exact ht
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem mem_fixV_zpowers_iff_of_involution {V : Type*} [CommGroup V] {t : MulAut V}
    (ht : t * t = 1) {v : V} : v ∈ fixV (Subgroup.zpowers t) ↔ t v = v := by
  refine ⟨fun h => mem_fixV.mp h t (Subgroup.mem_zpowers t), fun h => mem_fixV.mpr fun x hx => ?_⟩
  rcases mem_zpowers_involution ht hx with rfl | rfl
  · rfl
  · exact h

theorem outer_apply_pairVec (A : GL (Fin n) (ZMod 2)) (a b : Fin n → ZMod 2) :
    (pairActN n A * swapN n) (pairVec a b) =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b)
        (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) := by
  rw [MulAut.mul_apply, swapN_pairVec, pairActN_pairVec]

theorem outer_involution_mulVec_dual (A : GL (Fin n) (ZMod 2))
    (h : (pairActN n A * swapN n) * (pairActN n A * swapN n) = 1) (a : Fin n → ZMod 2) :
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) = a := by
  have h1 := congrArg (fun e : MulAut (PairN n) => e (pairVec a 0)) h
  simp only [MulAut.mul_apply, outer_apply_pairVec, Matrix.mulVec_zero, MulAut.one_apply] at h1
  exact (pairVec_inj.mp h1).1

theorem outer_involution_dual_mulVec (A : GL (Fin n) (ZMod 2))
    (h : (pairActN n A * swapN n) * (pairActN n A * swapN n) = 1) (b : Fin n → ZMod 2) :
    (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b)) = b := by
  have h1 := congrArg (fun e : MulAut (PairN n) => e (pairVec 0 b)) h
  simp only [MulAut.mul_apply, outer_apply_pairVec, Matrix.mulVec_zero, MulAut.one_apply] at h1
  exact (pairVec_inj.mp h1).2

theorem exists_pairVec_of_mem_V1n {x : PairN n} (hx : x ∈ V1n n) :
    ∃ a : Fin n → ZMod 2, x = pairVec a 0 := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  refine ⟨a, ?_⟩
  have hb : b = 0 := ofAdd_eq_one.mp (mem_V1n.mp hx)
  rw [hb]

theorem thetaIso_of_outer_form {t : MulAut (PairN n)} (A : GL (Fin n) (ZMod 2))
    (hA : t = pairActN n A * swapN n) (htt : t * t = 1) : ThetaIso n t := by
  have htt' : (pairActN n A * swapN n) * (pairActN n A * swapN n) = 1 := by
    rw [← hA]; exact htt
  have hAD := outer_involution_mulVec_dual A htt'
  have hDA := outer_involution_dual_mulVec A htt'
  have htv : ∀ a b : Fin n → ZMod 2, t (pairVec a b) =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b)
        (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) := by
    intro a b
    rw [hA]
    exact outer_apply_pairVec A a b
  have hwt : ∀ a : Fin n → ZMod 2, pairVec a 0 * t (pairVec a 0) =
      pairVec a (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) := by
    intro a
    rw [htv, Matrix.mulVec_zero, pairVec_mul, add_zero, zero_add]
  have hfixiff : ∀ a b : Fin n → ZMod 2, t (pairVec a b) = pairVec a b ↔
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b = a ∧
        ((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a = b := by
    intro a b
    rw [htv, pairVec_inj]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have key : ∀ v : PairN n, t (t v * v⁻¹) = t v * v⁻¹ := by
      intro v
      obtain ⟨a, b, rfl⟩ := pairVec_surj v
      rw [pairVec_inv, htv a b, pairVec_mul, htv, Matrix.mulVec_add, Matrix.mulVec_add, hAD, hDA]
      exact pairVec_inj.mpr ⟨add_comm _ _, add_comm _ _⟩
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨x, hx, v, rfl⟩
      refine (mem_fixV_zpowers_iff_of_involution htt).mpr ?_
      rcases mem_zpowers_involution htt hx with rfl | rfl
      · have h1 : ∀ v : PairN n, t (v * v⁻¹) = v * v⁻¹ := fun v => by
          have e : v * v⁻¹ = 1 := mul_inv_cancel v
          rw [e, map_one]
        exact h1 v
      · exact key v
    · intro y hy
      have hy' : t y = y := (mem_fixV_zpowers_iff_of_involution htt).mp hy
      obtain ⟨a, b, rfl⟩ := pairVec_surj y
      obtain ⟨hb1, -⟩ := (hfixiff a b).mp hy'
      have hgen : t (pairVec 0 b) * (pairVec 0 b)⁻¹ = pairVec a b := by
        rw [pairVec_inv, htv, Matrix.mulVec_zero, pairVec_mul, add_zero, zero_add, hb1]
      exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, pairVec 0 b, hgen⟩
  · intro w hw w' hw' h
    obtain ⟨a, rfl⟩ := exists_pairVec_of_mem_V1n hw
    obtain ⟨a', rfl⟩ := exists_pairVec_of_mem_V1n hw'
    rw [hwt, hwt, pairVec_inj] at h
    rw [h.1]
  · intro x hx
    have hx' : t x = x := (mem_fixV_zpowers_iff_of_involution htt).mp hx
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    obtain ⟨-, hb⟩ := (hfixiff a b).mp hx'
    exact ⟨pairVec a 0, pairVec_mem_V1n a, by rw [hwt, hb]⟩
  · intro w hw
    obtain ⟨a, rfl⟩ := exists_pairVec_of_mem_V1n hw
    have h1 : t (pairVec a (((dualGLn n A : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)) =
        pairVec a (((dualGLn n A : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) :=
      (hfixiff _ _).mpr ⟨hAD a, rfl⟩
    exact (mem_fixV_zpowers_iff_of_involution htt).mpr
      ((congrArg t (hwt a)).trans (h1.trans (hwt a).symm))
  · intro g hg w _
    have hgt : g (t w) = t (g w) :=
      (congrArg (fun e : MulAut (PairN n) => e w)
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 t
          (Set.mem_singleton t))).symm
    rw [map_mul, hgt]

end CFSG.ASVolI.ChH
