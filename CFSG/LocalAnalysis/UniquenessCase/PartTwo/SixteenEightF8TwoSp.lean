module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoCoord
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K]

private theorem s16g_fin_ne_sp {m i j : ℕ} (hi : i < m) (hj : j < m) (h : i ≠ j) :
    (⟨i, hi⟩ : Fin m) ≠ ⟨j, hj⟩ := fun e => h (Fin.mk.inj_iff.1 e)

private theorem s16g_single_ne_zero_sp {ι : Type} [DecidableEq ι] (i : ι) :
    (Pi.single i 1 : ι → K) ≠ 0 := fun h => by
  have h1 := congrFun h i
  simp at h1

theorem s16g_fixNc_statedSp_blocks {m : ℕ} (hm : 3 ≤ m) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixNc (StatedSp m K) p := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.one_lt.ne hg
  have h01 := s16g_fin_ne_sp (m := m) (i := 0) (j := 1) (by omega) (by omega) (by omega)
  have h02 := s16g_fin_ne_sp (m := m) (i := 0) (j := 2) (by omega) (by omega) (by omega)
  have h12 := s16g_fin_ne_sp (m := m) (i := 1) (j := 2) (by omega) (by omega) (by omega)
  have hx : orderOf (pairGL (Sum.inl_ne_inr : (Sum.inl ⟨0, by omega⟩ : Fin m ⊕ Fin m) ≠
      Sum.inr ⟨0, by omega⟩) g) = p :=
    (orderOf_injective _ (s16g_pairGL_injective _) g).trans hg
  have hy : orderOf (pairGL (Sum.inl_ne_inr : (Sum.inl ⟨1, by omega⟩ : Fin m ⊕ Fin m) ≠
      Sum.inr ⟨1, by omega⟩) g) = p :=
    (orderOf_injective _ (s16g_pairGL_injective _) g).trans hg
  have hcomm := s16g_pairGL_commute (Sum.inl_ne_inr : (Sum.inl ⟨0, by omega⟩ : Fin m ⊕ Fin m) ≠
      Sum.inr ⟨0, by omega⟩) (Sum.inl_ne_inr : (Sum.inl ⟨1, by omega⟩ : Fin m ⊕ Fin m) ≠
      Sum.inr ⟨1, by omega⟩) (Sum.inl_injective.ne h01) Sum.inl_ne_inr Sum.inr_ne_inl
    (Sum.inr_injective.ne h01) g g
  refine s16g_fixNc_of_fixed_pair (StatedSp m K) hp
    (fun x y hx hy => CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hx hy)
    (pairGL_inl_inr_mem ⟨0, by omega⟩ g) (pairGL_inl_inr_mem ⟨1, by omega⟩ g) hcomm hx hy ?_
    (s16g_single_ne_zero_sp (Sum.inl (⟨2, by omega⟩ : Fin m)))
    (s16g_pairGL_mulVec_single _ (Sum.inl_injective.ne h02.symm) Sum.inl_ne_inr g)
    (s16g_pairGL_mulVec_single _ (Sum.inl_injective.ne h12.symm) Sum.inl_ne_inr g)
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rw [← map_zpow] at hk
  exact hg1 (s16g_pairGL_eq_pairGL_disjoint _ _ (Sum.inl_injective.ne h01.symm) Sum.inl_ne_inr
    Sum.inr_ne_inl (Sum.inr_injective.ne h01.symm) hk.symm)

theorem s16g_fixOrd_statedSp {m : ℕ} (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixOrd (StatedSp m K) p := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have h01 := s16g_fin_ne_sp (m := m) (i := 0) (j := 1) (by omega) (by omega) (by omega)
  exact s16g_fixOrd_of_fixed_vector (StatedSp m K)
    (fun x y hx hy => CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hx hy)
    (pairGL_inl_inr_mem ⟨0, by omega⟩ g)
    ((orderOf_injective _ (s16g_pairGL_injective _) g).trans hg)
    (s16g_single_ne_zero_sp (Sum.inl (⟨1, by omega⟩ : Fin m)))
    (s16g_pairGL_mulVec_single _ (Sum.inl_injective.ne h01.symm) Sum.inl_ne_inr g)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
