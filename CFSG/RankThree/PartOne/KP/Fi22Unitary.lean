module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Fischer.T46Unitary

public section

namespace CFSG.RankThree.PartOne

open CFSG.Fischer CFSG.Assembly.LowTwoRank Matrix

theorem isIsom_iff_stated {A : Matrix (Fin 6) (Fin 6) F4} :
    IsIsom A ↔ (A.map (· ^ 2))ᵀ * A = 1 := by
  constructor
  · intro h
    ext a b
    have hab := h (Pi.single b 1) (Pi.single a 1)
    rw [herm_eq, herm_eq] at hab
    simp only [mulVec_single_one] at hab
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply]
    simp only [Pi.single_apply] at hab
    have e2 : ∑ x : Fin 6, (if x = b then (1 : F4) else 0) * (if x = a then 1 else 0) ^ 2 =
        if a = b then 1 else 0 := by
      rw [Finset.sum_eq_single b]
      · by_cases hba : b = a
        · subst hba
          simp
        · simp [hba, Ne.symm hba]
      · intro x _ hx
        simp [hx]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    rw [e2] at hab
    rw [← hab]
    exact Finset.sum_congr rfl fun x _ => by simp [Matrix.col_apply, mul_comm]
  · intro h x y
    rw [herm_eq, herm_eq]
    have hh : ∀ a b : Fin 6, ∑ k, A k a ^ 2 * A k b = if a = b then 1 else 0 := fun a b => by
      have := congrFun (congrFun h a) b
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have e1 : ∀ k, ((A.mulVec y) k) ^ 2 = ∑ b, A k b ^ 2 * y b ^ 2 := fun k => by
      rw [Matrix.mulVec, dotProduct, sum_pow_char 2]
      simp only [mul_pow]
    calc ∑ k, (A.mulVec x) k * ((A.mulVec y) k) ^ 2
        = ∑ k, ∑ a, ∑ b, (x a * (y b) ^ 2) * (A k a * A k b ^ 2) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [e1 k]
          simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ a, ∑ b, (x a * (y b) ^ 2) * ∑ k, A k a * A k b ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ = ∑ a, x a * (y a) ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hk : ∀ b, ∑ k, A k a * A k b ^ 2 = if b = a then 1 else 0 := fun b => by
            rw [← hh b a]
            exact Finset.sum_congr rfl fun k _ => mul_comm _ _
          simp_rw [hk]
          simp

theorem statedSU_eq_SU0 : StatedSU 6 (2 ^ 1) F4 = SU0 := by
  apply le_antisymm
  · rw [StatedSU, Subgroup.closure_le]
    rintro A ⟨hdet, hcond⟩
    rw [SetLike.mem_coe, mem_SU0]
    refine ⟨Units.ext ?_, isIsom_iff_stated.2 ?_⟩
    · rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]
      rfl
    · simpa using hcond
  · intro g hg
    rw [mem_SU0] at hg
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, hg.1]
      rfl
    · simpa using isIsom_iff_stated.1 hg.2

theorem card_center_SU0_le : Nat.card (Subgroup.center SU0) ≤ 3 := by
  have h1 := card_SU0_eq
  rw [range_piSU, card_T46, ker_piSU] at h1
  have h2 := card_SU0_mul_three_le
  have h3 := card_GU0_le
  omega

theorem scalarGL_eq_scalar (c : F4ˣ) :
    scalarGL c = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  apply Units.ext
  rw [scalarGL_val, Matrix.GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem center_SU0_eq_scalars :
    Subgroup.center SU0 = (StatedScalars (Fin 6) F4).subgroupOf SU0 := by
  have hle : (StatedScalars (Fin 6) F4).subgroupOf SU0 ≤ Subgroup.center SU0 := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hz' : (z : GL (Fin 6) F4) ∈ StatedScalars (Fin 6) F4 := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (g : GL (Fin 6) F4))
  have h3 : 3 ≤ Nat.card ((StatedScalars (Fin 6) F4).subgroupOf SU0) := by
    classical
    let f : F4ˣ → (StatedScalars (Fin 6) F4).subgroupOf SU0 := fun c =>
      ⟨⟨scalarGL c, scalarGL_mem c⟩, by
        show scalarGL c ∈ StatedScalars (Fin 6) F4
        rw [scalarGL_eq_scalar]
        exact ⟨c, rfl⟩⟩
    have hf : Function.Injective f := fun c d h =>
      scalarGL_injective (congrArg
        (fun z : (StatedScalars (Fin 6) F4).subgroupOf SU0 => ((z : SU0) : GL (Fin 6) F4)) h)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_units] at this
    have h4 : Nat.card F4 - 1 = 3 := by rw [Nat.card_eq_fintype_card, F4.card]
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (le_trans card_center_SU0_le h3)).symm

@[expose] noncomputable def statedProjCongr {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {H H' : Subgroup (GL ι K)} (h : H = H') : StatedProj H ≃* StatedProj H' := by
  subst h
  exact MulEquiv.refl _

@[expose] noncomputable def statedProjEquivT46 :
    StatedProj (StatedSU 6 (2 ^ 1) F4) ≃* T46 :=
  (statedProjCongr statedSU_eq_SU0).trans
    ((QuotientGroup.quotientMulEquivOfEq center_SU0_eq_scalars.symm).trans suQuotEquiv)

end CFSG.RankThree.PartOne
