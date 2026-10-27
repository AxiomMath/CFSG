module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthPairA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem s16t3_exists_pair_omega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a b c d : ι → K} (ha : Q a = 1) (hb : Q b = 1) (hc : Q c = 1) (hd : Q d = 1)
    (hab : a ⬝ᵥ (M *ᵥ b) = 1) (hcd : c ⬝ᵥ (M *ᵥ d) = 1)
    (hac : a ⬝ᵥ (M *ᵥ c) = 0) (had : a ⬝ᵥ (M *ᵥ d) = 0)
    (hbc : b ⬝ᵥ (M *ᵥ c) = 0) (hbd : b ⬝ᵥ (M *ᵥ d) = 0) :
    ∃ F : Subgroup (Matrix.GeneralLinearGroup ι K), F ≤ StatedOmega Q ∧ IsPGroup 3 ↥F ∧
      ¬ IsCyclic ↥F ∧ ∀ v : ι → K, v ⬝ᵥ (M *ᵥ a) = 0 → v ⬝ᵥ (M *ᵥ b) = 0 →
        v ⬝ᵥ (M *ᵥ c) = 0 → v ⬝ᵥ (M *ᵥ d) = 0 →
          ∀ f ∈ F, ((f : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v = v := by
  classical
  obtain ⟨u, huOm, hu3, hu⟩ := s16t3_pair_omega_aux h ha hb hab
  obtain ⟨w, hwOm, hw3, hw⟩ := s16t3_pair_omega_aux h hc hd hcd
  have hca : c ⬝ᵥ (M *ᵥ a) = 0 := (h.symm c a).trans hac
  have hda : d ⬝ᵥ (M *ᵥ a) = 0 := (h.symm d a).trans had
  have hcb : c ⬝ᵥ (M *ᵥ b) = 0 := (h.symm c b).trans hbc
  have hdb : d ⬝ᵥ (M *ᵥ b) = 0 := (h.symm d b).trans hbd
  have hcomm : u * w = w * u := by
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    change ((u : Matrix ι ι K) * (w : Matrix ι ι K)) *ᵥ x =
      ((w : Matrix ι ι K) * (u : Matrix ι ι K)) *ᵥ x
    rw [← mulVec_mulVec, hu, hw]
    rw [← mulVec_mulVec, hu, hw]
    rw [s16t3_transvFun_comm hbc hcb, s16t3_transvFun_comm hbd hdb,
      s16t3_transvFun_comm hac hca, s16t3_transvFun_comm had hda]
  have hua : (u : Matrix ι ι K) *ᵥ a = b := by
    rw [hu]
    have hba : transvFun M b a = a + b := by simp only [transvFun, hab, one_smul]
    rw [hba]
    have h3 : transvFun M a (a + b) = b := by
      have hcoe : (a + b) ⬝ᵥ (M *ᵥ a) = 1 := by
        rw [add_dotProduct, h.self, (h.symm b a).trans hab, zero_add]
      rw [transvFun, hcoe, one_smul]
      have h2a : a + a = 0 := by rw [← two_smul K a, two_eq_zero_K (K := K), zero_smul]
      rw [show (a + b) + a = (a + a) + b by abel, h2a, zero_add]
    rw [h3]
  have hne : b ≠ a := by
    intro hba
    have h' : a ⬝ᵥ (M *ᵥ a) = 1 := by simpa [hba] using hab
    rw [h.self] at h'
    exact zero_ne_one h'
  have hu1 : u ≠ 1 := by
    intro h1
    have h' : (u : Matrix ι ι K) *ᵥ a = a := by simp [h1]
    rw [hua] at h'
    exact hne h'
  have huc : (u : Matrix ι ι K) *ᵥ c = c := by
    rw [hu]
    have h1 : transvFun M b c = c := by simp only [transvFun, hcb, zero_smul, add_zero]
    have h2 : transvFun M a c = c := by simp only [transvFun, hca, zero_smul, add_zero]
    rw [h1, h2]
  have hupow : ∀ k : ℕ, ((u ^ k : GL ι K) : Matrix ι ι K) *ᵥ c = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Units.val_mul, ← mulVec_mulVec, huc]
        exact ih
  have hu_c : (u : Matrix ι ι K) *ᵥ c = c := by simpa using hupow 1
  have hu2_c : ((u ^ 2 : GL ι K) : Matrix ι ι K) *ᵥ c = c := hupow 2
  have hwc : (w : Matrix ι ι K) *ᵥ c = d := by
    rw [hw]
    have hdc : transvFun M d c = c + d := by simp only [transvFun, hcd, one_smul]
    rw [hdc]
    have h3 : transvFun M c (c + d) = d := by
      have hcoe : (c + d) ⬝ᵥ (M *ᵥ c) = 1 := by
        rw [add_dotProduct, h.self, (h.symm d c).trans hcd, zero_add]
      rw [transvFun, hcoe, one_smul]
      have h2c : c + c = 0 := by rw [← two_smul K c, two_eq_zero_K (K := K), zero_smul]
      rw [show (c + d) + c = (c + c) + d by abel, h2c, zero_add]
    rw [h3]
  have hnecd : d ≠ c := by
    intro hdc
    have h' : c ⬝ᵥ (M *ᵥ c) = 1 := by simpa [hdc] using hcd
    rw [h.self] at h'
    exact zero_ne_one h'
  have hw1 : w ≠ 1 := by
    intro h1
    have h' : (w : Matrix ι ι K) *ᵥ c = c := by simp [h1]
    rw [hwc] at h'
    exact hnecd h'
  have hwu : w ≠ u := by
    intro h'
    have h'' : (w : Matrix ι ι K) *ᵥ c = c := by rw [h']; exact hu_c
    rw [hwc] at h''
    exact hnecd h''
  have hwu2 : w ≠ u ^ 2 := by
    intro h'
    have h'' : (w : Matrix ι ι K) *ᵥ c = c := by rw [h']; exact hu2_c
    rw [hwc] at h''
    exact hnecd h''
  refine ⟨Subgroup.closure ({u, w} : Set (GL ι K)), ?_, ?_, ?_, ?_⟩
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact huOm
    · exact hwOm
  · exact (s16c1g_closure_pair hu3 hw3 hcomm hu1 hw1 hwu hwu2).1
  · exact (s16c1g_closure_pair hu3 hw3 hcomm hu1 hw1 hwu hwu2).2
  · intro v hva hvb hvc hvd f hf
    have huT : (u : Matrix ι ι K) *ᵥ v = v := by
      rw [hu]
      have h1 : transvFun M b v = v := by simp only [transvFun, hvb, zero_smul, add_zero]
      have h2 : transvFun M a v = v := by simp only [transvFun, hva, zero_smul, add_zero]
      rw [h1, h2]
    have hwT : (w : Matrix ι ι K) *ᵥ v = v := by
      rw [hw]
      have h1 : transvFun M d v = v := by simp only [transvFun, hvd, zero_smul, add_zero]
      have h2 : transvFun M c v = v := by simp only [transvFun, hvc, zero_smul, add_zero]
      rw [h1, h2]
    let T : Subgroup (GL ι K) :=
      { carrier := {g | (g : Matrix ι ι K) *ᵥ v = v}
        one_mem' := by simp
        mul_mem' := by
          intro g g' hg hg'
          show ((g * g' : GL ι K) : Matrix ι ι K) *ᵥ v = v
          rw [Units.val_mul, ← mulVec_mulVec, hg']
          exact hg
        inv_mem' := by
          intro g hg
          show ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = v
          have h1 : ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          calc ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
              = (((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K)) *ᵥ v := by
                  rw [← mulVec_mulVec, hg]
            _ = (1 : Matrix ι ι K) *ᵥ v := by rw [h1]
            _ = v := one_mulVec v }
    have hT : Subgroup.closure ({u, w} : Set (GL ι K)) ≤ T := by
      refine (Subgroup.closure_le T).mpr ?_
      intro g hg
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact huT
      · exact hwT
    exact hT hf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
