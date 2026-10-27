module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.ClassicalGroups.McLaughlin.Theorem

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.McLaughlin
open scoped Matrix

section Transport

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem toLin_mulVec (g : GL ι K) (x : ι → K) :
    (Matrix.GeneralLinearGroup.toLin g : (ι → K) →ₗ[K] (ι → K)) x = (g : Matrix ι ι K) *ᵥ x :=
  rfl

private theorem matrix_eq_of_mulVec_eq' (A B : Matrix ι ι K) (h : ∀ x, A *ᵥ x = B *ᵥ x) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

private def dotLin (f : ι → K) : (ι → K) →ₗ[K] K where
  toFun x := f ⬝ᵥ x
  map_add' x y := dotProduct_add f x y
  map_smul' c x := by simp [dotProduct, Finset.mul_sum, mul_left_comm]

private theorem dotLin_apply (f x : ι → K) : dotLin f x = f ⬝ᵥ x :=
  rfl

private theorem exists_dotLin (φ : Module.Dual K (ι → K)) : ∃ f : ι → K, φ = dotLin f := by
  refine ⟨fun j => φ (Pi.single j 1), LinearMap.ext fun x => ?_⟩
  have hx : x = ∑ j, x j • (Pi.single j (1 : K) : ι → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [dotLin_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem one_add_vecMulVec_mulVec (v f x : ι → K) :
    (1 + Matrix.vecMulVec v f) *ᵥ x = x + (f ⬝ᵥ x) • v := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

private theorem det_toLin_eq (g : GL ι K) :
    LinearMap.det (Matrix.GeneralLinearGroup.toLin g : (ι → K) →ₗ[K] (ι → K)) =
      (g : Matrix ι ι K).det := by
  rw [show (Matrix.GeneralLinearGroup.toLin g : (ι → K) →ₗ[K] (ι → K)) =
    Matrix.toLin' (g : Matrix ι ι K) from LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply]
      rfl]
  exact LinearMap.det_toLin' _

private theorem mem_slCore_iff (g : GL ι K) :
    g ∈ CFSG.MatrixModel.slCore ι K ↔ (g : Matrix ι ι K).det = 1 := by
  simp [CFSG.MatrixModel.slCore, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply]

private theorem genByRoots_map (X : Subgroup (GL ι K)) (hgen : GenByTransvLines X) :
    GenByRoots (X.map (Matrix.GeneralLinearGroup.toLin :
      GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom) := by
  unfold GenByTransvLines at hgen
  have hX : X.map (Matrix.GeneralLinearGroup.toLin :
      GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom =
      Subgroup.closure ((Matrix.GeneralLinearGroup.toLin :
        GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom ''
        {g : GL ι K | ∃ v f : ι → K, v ≠ 0 ∧ f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧
          (g : Matrix ι ι K) = 1 + Matrix.vecMulVec v f ∧
          ∀ c : K, ∃ h ∈ X, (h : Matrix ι ι K) = 1 + c • Matrix.vecMulVec v f}) := by
    conv_lhs => rw [hgen]
    rw [MonoidHom.map_closure]
  unfold GenByRoots
  conv_lhs => rw [hX]
  congr 1
  ext t
  constructor
  · rintro ⟨g, ⟨v, f, hv, hf, hfv, hg, hall⟩, rfl⟩
    have hdf : dotLin f ≠ 0 := by
      intro h
      apply hf
      funext j
      have := LinearMap.congr_fun h (Pi.single j 1)
      simpa [dotLin_apply] using this
    have hψg : (Matrix.GeneralLinearGroup.toLin g : (ι → K) →ₗ[K] (ι → K)) =
        1 + (dotLin f).smulRight v := by
      apply LinearMap.ext
      intro x
      rw [toLin_mulVec, hg, one_add_vecMulVec_mulVec]
      simp [dotLin_apply]
    refine ⟨v, dotLin f, hv, hdf, ⟨by rw [dotLin_apply]; exact hfv, fun c => ?_⟩, hψg⟩
    obtain ⟨h, hh, hhm⟩ := hall c
    refine ⟨Matrix.GeneralLinearGroup.toLin h, Subgroup.mem_map_of_mem _ hh, ?_⟩
    apply LinearMap.ext
    intro x
    rw [toLin_mulVec, hhm, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec]
    simp [dotLin_apply]
  · rintro ⟨v, φ, hv, hφ, hroot, ht⟩
    obtain ⟨f, rfl⟩ := exists_dotLin (ι := ι) φ
    have hf : f ≠ 0 := fun h => hφ (by rw [h]; exact LinearMap.ext fun x => by simp [dotLin_apply])
    have hfv : f ⬝ᵥ v = 0 := by
      have := hroot.1
      rw [dotLin_apply] at this
      exact this
    have hmat : ((Matrix.GeneralLinearGroup.toLin.symm t : GL ι K) : Matrix ι ι K) =
        1 + Matrix.vecMulVec v f := by
      apply matrix_eq_of_mulVec_eq'
      intro x
      rw [one_add_vecMulVec_mulVec, ← toLin_mulVec, MulEquiv.apply_symm_apply, ht]
      simp [dotLin_apply]
    have hall : ∀ c : K, ∃ h ∈ X, (h : Matrix ι ι K) = 1 + c • Matrix.vecMulVec v f := by
      intro c
      obtain ⟨g', hg', hg'eq⟩ := hroot.2 c
      obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hg'
      have hhg' : (Matrix.GeneralLinearGroup.toLin h : LinearMap.GeneralLinearGroup K (ι → K)) =
          g' := hhg
      refine ⟨h, hh, ?_⟩
      apply matrix_eq_of_mulVec_eq'
      intro x
      rw [← toLin_mulVec, hhg', hg'eq]
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
      simp [dotLin_apply]
    exact ⟨Matrix.GeneralLinearGroup.toLin.symm t, ⟨v, f, hv, hf, hfv, hmat, hall⟩,
      MulEquiv.apply_symm_apply _ t⟩

private theorem irred_map (X : Subgroup (GL ι K)) (hirr : NatIrred X) :
    CFSG.ClassicalGroups.McLaughlin.Irred (X.map (Matrix.GeneralLinearGroup.toLin :
      GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom) := by
  intro W hW
  apply hirr W
  intro g hg x hx
  exact hW _ (Subgroup.mem_map_of_mem _ hg) x hx

end Transport

theorem mcLaughlinStatement_holds : McLaughlinStatement := by
  intro K _ _ _ ι _ _ X hcard hK hirr hgen
  have hn : 2 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hcard
  have hK3 : 3 ≤ Nat.card K := by omega
  have hgenX := genByRoots_map X hgen
  have hirrX := irred_map X hirr
  set X' : Subgroup (LinearMap.GeneralLinearGroup K (ι → K)) :=
    X.map (Matrix.GeneralLinearGroup.toLin :
      GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom with hX'
  have key : ∀ g : GL ι K, g ∈ X ↔ Matrix.GeneralLinearGroup.toLin g ∈ X' := by
    intro g
    rw [hX', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  by_cases hA : ∀ v : ι → K, v ≠ 0 →
      Module.finrank K (CFSG.ClassicalGroups.McLaughlin.axisSpace X' v) + 1 =
        Module.finrank K (ι → K)
  · obtain ⟨β, hβnd, hβalt, hβ⟩ :=
      CFSG.ClassicalGroups.McLaughlin.exists_alt_isometry_of_axisSpace_hyperplane hK3 hn hgenX
        hirrX hA
    refine Or.inr ⟨β, hβnd, hβalt, fun g => ?_⟩
    rw [key g]
    exact hβ (Matrix.GeneralLinearGroup.toLin g)
  · push Not at hA
    obtain ⟨v, hv, hne⟩ := hA
    have hc : CFSG.ClassicalGroups.McLaughlin.IsCentre X' v :=
      CFSG.ClassicalGroups.McLaughlin.isCentre_of_ne_zero hK3 hn hgenX hirrX hv
    have htop : CFSG.ClassicalGroups.McLaughlin.axisSpace X' v ≠ ⊤ := by
      intro htop
      obtain ⟨-, φ, hφ0, hφ⟩ := hc
      apply hφ0
      apply LinearMap.ext
      intro x
      have hx : x ∈ CFSG.ClassicalGroups.McLaughlin.axisSpace X' v := by
        rw [htop]
        exact Submodule.mem_top
      exact (CFSG.ClassicalGroups.McLaughlin.mem_axisSpace_iff.mp hx) φ hφ
    have hlt := Submodule.finrank_lt htop
    have hB : Module.finrank K (CFSG.ClassicalGroups.McLaughlin.axisSpace X' v) + 1 <
        Module.finrank K (ι → K) := by
      omega
    refine Or.inl ?_
    ext g
    rw [mem_slCore_iff, key g,
      CFSG.ClassicalGroups.McLaughlin.eq_sl_of_axisSpace hK3 hgenX hirrX hv hB
        (Matrix.GeneralLinearGroup.toLin g), det_toLin_eq g]

end CFSG.RankThree.GF2n.Stroth80

end
