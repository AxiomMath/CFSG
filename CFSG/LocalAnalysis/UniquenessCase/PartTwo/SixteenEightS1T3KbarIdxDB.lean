module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxDA
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

open scoped Matrix

variable {W : Type} [CommGroup W]

private theorem s16t3_zero_or_one {K : Type*} [Field K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    rw [hy x hx, hy 1 one_ne_zero]

noncomputable def s16t3_addAutEquivLinear {K : Type*} [Field K] (hK : Nat.card K = 2)
    (M : Type*) [AddCommGroup M] [Module K M] :
    Multiplicative (AddAut M) ≃* (M ≃ₗ[K] M) where
  toFun a := (Multiplicative.toAdd a).toLinearEquiv fun c x => by
    rcases s16t3_zero_or_one hK c with hc | hc
    · rw [hc, zero_smul, zero_smul, map_zero]
    · rw [hc, one_smul, one_smul]
  invFun f := Multiplicative.ofAdd f.toAddEquiv
  left_inv _ := rfl
  right_inv f := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

noncomputable def s16t3_mulAutEquivGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) :
    MulAut (Multiplicative (ι → K)) ≃* Matrix.GeneralLinearGroup ι K :=
  ((MulAutMultiplicative (ι → K)).trans (s16t3_addAutEquivLinear hK (ι → K))).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm)

theorem s16t3_mulAutEquivGL_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) (α : MulAut (Multiplicative (ι → K))) (v : ι → K) :
    (s16t3_mulAutEquivGL hK α : Matrix ι ι K) *ᵥ v =
      Multiplicative.toAdd (α (Multiplicative.ofAdd v)) := by
  have h := congrArg (fun L : LinearMap.GeneralLinearGroup K (ι → K) =>
    (L : (ι → K) →ₗ[K] (ι → K)) v)
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).symm
        (s16t3_addAutEquivLinear hK (ι → K)
          (MulAutMultiplicative (ι → K) α))))
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h
  exact h

noncomputable def s16t3_natAut {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) (g : Matrix.GeneralLinearGroup ι K) :
    MulAut (Multiplicative (ι → K)) :=
  (s16t3_mulAutEquivGL hK).symm g

theorem s16t3_natAut_fst {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) (g : Matrix.GeneralLinearGroup ι K) :
    s16t3_mulAutEquivGL hK (s16t3_natAut hK g) = g :=
  (s16t3_mulAutEquivGL hK).apply_symm_apply g

theorem s16t3_natAut_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) (g : Matrix.GeneralLinearGroup ι K) (v : ι → K) :
    s16t3_natAut hK g (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ v) := by
  have h := s16t3_mulAutEquivGL_mulVec hK (s16t3_natAut hK g) v
  rw [s16t3_natAut_fst] at h
  rw [h, ofAdd_toAdd]

theorem s16t3_normIdx_of_realizes_nat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (hK : Nat.card K = 2) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hnorm : s16t3_normIdx Γ) {L : Subgroup (MulAut W)} {J₀ Z : Subgroup W}
    {π : ↥Γ →* ↥L} (hR : (FFModel.nat Γ).RealizesVia L J₀ Z π)
    (gL : ↥L →* MulAut (↥J₀ ⧸ Z.subgroupOf J₀))
    (hgL : ∀ (γ : ↥Γ) (u : ↥J₀), ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
      gL (π γ) (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) :
    s16t3_normIdx ((⊤ : Subgroup ↥L).map gL) := by
  classical
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hR
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have hker : β.ker = Z.subgroupOf J₀ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  let βq : (↥J₀ ⧸ Z.subgroupOf J₀) ≃* Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)
  have hβq : ∀ u : ↥J₀, βq (QuotientGroup.mk u) = β u := by
    intro u
    show (QuotientGroup.quotientKerEquivOfSurjective β hβs)
      ((QuotientGroup.quotientMulEquivOfEq hker.symm) (QuotientGroup.mk u)) = β u
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk β u
  let Φ : Matrix.GeneralLinearGroup ι K ≃* MulAut (↥J₀ ⧸ Z.subgroupOf J₀) :=
    (s16t3_mulAutEquivGL hK).symm.trans (MulAut.congr βq).symm
  have hcongr : ∀ γ : ↥Γ, MulAut.congr βq (gL (π γ)) =
      s16t3_natAut hK (γ : Matrix.GeneralLinearGroup ι K) := by
    intro γ
    apply MulEquiv.ext
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (βq.symm x)
    have hx : x = βq (QuotientGroup.mk u) := by
      rw [hu, MulEquiv.apply_symm_apply]
    rw [hx]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hgL γ u (R.U_inv (π γ) u u.2)]
    rw [hβq]
    rw [hβe γ u (R.U_inv (π γ) u u.2)]
    rw [hβq]
    rw [← ofAdd_toAdd (β u), s16t3_natAut_apply]
    rfl
  have hΦ : ∀ γ : ↥Γ, Φ γ = gL (π γ) := by
    intro γ
    apply (MulAut.congr βq).injective
    have h1 : MulAut.congr βq (Φ γ) = s16t3_natAut hK (γ : Matrix.GeneralLinearGroup ι K) := by
      show MulAut.congr βq ((MulAut.congr βq).symm
        (s16t3_natAut hK (γ : Matrix.GeneralLinearGroup ι K))) = _
      rw [MulEquiv.apply_symm_apply]
    rw [h1]
    exact (hcongr γ).symm
  have hmap : Γ.map Φ.toMonoidHom = (⊤ : Subgroup ↥L).map gL := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨π ⟨γ, hγ⟩, Subgroup.mem_top _, (hΦ ⟨γ, hγ⟩).symm⟩
    · rintro ⟨l, -, rfl⟩
      obtain ⟨γ, rfl⟩ := R.surj l
      exact ⟨(γ : Matrix.GeneralLinearGroup ι K), γ.2, hΦ γ⟩
  have hnorm' : s16t3_normIdx (Γ.map Φ.toMonoidHom) :=
    s16t3_normIdx_map_mulEquiv Φ hnorm
  rwa [hmap] at hnorm'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
