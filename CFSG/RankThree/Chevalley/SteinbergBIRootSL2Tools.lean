module

public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical

variable {τ : Tag} {K : Type} [Field K]

theorem rootSL2_injective_of_field (β : Fin τ.rank → ℤ) : Function.Injective (rootSL2 τ K β) := by
  by_cases hK : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq hK
    intro A B h
    rw [rootSL2_apply, rootSL2_apply] at h
    exact simpleRootSL2_injective_of_charTwo _ (by simpa using h)
  · exact ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.2.1 hK).1

theorem range_rootSL2_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (rootSL2 τ K β).range = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) :=
  (exceptional_Lang_root_rank_one_torus_transport τ K hβ).1

@[expose] def rootSL2Equiv {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    SL2 K ≃* (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) :=
  (MonoidHom.ofInjective (rootSL2_injective_of_field β)).trans
    (MulEquiv.subgroupCongr (range_rootSL2_of_isRoot hβ))

theorem coe_rootSL2Equiv {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (A : SL2 K) :
    (rootSL2Equiv hβ A : ModGL τ K) = rootSL2 τ K β A :=
  rfl

theorem baseChangeGL_weylElt_one {L : Type} [Field L] (f : K →+* L) (i : Fin τ.rank) :
    baseChangeGL f (weylElt τ K i 1) = weylElt τ L i 1 :=
  Units.ext ((baseChange_baseChangeEnd f _).unique (BaseChange.weylElt_one (f := f) i))

theorem baseChangeGL_pinnedWeyl {L : Type} [Field L] (f : K →+* L) (β : Fin τ.rank → ℤ) :
    baseChangeGL f (pinnedWeyl τ K β) = pinnedWeyl τ L β :=
  Units.ext ((baseChange_baseChangeEnd f _).unique
    (baseChange_prod_reverse_weylElt (τ := τ) f (pinnedData τ β).2.1))

theorem baseChangeGL_simpleRootSL2_of_field {L : Type} [Field L] (f : K →+* L) (i : Fin τ.rank)
    (A : SL2 K) :
    baseChangeGL f (simpleRootSL2 τ K i A) =
      simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f A) := by
  have h : (baseChangeGL f).comp (simpleRootSL2 τ K i) =
      (simpleRootSL2 τ L i).comp (Matrix.SpecialLinearGroup.map f) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change baseChangeGL f (simpleRootSL2 τ K i (uSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (uSL c))
        rw [simpleRootSL2_uSL, baseChangeGL_xUnit, map_uSL, simpleRootSL2_uSL]
      · change baseChangeGL f (simpleRootSL2 τ K i (vSL c)) =
          simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map f (vSL c))
        rw [simpleRootSL2_vSL, baseChangeGL_yUnit, map_vSL, simpleRootSL2_vSL]
  exact DFunLike.congr_fun h A

theorem baseChangeGL_rootSL2_of_field {L : Type} [Field L] (f : K →+* L) (β : Fin τ.rank → ℤ)
    (A : SL2 K) :
    baseChangeGL f (rootSL2 τ K β A) = rootSL2 τ L β (Matrix.SpecialLinearGroup.map f A) := by
  rw [rootSL2_apply, rootSL2_apply, map_mul, map_mul, map_inv, baseChangeGL_pinnedWeyl,
    baseChangeGL_simpleRootSL2_of_field]

theorem entrywise_rootSL2_of_field (σ : K →+* K) (β : Fin τ.rank → ℤ) (A : SL2 K) :
    Units.map (entrywiseHom σ) (rootSL2 τ K β A) =
      rootSL2 τ K β (Matrix.SpecialLinearGroup.map σ A) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL_self]
  exact baseChangeGL_rootSL2_of_field σ β A

theorem rootChar_neg' (a : Fin τ.rank → Kˣ) (β : Fin τ.rank → ℤ) :
    rootChar a (-β) = (rootChar a β)⁻¹ := by
  rw [show -β = 0 - β by rw [zero_sub], rootChar_sub, rootChar_zero, one_mul]

theorem rootDiagUnit_conj_rootSL2 (a : Fin τ.rank → Kˣ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (A : SL2 K) :
    rootDiagUnit τ a * rootSL2 τ K β A * (rootDiagUnit τ a)⁻¹ =
      rootSL2 τ K β (conjSL (diagUnitOne (rootChar a β)) A) := by
  obtain ⟨ε, -, hv⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  have h : (MulAut.conj (rootDiagUnit τ a)).toMonoidHom.comp (rootSL2 τ K β) =
      (rootSL2 τ K β).comp (conjSL (diagUnitOne (rootChar a β))) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conjSL_sl2Upper,
          MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        change rootDiagUnit τ a * rootSL2 τ K β (uSL c) * (rootDiagUnit τ a)⁻¹ =
          rootSL2 τ K β (uSL ((rootChar a β : K) * c))
        rw [rootSL2_uSL_eq, rootSL2_uSL_eq, rootDiagUnit_conj_pinnedX a hβ, mul_smul_comm]
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conjSL_sl2Lower,
          MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        change rootDiagUnit τ a * rootSL2 τ K β (vSL c) * (rootDiagUnit τ a)⁻¹ =
          rootSL2 τ K β (vSL (((rootChar a β)⁻¹ : Kˣ) * c))
        rw [hv, hv, rootDiagUnit_conj_pinnedX a (IsRoot.neg hβ), rootChar_neg']
        ring_nf
  exact DFunLike.congr_fun h A

theorem diagUnitOne_mul (a b : Kˣ) : diagUnitOne a * diagUnitOne b = diagUnitOne (a * b) := by
  ext i j
  rw [Units.val_mul, coe_diagUnitOne, coe_diagUnitOne, coe_diagUnitOne]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnitOne_one : diagUnitOne (1 : Kˣ) = 1 := by
  ext i j
  rw [coe_diagUnitOne]
  fin_cases i <;> fin_cases j <;> simp

theorem conjSL_diagUnitOne_mul (a b : Kˣ) (A : SL2 K) :
    conjSL (diagUnitOne a) (conjSL (diagUnitOne b) A) = conjSL (diagUnitOne (a * b)) A := by
  rw [← conjSL_mul, diagUnitOne_mul]

theorem conjSL_diagUnitOne_one (A : SL2 K) : conjSL (diagUnitOne (1 : Kˣ)) A = A := by
  rw [diagUnitOne_one, conjSL_one]

theorem exists_unit_zsmul_eq_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ u : Kˣ, u * u = 1 ∧ ∀ z : K, ε • z = (u : K) * z := by
  rcases hε with rfl | rfl
  · exact ⟨1, mul_one 1, fun z => by simp⟩
  · exact ⟨-1, by simp, fun z => by simp⟩

theorem conj_rootSL2_mem {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K) {w : WeylGroup τ}
    (hw : MapsRootLines n w) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : w • β = γ)
    (A : SL2 K) : n * rootSL2 τ K β A * n⁻¹ ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  have hπ : weylQuotientHom τ K ⟨n, hn⟩ = w := weylQuotientHom_eq hw
  have hle : rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ≤
      (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)).comap (MulAut.conj n).toMonoidHom := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hβ
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hμ,
        hπ, hγ]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (IsRoot.neg hβ)
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hμ,
        hπ, smul_neg, hγ]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  have hA : rootSL2 τ K β A ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
    rw [← range_rootSL2_of_isRoot hβ]
    exact ⟨A, rfl⟩
  exact hle hA

theorem exists_conj_rootSL2_eq {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K)
    {w : WeylGroup τ} (hw : MapsRootLines n w) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : w • β = γ) :
    ∃ s : Kˣ, ∀ A : SL2 K, n * rootSL2 τ K β A * n⁻¹ =
      rootSL2 τ K γ (conjSL (diagUnitOne s) A) := by
  have hγr : IsRoot τ γ := hγ ▸ IsRoot.smul hβ w
  have hπ : weylQuotientHom τ K ⟨n, hn⟩ = w := weylQuotientHom_eq hw
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hβ
  obtain ⟨μ', hμ'⟩ := monomial_conj_pinnedX hn (IsRoot.neg hβ)
  rw [hπ, hγ] at hμ
  rw [hπ, smul_neg, hγ] at hμ'
  obtain ⟨uβ, -, huβ⟩ := exists_unit_zsmul_eq_mul (K := K) (pinnedSign_eq τ β)
  obtain ⟨uγ, huγ, huγ'⟩ := exists_unit_zsmul_eq_mul (K := K) (pinnedSign_eq τ γ)
  obtain ⟨eβ, heβ, hvβ⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  obtain ⟨eγ, heγ, hvγ⟩ := exists_rootSL2_vSL_eq (K := K) hγr
  let conjHom : SL2 K →* (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) : Subgroup (ModGL τ K)) :=
    ((MulAut.conj n).toMonoidHom.comp (rootSL2 τ K β)).codRestrict _
      (conj_rootSL2_mem hn hw hβ hγ)
  let T : SL2 K →* SL2 K := (rootSL2Equiv (K := K) hγr).symm.toMonoidHom.comp conjHom
  have hT : ∀ A, rootSL2 τ K γ (T A) = n * rootSL2 τ K β A * n⁻¹ := fun A => by
    rw [← coe_rootSL2Equiv hγr]
    change (((rootSL2Equiv hγr) ((rootSL2Equiv hγr).symm (conjHom A)) : ModGL τ K)) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  set s : Kˣ := uγ * μ * uβ with hs
  set s' : Kˣ := Units.mkOfMulEqOne eγ eγ heγ * μ' * Units.mkOfMulEqOne eβ eβ heβ with hs'
  have hu : ∀ c, T (sl2Upper K c) = sl2Upper K (s * (RingEquiv.refl K) c) := fun c => by
    apply rootSL2_injective_of_field γ
    rw [hT]
    change n * rootSL2 τ K β (uSL c) * n⁻¹ = rootSL2 τ K γ (uSL ((s : K) * c))
    rw [rootSL2_uSL_eq, rootSL2_uSL_eq, hμ, huβ, huγ', hs]
    congr 1
    have huγK : (uγ : K) * uγ = 1 := by rw [← Units.val_mul, huγ, Units.val_one]
    simp only [Units.val_mul]
    linear_combination (μ * uβ * c : K) * huγK.symm
  have hl : ∀ c, T (sl2Lower K c) = sl2Lower K (s' * (RingEquiv.refl K) c) := fun c => by
    apply rootSL2_injective_of_field γ
    rw [hT]
    change n * rootSL2 τ K β (vSL c) * n⁻¹ = rootSL2 τ K γ (vSL ((s' : K) * c))
    rw [hvβ, hvγ, hμ', hs']
    congr 1
    simp only [Units.val_mul, Units.val_mkOfMulEqOne]
    linear_combination (μ' * eβ * c : K) * heγ.symm
  obtain ⟨-, M, hM, hTA⟩ := sl2_semilinear_root_compatibility (RingEquiv.refl K) s s' T hu hl
  have hMd : M = diagUnitOne s := Units.ext (by rw [hM, coe_diagUnitOne])
  subst hMd
  refine ⟨s, fun A => ?_⟩
  rw [← hT]
  congr 1
  apply Subtype.ext
  rw [hTA, coe_conjSL]
  congr 2

end CFSG.RankThree.Chevalley
