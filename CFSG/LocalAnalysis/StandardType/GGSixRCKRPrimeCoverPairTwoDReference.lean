module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairFix
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairPinE6
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.ClassicalInvolution.WeakCT
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.RankThree.Chevalley
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups


private theorem rckTwoD_root_image_of_param
    {τ : Tag} {F : Type} [Field F] {U : Type} [Group U] (H : Subgroup U)
    (φ : U →* ModGL τ GGL) (param : F → U)
    (hmem : ∀ c, param c ∈ H) (hsurj : ∀ u ∈ H, ∃ c, param c = u)
    (σ : GGL ≃+* GGL) (κ : F ≃+* ↥(fixSubfield σ)) (z : ModGL τ GGL)
    (γ : Fin τ.rank → ℤ)
    (hparam : ∀ c, φ (param c) = z * pinnedX τ GGL γ (κ c : GGL) * z⁻¹) :
    H.map φ = ((rootSubgroup τ ↥(fixSubfield σ) γ).map
      (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, rfl⟩ := hsurj u hu
    refine ⟨pinnedX τ GGL γ (κ c : GGL), ?_, ?_⟩
    · refine ⟨pinnedX τ ↥(fixSubfield σ) γ (κ c), mem_rootSubgroup.mpr ⟨κ c, rfl⟩, ?_⟩
      rw [baseChangeGL_pinnedX]
      rfl
    · change z * pinnedX τ GGL γ (κ c : GGL) * z⁻¹ = φ (param c)
      exact (hparam c).symm
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hv
    refine ⟨param (κ.symm c), hmem _, ?_⟩
    rw [hparam, κ.apply_symm_apply, baseChangeGL_pinnedX]
    rfl

theorem rckTwoD_reference_pair
    {τ : Tag} {p₀ h : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} (P : RCKTwoDCanonicalData S a i h) :
    let n := compRank (componentRoots (rootCharHom a) i)
    let k : Fin (n - 1) := ⟨0, by have := P.rank_four_le; omega⟩
    ∃ γ ∈ componentRoots (rootCharHom a) i, ∃ σ : GGL ≃+* GGL,
      (∀ g ∈ rootSpan τ GGL {γ, -γ},
        S.D.step (P.z * g * P.z⁻¹) = P.z * frobGL σ g * P.z⁻¹) ∧
      ((ggU .POmegaMinus n h).D.rootGroup (Pi.single k 1)).map P.φ =
        ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj P.z).toMonoidHom ∧
      ((ggU .POmegaMinus n h).D.rootGroup (-Pi.single k 1)).map P.φ =
        ((rootSubgroup τ ↥(fixSubfield σ) (-γ)).map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj P.z).toMonoidHom := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP GGL 2 := by change CharP (AlgebraicClosure (ZMod 2)) 2; infer_instance
  let n := compRank (componentRoots (rootCharHom a) i)
  let k : Fin (n - 1) := ⟨0, by have := P.rank_four_le; omega⟩
  let j : Fin n := ⟨0, by have := P.rank_four_le; omega⟩
  have hk : k.val + 1 < n - 1 := by have := P.rank_four_le; dsimp [k, n]; omega
  have hj : j.val + 2 < n := by have := P.rank_four_le; dsimp [j, n]; omega
  let γ : Fin τ.rank → ℤ := P.ε.symm j
  have hγ : IsRoot τ γ := simpleRoots_isRoot (P.ε.symm j).2
  have hγΨ : γ ∈ componentRoots (rootCharHom a) i := simpleRoots_subset (P.ε.symm j).2
  let σ : GGL ≃+* GGL := iterateFrobeniusEquiv GGL 2 P.D.e
  have hσ : ∀ c, σ c = c ^ 2 ^ P.D.e := fun c => iterateFrobeniusEquiv_def _ _ _ c
  have hring : σ.toRingHom = iterateFrobenius GGL 2 P.D.e := by
    ext c
    exact (hσ c).trans (iterateFrobenius_def 2 P.D.e c).symm
  have hfields : fixSubfield σ = frobeniusFixedField GGL 2 P.D.e := by
    ext c
    rw [mem_fixSubfield, mem_frobeniusFixedField, hσ]
  let κ : GaloisField 2 h ≃+* ↥(fixSubfield σ) :=
    P.κ.trans (RingEquiv.subfieldCongr hfields.symm)
  have hκ : ∀ c, (κ c : GGL) = (P.κ c : GGL) := fun c => rfl
  let ι : GaloisField 2 h →+* GGL := (frobeniusFixedField GGL 2 P.D.e).subtype.comp P.κ.toRingHom
  have hι : ∀ c, ι c = (P.κ c : GGL) := fun c => rfl
  have hupper : ∀ c : GaloisField 2 h,
      P.φ (rLong n (minusCoeffs 2 h).1 (minusCoeffs 2 h).2 hk (tv 0 1 c)) =
        P.z * pinnedX τ GGL γ (κ c : GGL) * P.z⁻¹ := by
    intro c
    have h := congrArg (fun f => f (tv 0 1 c)) (P.long_param k hk)
    change P.φ (rLong n _ _ hk (tv 0 1 c)) =
      P.z * rootSL2 τ GGL γ (Matrix.SpecialLinearGroup.map ι (tv 0 1 c)) * P.z⁻¹ at h
    rw [rckPin_tv01_eq_uSL, map_uSL, rootSL2_uSL_of_charTwo hγ] at h
    simpa only [rckPin_tv01_eq_uSL, hκ, hι] using h
  have hlower : ∀ c : GaloisField 2 h,
      P.φ (rLong n (minusCoeffs 2 h).1 (minusCoeffs 2 h).2 hk (tv 1 0 c)) =
        P.z * pinnedX τ GGL (-γ) (κ c : GGL) * P.z⁻¹ := by
    intro c
    have h := congrArg (fun f => f (tv 1 0 c)) (P.long_param k hk)
    change P.φ (rLong n _ _ hk (tv 1 0 c)) =
      P.z * rootSL2 τ GGL γ (Matrix.SpecialLinearGroup.map ι (tv 1 0 c)) * P.z⁻¹ at h
    rw [rckPin_tv10_eq_vSL, map_vSL, rootSL2_vSL_of_charTwo hγ] at h
    simpa only [rckPin_tv10_eq_vSL, hκ, hι] using h
  refine ⟨γ, hγΨ, σ, ?_, ?_, ?_⟩
  · intro g hg
    have hspan : rootSpan τ GGL {γ, -γ} = (rootSL2 τ GGL γ).range := by
      rw [range_rootSL2_of_isRoot hγ]
      simp only [rootSpan, iSup_pair]
    obtain ⟨A, rfl⟩ := hspan ▸ hg
    let x : adjointGroup τ GGL := ⟨rootSL2 τ GGL γ A, CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup γ A⟩
    have hγD : γ ∈ P.D.simpleRootsJ := by rw [P.simple_eq]; exact (P.ε.symm j).2
    have hDF := P.D.map_rootSL2 γ hγD.1 γ (P.fix_long j hj) A x rfl
    calc S.D.step (P.z * rootSL2 τ GGL γ A * P.z⁻¹) = P.z * (P.D.F x : ModGL τ GGL) * P.z⁻¹ := P.frob_eq x
      _ = P.z * rootSL2 τ GGL γ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * P.z⁻¹ := by rw [hDF, hring]
      _ = P.z * frobGL σ (rootSL2 τ GGL γ A) * P.z⁻¹ := by rw [frobGL_rootSL2 σ hγ]
  · haveI := fact_shortField (minusCoeffs_irr 2 h)
    exact rckTwoD_root_image_of_param _ P.φ
      (fun c => rLong n _ _ hk (tv 0 1 c)) (rLong_upper (hirr := minusCoeffs_irr 2 h) hk)
      (rLong_param_upper (hirr := minusCoeffs_irr 2 h) hk) σ κ P.z γ hupper
  · haveI := fact_shortField (minusCoeffs_irr 2 h)
    exact rckTwoD_root_image_of_param _ P.φ
      (fun c => rLong n _ _ hk (tv 1 0 c)) (rLong_lower (hirr := minusCoeffs_irr 2 h) hk)
      (rLong_param_lower (hirr := minusCoeffs_irr 2 h) hk) σ κ P.z (-γ) hlower

end CFSG.StandardType.RCKRP
