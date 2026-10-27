module

public import CFSG.LocalAnalysis.StandardType.GGLangRatRouteCCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDRank
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Models.Transport
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

section InnerD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem langRatRouteC_closure_le_componentWeylGroup
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} ≤ componentWeylGroup Ψ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
  obtain ⟨u, j, hu⟩ := isRoot_iff_exists_smul_single.1 (simpleRoots_isRoot hβ)
  have h3 : rootReflection (w • β) = w * rootReflection β * w⁻¹ := by
    rw [rootReflection_eq_conj (w := w * u) (j := j) (by rw [mul_smul, hu]),
      rootReflection_eq_conj hu]
    group
  rw [SetLike.mem_coe, h3]
  exact mul_mem (mul_mem hw (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hw)

theorem langRatRouteC_exists_cartanD_neg_one {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    ∃ k : Fin n, CFSG.LieType.Universal.Spin.cartanD n j k = -1 := by
  have hj := j.2
  by_cases h : j.val + 2 < n
  · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = j.val + 1 := ⟨⟨j.val + 1, by omega⟩, rfl⟩
    refine ⟨k, ?_⟩
    have hne : j ≠ k := fun h' => by rw [h'] at hk; omega
    simp only [CFSG.LieType.Universal.Spin.cartanD, Matrix.of_apply, hne, ↓reduceIte]
    split_ifs <;> omega
  · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = n - 3 := ⟨⟨n - 3, by omega⟩, rfl⟩
    refine ⟨k, ?_⟩
    have hne : j ≠ k := fun h' => by rw [h'] at h; omega
    simp only [CFSG.LieType.Universal.Spin.cartanD, Matrix.of_apply, hne, ↓reduceIte]
    split_ifs <;> omega

theorem langRatRouteC_isGraphTwist_of_eqOn
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2) {n : ℕ} (e : simpleRoots Ψ ≃ Fin n)
    (he : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD n (e β) (e γ))
    (hn : 3 ≤ n) (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (hid : ∀ γ ∈ Ψ, δ γ = γ) :
    IsGraphTwist Ψ δ where
  invol γ hγ := by rw [hid γ hγ, hid γ hγ]
  orth γ hγ hne := absurd (hid γ hγ) hne
  reach γ hγ := by
    obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
    have hset : {g : WeylGroup τ | ∃ β ∈ simpleRoots Ψ,
        g = setReflection ({β, δ β} : Set (Fin τ.rank → ℤ))} =
        rootReflection '' (simpleRoots Ψ : Set (Fin τ.rank → ℤ)) := by
      ext g
      constructor
      · rintro ⟨β', hβ', rfl⟩
        refine ⟨β', hβ', ?_⟩
        rw [hid β' (simpleRoots_subset hβ'), Set.pair_eq_singleton, setReflection_singleton]
      · rintro ⟨β', hβ', rfl⟩
        refine ⟨β', hβ', ?_⟩
        rw [hid β' (simpleRoots_subset hβ'), Set.pair_eq_singleton, setReflection_singleton]
    refine ⟨w⁻¹, ?_, by rw [inv_smul_smul]; exact hβ⟩
    rw [hset]
    exact inv_mem hw
  adj β hβ _ := by
    obtain ⟨k, hk⟩ := langRatRouteC_exists_cartanD_neg_one hn (e ⟨β, hβ⟩)
    refine ⟨e.symm k, (e.symm k).2, hid _ (simpleRoots_subset (e.symm k).2), ?_⟩
    have h := he ⟨β, hβ⟩ (e.symm k)
    rw [Equiv.apply_symm_apply, hk] at h
    simp only [corootPair, hsl β hβ] at h
    omega

theorem langRatRouteC_datumAt_innerD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {n : ℕ}
    (e₀ : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin n)
    (he₀ : ∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD n (e₀ β) (e₀ γ))
    (h5 : 5 ≤ n)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    TwoDExcFixedPointsDatumAt S a i := by
  classical
  revert e₀
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  intro e₀ he₀
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hcardΔ : (simpleRoots Ψ).card = n := by
    rw [← Fintype.card_coe, Fintype.card_congr e₀, Fintype.card_fin]
  have hrank : compRank Ψ = n := by rw [compRank_eq_card hΨ, hcardΔ]
  have h5' : 5 ≤ compRank Ψ := hrank ▸ h5
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r = 2 := CharP.eq L hchar ‹CharP L 2›
  subst hr2
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := S.componentOrbitLength_eq_one_of_five_leT hT i h5'
  rw [hs1, Function.iterate_one] at hinner
  obtain ⟨w, hw, hρw⟩ := hinner
  have hwW : w ∈ componentWeylGroup Ψ := langRatRouteC_closure_le_componentWeylGroup hΨ hw
  have hv : w⁻¹ ∈ componentWeylGroup Ψ := inv_mem hwW
  have hid : ∀ γ ∈ Ψ, S.rhoTwist w⁻¹ γ = γ := fun γ hγ => by
    rw [S.rhoTwist_apply, hρw γ hγ, inv_smul_smul]
  have hmaps : ∀ γ ∈ Ψ, S.rhoTwist w⁻¹ γ ∈ Ψ := fun γ hγ => by rw [hid γ hγ]; exact hγ
  have hpos : ∀ γ ∈ posRoots Ψ, S.rhoTwist w⁻¹ γ ∈ posRoots Ψ := fun γ hγ => by
    rw [hid γ hγ.1]; exact hγ
  have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 :=
    simplyLaced_of_five_le_rank (τ := τ) (by have := compRank_le Ψ; omega)
  have hsl : ∀ β ∈ simpleRoots Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β (simpleRoots_subset hβ))
  have hG : IsGraphTwist Ψ (S.rhoTwist w⁻¹) :=
    langRatRouteC_isGraphTwist_of_eqOn hΨ hsl e₀ he₀ (by omega) _ hid
  have hiso := S.iform_rhoTwist w⁻¹
  have hΔ : ∀ β ∈ simpleRoots Ψ, S.rhoTwist w⁻¹ β ∈ simpleRoots Ψ := fun β hβ => by
    rw [hid β (simpleRoots_subset hβ)]; exact hβ
  obtain ⟨y, hyZ, hyM, hyv, hpin⟩ := S.exists_twoD_pin hq i hv hΔ
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hSC : ∀ T : Set (Fin τ.rank → ℤ),
      torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L := fun T =>
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hyC : y ∈ adjointGroup τ L := hSC Ψ hyZ
  have hFc : ∀ g, frobTwistGL τ L 2 e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ L).map (MulAut.conj (y * Q)).toMonoidHom = adjointGroup τ L := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ L ⟨y, hyM⟩ = w⁻¹ := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ Ψ, (rootSubgroup τ L γ).map (frobTwistGL τ L 2 e (y * Q)) =
      rootSubgroup τ L (S.rhoTwist w⁻¹ γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ L 2 e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots Ψ, ∀ A : SL2 L,
      frobTwistGL τ L 2 e (y * Q) (rootSL2 τ L β A) =
        rootSL2 τ L (S.rhoTwist w⁻¹ β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 e) A) :=
    fun β hβ A => by rw [hFc]; exact hpin β hβ A
  obtain ⟨D, -, hDroots, hDsimple, hDperf, hDtor, hDfixed⟩ :=
    exists_twoD_datum_fixed_roots hτ he i (S.rhoTwist w⁻¹) hiso hmaps hpos hG hcT hcG hU hpin'
  have hyZ' : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
  obtain ⟨z, hzZ, hz⟩ := S.exists_lang_twoDT he hQT hstep hT hyZ'
  have hzC : z ∈ adjointGroup τ L := hSC _ hzZ
  have hzN : z ∈ Subgroup.normalizer (rootSpan τ L Ψ) := mem_normalizer_rootSpan_of_mem_Z hzZ i
  have hconj := map_fixedPointSubgroup_conj_eq_of_pin (Ψ := Ψ) (F := S.D.step)
    (F' := frobTwistGL τ L 2 e (y * Q)) hFc hz hzN hzC
  have hdet : (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 := by
    have hmat : (Matrix.of fun β γ : simpleRoots Ψ =>
        corootPair (β : Fin τ.rank → ℤ) γ) =
        (CFSG.LieType.Universal.Spin.cartanD n).submatrix e₀ e₀ := by
      ext β γ
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      exact he₀ β γ
    rw [hmat, Matrix.det_submatrix_equiv_self]
    exact CFSG.StandardType.PsiDiag.SpinP.det_cartanD (by omega)
  have hcenter : Subgroup.center (rootSpan τ L Ψ) = ⊥ := center_eq_bot_of_cartan_det_eq_four i hdet
  have hiter : iterHom S.D.step 1 = S.D.step :=
    MonoidHom.ext fun g => by rw [iterHom_eq_iterate, Function.iterate_one]
  refine ⟨D, simpleRoots Ψ, z, hDperf, ?_, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hDsimple]
  · intro γ hγ
    rw [hDroots] at hγ
    exact exists_coords hΨ hγ
  · rw [hDroots]
    exact hcenter
  · rw [hDroots]
    exact hDtor
  · rw [hs1, hiter, hconj, hDfixed]

end InnerD

theorem langRatRouteC_modelPerfect_innerD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {n : ℕ}
    (e : simpleRoots (componentRoots (rootCharHom b) i) ≃ Fin n)
    (he : ∀ β γ : simpleRoots (componentRoots (rootCharHom b) i),
      corootPair (β : Fin τ.rank → ℤ) γ = CFSG.LieType.Universal.Spin.cartanD n (e β) (e γ))
    (h5 : 5 ≤ n)
    (hinner : twistInner (componentRoots (rootCharHom b) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) i)])) :
    Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
  have hcardΔ : (simpleRoots (componentRoots (rootCharHom b) i)).card = n := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have h5' : 5 ≤ compRank (componentRoots (rootCharHom b) i) := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card
      (isRootComponent_componentRoots i), hcardΔ]
    exact h5
  obtain ⟨D, Δ, z, hperf, hΔ, hdet, hspan, hcenter, -, hHmap⟩ :=
    langRatRouteC_datumAt_innerD S hb i e he h5 hinner
  have hΔroot : ∀ β ∈ Δ, IsRoot τ β := by
    intro β hβ
    have hβJ : β ∈ D.simpleRootsJ := by rw [← hΔ]; exact hβ
    exact CFSG.LieType.Chevalley.isRoot_of_mem_unionSimpleRoots hβJ.1
  have hP := CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedPointsPerfect_of_datum S D Δ hΔ
    hΔroot hdet hspan hcenter z hHmap hperf
  exact langRatRouteC_modelPerfect_of_fixedData S hb i h5'
    (CFSG.LocalAnalysis.GLTheoremA.T171Sh.twoDExcFixedData_of_perfect hP)

end CFSG.StandardType.LangRat

end
