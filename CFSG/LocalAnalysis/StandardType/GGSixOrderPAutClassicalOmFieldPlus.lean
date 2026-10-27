module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmPlus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank QuadraticMap
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.CatalogueBHigherLinearField TableBOrth

namespace OrdPOm

section FieldPlus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem glFieldAut_diagGL_of_fix {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K)
    {d : ι → Kˣ} (h : ∀ i, σ (d i) = d i) :
    glFieldAut ι K σ (TauCeti.diagGL d) = TauCeti.diagGL d := by
  apply Units.ext
  rw [RecipeFieldOmega.glFieldAut_apply_val, TauCeti.diagGL_coe, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  exact h i

omit [Finite K] [CharP K 2] in
theorem fieldAutP_spinModelPlus_fix (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) {τ : K ≃+* K}
    (hτp : τ ^ p = 1) {ζ : Kˣ} (hζp : ζ ^ p = 1) {x : spinGroup (quadPlus n K)}
    (hx : spinMatrix (quadPlus n K) x ∈ (TableBSymp.spTorusGL (K := K) (m := n) hζp).range) :
    AutOm.fieldAutP n τ (AutOm.spinModelPlus hn x) = AutOm.spinModelPlus hn x := by
  obtain ⟨a, ha⟩ := hx
  apply Subtype.ext
  rw [RecipeFieldOmega.fieldAutP_apply_val]
  change glFieldAut (Fin (2 * n)) K τ (reindexMatrixEquiv (plusIndexEquiv n)
      (spinMatrix (quadPlus n K) x)) = reindexMatrixEquiv (plusIndexEquiv n)
      (spinMatrix (quadPlus n K) x)
  rw [RecipeFieldOmega.glFieldAut_reindex, ← ha, TableBSymp.spTorusGL_apply,
    glFieldAut_diagGL_of_fix]
  have hz : ∀ k, (TableBSymp.zmodPowHom hζp (a k)) ^ p = 1 := fun k => by
    rw [← map_pow, show a k ^ p = 1 from congrFun (TableBSymp.pow_card_eq_one_zmod a) k,
      map_one]
  intro i
  rcases i with k | k
  · exact OrdPRest.ringAut_fix_of_pow_eq_one hp hτp
      (by rw [← Units.val_pow_eq_pow_val]; simp [TableBSymp.pairedUnits, hz k])
  · exact OrdPRest.ringAut_fix_of_pow_eq_one hp hτp
      (by rw [← Units.val_pow_eq_pow_val]; simp [TableBSymp.pairedUnits, inv_pow, hz k])

end FieldPlus

section FieldPlusMain

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem exists_conj_mem_centralizer_field_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hn4 : 4 ≤ n) (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n K) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (plusDatum n K hn) .POmegaPlus n f ψ)
    (hp : p ∣ Nat.card K - 1) (hne : ¬ (n = 4 ∧ p = 3)) {y : G}
    (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag (plusDatum n K hn) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  set j := spinMatrix (quadPlus n K) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (LargeEvenQPlus K n) := range_spinMatrix_quadPlus hn
  set π := AutOm.spinModelPlus (K := K) hn with hπdef
  have hπ : Function.Injective π := AutOm.spinModelPlus_injective hn
  have hπs : Function.Surjective π := AutOm.spinModelPlus_surjective hn
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := p) hp
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n K hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
  obtain ⟨hA, hAj, hAc⟩ := transfer_range ψ hψ j hj hS.elem hBsψ
  have hBs : Nat.card Bs ≤ p ^ n := by
    rw [← hAc]
    exact card_le_plus hp2 hζ (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  have hk : π.ker = ψ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hπ, (MonoidHom.ker_eq_bot_iff _).2 hψ]
  set Θ := AutSt.modelEquiv ψ π hπs hk with hΘdef
  have hΘ : ∀ x, ((Θ (π x) : ψ.range) : G) = ψ x := AutSt.modelEquiv_apply ψ π hπs hk
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hyM
  set a : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : ψ.range, ((a x : ψ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (matrixDerived (coordinateQuadPlus n K)) := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ z, Θ (β z) = a (Θ z) := fun z => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ z, ((Θ (β z) : ψ.range) : G) = y⁻¹ * Θ z * y := fun z => by rw [hβ, ha]
  obtain ⟨h, τ, hβeq⟩ := OrdPGraphOmega.exists_conj_mul_fieldAutP_of_pow hn4 hpp hp2 hne hβp
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hβeq
    obtain ⟨x₀, hx₀⟩ := hπs h
    apply hyI
    have hcent : y * ψ x₀ ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have e := hrel (π x)
      rw [hβeq, MulAut.conj_apply, ← hx₀, ← map_inv, ← map_mul, ← map_mul, hΘ, hΘ] at e
      rw [map_mul, map_mul, map_inv] at e
      calc ψ x * (y * ψ x₀) = y * (y⁻¹ * ψ x * y) * ψ x₀ := by group
        _ = y * (ψ x₀ * ψ x * (ψ x₀)⁻¹) * ψ x₀ := by rw [← e]
        _ = y * ψ x₀ * ψ x := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hy : y = ψ x₀⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hcent
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨x₀⁻¹, hy.symm⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadPlus n K hn
  have hAP := coordinate_plus_point_action_properties n K hn
  have hm : 1 ≤ n := by omega
  set S := CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus n K) τ
    (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n τ) with hSdef
  have hfS : AutOm.fieldAutP n τ = conjAct _ S := AutOm.fieldAutP_apply n τ
  have hSmap : ∀ v, coordinateSemilinearMap S.val v = coordinateFieldMap (2 * n) τ v := fun v => by
    funext i
    simp [S, CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair, coordinateSemilinearMap_apply,
      coordinateFieldMap_apply]
  have hSiso : RecipeFieldOmega.IsIsoPair (coordinateQuadPlus n K) S.val := fun v => by
    rw [hSmap]
    exact CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n τ v
  have hSw : coordinateSemilinearMap S.val (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hm) =
      CFSG.SeitzReduction.OmegaPilot.plusUnitVector hm := by
    rw [hSmap]
    exact CFSG.SeitzReduction.OmegaPilot.coordinateFieldMap_plusUnitVector hm τ
  have hout : MulAut.conj h * conjAct _ S ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus n K)) := by
    intro hI
    apply hτ1
    refine AutOm.eq_one_of_mem_inner_plusCompl hn (Or.inl rfl) ?_
    have e : AutOm.fieldAutP n τ = (MulAut.conj h)⁻¹ * (MulAut.conj h * conjAct _ S) := by
      rw [hfS, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem ⟨h, rfl⟩) hI
  have hord' : (MulAut.conj h * conjAct _ S) ^ p = 1 := by
    rw [← hfS, ← hβeq, hβp]
  have hfp : conjAct _ S ^ p = 1 := by
    have h1 := RecipeFieldOmega.pow_mem_inner_of_mul_pow_eq_one ⟨h, rfl⟩ hord'
    rw [← hfS, ← map_pow] at h1
    rw [← hfS, ← map_pow, AutOm.eq_one_of_mem_inner_plusCompl hn (Or.inl rfl) h1, map_one]
  have hτp : τ ^ p = 1 := by
    have h1 := hfp
    rw [← hfS, ← map_pow] at h1
    exact AutOm.eq_one_of_fieldAutP_eq_one hn h1
  obtain ⟨u', ⟨w, rfl⟩, heq⟩ := RecipeFieldOmega.exists_conj_of_isIsoPair hm hnd hT3 hAP hpp hp2
    hSiso (AutOm.plusUnitVector_form_ne_zero hm) hSw h hout hord' hfp
  have hβw : β = MulAut.conj w * AutOm.fieldAutP n τ * (MulAut.conj w)⁻¹ := by
    rw [hβeq, hfS, heq]
  set T := (TableBSymp.spTorusGL (K := K) (m := n) hζp).range with hT
  set EΓ := ((T.comap j).map π).map (MulAut.conj w).toMonoidHom with hEΓ
  have hfix : ∀ z ∈ EΓ, β z = z := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have e1 : (MulAut.conj w)⁻¹ (MulAut.conj w (π x)) = π x := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    calc β ((MulAut.conj w).toMonoidHom (π x)) =
        MulAut.conj w (AutOm.fieldAutP n τ ((MulAut.conj w)⁻¹ (MulAut.conj w (π x)))) := by
          rw [hβw]
          rfl
      _ = MulAut.conj w (π x) := by rw [e1, fieldAutP_spinModelPlus_fix hn hpp hτp hζp hx]
      _ = (MulAut.conj w).toMonoidHom (π x) := rfl
  set ι : matrixDerived (coordinateQuadPlus n K) →* G := ψ.range.subtype.comp Θ.toMonoidHom
    with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp Θ.injective
  have hTj : T ≤ j.range := by
    rw [hjr]
    rintro _ ⟨a, rfl⟩
    exact TableBSymp.spTorusGL_mem_omegaPlus hζp hodd a
  have hEel : IsElemAbelian p (EΓ.map ι) := isElemAbelian_map _ (isElemAbelian_map _
    (isElemAbelian_map _ (isElemAbelian_comap j hj (isElemAbelian_range_spTorusGL hζp))))
  have hEcard : Nat.card (EΓ.map ι) = p ^ n := by
    rw [Subgroup.card_map_of_injective hι, hEΓ,
      Subgroup.card_map_of_injective (MulAut.conj w).injective,
      Subgroup.card_map_of_injective hπ, ← Subgroup.card_map_of_injective hj,
      Subgroup.map_comap_eq_self hTj, card_range_spTorusGL hζp hζ hodd]
  have hEM : EΓ.map ι ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨z, -, rfl⟩
    exact (hrange.le.trans Subgroup.le_normalizer) (Θ z).2
  have hcomm : ∀ e ∈ EΓ.map ι, y * e = e * y := by
    rintro _ ⟨z, hz, rfl⟩
    have e := hrel z
    rw [hfix z hz] at e
    change y * (Θ z : G) = (Θ z : G) * y
    calc y * (Θ z : G) = y * (y⁻¹ * Θ z * y) := by rw [← e]
      _ = Θ z * y := by group
  exact OrdPNS.exists_conj_mem_centralizer_of_card hS hEM hEel (by rw [hEcard]; exact hBs) hcomm

end FieldPlusMain

end OrdPOm

section Family

theorem ggOrdPFieldConj_POmegaPlus_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .POmegaPlus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ → p ∣ 2 ^ f - 1 →
    ¬ (n = 4 ∧ p = 3) → ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hS hp hne y hyM hyo hyI
    obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
    obtain ⟨-, hf, hn4⟩ := hadm
    exact OrdPOm.exists_conj_mem_centralizer_field_plus (K := GaloisField 2 f) hn4 hn hS
      (by rw [GaloisField.card 2 f (by omega)]; exact hp) hne hyM (hyo ▸ pow_orderOf_eq_one y) hyI
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ hS
    exact absurd hS.presents.1.2 (by decide)

@[expose] def GGOrdPFieldConjPOmegaPlusRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .POmegaPlus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) →
    (¬ p ∣ 2 ^ f - 1 ∨ (n = 4 ∧ p = 3)) →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiDiagField (ggU .POmegaPlus n f).D ψ y → ¬ GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPFieldConjAt_POmegaPlus_of_rest (h : GGOrdPFieldConjPOmegaPlusRest) :
    GGOrdPFieldConjAt .POmegaPlus := by
  intro G _ _ p Bs G₀ n f ψ hS h24 y hyM hyo hDF hyI
  by_cases hpq : p ∣ 2 ^ f - 1 ∧ ¬ (n = 4 ∧ p = 3)
  · exact ggOrdPFieldConj_POmegaPlus_split G p Bs G₀ n f ψ hS hpq.1 hpq.2 y hyM hyo hyI
  · refine h G p Bs G₀ n f ψ hS h24 ?_ y hyM hyo hDF hyI
    by_cases hp : p ∣ 2 ^ f - 1
    · exact Or.inr (not_not.mp fun hne => hpq ⟨hp, hne⟩)
    · exact Or.inl hp

end Family

end CFSG.StandardType
