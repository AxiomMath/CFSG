module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldDesc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmFieldMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  QuadraticMap CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.CatalogueBHigherLinearField TableBOrth Module

namespace OrdPFieldNsOm

open NoOffOm OrdPNsOm

section Setting

theorem exists_conj_mem_centralizer_of_semilinear {G : Type} [Group G] [Finite G] {U : Type}
    [Group U] {p : ℕ} {Bs G₀ : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag}
    {m f : ℕ} {ψ : U →* G} (hS : GGSixFusionSetting p Bs G₀ Δ t m f ψ)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ)
    (hφG : φ.range ≤ Subgroup.normalizer (G₀ : Set G)) (hBφ : Bs ≤ φ.range)
    {S : coordinateSemilinearGroup (2 * n) K} (hSQ : RecipeFieldOmega.IsIsoPair Q S)
    (hSp : S ^ p = 1) (w : matrixDerived Q) {y : G}
    (hy : ∀ X : matrixDerived Q, matrixConjugation S (X : GL (Fin (2 * n)) K) = X →
      y * φ (w * X * w⁻¹) = φ (w * X * w⁻¹) * y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have hA := genMax_of_orth hnd hT hp hp2 hS.elem hS.omega φ hφ hBφ
  have hAcard : Nat.card ((Bs.comap φ).map (matrixDerived Q).subtype) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective,
      ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hBφ]
  obtain ⟨E, hEΓ, hEc, hEp, hEcard, hEfix⟩ := exists_fixed_elemAb hn hnd hT hSQ hSp hA
  set E₁ := E.comap (matrixDerived Q).subtype with hE₁
  have hE₁map : E₁.map (matrixDerived Q).subtype = E :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hEΓ)
  have hE₁card : Nat.card E₁ = Nat.card E := by
    rw [← Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective, hE₁map]
  set ρ : matrixDerived Q →* G := φ.comp (MulAut.conj w).toMonoidHom with hρdef
  have hρinj : Function.Injective ρ := hφ.comp (MulAut.conj w).injective
  have hρ : ∀ X, ρ X = φ (w * X * w⁻¹) := fun X => rfl
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS (E := E₁.map ρ) ?_ ?_ ?_ ?_
  · rintro _ ⟨X, -, rfl⟩
    exact hφG ⟨_, rfl⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, s, hs, rfl⟩ := a
      obtain ⟨_, s', hs', rfl⟩ := b
      apply Subtype.ext
      change ρ s * ρ s' = ρ s' * ρ s
      have h1 : s * s' = s' * s := Subtype.ext (hEc _ hs _ hs')
      rw [← map_mul, ← map_mul, h1]
    · rintro _ ⟨s, hs, rfl⟩
      have h1 : s ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hEp _ hs)
      rw [← map_pow, h1, map_one]
  · rw [Subgroup.card_map_of_injective hρinj, hE₁card, ← hAcard]
    exact hEcard
  · rintro _ ⟨X, hX, rfl⟩
    rw [hρ]
    exact hy X (hEfix _ hX)

end Setting

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem exists_conj_mem_centralizer_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hn4 : 4 ≤ n) (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n K) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (plusDatum n K hn) .POmegaPlus n f ψ)
    (hM : ∀ β : MulAut (matrixDerived (coordinateQuadPlus n K)), β ^ p = 1 →
      OrdPGraph.ModelDiagField (plusDatum n K hn) (AutOm.spinModelPlus hn) β →
        ∃ (h : matrixDerived (coordinateQuadPlus n K)) (τ : K ≃+* K),
          β = MulAut.conj h * AutOm.fieldAutP n τ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hDF : GGPsiDiagField (plusDatum n K hn) ψ y) (hyI : ¬ GGPsiInnerDiag (plusDatum n K hn) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have hpp := hS.prime
  have hp2 := hS.ne_two
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  set π := AutOm.spinModelPlus (K := K) hn with hπdef
  have hπ : Function.Injective π := AutOm.spinModelPlus_injective hn
  have hπs : Function.Surjective π := AutOm.spinModelPlus_surjective hn
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n K hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
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
  have hMD : OrdPGraph.ModelDiagField (plusDatum n K hn) π β := by
    obtain ⟨g, ⟨x₁, rfl⟩, hall⟩ := hDF
    refine ⟨π x₁, fun γ hγ z hz => ?_⟩
    obtain ⟨z', hz', e⟩ := hall γ hγ z hz
    refine ⟨z', hz', Θ.injective (Subtype.ext ?_)⟩
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrel,
      hΘ, hΘ, hΘ, ← e]
    group
  obtain ⟨h, τ, hβeq⟩ := hM β hβp hMD
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
  obtain ⟨u', ⟨w, rfl⟩, heq⟩ := RecipeFieldOmega.exists_conj_of_isIsoPair hm hnd hT3 hAP hpp hp2
    hSiso (AutOm.plusUnitVector_form_ne_zero hm) hSw h hout hord' hfp
  have hβw : β = MulAut.conj w * AutOm.fieldAutP n τ * (MulAut.conj w)⁻¹ := by
    rw [hβeq, hfS, heq]
  have hSp : S ^ p = 1 := RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT3 hAP
    ⟨_, AutOm.plusUnitVector_form_ne_zero hm⟩
    (by rw [SubmonoidClass.coe_pow]; exact hSiso.pow p) (by rw [map_pow, hfp])
  refine exists_conj_mem_centralizer_of_semilinear hS hn4 hnd hT3
    (ψ.range.subtype.comp Θ.toMonoidHom) (Subtype.val_injective.comp Θ.injective) ?_ ?_ hSiso
    (by rw [← SubmonoidClass.coe_pow, hSp]; rfl) w fun X hX => ?_
  · rintro _ ⟨z, rfl⟩
    exact (hrange.le.trans Subgroup.le_normalizer) (Θ z).2
  · intro b hb
    exact ⟨Θ.symm ⟨b, hBsψ hb⟩, by simp⟩
  · have hfixX : conjAct _ S X = X := Subtype.ext hX
    have e1 : (MulAut.conj w)⁻¹ (w * X * w⁻¹) = X := by
      rw [MulAut.conj_inv_apply]
      group
    have hβX : β (w * X * w⁻¹) = w * X * w⁻¹ := by
      rw [hβw, MulAut.mul_apply, MulAut.mul_apply, e1, hfS, hfixX, MulAut.conj_apply]
    have e := hrel (w * X * w⁻¹)
    rw [hβX] at e
    change y * (Θ (w * X * w⁻¹) : G) = (Θ (w * X * w⁻¹) : G) * y
    generalize (Θ (w * X * w⁻¹) : G) = θ at e ⊢
    calc y * θ = y * (y⁻¹ * θ * y) := by rw [← e]
      _ = θ * y := by group

end Plus

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ} {b c : K}

theorem exists_conj_mem_centralizer_minus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n) {f₀ : ℕ}
    (hf : Nat.card K = 2 ^ f₀) (hf1 : 1 ≤ f₀) {ψ : spinGroup (quadMinus n K b c) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (minusDatum n hirr) .POmegaMinus n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G))
    (hyp : y ^ p = 1) (hyI : ¬ GGPsiInnerDiag (minusDatum n hirr) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hn : 1 ≤ n := by omega
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn4]
    exact hker
  set π := AutOm.spinModelMinus hn4 hirr with hπdef
  have hπ : Function.Injective π := AutOm.spinModelMinus_injective hn4 hirr
  have hπs : Function.Surjective π := AutOm.spinModelMinus_surjective hn4 hirr
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn4 ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
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
  set β : MulAut (matrixDerived (Qm n hn4 b c)) := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ z, Θ (β z) = a (Θ z) := fun z => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ z, ((Θ (β z) : ψ.range) : G) = y⁻¹ * Θ z * y := fun z => by rw [hβ, ha]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (Qm n hn4 b c)) := by
    rintro ⟨h, hh⟩
    obtain ⟨x₀, hx₀⟩ := hπs h
    apply hyI
    have hcent : y * ψ x₀ ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have e := hrel (π x)
      rw [← hh, MulAut.conj_apply, ← hx₀, ← map_inv, ← map_mul, ← map_mul, hΘ, hΘ] at e
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
  obtain ⟨ι, ⟨h, rfl⟩, k, hβeq⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf β
  have hb := ne_zero_of_irreducible_tail b c hirr
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  set S := (frobPair n hn b c hb) ^ k with hSdef
  have hτS : AutOm.frobAut hn4 hirr ^ k = conjAct (Qm n hn4 b c) S := by
    change AutOm.frobAut hn4 hirr ^ k = conjAct (Qm n hn4 b c) (frobPair n hn b c hb ^ k)
    rw [map_pow]
    rfl
  have hSiso : RecipeFieldOmega.IsIsoPair (Qm n hn4 b c) S.val := by
    rw [SubmonoidClass.coe_pow]
    exact (RecipeFieldOmega.isIsoPair_frobPair hn hb).pow k
  have hout : MulAut.conj h * conjAct _ S ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
    rw [← hτS, ← hβeq]
    exact hβout
  have hord' : (MulAut.conj h * conjAct _ S) ^ p = 1 := by
    rw [← hτS, ← hβeq, hβp]
  have hfp : conjAct _ S ^ p = 1 := by
    have h1 := RecipeFieldOmega.pow_mem_inner_of_mul_pow_eq_one ⟨h, rfl⟩ hord'
    rw [← hτS, ← pow_mul] at h1
    have h2 : AutOm.frobAut hn4 hirr ^ (k * p) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) ⊓
          Subgroup.zpowers (AutOm.frobAut hn4 hirr) :=
      ⟨h1, Subgroup.npow_mem_zpowers _ _⟩
    rw [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at h2
    rw [← hτS, ← pow_mul, h2]
  obtain ⟨u', ⟨w, rfl⟩, heq⟩ := RecipeFieldOmega.exists_conj_of_isIsoPair hn hnd hT3 hAP hpp hp2
    hSiso (AutOm.tailVec_form_ne_zero n hn b c) (RecipeFieldOmega.frobPair_pow_tailVec hn hb k) h
    hout hord' hfp
  have hβw : β = MulAut.conj w * conjAct _ S * (MulAut.conj w)⁻¹ := by
    rw [hβeq, hτS, heq]
  have hSp : S ^ p = 1 := RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT3 hAP
    ⟨_, AutOm.tailVec_form_ne_zero n hn b c⟩
    (by rw [SubmonoidClass.coe_pow]; exact hSiso.pow p) (by rw [map_pow, hfp])
  refine exists_conj_mem_centralizer_of_semilinear hS hn4 hnd hT3
    (ψ.range.subtype.comp Θ.toMonoidHom) (Subtype.val_injective.comp Θ.injective) ?_ ?_ hSiso
    (by rw [← SubmonoidClass.coe_pow, hSp]; rfl) w fun X hX => ?_
  · rintro _ ⟨z, rfl⟩
    exact (hrange.le.trans Subgroup.le_normalizer) (Θ z).2
  · intro b hb
    exact ⟨Θ.symm ⟨b, hBsψ hb⟩, by simp⟩
  · have hfixX : conjAct _ S X = X := Subtype.ext hX
    have e1 : (MulAut.conj w)⁻¹ (w * X * w⁻¹) = X := by
      rw [MulAut.conj_inv_apply]
      group
    have hβX : β (w * X * w⁻¹) = w * X * w⁻¹ := by
      rw [hβw, MulAut.mul_apply, MulAut.mul_apply, e1, hfixX, MulAut.conj_apply]
    have e := hrel (w * X * w⁻¹)
    rw [hβX] at e
    change y * (Θ (w * X * w⁻¹) : G) = (Θ (w * X * w⁻¹) : G) * y
    generalize (Θ (w * X * w⁻¹) : G) = θ at e ⊢
    calc y * θ = y * (y⁻¹ * θ * y) := by rw [← e]
      _ = θ * y := by group

end Minus

end OrdPFieldNsOm

section FourInput

@[expose] def GGOmegaPlusFourDiagFieldInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (β : MulAut (matrixDerived (coordinateQuadPlus 4 K))), β ^ 3 = 1 →
    OrdPGraph.ModelDiagField (plusDatum 4 K (by norm_num)) (AutOm.spinModelPlus (by norm_num)) β →
      ∃ (h : matrixDerived (coordinateQuadPlus 4 K)) (τ : K ≃+* K),
        β = MulAut.conj h * AutOm.fieldAutP 4 τ

end FourInput

section Family

theorem ggOrdPFieldConjPOmegaMinusNonsplit_holds : GGOrdPFieldConjPOmegaMinusNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ _ y hyM hyo _ hyI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨-, hf, hn⟩ := hadm
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact OrdPFieldNsOm.exists_conj_mem_centralizer_minus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hK hf hS hyM (hyo ▸ pow_orderOf_eq_one y) hyI

theorem ggOrdPFieldConjAt_POmegaMinus : GGOrdPFieldConjAt .POmegaMinus :=
  ggOrdPFieldConjAt_POmegaMinus_of_nonsplit ggOrdPFieldConjPOmegaMinusNonsplit_holds

theorem ggOrdPFieldConjPOmegaPlus_of_ne : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .POmegaPlus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ → ¬ (n = 4 ∧ p = 3) →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiDiagField (ggU .POmegaPlus n f).D ψ y → ¬ GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hS hne y hyM hyo hDF hyI
    obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
    obtain ⟨-, -, hn4⟩ := hadm
    exact OrdPFieldNsOm.exists_conj_mem_centralizer_plus (K := GaloisField 2 f) hn4 hn hS
      (fun β hβp _ => OrdPGraphOmega.exists_conj_mul_fieldAutP_of_pow hn4 hS.prime hS.ne_two hne
        hβp) hyM (hyo ▸ pow_orderOf_eq_one y) hDF hyI
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ hS
    exact absurd hS.presents.1.2 (by decide)

theorem ggOrdPFieldConjPOmegaPlusRest_of_fourDiagField (h43 : GGOmegaPlusFourDiagFieldInput) :
    GGOrdPFieldConjPOmegaPlusRest := by
  intro G _ _ p Bs G₀ n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hS _ _ y hyM hyo hDF hyI
    obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
    obtain ⟨-, -, hn4⟩ := hadm
    refine OrdPFieldNsOm.exists_conj_mem_centralizer_plus (K := GaloisField 2 f) hn4 hn hS
      (fun β hβp hMD => ?_) hyM (hyo ▸ pow_orderOf_eq_one y) hDF hyI
    by_cases hne : n = 4 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hne
      exact h43 (GaloisField 2 f) β hβp hMD
    · exact OrdPGraphOmega.exists_conj_mul_fieldAutP_of_pow hn4 hS.prime hS.ne_two hne hβp
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ hS
    exact absurd hS.presents.1.2 (by decide)

theorem ggOrdPFieldConjAt_POmegaPlus_of_fourDiagField (h43 : GGOmegaPlusFourDiagFieldInput) :
    GGOrdPFieldConjAt .POmegaPlus :=
  ggOrdPFieldConjAt_POmegaPlus_of_rest (ggOrdPFieldConjPOmegaPlusRest_of_fourDiagField h43)

end Family

end CFSG.StandardType
