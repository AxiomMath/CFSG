module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeHermModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagSelfDual
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLBlock
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAPinHom

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open scoped Matrix

private lemma rckRPsu_isom_inv {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {σ : K ≃+* K} {β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K} {u : W ≃ₗ[K] W}
    (hu : ∀ w w', β (u w) (u w') = β w w') :
    ∀ w w', β (u⁻¹ w) (u⁻¹ w') = β w w' := by
  intro w w'
  rw [← hu (u⁻¹ w) (u⁻¹ w')]
  simp

private lemma rckRPsu_isom_mul {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {σ : K ≃+* K} {β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K} {u v : W ≃ₗ[K] W}
    (hu : ∀ w w', β (u w) (u w') = β w w') (hv : ∀ w w', β (v w) (v w') = β w w') :
    ∀ w w', β ((u * v) w) ((u * v) w') = β w w' := by
  intro w w'
  exact (hu (v w) (v w')).trans (hv w w')

private lemma rckRPsu_isom_commutator {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    {σ : K ≃+* K} {β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K} {u v : W ≃ₗ[K] W}
    (hu : ∀ w w', β (u w) (u w') = β w w') (hv : ∀ w w', β (v w) (v w') = β w w') :
    ∀ w w', β ((u * v * u⁻¹ * v⁻¹ : W ≃ₗ[K] W) w) ((u * v * u⁻¹ * v⁻¹ : W ≃ₗ[K] W) w') =
      β w w' :=
  rckRPsu_isom_mul (rckRPsu_isom_mul (rckRPsu_isom_mul hu hv) (rckRPsu_isom_inv hu))
    (rckRPsu_isom_inv hv)

private lemma rckRPsu_det_commutator {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (u v : W ≃ₗ[K] W) :
    LinearMap.det ((u * v * u⁻¹ * v⁻¹ : W ≃ₗ[K] W) : W →ₗ[K] W) = 1 := by
  have hD : LinearEquiv.det (u * v * u⁻¹ * v⁻¹ : W ≃ₗ[K] W) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [mul_right_comm (LinearEquiv.det u) (LinearEquiv.det v) ((LinearEquiv.det u)⁻¹),
      mul_inv_cancel, one_mul, mul_inv_cancel]
  have h := congrArg (fun z : Kˣ => (z : K)) hD
  rw [LinearEquiv.coe_det] at h
  exact h

theorem rckRP_exists_model_of_suBlock
    {G : Type} [Group G] [Finite G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (j : G →* GL ι F) {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : G, ∀ b ∈ B, ∀ m m' : ι → F,
      b ((j y : Matrix ι ι F).mulVec m) ((j y : Matrix ι ι F).mulVec m') = b m m')
    {S : Set (GL ι F)} {e : Matrix ι ι F} (he : IsIdempotentElem e) {J' : Subgroup G}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer j S e, glBlockCentralizer j S e⁆)
    {K W : Type} [Field K] [Finite K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W] [FiniteDimensional K W] {q : ℕ} (hK : Nat.card K = (2 ^ q) ^ 2)
    (hq : 2 ≤ q) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (hβs : β.IsSymm) (hβn : β.SeparatingLeft)
    (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    (φ : ↥(glBlockCentralizer j S e) →* (W ≃ₗ[K] W)) (hφ : Function.Injective φ)
    (hφiso : ∀ g w w', β (φ g w) (φ g w') = β w w')
    (hφsurj : ∀ g : W ≃ₗ[K] W, (∀ w w', β (g w) (g w') = β w w') →
      LinearMap.det (g : W →ₗ[K] W) = 1 → g ∈ φ.range)
    (hact : ∀ (g : ↥(glBlockCentralizer j S e)) w, (eW (φ g w) : ι → F) =
      ((j (g : G) : GL ι F) : Matrix ι ι F) *ᵥ (eW w : ι → F))
    (hform : ∀ b ∈ B, (∀ m₁ m₂ n : ι → F, b (m₁ + m₂) n = b m₁ n + b m₂ n) ∧
      (∀ m n : ι → F, b ((1 - e) *ᵥ m) (e *ᵥ n) = 0) ∧
      (∀ w w' : W, b (eW w : ι → F) (eW w' : ι → F) = Algebra.trace F K (β w w')) ∧
      ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    ∃ (t : CFSG.Open.StatedLieTag) (k : ℕ) (κ : (ggU t k q).K →* G), (t = .PSU ∨ t = .PSL) ∧
      RCKNormalizedModel t k q ∧ κ.range = J' ∧
      (∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k q).K) ∧
      RCKRPRootFlags j B κ ∧
      ∀ γ ∈ (ggU t k q).D.roots, GGLongRoot (ggU t k q).D γ →
        Nat.card ((ggU t k q).D.rootGroup γ) = 2 ^ q := by
  classical
  let Ge : Subgroup G := glBlockCentralizer j S e
  have hm : 2 ≤ Module.finrank K W := by
    by_contra hcon
    have hle : Module.finrank K W ≤ 1 := by omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle
    have hscalar : ∀ f : W →ₗ[K] W, ∃ d : K, ∀ w, f w = d • w := by
      intro f
      obtain ⟨d, hd⟩ := hv (f v)
      refine ⟨d, fun w => ?_⟩
      obtain ⟨c, hc⟩ := hv w
      rw [← hc, map_smul, ← hd]
      exact smul_comm c d v
    have hisocomm : ∀ a b : ↥Ge, Commute a b := by
      intro a b
      obtain ⟨c, hc⟩ := hscalar (φ a : W →ₗ[K] W)
      obtain ⟨d, hd⟩ := hscalar (φ b : W →ₗ[K] W)
      have hc' : ∀ w, φ a w = c • w := fun w => hc w
      have hd' : ∀ w, φ b w = d • w := fun w => hd w
      have key : (φ a) * (φ b) = (φ b) * (φ a) := by
        ext w
        change φ a (φ b w) = φ b (φ a w)
        rw [hd' w, map_smul, hc' w, map_smul, hd' w]
        exact smul_comm d c w
      exact hφ (by rw [map_mul, map_mul]; exact key)
    have hbot : ⁅Ge, Ge⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hisocomm ⟨b, hb⟩ ⟨a, ha⟩).eq
    have hJbot : J' = ⊥ := by
      rw [eq_bot_iff]
      exact hJe.1.trans (le_of_eq hbot)
    have hntriv : Nontrivial ↥J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
    rw [Subgroup.nontrivial_iff_ne_bot] at hntriv
    exact hntriv hJbot
  obtain ⟨ρ, hρinj, hρrange, β₀, v, hβ₀root, hβ₀long, hβ₀card, hv0, hvv, htrans⟩ :=
    exists_suModel_of_hermForm (K := K) (W := W) (q := q) (m := Module.finrank K W)
      hK (by omega) rfl hm hσ2 hσ1 β hβs hβn
  have hρq : CFSG.IsQuasisimple ↥ρ.range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hρinj)
      (isQuasisimple_ggU_PSU hm hq)
  have hρperfect : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    rw [← Subgroup.map_subtype_commutator, hρq.1.commutator_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hφc : (commutator ↥Ge).map φ = ρ.range := by
    have hle : ⁅φ.range, φ.range⁆ ≤ ρ.range := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      refine (hρrange _).mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact rckRPsu_isom_commutator (hφiso g) (hφiso h)
      · rw [commutatorElement_def]
        exact rckRPsu_det_commutator (φ g) (φ h)
    have hge : ρ.range ≤ ⁅φ.range, φ.range⁆ := by
      have hφle : ρ.range ≤ φ.range := by
        intro a ha
        obtain ⟨hisom, hdet⟩ := (hρrange a).mp ha
        exact hφsurj a hisom hdet
      calc ρ.range = ⁅ρ.range, ρ.range⁆ := hρperfect.symm
        _ ≤ ⁅φ.range, φ.range⁆ := Subgroup.commutator_mono hφle hφle
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact le_antisymm hle hge
  obtain ⟨κG, hκGinj, hκGrange, hκGφ⟩ :=
    rckRP_exists_kappa_of_map_commutator_eq (G := Ge) φ hφ ρ hρinj hφc
  let κ : (ggU .PSU (Module.finrank K W) q).K →* G := Ge.subtype.comp κG
  have hκinj : Function.Injective κ := Ge.subtype_injective.comp hκGinj
  have hSLq : CFSG.IsQuasisimple (ggU .PSU (Module.finrank K W) q).K :=
    isQuasisimple_ggU_PSU hm hq
  have hMq : CFSG.IsQuasisimple ↥⁅Ge, Ge⁆ := by
    rw [← hκGrange]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hκinj) hSLq
  have hJeq : J' = ⁅Ge, Ge⁆ :=
    CFSG.StandardType.Line63.H5.eq_of_isComponentOf_of_isQuasisimple hJe
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hMq)
  have hκrange : κ.range = J' := hκGrange.trans hJeq.symm
  have hcenter : ∀ y, κ y ∈ Subgroup.center G →
      y ∈ Subgroup.center (ggU .PSU (Module.finrank K W) q).K := fun _ hy =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.pinned_center_of_inj κ hκinj hy
  have hflag₀ : GLGeoFlag B ((((ggU .PSU (Module.finrank K W) q).D.rootGroup β₀).map κ).map j) := by
    refine glGeoFlag_of_blockTransv (e := e) he eW hσ2 hσ1 β hβs hβn hv0 hvv ?_ ?_ hform
    · rintro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp ha
      exact (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp (κG y).2)).2
    · rintro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨c, hcσ, hc⟩ := htrans y hy
      refine ⟨c, hcσ, fun w => ?_⟩
      simp only [κ, MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← hact (κG y) w, hκGφ y, hc w]
  rcases lt_or_eq_of_le hm with hm3 | hm2
  ·
    have hκq : CFSG.Assembly.IsQuasisimple ↥κ.range := by
      rw [hκrange]
      exact hJe.2.2
    have hadm : CFSG.Open.StatedLieAdmissible .PSU (Module.finrank K W) 2 q := by
      rcases rckRP_admissible_PSU_of_quasisimple_range (r := Module.finrank K W) (g := q)
        (by omega) κ hκq with h | ⟨h2, -⟩
      · exact h
      · omega
    have hnorm : RCKNormalizedModel .PSU (Module.finrank K W) q := ⟨by simp [GGPosTag], hadm⟩
    have hnot : ¬ ((CFSG.Open.StatedLieTag.PSU = CFSG.Open.StatedLieTag.PSp ∧
        Module.finrank K W = 2) ∨ CFSG.Open.StatedLieTag.PSU = CFSG.Open.StatedLieTag.F4) := by
      simp
    have hflags : RCKRPRootFlags j B κ :=
      rckRP_rootFlags_of_long (j := j) (B := B) hiso hnorm hnot κ hβ₀root hβ₀long hflag₀
    refine ⟨.PSU, Module.finrank K W, κ, Or.inl rfl, hnorm, hκrange, hcenter, hflags, ?_⟩
    intro γ hγ hlong
    obtain ⟨u, hu⟩ :=
      CFSG.StandardType.RCKK1I.rckK1I_longRootConj hnorm.1 hnorm.2 hβ₀root hβ₀long hγ hlong
    rw [← hu]
    exact (Subgroup.card_map_of_injective (MulAut.conj u).injective).trans hβ₀card
  ·
    obtain ⟨ψ⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := q) (by omega : 1 ≤ q)
    have hψ : (ggU .PSL 2 q).K ≃* (ggU .PSU (Module.finrank K W) q).K := by
      rw [hm2.symm]
      exact ψ
    let κ' : (ggU .PSL 2 q).K →* G := κ.comp hψ.toMonoidHom
    have hκ'range : κ'.range = J' := by
      dsimp only [κ']
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ hψ.surjective,
        ← MonoidHom.range_eq_map, hκrange]
    have hκ'inj : Function.Injective κ' := hκinj.comp hψ.injective
    have hκ'ker : κ'.ker ≤ Subgroup.center (ggU .PSL 2 q).K := by
      rw [(MonoidHom.ker_eq_bot_iff κ').mpr hκ'inj]
      exact bot_le
    have hκ'q : CFSG.Assembly.IsQuasisimple ↥κ'.range := by
      rw [hκ'range]
      exact hJe.2.2
    have hnorm' : RCKNormalizedModel .PSL 2 q :=
      ⟨by simp [GGPosTag],
        rckRP_admissible_PSL_of_quasisimple_range (k := 1) (f := q) (by omega) κ' hκ'q⟩
    have hP₀le : ((ggU .PSU (Module.finrank K W) q).D.rootGroup β₀).map κ ≤ κ'.range := by
      rw [hκ'range, ← hκrange]
      exact Subgroup.map_le_range κ _
    have hP₀card : Nat.card (((ggU .PSU (Module.finrank K W) q).D.rootGroup β₀).map κ) = 2 ^ q :=
      (Subgroup.card_map_of_injective hκinj).trans hβ₀card
    have hcenter' : ∀ y, κ' y ∈ Subgroup.center G →
        y ∈ Subgroup.center (ggU .PSL 2 q).K := by
      intro y hy
      have hy' : hψ y ∈ Subgroup.center (ggU .PSU (Module.finrank K W) q).K :=
        hcenter (hψ y) hy
      have hcentermap : (Subgroup.center (ggU .PSL 2 q).K).map (hψ : _ →* _) =
          Subgroup.center (ggU .PSU (Module.finrank K W) q).K := Subgroup.map_center_eq hψ
      rw [← hcentermap] at hy'
      exact (Subgroup.mem_map_iff_mem hψ.injective).mp hy'
    have hflags' : RCKRPRootFlags j B κ' :=
      rckRP_rootFlags_PSL_two (j := j) (B := B) (f := q) hiso (by omega) κ' hκ'ker hP₀le hP₀card
        hflag₀
    refine ⟨.PSL, 2, κ', Or.inr rfl, hnorm', hκ'range, hcenter', hflags', ?_⟩
    intro γ hγ _
    exact card_rootGroup_specialLinear_galoisField (p := 2) (k := 1) (q := q) (by omega : q ≠ 0) hγ

theorem rckRP_flaggedModel_of_suBlock
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    {X : Subgroup (GL ι F)} {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : ↥X, ∀ b ∈ B, ∀ m m' : ι → F,
      b (((y : GL ι F) : Matrix ι ι F).mulVec m) (((y : GL ι F) : Matrix ι ι F).mulVec m') =
        b m m')
    {S : Set (GL ι F)} {e : Matrix ι ι F} (he : IsIdempotentElem e) {J' : Subgroup ↥X}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer X.subtype S e, glBlockCentralizer X.subtype S e⁆)
    {K W : Type} [Field K] [Finite K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W] [FiniteDimensional K W] {q : ℕ} (hK : Nat.card K = (2 ^ q) ^ 2)
    (hq : 2 ≤ q) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (hβs : β.IsSymm) (hβn : β.SeparatingLeft)
    (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    (φ : ↥(glBlockCentralizer X.subtype S e) →* (W ≃ₗ[K] W)) (hφ : Function.Injective φ)
    (hφiso : ∀ g w w', β (φ g w) (φ g w') = β w w')
    (hφsurj : ∀ g : W ≃ₗ[K] W, (∀ w w', β (g w) (g w') = β w w') →
      LinearMap.det (g : W →ₗ[K] W) = 1 → g ∈ φ.range)
    (hact : ∀ g w, (eW (φ g w) : ι → F) =
      (((g : ↥X) : GL ι F) : Matrix ι ι F) *ᵥ (eW w : ι → F))
    (hform : ∀ b ∈ B, (∀ m₁ m₂ n : ι → F, b (m₁ + m₂) n = b m₁ n + b m₂ n) ∧
      (∀ m n : ι → F, b ((1 - e) *ᵥ m) (e *ᵥ n) = 0) ∧
      (∀ w w' : W, b (eW w : ι → F) (eW w' : ι → F) = Algebra.trace F K (β w w')) ∧
      ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    RCKRPFlaggedModel X.subtype B J' := by
  obtain ⟨t, k, κ, -, hnorm, hrange, hcen, hflags, -⟩ :=
    rckRP_exists_model_of_suBlock X.subtype hiso he hJe hK hq hσ2 hσ1 β hβs hβn eW φ hφ hφiso
      hφsurj hact hform
  exact ⟨t, k, q, κ, hnorm, hrange, hcen, hflags⟩

end CFSG.StandardType.RCKRP
