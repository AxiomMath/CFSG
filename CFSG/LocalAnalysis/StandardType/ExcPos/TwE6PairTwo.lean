module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairDefs
import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.LocalAnalysis.StandardType.GGFinModelBCTw
import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneJoint
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LocalAnalysis.StandardType.GGFinModelInnDiagTw
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.GroupTheory.OddKernelImage
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem pairTwo_orbit_data
    {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x) (hb : B.b = 2) :
    B.Δ.n = 1 ∧
      B.diag = diagramAt .E6 (ExcOmega f) .E6 rfl ∧ p ∣ 2 ^ f - 1 := by
  have hf := B.one_le_f
  rcases B.orbit with h | ⟨h, ⟨ht, hdiag⟩, hdiv, hn⟩
  · change B.b = 1 at h
    omega
  · refine ⟨hn, ?_, ?_⟩
    · simpa using hdiag
    · simpa only [GaloisField.card 2 f (by omega : f ≠ 0)] using hdiv

private theorem pairTwo_components {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hx : x ∈ D) (hb : B.b = 2) :
    ∃ i₂ : KernelComponent (LieCore.jointChar (B.coord x) (B.coord B.d)),
      i₂ ≠ B.iJ ∧ B.ρ '' B.rootsJ =
        componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂ ∧
      ∀ α ∈ B.rootsJ, ∀ β ∈ componentRoots
        (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂,
        CFSG.LieType.Steinberg.Adjoint.iform α β = 0 := by
  have hker : Set.MapsTo B.ρ
      (kernelRoots (LieCore.jointChar (B.coord x) (B.coord B.d)))
      (kernelRoots (LieCore.jointChar (B.coord x) (B.coord B.d))) := by
    intro γ hγ
    simpa using LieCore.iterate_mem_kernelRoots_jointChar B.frob
      (B.coord_torus x hx) (B.coord_torus B.d B.d_mem) 1 hγ
  obtain ⟨i₂, hi₂⟩ := exists_image_componentRoots hker B.frob.iform_eq B.iJ
  have hij : B.iJ ≠ i₂ := by
    rintro rfl
    change B.ρ '' B.rootsJ = B.rootsJ at hi₂
    have hone : B.b = 1 := componentOrbitLength_eq_one
      (kernelRoots_finite.subset fun _ h => h.1) (by
        intro α hα
        rw [← hi₂]
        exact Set.mem_image_of_mem _ hα)
    omega
  refine ⟨i₂, Ne.symm hij, hi₂, ?_⟩
  rintro α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩
  apply iform_eq_zero_of_mk_ne (α := ⟨α, hα⟩) (β := ⟨β, hβ⟩)
  intro h
  exact hij (hαi.symm.trans (h.trans hβi))

private theorem pairTwo_step_eq {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    B.Δ.step = ggPhi .twistedE6 f := by
  apply MonoidHom.ext
  intro y
  change B.Δ.n * B.Δ.Φ y * B.Δ.n⁻¹ = ggPhi .twistedE6 f y
  rw [(pairTwo_orbit_data B hb).1, hB.Φ_eq]
  simp only [one_mul, inv_one, mul_one]
  rfl

private theorem pairTwo_rho_eq {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    B.ρ α = ggGraphLat .twistedE6 α := by
  have hmap := B.frob.map_rootSubgroup α hα
  rw [pairTwo_step_eq B hB hb] at hmap
  have hgraph : IsRoot .E6 (ggGraphLat .twistedE6 α) :=
    hα.permLattice (TwistTag.cartan_perm .E6)
  exact LieCore.rootSubgroup_injective_of_isRoot ((B.frob.isRoot_iff α).2 hα) hgraph
    (hmap.symm.trans (LieCore.ggLieDP_map_ggPhi_rootSubgroup
      (Or.inr (Or.inr rfl)) f hα))

private theorem pairTwo_rho_sq {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) : B.ρ (B.ρ α) = α := by
  rw [pairTwo_rho_eq B hB hb ((B.frob.isRoot_iff α).2 hα), pairTwo_rho_eq B hB hb hα]
  change permLattice (TwistTag.perm .E6) (permLattice (TwistTag.perm .E6) α) = α
  funext i
  fin_cases i <;> rfl

private theorem pairTwo_curve_sq {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    ((excCurve α (1 : ModGL .E6 (ExcOmega f))).map B.Δ.step).map B.Δ.step =
      excCurve α 1 := by
  have hcurve : excCurve α (1 : ModGL .E6 (ExcOmega f)) =
      rootSubgroup .E6 (ExcOmega f) α := by
    simp only [excCurve, map_one]
    change (rootSubgroup .E6 (ExcOmega f) α).map (MonoidHom.id _) = _
    exact Subgroup.map_id _
  rw [hcurve, B.frob.map_rootSubgroup α hα,
    B.frob.map_rootSubgroup (B.ρ α) ((B.frob.isRoot_iff α).2 hα), pairTwo_rho_sq B hB hb hα]

private theorem pairTwo_short_data {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B)
    (hx : x ∈ D) (hb : B.b = 2) {α : Fin (Tag.rank .E6) → ℤ} (hα : α ∈ B.rootsJ) :
    CFSG.LieType.Steinberg.TwistedE6.rho α ≠ α ∧
      ¬ IsRoot .E6 (α + CFSG.LieType.Steinberg.TwistedE6.rho α) ∧
      α + CFSG.LieType.Steinberg.TwistedE6.rho α ≠ 0 := by
  obtain ⟨i₂, hne, himage, -⟩ := pairTwo_components B hx hb
  have hρα : B.ρ α = CFSG.LieType.Steinberg.TwistedE6.rho α :=
    pairTwo_rho_eq B hB hb hα.1.1
  have hmem : B.ρ α ∈ componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂ := by
    rw [← himage]
    exact Set.mem_image_of_mem _ hα
  have hnonfix : CFSG.LieType.Steinberg.TwistedE6.rho α ≠ α := by
    intro heq
    rw [hρα, heq] at hmem
    exact hne (hmem.2.symm.trans hα.2)
  exact ⟨hnonfix, CFSG.LieType.Steinberg.TwistedE6.not_isRoot_add_rho hα.1.1 hnonfix,
    CFSG.LieType.Steinberg.TwistedE6.add_rho_ne_zero hα.1.1 hnonfix⟩

private theorem pairTwo_A2_data {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hP : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x)
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hb : B.b = 2) :
    ∃ i₂ : KernelComponent (LieCore.jointChar (B.coord x) (B.coord B.d)), i₂ ≠ B.iJ ∧ B.ρ '' B.rootsJ = componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂ ∧
      compRank B.rootsJ = 2 ∧ B.rootsJ.ncard = 6 ∧
      compRank (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂) = 2 ∧ (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂).ncard = 6 := by
  obtain ⟨i₂, hne, himage, -⟩ := pairTwo_components B B.x_mem hb
  change B.ρ '' B.rootsJ = componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂ at himage
  have hrank : 2 ≤ compRank B.rootsJ := excBase_rank_ge_two (Or.inr (Or.inr (Or.inr rfl))) hP B
  have hcard : B.rootsJ.ncard = (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂).ncard := by
    rw [← himage, Set.ncard_image_of_injective _ B.ρ.injective]
  exact ⟨i₂, hne, himage, twE6_twoOrbit_is_A2_pair rfl (LieCore.jointChar (B.coord x) (B.coord B.d)) hne.symm hrank hcard⟩

private theorem pairTwo_native_image (n f : ℕ) (hf : 1 ≤ f)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    ((ggU .twistedE6 n f).D.rootGroup (CFSG.LieType.Steinberg.TwistedE6.proj α)).map
        (ggIotaK .twistedE6 n f hf) =
      (rootSubgroup .E6 GGL α ⊔
        rootSubgroup .E6 GGL (CFSG.LieType.Steinberg.TwistedE6.rho α)) ⊓
      (ggPhi .twistedE6 f).eqLocus (MonoidHom.id _) := by
  have hβ : CFSG.LieType.Steinberg.TwistedE6.proj α ∈ (ggU .twistedE6 n f).D.roots := by
    exact isRoot_iff_mem_roots.mp (CFSG.LieType.Steinberg.TwistedE6.isRoot_proj hα)
  rw [ggBC_twistedE6 n f hf _ hβ]
  unfold CFSG.LieType.Steinberg.twistedRootSubgroup
  congr 1
  apply le_antisymm
  · refine iSup_le fun γ => iSup_le fun hγ => iSup_le fun hc => ?_
    obtain ⟨c, hc, he⟩ := hc
    have he' : CFSG.LieType.Steinberg.TwistedE6.proj γ =
        c • CFSG.LieType.Steinberg.TwistedE6.proj α := he
    have hc1 := CFSG.LieType.Steinberg.TwistedE6.eq_one_of_proj_eq_nsmul hγ hα hc he'
    subst c
    have hproj : CFSG.LieType.Steinberg.TwistedE6.proj α =
        CFSG.LieType.Steinberg.TwistedE6.proj γ := by simpa only [one_smul] using he'.symm
    rcases (CFSG.LieType.Steinberg.TwistedE6.proj_eq_proj_iff hα hγ).mp hproj with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · exact le_iSup_of_le α (le_iSup_of_le hα
        (le_iSup_of_le (⟨1, by omega, by simp only [one_smul]; rfl⟩ :
          ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum
            CFSG.LieType.Steinberg.TwistedE6.orbitMap α =
              c • CFSG.LieType.Steinberg.TwistedE6.proj α) le_rfl))
    · exact le_iSup_of_le (CFSG.LieType.Steinberg.TwistedE6.rho α)
        (le_iSup_of_le (CFSG.LieType.Steinberg.TwistedE6.isRoot_rho hα)
          (le_iSup_of_le (⟨1, by omega, by
            simpa only [one_smul, ← CFSG.LieType.Steinberg.TwistedE6.proj_apply] using
              CFSG.LieType.Steinberg.TwistedE6.proj_rho α⟩ :
            ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum
              CFSG.LieType.Steinberg.TwistedE6.orbitMap
                (CFSG.LieType.Steinberg.TwistedE6.rho α) =
                  c • CFSG.LieType.Steinberg.TwistedE6.proj α) le_rfl))

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional in
private theorem pairTwo_fixed_curve_card (f : ℕ) (hf : 1 ≤ f)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hne : rho α ≠ α) (hsum : ¬ IsRoot .E6 (α + rho α)) (hzero : α + rho α ≠ 0) :
    Nat.card ↥((rootSubgroup (langTag .twistedE6) GGL α ⊔ rootSubgroup (langTag .twistedE6) GGL (rho α)) ⊓
      (ggPhi .twistedE6 f).eqLocus (MonoidHom.id _)) = Nat.card (GaloisField 2 f) ^ 2 := by
  classical
  let Q : Subgroup (ModGL (langTag .twistedE6) GGL) := (rootSubgroup (langTag .twistedE6) GGL α ⊔ rootSubgroup (langTag .twistedE6) GGL (rho α)) ⊓
    (ggPhi .twistedE6 f).eqLocus (MonoidHom.id _)
  let v : GaloisField 2 (2 * f) → ModGL (langTag .twistedE6) GGL := fun c =>
    pinnedX (langTag .twistedE6) GGL α (ggRatEmb (2 * f) c) *
      pinnedX (langTag .twistedE6) GGL (rho α) (ggRatEmb (2 * f) (frobQ 2 f c))
  have hx : ∀ β c, pinnedX (langTag .twistedE6) GGL β c ∈ rootSubgroup (langTag .twistedE6) GGL β :=
    fun β c => Subgroup.subset_closure ⟨c, rfl⟩
  have hcomm := ggCommuteRoot hα hne hsum hzero
  have hpow : ∀ c : GaloisField 2 (2 * f),
      (ggRatEmb (2 * f) c) ^ 2 ^ f = ggRatEmb (2 * f) (frobQ 2 f c) := by
    intro c
    rw [frobQ_apply, map_pow]
  have hv : ∀ c, v c ∈ Q := by
    intro c
    refine ⟨Subgroup.mul_mem_sup (hx _ _) (hx _ _), ?_⟩
    change ggPhi .twistedE6 f (v c) = v c
    dsimp [v]
    rw [map_mul, ggPhi_pinnedX_twistedE6 f hα _,
      ggPhi_pinnedX_twistedE6 f (isRoot_rho hα) _]
    change pinnedX (langTag .twistedE6) GGL (rho α) ((ggRatEmb (2 * f) c) ^ 2 ^ f) *
      pinnedX (langTag .twistedE6) GGL (rho (rho α))
        ((ggRatEmb (2 * f) (frobQ 2 f c)) ^ 2 ^ f) = _
    rw [rho_rho, hpow, hpow, frobQ_frobQ 2 f hf]
    exact (hcomm _ (hx _ _) _ (hx _ _)).eq.symm
  have hheight : height (rho α) = height α := by
    rw [height, height, rho, permLattice]
    exact Equiv.sum_comp rhoPerm.symm α
  have hsign : (0 < height α ∧ 0 < height (rho α)) ∨
      (height α < 0 ∧ height (rho α) < 0) := by
    rcases IsRoot.height_pos_or_neg hα with h | h
    · exact Or.inl ⟨h, hheight.symm ▸ h⟩
    · exact Or.inr ⟨h, hheight.symm ▸ h⟩
  let vQ : GaloisField 2 (2 * f) → Q := fun c => ⟨v c, hv c⟩
  have hinj : Function.Injective vQ := by
    intro c d heq
    have heq' : v c = v d := congrArg Subtype.val heq
    have hp := ggPinnedXPairInj hα (isRoot_rho hα) hne.symm hsign heq'
    exact (ggRatEmb (2 * f)).injective hp.1
  have hsurj : Function.Surjective vQ := by
    intro y
    obtain ⟨c, hc⟩ := ggTwDescent_short_param f hf hα hne hsum hzero y.2.1 y.2.2
    exact ⟨c, Subtype.ext hc⟩
  calc
    Nat.card Q = Nat.card (GaloisField 2 (2 * f)) :=
      Nat.card_congr (Equiv.ofBijective vQ ⟨hinj, hsurj⟩).symm
    _ = 2 ^ (2 * f) := GaloisField.card 2 (2 * f) (by omega)
    _ = Nat.card (GaloisField 2 f) ^ 2 := by
      rw [GaloisField.card 2 f (by omega), Nat.mul_comm 2 f, pow_mul]

private theorem pairTwo_rational_curve_card {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B)
    (hb : B.b = 2) {α : Fin (Tag.rank .E6) → ℤ} (hα : α ∈ B.rootsJ) :
    Nat.card ↥((rootSubgroup .E6 (ExcOmega f) α ⊔
      (rootSubgroup .E6 (ExcOmega f) α).map B.Δ.step) ⊓
      B.Δ.step.eqLocus (MonoidHom.id _)) = Nat.card (GaloisField 2 f) ^ 2 := by
  obtain ⟨hne, hsum, hzero⟩ := pairTwo_short_data B hB B.x_mem hb hα
  rw [B.frob.map_rootSubgroup α hα.1.1, pairTwo_rho_eq B hB hb hα.1.1,
    pairTwo_step_eq B hB hb]
  exact pairTwo_fixed_curve_card f B.one_le_f hα.1.1 hne hsum hzero

private theorem pairTwo_lang_pkg {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) :
    GGLangPkg B.Δ (ggIota .twistedE6 n f B.one_le_f) := by
  exact (ggLangPkg_twE6_adjoint B.one_le_f B.Δ hB.Φ_eq).of_equiv
    (ggKbEquivTwE6 n f B.one_le_f)

private theorem pairTwo_g0_fixed {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    (@id (ModGL (langTag .twistedE6) GGL) B.Δ.g0) ∈ ggFixGp .twistedE6 f := by
  refine ⟨B.Δ.g0_mem, ?_⟩
  change ggPhi .twistedE6 f B.Δ.g0 = B.Δ.g0
  rw [← hB.Φ_eq]
  exact (B.Δ.lang.trans (by rw [(pairTwo_orbit_data B hb).1, mul_one]))

private theorem pairTwo_g0_normalizer {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    B.Δ.g0 ∈ Subgroup.normalizer
      ((@id (Subgroup (ModGL .E6 (ExcOmega f)))
        (ggIota .twistedE6 n f B.one_le_f).range) : Set (ModGL .E6 (ExcOmega f))) := by
  have hfix : B.Δ.g0 ∈ B.Δ.fix := by
    refine ⟨B.Δ.g0_mem, ?_⟩
    change B.Δ.Φ B.Δ.g0 = B.Δ.g0
    exact B.Δ.lang.trans (by rw [(pairTwo_orbit_data B hb).1, mul_one])
  exact Eq.mp (congrArg (fun H : Subgroup (ModGL .E6 (ExcOmega f)) =>
    B.Δ.g0 ∈ Subgroup.normalizer (H : Set (ModGL .E6 (ExcOmega f))))
    (pairTwo_lang_pkg B hB).desc.derived)
    (Subgroup.normalizer_commutator_ge_left B.Δ.fix B.Δ.fix hfix)

private theorem pairTwo_orbit_roots {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    LieCore.ratOrbit B.ρ B.rootsJ = B.rootsJ ∪ B.ρ '' B.rootsJ := by
  have hU : Set.MapsTo B.ρ (B.rootsJ ∪ B.ρ '' B.rootsJ)
      (B.rootsJ ∪ B.ρ '' B.rootsJ) := by
    rintro α (hα | ⟨β, hβ, rfl⟩)
    · exact Or.inr (Set.mem_image_of_mem _ hα)
    · apply Or.inl
      rw [pairTwo_rho_sq B hB hb hβ.1.1]
      exact hβ
  ext α
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    exact hU.iterate k (Or.inl hδ)
  · rintro (hα | ⟨δ, hδ, rfl⟩)
    · exact ⟨0, α, hα, rfl⟩
    · exact ⟨1, δ, hδ, rfl⟩

private theorem pairTwo_span_sq {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    ((rootSpan .E6 (ExcOmega f) B.rootsJ).map B.Δ.step).map B.Δ.step =
      rootSpan .E6 (ExcOmega f) B.rootsJ := by
  rw [B.frob.map_rootSpan B.rootsJ (fun _ h => h.1.1),
    B.frob.map_rootSpan (B.ρ '' B.rootsJ) (by
      rintro _ ⟨α, hα, rfl⟩
      exact (B.frob.isRoot_iff α).2 hα.1.1)]
  congr 1
  ext α
  constructor
  · rintro ⟨β, ⟨γ, hγ, rfl⟩, rfl⟩
    rw [pairTwo_rho_sq B hB hb hγ.1.1]
    exact hγ
  · intro hα
    exact ⟨B.ρ α, ⟨α, hα, rfl⟩, pairTwo_rho_sq B hB hb hα.1.1⟩

private noncomputable def pairTwo_cycle {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    CycFamily B.Δ.step 2 := by
  classical
  let S₀ : Subgroup (ModGL .E6 (ExcOmega f)) := rootSpan .E6 (ExcOmega f) B.rootsJ
  let S₁ : Subgroup (ModGL .E6 (ExcOmega f)) := S₀.map B.Δ.step
  have hc : ∀ u ∈ S₀, ∀ v ∈ S₁, Commute u v := by
    obtain ⟨i₂, hne, himage, -⟩ := pairTwo_components B B.x_mem hb
    have hbot := (root_character_kernel_orthogonal_central_product .E6 (ExcOmega f)
      (LieCore.jointChar (B.coord x) (B.coord B.d))).2.2.1 B.iJ i₂ hne.symm
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot
    have hS₁ : S₁ = componentRootSpan (ExcOmega f)
        (LieCore.jointChar (B.coord x) (B.coord B.d)) i₂ := by
      dsimp [S₁, S₀]
      rw [B.frob.map_rootSpan B.rootsJ (fun _ h => h.1.1), himage]
      rfl
    intro u hu v hv
    have hv' := hS₁ ▸ hv
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) v hv').symm
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hcases : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine { S := fun k => if k = 0 then S₀ else S₁, map_eq := ?_, comm := ?_ }
  · intro k
    rcases hcases k with rfl | rfl
    · simp only [zero_add, if_neg h10]
      rfl
    · simp only [if_neg h10, h11]
      exact pairTwo_span_sq B hB hb
  · intro j k hjk u hu v hv
    rcases hcases j with rfl | rfl <;> rcases hcases k with rfl | rfl
    · exact (hjk rfl).elim
    · exact hc u (by simpa only [if_pos rfl, if_true] using hu)
        v (by simpa only [if_neg h10] using hv)
    · exact (hc v (by simpa only [if_pos rfl, if_true] using hv)
        u (by simpa only [if_neg h10] using hu)).symm
    · exact (hjk rfl).elim

open scoped commutatorElement in
private theorem pairTwo_cycle_derived_quasisimple
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin (Tag.rank .E6) → ℤ) →* M) (i : KernelComponent χ)
    {F : ModGL .E6 GGL →* ModGL .E6 GGL} (P : CycFamily F 2)
    (hP0 : P.S 0 = componentRootSpan GGL χ i) (σ : GGL ≃+* GGL)
    (hF : ∀ y ∈ P.S 0, iterHom F 2 y = frobGL σ y)
    {t : (CFSG.LieType.Chevalley.fixSubfield σ)ˣ} (ht : t ^ 2 ≠ 1) :
    CFSG.IsQuasisimple ↥⁅P.Afix, P.Afix⁆ ∧
      P.normImage (CQ σ i) ≤ ⁅P.Afix, P.Afix⁆ := by
  classical
  let C := CQ σ i
  have hCS : C ≤ P.S 0 := by
    rw [hP0]
    unfold C CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, -, rfl⟩
    rw [unionRoots_singleton] at hγ
    exact pinnedX_mem_rootSpan hγ c
  have hC : CFSG.IsQuasisimple C := by
    let C₀ := componentRootSpan (CFSG.LieType.Chevalley.fixSubfield σ) χ i
    let u : C₀ →* ModGL .E6 GGL :=
      (baseChangeGL (CFSG.LieType.Chevalley.fixSubfield σ).subtype).comp C₀.subtype
    have hu : Function.Injective u :=
      (baseChangeGL_injective (CFSG.LieType.Chevalley.fixSubfield σ).subtype).comp
        C₀.subtype_injective
    have hker : u.ker ≤ Subgroup.center C₀ := by
      rw [(MonoidHom.ker_eq_bot_iff u).2 hu]
      exact bot_le
    have h := isQuasisimple_range_of_ker_le_center
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.isQuasisimple_componentRootSpan_of_sq_ne_one ht i)
      u hker
    have hr : u.range = C := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, ← CQ_eq_map]
    exact hr ▸ h
  have hCfix : ∀ c : C, iterHom F 2 (c : ModGL .E6 GGL) = c := by
    intro c
    rw [hF _ (hCS c.2)]
    have hle : C ≤ (frobGL σ).eqLocus (MonoidHom.id _) := by
      unfold C CQ
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨γ, -, a, ha, rfl⟩
      change frobGL σ (pinnedX .E6 GGL γ a) = pinnedX .E6 GGL γ a
      rw [frobGL_pinnedX, ha]
    exact hle c.2
  let θ : C →* P.S 0 := C.subtype.codRestrict (P.S 0) fun c => hCS c.2
  let N : C →* ModGL .E6 GGL := P.norm.comp θ
  have hNA : ∀ c, N c ∈ P.Afix := fun c => P.norm_mem_Afix (y := θ c) (hCfix c)
  have hNker : N.ker ≤ Subgroup.center C := by
    intro c hc
    have hz : (c : ModGL .E6 GGL) ∈ P.Z :=
      P.mem_Z_of_norm_eq_one (y := θ c) hc
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (P.mem_Z.1 hz d (P.S_le_A 0 (hCS d.2)))
  have hderived_le : ⁅P.Afix, P.Afix⁆ ≤ N.range := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, b, ha, hb, heq⟩ := P.commutator_fixed hx hy
    have hsL : ∃ s : GGLˣ, s ^ 2 ≠ 1 := by
      refine ⟨Units.map (CFSG.LieType.Chevalley.fixSubfield σ).subtype.toMonoidHom t, ?_⟩
      intro he
      apply ht
      apply Units.ext
      apply Subtype.ext
      simpa using congrArg (fun v : GGLˣ => (v : GGL)) he
    have hab : ⁅(a : ModGL .E6 GGL), (b : ModGL .E6 GGL)⁆ ∈ C := by
      apply commutator_mem_CQ (σ := σ) hsL
        (Z := P.Z) (fun z hz v hv => P.mem_Z.1 hz v (P.S_le_A 0 (hP0.symm ▸ hv)))
      · change (a : ModGL .E6 GGL) ∈ rootSpan .E6 GGL (unionRoots χ {i})
        rw [unionRoots_singleton]
        exact Eq.mp (congrArg (fun H : Subgroup (ModGL .E6 GGL) =>
          (a : ModGL .E6 GGL) ∈ H) hP0) a.2
      · change (b : ModGL .E6 GGL) ∈ rootSpan .E6 GGL (unionRoots χ {i})
        rw [unionRoots_singleton]
        exact Eq.mp (congrArg (fun H : Subgroup (ModGL .E6 GGL) =>
          (b : ModGL .E6 GGL) ∈ H) hP0) b.2
      · rw [← hF _ a.2]
        exact ha.2
      · rw [← hF _ b.2]
        exact hb.2
    refine ⟨⟨_, hab⟩, ?_⟩
    exact heq.symm
  have hN_le : N.range ≤ ⁅P.Afix, P.Afix⁆ := by
    rintro _ ⟨c, rfl⟩
    exact map_mem_commutator_of_perfect hC.1 N P.Afix hNA c
  have hNqs := isQuasisimple_range_of_ker_le_center hC N hNker
  refine ⟨?_, ?_⟩
  · rwa [← le_antisymm hderived_le hN_le] at hNqs
  · intro z hz
    obtain ⟨c, hc, hcs, rfl⟩ := P.mem_normImage.1 hz
    exact hN_le ⟨⟨c, hc⟩, rfl⟩

open CFSG.LieType.AlgebraicGroups in
private theorem pairTwo_phi_sq_field (f : ℕ)
    (S : Set (Fin (langTag .twistedE6).rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot (langTag .twistedE6) α) :
    rootSpan (langTag .twistedE6) GGL S ≤
      (iterHom (ggPhi .twistedE6 f) 2).eqLocus
        (frobGL (iterateFrobeniusEquiv GGL 2 (2 * f))) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  change ggPhi .twistedE6 f (ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL α c)) =
    frobGL (iterateFrobeniusEquiv GGL 2 (2 * f)) (pinnedX (langTag .twistedE6) GGL α c)
  calc
    _ = ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL
        (CFSG.LieType.Steinberg.TwistedE6.rho α) (c ^ 2 ^ f)) :=
      congrArg (ggPhi .twistedE6 f) (ggPhi_pinnedX_twistedE6 f (hS α hα) c)
    _ = pinnedX (langTag .twistedE6) GGL
        (CFSG.LieType.Steinberg.TwistedE6.rho (CFSG.LieType.Steinberg.TwistedE6.rho α))
        ((c ^ 2 ^ f) ^ 2 ^ f) :=
      ggPhi_pinnedX_twistedE6 f (CFSG.LieType.Steinberg.TwistedE6.isRoot_rho (hS α hα)) _
    _ = pinnedX (langTag .twistedE6) GGL α ((iterateFrobeniusEquiv GGL 2 (2 * f)) c) := by
      have hc : (c ^ 2 ^ f) ^ 2 ^ f = (iterateFrobeniusEquiv GGL 2 (2 * f)) c := by
        rw [← pow_mul, ← pow_add, iterateFrobeniusEquiv_def]
        congr 2
        omega
      exact congrArg₂ (pinnedX (langTag .twistedE6) GGL)
        (CFSG.LieType.Steinberg.TwistedE6.rho_rho α) hc
    _ = _ := (frobGL_pinnedX _ α c).symm

private theorem pairTwo_cycle_structure {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    CFSG.IsQuasisimple ↥⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ ∧
      (pairTwo_cycle B hB hb).normImage
        (CQ (iterateFrobeniusEquiv GGL 2 (2 * f)) B.iJ) ≤
        ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ := by
  let σ := iterateFrobeniusEquiv GGL 2 (2 * f)
  have hσ : ∀ c, σ c = c ^ (2 ^ (2 * f)) := by
    intro c
    rw [iterateFrobeniusEquiv_apply,
      iterateFrobenius_def]
  have h4 : 4 ≤ 2 ^ (2 * f) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := B.one_le_f; omega)
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one σ hσ (by have := B.one_le_f; omega) h4
  apply pairTwo_cycle_derived_quasisimple
    (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ (pairTwo_cycle B hB hb) (by
      simp only [pairTwo_cycle]
      rfl) σ (t := t) (ht := ht)
  intro y hy
  have hy' : y ∈ rootSpan .E6 GGL B.rootsJ := by
    simpa only [pairTwo_cycle, if_pos rfl, if_true] using hy
  have heq := pairTwo_phi_sq_field f B.rootsJ (fun _ h => h.1.1) hy'
  exact Eq.mp (congrArg (fun F : ModGL .E6 GGL →* ModGL .E6 GGL =>
    iterHom F 2 y = frobGL σ y) (pairTwo_step_eq B hB hb).symm) heq

private theorem pairTwo_cycle_derived {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    CFSG.IsQuasisimple ↥⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ :=
  (pairTwo_cycle_structure B hB hb).1

private theorem pairTwo_cycle_A {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    (pairTwo_cycle B hB hb).A = rootSpan .E6 (ExcOmega f) (LieCore.ratOrbit B.ρ B.rootsJ) := by
  classical
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h₀ : (pairTwo_cycle B hB hb).S 0 = rootSpan .E6 (ExcOmega f) B.rootsJ := by
    simp only [pairTwo_cycle, if_true]
  have h₁ : (pairTwo_cycle B hB hb).S 1 =
      rootSpan .E6 (ExcOmega f) (B.ρ '' B.rootsJ) := by
    simp only [pairTwo_cycle, if_neg h10]
    exact B.frob.map_rootSpan B.rootsJ (fun _ h => h.1.1)
  apply le_antisymm
  · refine iSup_le fun k => ?_
    have hk : k = 0 ∨ k = 1 := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hk with rfl | rfl
    · rw [h₀]
      apply rootSpan_mono
      intro α hα
      exact ⟨0, α, hα, rfl⟩
    · rw [h₁]
      apply rootSpan_mono
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨1, α, hα, rfl⟩
  · refine iSup₂_le fun α hα => ?_
    rw [pairTwo_orbit_roots B hB hb] at hα
    rcases hα with hα | hα
    · have hle : rootSubgroup .E6 (ExcOmega f) α ≤ (pairTwo_cycle B hB hb).S 0 := by
        rw [h₀]
        exact le_iSup₂_of_le α hα le_rfl
      exact hle.trans ((pairTwo_cycle B hB hb).S_le_A 0)
    · have hle : rootSubgroup .E6 (ExcOmega f) α ≤ (pairTwo_cycle B hB hb).S 1 := by
        rw [h₁]
        exact le_iSup₂_of_le α hα le_rfl
      exact hle.trans ((pairTwo_cycle B hB hb).S_le_A 1)

private theorem pairTwo_mapJ_le_fixed {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    (J.subgroupOf G₀).map B.η ≤ (pairTwo_cycle B hB hb).Afix := by
  intro y hy
  refine ⟨?_, ?_⟩
  · rw [pairTwo_cycle_A B hB hb]
    exact B.map_J_le hy
  · have hr : y ∈ B.η.range := by
      obtain ⟨a, -, rfl⟩ := hy
      exact ⟨a, rfl⟩
    rw [B.range_η] at hr
    exact (Subgroup.commutator_le_self B.Δ.model hr).2

private theorem pairTwo_derived_le_joint {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ ≤
      B.Δ.Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit .E6 (B.coord x), rootDiagUnit .E6 (B.coord B.d)} :
          Set (ModGL .E6 (ExcOmega f))) := by
  let Q := ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆
  have hQspan : Q ≤ rootSpan .E6 (ExcOmega f) (LieCore.ratOrbit B.ρ B.rootsJ) := by
    rw [← pairTwo_cycle_A B hB hb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hQmodel : Q ≤ B.Δ.model := by
    intro y hy
    have hfixed := (Subgroup.commutator_le_self _ hy).2
    refine ⟨?_, hfixed⟩
    have hspan : rootSpan .E6 (ExcOmega f) (LieCore.ratOrbit B.ρ B.rootsJ) ≤
        adjointGroup .E6 (ExcOmega f) := rootSpan_le_adjointGroup (ExcOmega f) _
    exact hspan (hQspan hy)
  have hQΓ : Q ≤ B.Δ.Γ := by
    intro y hy
    exact map_mem_commutator_of_perfect (pairTwo_cycle_derived B hB hb).1 Q.subtype
      B.Δ.model (fun a => hQmodel a.2) ⟨y, hy⟩
  have hker : LieCore.ratOrbit B.ρ B.rootsJ ⊆ kernelRoots B.chiD := by
    rintro _ ⟨k, α, hα, rfl⟩
    exact B.mapsTo_rho_chiD.iterate k hα.1
  have hpair : ∀ α ∈ LieCore.ratOrbit B.ρ B.rootsJ,
      rootChar (B.coord x) α = 1 ∧ rootChar (B.coord B.d) α = 1 := by
    intro α hα
    simpa [ExcBase.chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom]
      using (hker hα).2
  have hc₁ := rootSpan_le_centralizer (B.coord x) (fun α hα =>
    ⟨(hker hα).1, (hpair α hα).1⟩)
  have hc₂ := rootSpan_le_centralizer (B.coord B.d) (fun α hα =>
    ⟨(hker hα).1, (hpair α hα).2⟩)
  intro y hy
  refine ⟨hQΓ hy, ?_⟩
  change y ∈ Subgroup.centralizer
    ({rootDiagUnit .E6 (B.coord x), rootDiagUnit .E6 (B.coord B.d)} :
      Set (ModGL .E6 (ExcOmega f)))
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Set.mem_insert_iff.1 ha with rfl | ha
  · exact Subgroup.mem_centralizer_iff.1 (hc₁ (hQspan hy)) _ (Set.mem_singleton _)
  · rw [Set.mem_singleton_iff] at ha
    subst a
    exact Subgroup.mem_centralizer_iff.1 (hc₂ (hQspan hy)) _ (Set.mem_singleton _)

private theorem pairTwo_mapJ_eq_derived {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    (J.subgroupOf G₀).map B.η =
      ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ := by
  have hperfJ : Group.IsPerfect ↥((J.subgroupOf G₀).map B.η) := ⟨B.attach_J.2.2.1⟩
  have hJJ := Subgroup.isPerfect_iff.1 hperfJ
  have hle : (J.subgroupOf G₀).map B.η ≤
      ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆ := by
    rw [← hJJ]
    exact Subgroup.commutator_mono (pairTwo_mapJ_le_fixed B hB hb) (pairTwo_mapJ_le_fixed B hB hb)
  have hJQ := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le B.attach_J hle
    (pairTwo_derived_le_joint B hB hb)
  have hqs := pairTwo_cycle_derived B hB hb
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).1 hJQ
  have htop : (((J.subgroupOf G₀).map B.η).subgroupOf
      ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆) = ⊤ := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hqs hc.2 with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hc.1.2.2
      apply hab
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      have he : a * b = b * a := Subtype.ext
        (Subgroup.mem_center_iff.1 (h a.2) b).symm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, he]
  have heq := congrArg (Subgroup.map
    ⁅(pairTwo_cycle B hB hb).Afix, (pairTwo_cycle B hB hb).Afix⁆.subtype) htop
  simpa only [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top,
    Subgroup.range_subtype] using heq

private theorem pairTwo_norm {G : Type*} [Group G] {F : G →* G}
    (P : CycFamily F 2) (y : P.S 0) : P.norm y = (y : G) * F y := by
  classical
  unfold CycFamily.norm CycFamily.mu
  rw [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_apply]
  have hp := Finset.noncommProd_toFinset ([0, 1] : List (ZMod 2))
    (fun k => (P.diag y k : G)) (by
      intro j hj k hk hjk
      exact P.comm j k hjk _ (P.diag y j).2 _ (P.diag y k).2) (by decide)
  have hset : ([0, 1] : List (ZMod 2)).toFinset = Finset.univ := by
    decide
  rw [hset] at hp
  rw [hp]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

private theorem pairTwo_rational_curve_le_mapJ {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B)
    (hb : B.b = 2) {α : Fin (Tag.rank .E6) → ℤ} (hα : α ∈ B.rootsJ) :
    (rootSubgroup .E6 (ExcOmega f) α ⊔
      (rootSubgroup .E6 (ExcOmega f) α).map B.Δ.step) ⊓
      B.Δ.step.eqLocus (MonoidHom.id _) ≤ (J.subgroupOf G₀).map B.η := by
  intro y hy
  obtain ⟨hne, hsum, hzero⟩ := pairTwo_short_data B hB B.x_mem hb hα
  have hspan := hy.1
  rw [B.frob.map_rootSubgroup α hα.1.1, pairTwo_rho_eq B hB hb hα.1.1] at hspan
  have hfix : ggPhi .twistedE6 f y = y := by
    rw [← pairTwo_step_eq B hB hb]
    exact hy.2
  obtain ⟨c, hc⟩ := ggTwDescent_short_param f B.one_le_f hα.1.1 hne hsum hzero hspan hfix
  let z := pinnedX (langTag .twistedE6) GGL α (ggRatEmb (2 * f) c)
  have hzC : z ∈ CQ (iterateFrobeniusEquiv GGL 2 (2 * f)) B.iJ := by
    let : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite (GaloisField 2 (2 * f))
    apply pinnedX_mem_CQ
    · rwa [unionRoots_singleton]
    · rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def, ← map_pow]
      congr 1
      have hf2 : 2 * f ≠ 0 := by have := B.one_le_f; omega
      simpa only [← Nat.card_eq_fintype_card,
        GaloisField.card 2 (2 * f) hf2] using FiniteField.pow_card c
  have hzS : z ∈ (pairTwo_cycle B hB hb).S 0 := by
    simp only [pairTwo_cycle, if_true]
    exact pinnedX_mem_rootSpan hα _
  have hnorm : (pairTwo_cycle B hB hb).norm ⟨z, hzS⟩ = y := by
    rw [pairTwo_norm]
    change (@id (ModGL .E6 (ExcOmega f)) z) * B.Δ.step z = y
    rw [pairTwo_step_eq B hB hb]
    change @Eq (ModGL (langTag .twistedE6) GGL)
      (pinnedX (langTag .twistedE6) GGL α (ggRatEmb (2 * f) c) *
        ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL α (ggRatEmb (2 * f) c))) y
    rw [ggPhi_pinnedX_twistedE6 f hα.1.1 _]
    rw [CFSG.LieType.Steinberg.Exceptional.frobQ_apply, map_pow] at hc
    exact hc
  rw [pairTwo_mapJ_eq_derived B hB hb]
  apply (pairTwo_cycle_structure B hB hb).2
  exact (pairTwo_cycle B hB hb).mem_normImage.2 ⟨⟨z, hzS⟩, hzC, hnorm⟩

private theorem pairTwo_aut_conj {C : Type*} [Group C] (a : MulAut C) (c : C) :
    a⁻¹ * MulAut.conj c * a = MulAut.conj (a⁻¹ c) := by
  ext y
  change a⁻¹ (c * a y * c⁻¹) = a⁻¹ c * y * (a⁻¹ c)⁻¹
  rw [map_mul, map_mul, map_inv, MulAut.inv_apply_self]

private theorem pairTwo_innerDiag_root_transport
    {U C : Type*} [Group U] [Group C] (Δ : UniversalRootDatum U) (q : U →* C)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (κ : MulAut C)
    (hκ : GGPsiInnerDiag Δ ((MulAut.conj : C →* MulAut C).comp q) κ) :
    ∃ u : U, ∀ γ ∈ Δ.roots,
      (Δ.rootGroup γ).map ((κ⁻¹).toMonoidHom.comp q) =
        ((Δ.rootGroup γ).map (MulAut.conj u).toMonoidHom).map q := by
  obtain ⟨g, ⟨u, rfl⟩, hg⟩ := hκ
  refine ⟨u, ?_⟩
  intro γ hγ
  obtain ⟨h, hh, he⟩ := hg γ hγ
  have hhN : h ∈ Subgroup.normalizer (Δ.rootGroup γ : Set U) :=
    (show ggTorus Δ ≤ Subgroup.normalizer (Δ.rootGroup γ : Set U) from iInf₂_le γ hγ) hh
  have hhiN : h⁻¹ ∈ Subgroup.normalizer (Δ.rootGroup γ : Set U) :=
    Subgroup.inv_mem _ hhN
  have heq : ∀ z ∈ Δ.rootGroup γ,
      κ⁻¹ (q z) = q (u * (h * z * h⁻¹) * u⁻¹) := by
    intro z hz
    have e := he z hz
    change (κ * MulAut.conj (q u))⁻¹ * MulAut.conj (q z) *
      (κ * MulAut.conj (q u)) = MulAut.conj (q (h * z * h⁻¹)) at e
    rw [pairTwo_aut_conj] at e
    have e' := hinj e
    change (q u)⁻¹ * κ⁻¹ (q z) * q u = q (h * z * h⁻¹) at e'
    rw [map_mul, map_mul, map_inv]
    calc
      κ⁻¹ (q z) = q u * ((q u)⁻¹ * κ⁻¹ (q z) * q u) * (q u)⁻¹ := by group
      _ = _ := by rw [e']
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨u * (h * z * h⁻¹) * u⁻¹, ?_, ?_⟩
    · refine ⟨h * z * h⁻¹, ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hhN z).1 hz
    · exact (heq z hz).symm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : h⁻¹ * z * h ∈ Δ.rootGroup γ := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.1 hhiN z).1 hz
    refine ⟨h⁻¹ * z * h, hz', ?_⟩
    change κ⁻¹ (q (h⁻¹ * z * h)) = q (u * z * u⁻¹)
    rw [heq _ hz']
    congr 1
    group

private theorem pairTwo_conj_injective (n f : ℕ) (hf : 1 ≤ f) :
    Function.Injective (MulAut.conj : GGKb .twistedE6 n f →* MulAut (GGKb .twistedE6 n f)) := by
  have hcenter : Subgroup.center (GGKb .twistedE6 n f) = ⊥ := by
    have hc := center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
      (K := GaloisField 2 (2 * f))
      (σ := CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)
      (Finite.surjective_of_injective
        (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f).injective)
    have he := Subgroup.map_center_eq (ggKbEquivTwE6 n f hf)
    rw [hc] at he
    apply le_antisymm _ bot_le
    intro z hz
    have hz' : (ggKbEquivTwE6 n f hf) z ∈ (⊥ : Subgroup _) := by
      rw [← he]
      exact Subgroup.mem_map_of_mem _ hz
    rw [Subgroup.mem_bot] at hz' ⊢
    exact (ggKbEquivTwE6 n f hf).injective (hz'.trans (map_one _).symm)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : z ∈ Subgroup.center (GGKb .twistedE6 n f) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have he := congrArg (fun a : MulAut (GGKb .twistedE6 n f) => a y) hz
    change z * y * z⁻¹ = y at he
    calc
      y * z = (z * y * z⁻¹) * z := by rw [he]
      _ = z * y := by group
  simpa only [hcenter, Subgroup.mem_bot] using hzc

private theorem pairTwo_map_in_subgroup {U X M : Type*} [Group U] [Group X] [Group M]
    (ψ : U →* X) (H : Subgroup X) (hψ : ψ.range = H) (η : H →* M) (S : Subgroup U) :
    ((S.map ψ).subgroupOf H).map η =
      S.map (η.comp (ψ.codRestrict H (fun k => hψ ▸ (⟨k, rfl⟩ : ψ k ∈ ψ.range)))) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, he⟩ := ha
    refine ⟨k, hk, ?_⟩
    exact congrArg η (Subtype.ext he)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨ψ k, hψ ▸ (⟨k, rfl⟩ : ψ k ∈ ψ.range)⟩, ⟨k, hk, rfl⟩, rfl⟩

private theorem pairTwo_transport_roots {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2) :
    ∃ u : (ggU .twistedE6 n f).K, ∀ γ ∈ (ggU .twistedE6 n f).D.roots,
      ((ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀).map B.η =
        ((ggU .twistedE6 n f).D.rootGroup γ).map (ggIotaK .twistedE6 n f B.one_le_f) := by
  let ι := ggIota .twistedE6 n f B.one_le_f
  have hi : Function.Injective ι := (pairTwo_lang_pkg B hB).inj
  let q : (ggU .twistedE6 n f).K →* GGKb .twistedE6 n f := QuotientGroup.mk' _
  let m : Subgroup.normalizer (ι.range : Set (ModGL (langTag .twistedE6) GGL)) :=
    ⟨(@id (ModGL (langTag .twistedE6) GGL) B.Δ.g0)⁻¹,
      Subgroup.inv_mem _ (pairTwo_g0_normalizer B hB hb)⟩
  let κ := @CFSG.StandardType.GGFinModel.ggConjAut (GGKb .twistedE6 n f)
    (ModGL (langTag .twistedE6) GGL) _ _ ι hi m
  have hκ : GGInnDiagU .twistedE6 n f κ :=
    ggFixGp_conj_innDiagU_twE6 B.one_le_f hi m
      (Subgroup.inv_mem _ (pairTwo_g0_fixed B hB hb)) m.2
  obtain ⟨u, hu⟩ := pairTwo_innerDiag_root_transport (ggU .twistedE6 n f).D q
    (pairTwo_conj_injective n f B.one_le_f) κ hκ
  let ψG := ψ.codRestrict G₀ (fun k => hψ ▸ (⟨k, rfl⟩ : ψ k ∈ ψ.range))
  have hηψ : B.η.comp ψG = (@id (GGKb .twistedE6 n f →* ModGL .E6 GGL)
      (ι.comp κ.toMonoidHom)).comp q := by
    apply MonoidHom.ext
    intro k
    have he := hB.η_psi k (ψG k).2
    change B.η (ψG k) = (m : ModGL (langTag .twistedE6) GGL) * ι (q k) *
      (m : ModGL (langTag .twistedE6) GGL)⁻¹ at he
    change B.η (ψG k) = ι (κ (q k))
    exact he.trans (CFSG.StandardType.GGFinModel.ggConjAut_apply ι hi m (q k)).symm
  refine ⟨u, ?_⟩
  intro γ hγ
  unfold ggRootSub
  rw [pairTwo_map_in_subgroup ψ G₀ hψ B.η, hηψ]
  calc
    (((ggU .twistedE6 n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        ((@id (GGKb .twistedE6 n f →* ModGL .E6 GGL) (ι.comp κ.toMonoidHom)).comp q) =
        ((((ggU .twistedE6 n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map q).map
          (@id (GGKb .twistedE6 n f →* ModGL .E6 GGL) (ι.comp κ.toMonoidHom)) := by
      simp only [Subgroup.map_map]
      rfl
    _ = (((ggU .twistedE6 n f).D.rootGroup γ).map ((κ⁻¹).toMonoidHom.comp q)).map
          (@id (GGKb .twistedE6 n f →* ModGL .E6 GGL) (ι.comp κ.toMonoidHom)) := by
      rw [hu γ hγ]
    _ = _ := by
      rw [Subgroup.map_map]
      apply congrArg (fun a : (ggU .twistedE6 n f).K →* ModGL .E6 GGL =>
        ((ggU .twistedE6 n f).D.rootGroup γ).map a)
      apply MonoidHom.ext
      intro k
      change ι (κ (κ⁻¹ (q k))) = ι (q k)
      rw [MulAut.apply_inv_self]

private theorem pairTwo_curve_one {f : ℕ} (α : Fin (Tag.rank .E6) → ℤ) :
    excCurve α (1 : ModGL .E6 (ExcOmega f)) = rootSubgroup .E6 (ExcOmega f) α := by
  simp only [excCurve, map_one]
  change (rootSubgroup .E6 (ExcOmega f) α).map (MonoidHom.id _) = _
  exact Subgroup.map_id _

private theorem pairTwo_root_image_curve {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) (hB : TwE6BaseCompat n f p ψ B) (hb : B.b = 2)
    (u : (ggU .twistedE6 n f).K)
    (hu : ∀ γ ∈ (ggU .twistedE6 n f).D.roots,
      ((ggRootSub (ggU .twistedE6 n f).D ψ γ u).subgroupOf G₀).map B.η =
        ((ggU .twistedE6 n f).D.rootGroup γ).map (ggIotaK .twistedE6 n f B.one_le_f))
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    ((ggRootSub (ggU .twistedE6 n f).D ψ (CFSG.LieType.Steinberg.TwistedE6.proj α) u).subgroupOf G₀).map B.η =
      (rootSubgroup .E6 (ExcOmega f) α ⊔
        (rootSubgroup .E6 (ExcOmega f) α).map B.Δ.step) ⊓
        B.Δ.step.eqLocus (MonoidHom.id _) := by
  have hβ : CFSG.LieType.Steinberg.TwistedE6.proj α ∈ (ggU .twistedE6 n f).D.roots :=
    isRoot_iff_mem_roots.mp (CFSG.LieType.Steinberg.TwistedE6.isRoot_proj hα)
  rw [hu _ hβ, pairTwo_native_image n f B.one_le_f hα,
    B.frob.map_rootSubgroup α hα, pairTwo_rho_eq B hB hb hα, pairTwo_step_eq B hB hb]
  rfl

private theorem pairTwo_odd_kernel {X M : Type*} [Group X] [Finite X] [Group M]
    (H : Subgroup X) (η : H →* M) (hker : η.ker ≤ Subgroup.center H)
    (hodd : Odd (Nat.card (Subgroup.centralizer (H : Set X)))) : Odd (Nat.card η.ker) := by
  have hle : (Subgroup.center H).map H.subtype ≤ Subgroup.centralizer (H : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    apply Subgroup.mem_centralizer_iff.2
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)
  have hd : Nat.card (Subgroup.center H) ∣ Nat.card (Subgroup.centralizer (H : Set X)) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  exact (hodd.of_dvd_nat hd).of_dvd_nat (Subgroup.card_dvd_of_le hker)

private theorem pairTwo_root_isPGroup {X : Type} [Group X] {n f : ℕ}
    (ψ : (ggU .twistedE6 n f).K →* X) {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hβ : β ∈ (ggU .twistedE6 n f).D.roots) (u : (ggU .twistedE6 n f).K) :
    IsPGroup 2 (ggRootSub (ggU .twistedE6 n f).D ψ β u) := by
  have h2 : IsPGroup 2 ((ggU .twistedE6 n f).D.rootGroup β) :=
    CFSG.StandardType.LieKnownR2.Short.isPGroup_two_twistedRootGroup
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hβ
  exact (h2.map (MulAut.conj u).toMonoidHom).map ψ

private theorem pairTwo_le_J {X : Type} [Group X] [Finite X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x)
    (hodd : Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))))
    {R : Subgroup X} (hRG : R ≤ G₀) (hR2 : IsPGroup 2 R)
    (himage : (R.subgroupOf G₀).map B.η ≤ (J.subgroupOf G₀).map B.η) : R ≤ J := by
  have hs2 : IsPGroup 2 (R.subgroupOf G₀) :=
    hR2.comap_of_injective G₀.subtype G₀.subtype_injective
  have hle := CFSG.GroupTheory.le_of_map_le_map_of_odd B.ker_η
    (pairTwo_odd_kernel G₀ B.η B.ker_η hodd) hs2 himage
  intro y hy
  exact hle (show (⟨y, hRG hy⟩ : G₀) ∈ R.subgroupOf G₀ from hy)

theorem twE6PairTwo_holds : TwE6PairTwo := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hP B hB hb
  obtain ⟨_, _, _, _, hcard, _, _⟩ := pairTwo_A2_data hP B hb
  have hnon : B.rootsJ ≠ ∅ := by
    intro he
    rw [he, Set.ncard_empty] at hcard
    omega
  obtain ⟨α, hα⟩ := Set.nonempty_iff_ne_empty.2 hnon
  have hαm : -α ∈ B.rootsJ := (isRootComponent_componentRoots B.iJ).neg_mem α hα
  let β := CFSG.LieType.Steinberg.TwistedE6.proj α
  have hβ : β ∈ (ggU .twistedE6 n f).D.roots :=
    isRoot_iff_mem_roots.mp (CFSG.LieType.Steinberg.TwistedE6.isRoot_proj hα.1.1)
  have hβm : -β ∈ (ggU .twistedE6 n f).D.roots :=
    isRoot_iff_mem_roots.mp (IsRoot.neg (CFSG.LieType.Steinberg.TwistedE6.isRoot_proj hα.1.1))
  obtain ⟨u, hu⟩ := pairTwo_transport_roots hP.1 B hB hb
  let R := ggRootSub (ggU .twistedE6 n f).D ψ β u
  let Rm := ggRootSub (ggU .twistedE6 n f).D ψ (-β) u
  have hR : (R.subgroupOf G₀).map B.η =
      (rootSubgroup .E6 (ExcOmega f) α ⊔
        (rootSubgroup .E6 (ExcOmega f) α).map B.Δ.step) ⊓
        B.Δ.step.eqLocus (MonoidHom.id _) :=
    pairTwo_root_image_curve B hB hb u hu hα.1.1
  have hRm : (Rm.subgroupOf G₀).map B.η =
      (rootSubgroup .E6 (ExcOmega f) (-α) ⊔
        (rootSubgroup .E6 (ExcOmega f) (-α)).map B.Δ.step) ⊓
        B.Δ.step.eqLocus (MonoidHom.id _) := by
    have he := pairTwo_root_image_curve B hB hb u hu (IsRoot.neg hα.1.1)
    rw [map_neg] at he
    exact he
  have hRG : R ≤ G₀ := (Subgroup.map_le_range ψ _).trans hP.1.le
  have hRmG : Rm ≤ G₀ := (Subgroup.map_le_range ψ _).trans hP.1.le
  have hRJ : R ≤ J := pairTwo_le_J B hP.2.2.2.1 hRG
    (pairTwo_root_isPGroup ψ hβ u) (by
      rw [hR]
      exact pairTwo_rational_curve_le_mapJ B hB hb hα)
  have hRmJ : Rm ≤ J := pairTwo_le_J B hP.2.2.2.1 hRmG
    (pairTwo_root_isPGroup ψ hβm u) (by
      rw [hRm]
      exact pairTwo_rational_curve_le_mapJ B hB hb hαm)
  refine ⟨R, Rm, hRJ, hRmJ, ?_, ?_⟩
  · refine ⟨β, hβ, Or.inr ⟨Or.inr (Or.inr ⟨Or.inr rfl, (pairTwo_orbit_data B hb).2.2⟩), ?_⟩,
      u, rfl, rfl⟩
    intro h2β
    exact CFSG.LieType.Steinberg.Minuscule.not_isRoot_two_smul β (isRoot_iff_mem_roots.mpr h2β)
  · refine ⟨{
      α := α
      α_mem := hα
      wD := 1
      wD_mem := Subgroup.one_mem _
      pair_one := ?_
      pair_two := ?_ }⟩
    · intro hb1
      change B.b = 1 at hb1
      omega
    · intro _
      refine ⟨pairTwo_curve_sq B hB hb hα.1.1, ?_, ?_⟩
      · rw [pairTwo_curve_one, hR]
        exact inf_le_left
      · rw [hR]
        exact pairTwo_rational_curve_card B hB hb hα

end CFSG.StandardType.LieKnownR2.ExcPos
