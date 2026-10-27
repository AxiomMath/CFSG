module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLSpace
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeBlockTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPSL
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAPinHom

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open scoped Matrix

private lemma rckRPsb_exists_finrank {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [AddCommGroup W] [Module F W] [Module K W] [FiniteDimensional K W]
    {e : Matrix ι ι F} (he0 : e ≠ 0)
    (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e)) :
    ∃ k, Module.finrank K W = k + 1 := by
  have hrange_ne : LinearMap.range (Matrix.toLin' e) ≠ ⊥ := by
    intro h
    have hzero : Matrix.toLin' e = 0 := LinearMap.range_eq_bot.mp h
    exact he0 (Matrix.toLin'.injective (by simpa using hzero))
  have hWne : ∃ w : W, w ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.range (Matrix.toLin' e)) hrange_ne
    refine ⟨eW.symm ⟨v, hv⟩, ?_⟩
    intro h0
    apply hv0
    have h1 : eW (eW.symm ⟨v, hv⟩) = ⟨v, hv⟩ := eW.apply_symm_apply ⟨v, hv⟩
    rw [h0, map_zero] at h1
    exact (congrArg Subtype.val h1).symm
  have hfpos : 0 < Module.finrank K W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr hWne
  exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfpos)

theorem rckRP_exists_kappa_of_map_commutator_eq {A H L : Type} [Group A] [Group H] [Group L]
    {G : Subgroup A} (φ : G →* H) (hφ : Function.Injective φ) (ρ : L →* H)
    (hρ : Function.Injective ρ) (hφc : (commutator G).map φ = ρ.range) :
    ∃ κ : L →* G, Function.Injective κ ∧
      (G.subtype.comp κ).range = ⁅G, G⁆ ∧ ∀ y, φ (κ y) = ρ y := by
  let θ : G ≃* φ.range := MonoidHom.ofInjective hφ
  have hθ_apply (a : G) : ((θ a : φ.range) : H) = φ a :=
    MonoidHom.ofInjective_apply hφ
  have hθ_symm_apply (z : φ.range) : φ (θ.symm z) = (z : H) :=
    MonoidHom.apply_ofInjective_symm hφ z
  let κ₀ : L →* φ.range :=
    ρ.codRestrict φ.range fun y => by
      have hy : ρ y ∈ (commutator G).map φ := by
        rw [hφc]
        exact ⟨y, rfl⟩
      exact Subgroup.map_le_range φ (commutator G) hy
  let κ : L →* G := θ.symm.toMonoidHom.comp κ₀
  have hκ₀_apply (y : L) : ((κ₀ y : φ.range) : H) = ρ y := rfl
  have hκφ (y : L) : φ (κ y) = ρ y := by
    change φ (θ.symm (κ₀ y)) = ρ y
    rw [hθ_symm_apply, hκ₀_apply]
  have hκinj : Function.Injective κ := by
    have hκ₀inj : Function.Injective κ₀ := by
      intro a b hab
      apply hρ
      exact congrArg (fun z : φ.range => (z : H)) hab
    exact θ.symm.injective.comp hκ₀inj
  have hmapcomm : (commutator G).map G.subtype = ⁅G, G⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hle : κ.range ≤ commutator G := by
    rintro x ⟨y, rfl⟩
    have hy : φ (κ y) ∈ (commutator G).map φ := by
      rw [hφc, hκφ y]
      exact ⟨y, rfl⟩
    exact (Subgroup.mem_map_iff_mem hφ).mp hy
  have hge : commutator G ≤ κ.range := by
    rintro a ha
    have hφa : φ a ∈ ρ.range := by
      rw [← hφc]
      exact Subgroup.mem_map_of_mem φ ha
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hφa
    refine ⟨y, ?_⟩
    change θ.symm (κ₀ y) = a
    have hθeq : θ a = κ₀ y := by
      apply Subtype.ext
      rw [hθ_apply a, hκ₀_apply y]
      exact hy.symm
    rw [← hθeq, MulEquiv.symm_apply_apply]
  refine ⟨κ, hκinj, ?_, hκφ⟩
  rw [MonoidHom.range_comp, le_antisymm hle hge, hmapcomm]

private lemma rckRPsb_glGeoFlag_of_block
    {ι F K W G H₀ : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W] [Group G] [Group H₀]
    {j : G →* GL ι F} {B : Option ((ι → F) → (ι → F) → F)}
    {S : Set (GL ι F)} {e ε : Matrix ι ι F}
    (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    {φ : ↥(glBlockCentralizer j S ε) →* (W ≃ₗ[K] W)}
    (κG : H₀ →* ↥(glBlockCentralizer j S ε))
    (hact : ∀ g w, (eW (φ g w) : ι → F) = (j g : Matrix ι ι F) *ᵥ (eW w : ι → F))
    (hcomm : ∀ g : ↥(glBlockCentralizer j S ε),
      (j g : Matrix ι ι F) * e = e * (j g : Matrix ι ι F))
    (hflag : ∀ R : Subgroup (GL ι F), (∀ x ∈ R, x ∈ j.range) →
      (∀ x ∈ R, (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) →
      (∀ x ∈ R, (x : Matrix ι ι F) * (1 - ε) = 1 - ε) → (∀ x ∈ R, x * x = 1) →
      ∀ U₁ U₂ : Submodule F (ι → F), U₁ ≤ U₂ →
      (∀ x ∈ R, x ≠ 1 →
        LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁ ∧
        LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
          LinearMap.range (Matrix.toLin' e) = U₂) →
      GLGeoFlag B R)
    {Y : Subgroup H₀} (hinv : ∀ y ∈ Y, y * y = 1)
    {U₁' U₂' : Submodule K W} (hU' : U₁' ≤ U₂')
    (hfl : ∀ y ∈ Y, y ≠ 1 →
      LinearMap.range ((φ (κG y) : W →ₗ[K] W) - LinearMap.id) = U₁' ∧
      LinearMap.ker ((φ (κG y) : W →ₗ[K] W) - LinearMap.id) = U₂') :
    GLGeoFlag B ((Y.map ((glBlockCentralizer j S ε).subtype.comp κG)).map j) := by
  have hR : ∀ x ∈ (Y.map ((glBlockCentralizer j S ε).subtype.comp κG)).map j,
      ∃ y ∈ Y, x = j (κG y : G) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨y, hy, rfl⟩
  let Φ : W →ₗ[F] (ι → F) := (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap
  refine hflag _ ?_ ?_ ?_ ?_ ((U₁'.restrictScalars F).map Φ) ((U₂'.restrictScalars F).map Φ)
    (Submodule.map_mono hU') ?_
  · intro x hx
    obtain ⟨y, -, rfl⟩ := hR x hx
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := hR x hx
    exact hcomm (κG y)
  · intro x hx
    obtain ⟨y, -, rfl⟩ := hR x hx
    have hmem : j (κG y : G) ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (κG y).2
    exact (Subgroup.mem_inf.mp hmem).2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hR x hx
    have h := congrArg (fun z : H₀ => j (κG z : G)) (hinv y hy)
    simpa using h
  · intro x hx hx1
    obtain ⟨y, hy, rfl⟩ := hR x hx
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hx1 (by simp)
    have hCK := range_ker_block_of_action (eW := eW) (T := (φ (κG y) : W →ₗ[K] W))
      (fun w => (hact (κG y) w).symm)
    rw [hCK.1, hCK.2, (hfl y hy hy1).1, (hfl y hy hy1).2]
    exact ⟨rfl, rfl⟩

theorem rckRP_slModel_of_slBlock
    {G : Type} [Group G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : G, ∀ b ∈ B, ∀ m m' : ι → F,
      b ((j y : Matrix ι ι F).mulVec m) ((j y : Matrix ι ι F).mulVec m') = b m m')
    {S : Set (GL ι F)} {e ε : Matrix ι ι F} (he0 : e ≠ 0) {J' : Subgroup G}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer j S ε, glBlockCentralizer j S ε⁆)
    {K W : Type} [Field K] [Finite K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W] [FiniteDimensional K W] {q : ℕ} (hK : Nat.card K = 2 ^ q)
    (hq : 2 ≤ q) (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    (φ : ↥(glBlockCentralizer j S ε) →* (W ≃ₗ[K] W)) (hφ : Function.Injective φ)
    (hφc : (commutator ↥(glBlockCentralizer j S ε)).map φ = commutator (W ≃ₗ[K] W))
    (hact : ∀ g w, (eW (φ g w) : ι → F) = (j g : Matrix ι ι F) *ᵥ (eW w : ι → F))
    (hcomm : ∀ g : ↥(glBlockCentralizer j S ε),
      (j g : Matrix ι ι F) * e = e * (j g : Matrix ι ι F))
    (hflag : ∀ R : Subgroup (GL ι F), (∀ x ∈ R, x ∈ j.range) →
      (∀ x ∈ R, (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) →
      (∀ x ∈ R, (x : Matrix ι ι F) * (1 - ε) = 1 - ε) → (∀ x ∈ R, x * x = 1) →
      ∀ U₁ U₂ : Submodule F (ι → F), U₁ ≤ U₂ →
      (∀ x ∈ R, x ≠ 1 →
        LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁ ∧
        LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
          LinearMap.range (Matrix.toLin' e) = U₂) →
      GLGeoFlag B R) :
    ∃ (k : ℕ) (κ : (ggU .PSL (k + 1) q).K →* G), 1 ≤ k ∧ RCKNormalizedModel .PSL (k + 1) q ∧
      κ.range = J' ∧
      (∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU .PSL (k + 1) q).K) ∧
      RCKRPRootFlags j B κ := by
  let Gε := glBlockCentralizer j S ε
  obtain ⟨k, hW⟩ := rckRPsb_exists_finrank (F := F) (K := K) (W := W) he0 eW
  obtain ⟨ρ, hρinj, hρrange, hρflag⟩ :=
    exists_slModel_linearEquiv (K := K) (W := W) (q := q) (k := k) hK hq hW
  obtain ⟨κG, hκGinj, hκrange, hκφ⟩ :=
    rckRP_exists_kappa_of_map_commutator_eq (G := Gε) φ hφ ρ hρinj (hφc.trans hρrange.symm)
  let κ : (ggU .PSL (k + 1) q).K →* G := Gε.subtype.comp κG
  have hκinj : Function.Injective κ := Gε.subtype_injective.comp hκGinj
  have hκrange' : κ.range = ⁅Gε, Gε⁆ := hκrange
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Subsingleton (ggU .PSL (0 + 1) q).K := by
      show Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 q))
      infer_instance
    have : Subsingleton ↥κ.range := (MonoidHom.rangeRestrict_surjective κ).subsingleton
    have hJle : J' ≤ κ.range := by
      rw [hκrange']
      exact hJe.1
    obtain ⟨a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp
        hJe.2.2)
    have hsub : (⟨a.1, hJle a.2⟩ : ↥κ.range) = ⟨b.1, hJle b.2⟩ :=
      Subsingleton.elim _ _
    exact hab (Subtype.ext (congrArg (fun z : ↥κ.range => (z : G)) hsub))
  have hSLq : CFSG.IsQuasisimple (ggU .PSL (k + 1) q).K := by
    have hm : 2 ≤ k + 1 := by omega
    have h4 : 4 ≤ Nat.card (GaloisField 2 q) := by
      rw [GaloisField.card 2 q (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    exact CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le
      (K := GaloisField 2 q) hm (Or.inr h4)
  have hMq : CFSG.IsQuasisimple ↥⁅Gε, Gε⁆ := by
    rw [← hκrange']
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hκinj) hSLq
  have hJeq : J' = ⁅Gε, Gε⁆ :=
    CFSG.StandardType.Line63.H5.eq_of_isComponentOf_of_isQuasisimple hJe
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hMq)
  have hrange : κ.range = J' := hκrange'.trans hJeq.symm
  have hnorm : RCKNormalizedModel .PSL (k + 1) q :=
    ⟨by simp [GGPosTag], rckRP_admissible_PSL_of_quasisimple_range (k := k) (f := q)
      (by omega : 1 ≤ q) κ (by rw [hrange]; exact hJe.2.2)⟩
  refine ⟨k, κ, Nat.one_le_iff_ne_zero.mpr hk0, hnorm, hrange, fun _ hy =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.pinned_center_of_inj κ hκinj hy, ?_⟩
  refine rckRP_rootFlags_of_forall_rootGroup j hiso κ ?_
  intro β hβ
  obtain ⟨hinvβ, U₁', U₂', hU', hflβ⟩ := hρflag β hβ
  exact rckRPsb_glGeoFlag_of_block eW κG hact hcomm hflag hinvβ hU'
    fun y hy hy1 => by rw [hκφ y]; exact hflβ y hy hy1

theorem rckRP_flaggedModel_of_slBlock
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {X : Subgroup (GL ι F)}
    {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : ↥X, ∀ b ∈ B, ∀ m m' : ι → F,
      b (((y : GL ι F) : Matrix ι ι F).mulVec m) (((y : GL ι F) : Matrix ι ι F).mulVec m') =
        b m m')
    {S : Set (GL ι F)} {e ε : Matrix ι ι F} (he0 : e ≠ 0) {J' : Subgroup ↥X}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer X.subtype S ε, glBlockCentralizer X.subtype S ε⁆)
    {K W : Type} [Field K] [Finite K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W] [FiniteDimensional K W] {q : ℕ} (hK : Nat.card K = 2 ^ q)
    (hq : 2 ≤ q) (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    (φ : ↥(glBlockCentralizer X.subtype S ε) →* (W ≃ₗ[K] W)) (hφ : Function.Injective φ)
    (hφc : (commutator ↥(glBlockCentralizer X.subtype S ε)).map φ = commutator (W ≃ₗ[K] W))
    (hact : ∀ g w, (eW (φ g w) : ι → F) =
      (((g : ↥X) : GL ι F) : Matrix ι ι F) *ᵥ (eW w : ι → F))
    (hcomm : ∀ g : ↥(glBlockCentralizer X.subtype S ε),
      (((g : ↥X) : GL ι F) : Matrix ι ι F) * e = e * (((g : ↥X) : GL ι F) : Matrix ι ι F))
    (hflag : ∀ R : Subgroup (GL ι F), (∀ x ∈ R, x ∈ X) →
      (∀ x ∈ R, (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) →
      (∀ x ∈ R, (x : Matrix ι ι F) * (1 - ε) = 1 - ε) → (∀ x ∈ R, x * x = 1) →
      ∀ U₁ U₂ : Submodule F (ι → F), U₁ ≤ U₂ →
      (∀ x ∈ R, x ≠ 1 →
        LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁ ∧
        LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
          LinearMap.range (Matrix.toLin' e) = U₂) →
      GLGeoFlag B R) :
    RCKRPFlaggedModel X.subtype B J' := by
  obtain ⟨k, κ, -, hnorm, hrange, hcent, hflags⟩ :=
    rckRP_slModel_of_slBlock X.subtype hiso he0 hJe hK hq eW φ hφ hφc hact hcomm
      fun R hR => hflag R fun x hx => by simpa using hR x hx
  exact ⟨.PSL, k + 1, q, κ, hnorm, hrange, hcent, hflags⟩

end CFSG.StandardType.RCKRP
