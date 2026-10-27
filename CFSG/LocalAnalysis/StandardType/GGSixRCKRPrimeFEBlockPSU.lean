module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal

private lemma rckRPfeu_commutator_self_of_isPerfect {G : Type} [Group G] {H : Subgroup G}
    (hperf : Group.IsPerfect ↥H) : ⁅H, H⁆ = H := by
  have hmap : (commutator ↥H).map H.subtype = H := by
    rw [Group.isPerfect_def.mp hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hmap2 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    show (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H).map H.subtype = ⁅H, H⁆
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap2]
  exact hmap

private lemma rckRPfeu_derived_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (d : ℕ) (hdeg : 2 ≤ d)
    (K : Type) [Field K] [Finite K] [Algebra F K] (hKfr : Module.finrank F K = d)
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) F) * e = 0) :
    ⁅(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype,
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype⁆ =
      ⁅fePSU_dualPair_unitBlockCentralizer (f := f) S ε,
        fePSU_dualPair_unitBlockCentralizer (f := f) S ε⁆ := by
  by_cases hnt : ⁅glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε,
      glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε⁆ = ⊥
  · have hGG : ⁅(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype,
        (glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hnt, Subgroup.map_bot]
    have hUU : ⁅fePSU_dualPair_unitBlockCentralizer (f := f) S ε,
        fePSU_dualPair_unitBlockCentralizer (f := f) S ε⁆ = ⊥ := by
      by_contra hntU
      obtain ⟨_, _, _, hperf⟩ :=
        fePSU_dualPair_unitBlockCentralizer_derived_iso hc S hS hSU hε he heε hpair hεeq
          d hdeg K hKfr π hπsurj hπker hntU
      have hle := Subgroup.commutator_mono
        (fePSU_dualPair_unitBlockCentralizer_commutator_le_Geps (f := f) (ε := ε) S)
        (fePSU_dualPair_unitBlockCentralizer_commutator_le_Geps (f := f) (ε := ε) S)
      rw [rckRPfeu_commutator_self_of_isPerfect hperf, hGG] at hle
      exact hntU (le_bot_iff.mp hle)
    rw [hGG, hUU]
  · exact fePSU_dualPair_Geps_derived_eq hc S hS hSU hε he heε hpair hεeq d hdeg K hKfr π hπsurj
      hπker hnt

private lemma rckRPfeu_toHomUnits_injective {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (S : Set (GL (Fin n) F)) {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e)
    (K : Type) [Field K] [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin n → F) =
        Matrix.mulVec ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) w) :
    Function.Injective actK.toHomUnits := by
  intro u v huv
  have h1 : actK (u * v⁻¹) = 1 := by
    have h : actK.toHomUnits (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    exact congrArg Units.val h
  have h2 : (((u * v⁻¹ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
      GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e = e := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    show Matrix.mulVec ((((u * v⁻¹ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)) :
      GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e) x = Matrix.mulVec e x
    rw [← Matrix.mulVec_mulVec]
    have h := congrArg (fun T : Module.End K (LinearMap.range (Matrix.mulVecLin e)) =>
      T ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩) h1
    have h' := congrArg Subtype.val h
    rw [hact (u * v⁻¹) ⟨Matrix.mulVec e x, ⟨x, rfl⟩⟩] at h'
    simpa using h'
  exact mul_inv_eq_one.mp
    (fePSU_dualPair_unitBlockCentralizer_faithful S hε he hεeq (u * v⁻¹) h2)

private lemma rckRPfeu_blockAction {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    (hεeq : ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : Module K W)
      (_ : IsScalarTower F K W) (_ : FiniteDimensional K W)
      (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
      (φ : ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) →*
        (W ≃ₗ[K] W)),
      Nat.card K = 2 ^ (2 * f * blockDegree (Algebra.adjoin F (Units.val '' S)) e) ∧
      Function.Injective φ ∧
      (commutator ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).map φ =
        commutator (W ≃ₗ[K] W) ∧
      (∀ g w, (eW (φ g w) : Fin n → F) =
        Matrix.mulVec
          (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
            GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (eW w : Fin n → F)) ∧
      ∀ g : ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε),
        (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e =
        e * (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  classical
  obtain ⟨K, hKf, hKa, hKfin, π, hπsurj, hπker, hKfr, hcard⟩ :=
    fePSU_blockField_card hc S hS hodd he _ rfl
  letI : Field K := hKf
  letI : Algebra F K := hKa
  haveI : Finite K := hKfin
  obtain ⟨hmod, htower, actK, hact, hcomp⟩ :=
    fePSU_dualPair_unitBlockCentralizer_KAction_body (f := f) (ε := ε) S hS he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hmod
  haveI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) := htower
  haveI hWfd : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite F K _
  have hreal := fePSU_dualPair_unitBlockCentralizer_extension_realizes hc S hS hSU hε he heε
    hpair hεeq K π actK hact hcomp
  have hinj := rckRPfeu_toHomUnits_injective S hε he hεeq K actK hact
  let ι : ↥(glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε) →*
      ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) :=
    ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype.comp
      (glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
          ε).subtype).codRestrict
      (fePSU_dualPair_unitBlockCentralizer (f := f) S ε)
      (fun g => fePSU_dualPair_Geps_le_unitBlockCentralizer S
        (Subgroup.mem_map_of_mem
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype g.2))
  let Ψ : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) →*
      (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (LinearMap.range (Matrix.mulVecLin e))).toMonoidHom.comp actK.toHomUnits
  have hΨinj : Function.Injective Ψ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).injective.comp hinj
  have hΨsurj : Function.Surjective Ψ := by
    intro T
    obtain ⟨u, hu⟩ := hreal ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm T)
    refine ⟨u, ?_⟩
    change LinearMap.GeneralLinearGroup.generalLinearEquiv K _ (actK.toHomUnits u) = T
    rw [hu, MulEquiv.apply_symm_apply]
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h := congrArg (fun u : ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) =>
      (u : GL (Fin n) F)) hab
    exact Subtype.ext (Subtype.ext h)
  have hderived := rckRPfeu_derived_eq hc S hS hSU hε he heε hpair hεeq _ hdeg K hKfr π hπsurj
    hπker
  have h1 : commutator (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K]
      LinearMap.range (Matrix.mulVecLin e)) =
      (commutator ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε)).map Ψ := by
    simp only [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hΨsurj]
  have h2 : (commutator ↥(glBlockCentralizer
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S ε)).map ι =
      commutator ↥(fePSU_dualPair_unitBlockCentralizer (f := f) S ε) := by
    apply Subgroup.map_injective
      (fePSU_dualPair_unitBlockCentralizer (f := f) S ε).subtype_injective
    rw [Subgroup.map_map]
    have hι : (fePSU_dualPair_unitBlockCentralizer (f := f) S ε).subtype.comp ι =
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype.comp
          (glBlockCentralizer
            (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
              ε).subtype :=
      MonoidHom.ext fun _ => rfl
    rw [hι, ← Subgroup.map_map]
    simp only [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hderived
  refine ⟨K, hKf, hKa, hKfin, LinearMap.range (Matrix.mulVecLin e), inferInstance,
    inferInstance, hmod, htower, hWfd,
    LinearEquiv.ofEq _ _ (by rw [Matrix.toLin'_apply']), Ψ.comp ι, ?_, hΨinj.comp hιinj, ?_,
    ?_, ?_⟩
  · rw [hcard, ← pow_mul]
    congr 1
    ring
  · rw [h1, ← h2, Subgroup.map_map]
  · intro g w
    simp only [LinearEquiv.coe_ofEq_apply]
    change (actK (ι g) w : Fin n → F) = _
    rw [hact]
    rfl
  · intro g
    exact fePSU_unitBlockCentralizer_commute_adjoin S (ι g) he.1

theorem exists_blockAction_dualPair_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {S : Set (GL (Fin n) F)}
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) F}
    (hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (Algebra.adjoin F (Units.val '' S))
      (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
        (Unitary.antidiag n) e))
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : Module K W)
      (_ : IsScalarTower F K W) (_ : FiniteDimensional K W)
      (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
      (φ : ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
          (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) e)) →* (W ≃ₗ[K] W)),
      Nat.card K = 2 ^ (2 * f * blockDegree (Algebra.adjoin F (Units.val '' S)) e) ∧
      Function.Injective φ ∧
      (commutator ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
          (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) e))).map φ = commutator (W ≃ₗ[K] W) ∧
      (∀ g w, (eW (φ g w) : Fin n → F) =
        Matrix.mulVec
          (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
            GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (eW w : Fin n → F)) ∧
      ∀ g : ↥(glBlockCentralizer
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S
          (e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) e)),
        (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e =
        e * (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨he0, -⟩ := fePSU_dualPair_GepsGLK_natural_pairing hc S hS hSU hε he hpair
  exact rckRPfeu_blockAction hc S hSU hS hodd hε he
    (by rw [Matrix.mul_add, he.2.1.eq, he0, add_zero]) hdeg hpair rfl

end CFSG.StandardType.ClassicalPosition
