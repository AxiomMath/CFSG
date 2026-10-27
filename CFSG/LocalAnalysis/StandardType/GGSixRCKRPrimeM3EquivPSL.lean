module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSHom
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSConj
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SymmetricGroup

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private theorem rckM3eq_range_mulVecLin_ne_bot {n : ℕ} {F : Type} [Field F]
    {e : Matrix (Fin n) (Fin n) F} (he : e ≠ 0) :
    LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
  intro hbot
  apply he
  have h0 : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
  refine Matrix.mulVec_injective ?_
  rw [← Matrix.coe_mulVecLin (M := e),
    ← Matrix.coe_mulVecLin (M := (0 : Matrix (Fin n) (Fin n) F)), h0, Matrix.mulVecLin_zero]

private theorem rckM3eq_map_injective {R S : Type*} [CommRing R] [CommRing S]
    {n : Type*} [Fintype n] [DecidableEq n] (σ : R ≃+* S) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := n) σ.toRingHom) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply σ.injective
  have h' := congrFun (congrFun (congrArg
    (fun M : Matrix.SpecialLinearGroup n S => (M : Matrix n n S)) h) i) j
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply] using h'

private theorem rckM3eq_map_surjective {R S : Type*} [CommRing R] [CommRing S]
    {n : Type*} [Fintype n] [DecidableEq n] (σ : R ≃+* S) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := n) σ.toRingHom) := by
  intro B
  refine ⟨⟨σ.symm.mapMatrix (B : Matrix n n S), ?_⟩, ?_⟩
  · rw [← RingEquiv.map_det σ.symm (B : Matrix n n S), B.2, map_one]
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      RingEquiv.mapMatrix_apply, Matrix.map_apply]
    exact σ.apply_symm_apply _

private theorem rckM3eq_solvable_SL_two_of_card_two {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨e⟩ := TauCeti.nonempty_mulEquiv_permFinThree hF
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Equiv.Perm.isSolvable (by norm_num)
  have hGL : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_isSolvable_injective
    (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective

private theorem rckM3eq_card_ge_four {K : Type} [Field K] [Finite K] {g a : ℕ}
    (hKcard : Nat.card K = 2 ^ (g * a)) (hne2 : Nat.card K ≠ 2) :
    4 ≤ Nat.card K := by
  have hKge2 : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
  have hne0 : g * a ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hKcard
    omega
  have hne1 : g * a ≠ 1 := by
    intro h1
    exact hne2 (by rw [hKcard, h1]; norm_num)
  have hge2 : 2 ≤ g * a := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (g * a) := pow_right_monotone (by norm_num) hge2
    _ = Nat.card K := hKcard.symm

theorem rckM3_PSL_equiv (m g : ℕ) (hg : 1 ≤ g) (S : Set (GL (Fin (m + 1)) (GaloisField 2 g)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    ∃ (k h : ℕ) (ι : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 h) →*
        Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)),
      1 ≤ h ∧ Function.Injective ι ∧ ι.range = J' ∧
      ∀ s' : GL (Fin (m + 1)) (GaloisField 2 g), (∀ s ∈ S, Commute s' s) →
        ∃ t : GL (Fin (k + 1)) (GaloisField 2 h), ∀ y,
          Matrix.SpecialLinearGroup.toGL (ι (InnerDiagA.conjSL t y)) =
            s' * Matrix.SpecialLinearGroup.toGL (ι y) * s'⁻¹ := by
  classical
  let a : ℕ := blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e
  obtain ⟨K, hKfield, hKfin, hKalg, hKmod, hKtower, π, hπ⟩ :=
    rckBlockCoord_exists S hS hodd he
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : Algebra (GaloisField 2 g) K := hKalg
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hKmod
  letI : IsScalarTower (GaloisField 2 g) K (LinearMap.range (Matrix.mulVecLin e)) := hKtower
  have hKcard : Nat.card K = 2 ^ (g * a) := by
    rw [hπ.2.2, GaloisField.card 2 g (by omega), ← pow_mul]
  have hKge2 : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
  have hh1 : 1 ≤ g * a := by
    have h2 : 2 ≤ 2 ^ (g * a) := by rwa [← hKcard]
    by_contra h
    have h0 : g * a = 0 := by omega
    rw [h0, pow_zero] at h2
    omega
  haveI hWfin : Module.Finite K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 g) K
      (LinearMap.range (Matrix.mulVecLin e))
  have hWne : LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ :=
    rckM3eq_range_mulVecLin_ne_bot he.2.2.1
  haveI hWnt : Nontrivial (LinearMap.range (Matrix.mulVecLin e)) :=
    (Submodule.nontrivial_iff_ne_bot).mpr hWne
  have hfinpos : 0 < Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.finrank_pos_iff.mpr hWnt
  let k : ℕ := Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) - 1
  have hk : Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) = k + 1 := by
    dsimp only [k]
    omega
  let b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.finBasisOfFinrankEq K (LinearMap.range (Matrix.mulVecLin e)) hk
  obtain ⟨ρ, hρmat, hρinj, hρle, hρcomm⟩ :=
    rckBlockRS_hom (K := K) (π := π) hS he hπ b
  have hcardGF : Nat.card (GaloisField 2 (g * a)) = 2 ^ (g * a) :=
    GaloisField.card 2 (g * a) (by omega)
  have hcard_eq : Nat.card (GaloisField 2 (g * a)) = Nat.card K := by
    rw [hcardGF, hKcard]
  obtain ⟨σ⟩ := CFSG.RankThree.PartOne.CTP.nonempty_ringEquiv_of_natCard_eq hcard_eq
  let ι : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a)) →*
      Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) :=
    ρ.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
  have hιinj : Function.Injective ι := hρinj.comp (rckM3eq_map_injective σ)
  have hcoeeq : ∀ z : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a)),
      ((ι z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
      rckBlockRSMat b ((σ.toRingHom).mapMatrix
        (z : Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a)))) := by
    intro z
    rw [show ((ι z : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
        ((ρ (Matrix.SpecialLinearGroup.map σ.toRingHom z) :
          Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) from rfl]
    rw [hρmat, Matrix.SpecialLinearGroup.map_apply_coe]
  by_cases hsmall : k + 1 = 1 ∨ (k + 1 = 2 ∧ Nat.card K = 2)
  · exfalso
    rcases hsmall with hk1 | ⟨hk2, hK2⟩
    · haveI hsub1 : Subsingleton (Matrix.SpecialLinearGroup (Fin (k + 1)) K) := by
        rw [hk1]
        exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      have hρbot : ρ.range = ⊥ := by
        apply le_antisymm
        · rintro x ⟨y, rfl⟩
          rw [Subsingleton.elim y 1, map_one]
          exact Subgroup.mem_bot.mpr rfl
        · exact bot_le
      have hHbot : ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ = ⊥ :=
        le_bot_iff.mp (hρcomm.trans (le_of_eq hρbot))
      have hJbot : J' = ⊥ := le_bot_iff.mp (hJe.1.trans (le_of_eq hHbot))
      haveI hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
      rw [hJbot] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · haveI hsol : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (k + 1)) K) := by
        rw [hk2]
        exact rckM3eq_solvable_SL_two_of_card_two hK2
      haveI hsolRange : Group.IsSolvable ρ.range :=
        Group.isSolvable_of_surjective (f := (MonoidHom.ofInjective hρinj).toMonoidHom)
          (MonoidHom.ofInjective hρinj).surjective
      haveI hsolH : Group.IsSolvable ↥⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hρcomm)
          (fun _ _ h => (Subgroup.inclusion_inj hρcomm).mp h)
      haveI hsolJ : Group.IsSolvable J' :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJe.1)
          (fun _ _ h => (Subgroup.inclusion_inj hJe.1).mp h)
      haveI hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
      haveI hperf : Group.IsPerfect J' := ⟨hJe.2.2.1⟩
      exact (Group.IsPerfect.not_isSolvable J') hsolJ
  · have hk2ge : 2 ≤ k + 1 := by
      have h1 : k + 1 ≠ 1 := fun h => hsmall (Or.inl h)
      omega
    have hqs : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (k + 1)) K) := by
      by_cases hk2 : k + 1 = 2
      · have hKne : Nat.card K ≠ 2 := fun hK => hsmall (Or.inr ⟨hk2, hK⟩)
        have h4 : 4 ≤ Nat.card K := rckM3eq_card_ge_four hKcard hKne
        rw [hk2]
        exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
          2 K le_rfl (Or.inr hKne) (Or.inr (by omega))
      · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
          (k + 1) K hk2ge (Or.inl hk2) (Or.inl hk2)
    have hSLq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (k + 1)) K) :=
      ⟨hqs.1.commutator_eq_top, hqs.2.1⟩
    haveI hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (k + 1)) K) :=
      Group.IsPerfect.mk hSLq.1
    haveI hperfR : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have hρrange : ρ.range = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
      apply le_antisymm
      · calc ρ.range = ⁅ρ.range, ρ.range⁆ :=
            (Subgroup.commutator_eq_self (H := ρ.range)).symm
          _ ≤ ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
              glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :=
            Subgroup.commutator_mono hρle hρle
      · exact hρcomm
    have hHq : CFSG.Open.IsQuasisimple ρ.range :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hρinj).symm hSLq
    have hJe' : J' ≤ ρ.range := by
      rw [hρrange]
      exact hJe.1
    have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf ρ.range) ⊤ := by
      have h := CFSG.Open.IsSubnormal.of_mathlib
        (CFSG.Assembly.IsSubnormal.subgroupOf hJe.2.1)
      rwa [← hρrange] at h
    haveI hntJ : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
    haveI hperfJ : Group.IsPerfect J' := ⟨hJe.2.2.1⟩
    haveI hperfSub : Group.IsPerfect (J'.subgroupOf ρ.range) := by
      have h : Group.IsPerfect (J'.subgroupOf ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :=
        Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hJe.1).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hJe.1).symm.surjective
      rwa [← hρrange] at h
    have hJeq : J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
      rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
        hHq (J'.subgroupOf ρ.range) hsub with hbot | htop
      · have hJ'bot : J' = ⊥ := by
          have hdisj : Disjoint J' ρ.range := Subgroup.subgroupOf_eq_bot.mp hbot
          rwa [disjoint_iff, inf_eq_left.mpr hJe'] at hdisj
        rw [hJ'bot] at hntJ
        exact absurd hntJ (not_nontrivial_iff_subsingleton.mpr inferInstance)
      · have hle : ρ.range ≤ J' := Subgroup.subgroupOf_eq_top.mp htop
        rw [hρrange] at hle
        exact le_antisymm hJe.1 hle
    have hιrange : ι.range = J' := by
      have h1 : (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) σ.toRingHom).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (rckM3eq_map_surjective σ)
      have h2 : ι.range = ρ.range := by
        rw [← MonoidHom.map_range ρ
            (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) σ.toRingHom), h1,
          ← MonoidHom.range_eq_map ρ]
      rw [h2, hρrange, ← hJeq]
    refine ⟨k, g * a, ι, hh1, hιinj, hιrange, ?_⟩
    intro s' hs'
    obtain ⟨t₀, ht₀⟩ := rckBlockRSMat_conj he hπ b s' hs'
    refine ⟨Matrix.GeneralLinearGroup.map σ.symm.toRingHom t₀, ?_⟩
    intro y
    have hσmap : ∀ u : GL (Fin (k + 1)) K,
        (σ.toRingHom).mapMatrix
          (((Matrix.GeneralLinearGroup.map σ.symm.toRingHom u :
            GL (Fin (k + 1)) (GaloisField 2 (g * a))) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a)))) =
          (u : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
      intro u
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply]
    have hstep : (σ.toRingHom).mapMatrix
        (((InnerDiagA.conjSL (Matrix.GeneralLinearGroup.map σ.symm.toRingHom t₀) y :
          Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a))) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a)))) =
        (t₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *
          (σ.toRingHom).mapMatrix
            (y : Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a))) *
          ((t₀⁻¹ : GL (Fin (k + 1)) K) : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
      rw [InnerDiagA.coe_conjSL, map_mul, map_mul]
      have h1 : (σ.toRingHom).mapMatrix
          (((Matrix.GeneralLinearGroup.map σ.symm.toRingHom t₀ :
            GL (Fin (k + 1)) (GaloisField 2 (g * a))) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a)))) =
          (t₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := hσmap t₀
      have h2 : (σ.toRingHom).mapMatrix
          ((((Matrix.GeneralLinearGroup.map σ.symm.toRingHom t₀ :
            GL (Fin (k + 1)) (GaloisField 2 (g * a)))⁻¹ :
            GL (Fin (k + 1)) (GaloisField 2 (g * a))) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 (g * a)))) =
          ((t₀⁻¹ : GL (Fin (k + 1)) K) : Matrix (Fin (k + 1)) (Fin (k + 1)) K) := by
        rw [← Matrix.GeneralLinearGroup.map_inv (f := σ.symm.toRingHom)]
        exact hσmap t₀⁻¹
      rw [h1, h2]
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [hcoeeq]
    rw [hstep]
    rw [ht₀]
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hcoeeq y]

end CFSG.StandardType.RCKRP
