module

public import CFSG.Quasithin.EmptyFaithful.SzPS8G2
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Quasithin.Background.G10Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
  (pairedSympForm pairedSympForm_self pairedSympForm_nondegenerate)
open scoped Matrix

private abbrev sixteenC8SpinG2V : Type := Fin 3 ⊕ Fin 3 → ZMod 2

private noncomputable def sixteenC8SpinG2ToLin :
    GL (Fin 3 ⊕ Fin 3) (ZMod 2) ≃*
      (sixteenC8SpinG2V ≃ₗ[ZMod 2] sixteenC8SpinG2V) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) sixteenC8SpinG2V)

private lemma sixteenC8SpinG2ToLin_apply (A : GL (Fin 3 ⊕ Fin 3) (ZMod 2))
    (v : sixteenC8SpinG2V) :
    sixteenC8SpinG2ToLin A v =
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) sixteenC8SpinG2V
    (Matrix.GeneralLinearGroup.toLin A)) v = _
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

private noncomputable def sixteenC8SpinG2Map :
    ↥(StatedSp 3 (ZMod 2)) →*
      (sixteenC8SpinG2V ≃ₗ[ZMod 2] sixteenC8SpinG2V) :=
  sixteenC8SpinG2ToLin.toMonoidHom.comp (StatedSp 3 (ZMod 2)).subtype

private lemma sixteenC8SpinG2Map_injective : Function.Injective sixteenC8SpinG2Map :=
  sixteenC8SpinG2ToLin.injective.comp (StatedSp 3 (ZMod 2)).subtype_injective

private theorem sixteenC8SpinG2_pairedSympForm_mulVec {r : ℕ} {K : Type} [Field K]
    (A : StatedSp r K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u)
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
      pairedSympForm K r u v := by
  have hA := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp A.2
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  simp only [pairedSympForm, Matrix.toBilin'_apply']
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hA, ← Matrix.dotProduct_mulVec]

private theorem sixteenC8SpinG2_isPSU_psu3 : IsPSU 3 3 1 (CFSG.Open.PSU3 3 1) := by
  obtain ⟨e⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  refine CFSG.Quasithin.IsPSU.of_mulEquiv e ?_
  refine ⟨⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩, ?_⟩
  exact ⟨GaloisField 3 (2 * 1), inferInstance, inferInstance,
    CFSG.Timmesfeld.Final.GF9.card, ⟨MulEquiv.refl _⟩⟩

private theorem sixteenC8SpinG2_isPSU_u33G :
    IsPSU 3 3 1 U33G := by
  obtain ⟨e⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  exact CFSG.Quasithin.IsPSU.of_mulEquiv e.symm sixteenC8SpinG2_isPSU_psu3

private theorem sixteenC8SpinG2_center_u33G :
    Subgroup.center U33G = ⊥ := by
  haveI : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact h
  · exfalso
    let _ : CommGroup U33G := Group.commGroupOfCenterEqTop h
    have hprime := IsSimpleGroup.prime_card (α := U33G)
    rw [card_u33Pres] at hprime
    norm_num at hprime

private theorem sixteenC8SpinG2_g2_data
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y : Type} [Group Y]
    (B : LinearMap.BilinForm (ZMod 2) V) (hBalt : ∀ v, B v v = 0)
    (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0) (hdim : Module.finrank (ZMod 2) V = 6)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hΓB : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w)
    (hΓcard : Nat.card Γ = 12096) (e : Y ≃* Γ) :
    Subgroup.center Y = ⊥ ∧
      ∃ D : Subgroup Y, D.Normal ∧ D.index = 2 ∧ IsPSU 3 3 1 ↥D := by
  obtain ⟨b, hb⟩ := CFSG.Quasithin.H13.KGCert.kgSp6Order12096 V B hBalt hBnd hdim Γ hΓB hΓcard
  let Θ : (V ≃ₗ[ZMod 2] V) ≃* GL (Fin 6) (ZMod 2) :=
    MulEquiv.ofBijective (CFSG.Quasithin.H13.KGSp6.phi b)
      ⟨CFSG.Quasithin.H13.KGSp6.phi_injective b,
        CFSG.Quasithin.H13.KGSp6.phi_surjective b⟩
  set ρ : U33G →* (V ≃ₗ[ZMod 2] V) :=
    Θ.symm.toMonoidHom.comp CFSG.Quasithin.SzPS8.g2uRep with hρ
  have hρinj : Function.Injective ρ :=
    Θ.symm.injective.comp CFSG.Quasithin.SzPS8.g2uRep_injective
  have hgen : ∀ i : Fin 5, ρ (u33GenPG i) ∈ Γ := by
    intro i
    have hmem : CFSG.Quasithin.H13.U3.colMat (CFSG.Quasithin.SzPS8.G2U.g2uc i) ∈
        CFSG.Quasithin.H13.KGCert.g22Mats := by
      have h := CFSG.Quasithin.H13.KGCert.decodeC_evalWord_mem
        (CFSG.Quasithin.SzPS8.G2U.g2uw i)
      rw [CFSG.Quasithin.SzPS8.G2U.g2uc_words] at h
      exact h
    obtain ⟨γ, hγ, hγe⟩ := (hb _).mp hmem
    have h1 : Θ γ = CFSG.Quasithin.SzPS8.g2uGL i := by
      apply Units.ext
      rw [show Θ γ = CFSG.Quasithin.H13.KGSp6.phi b γ from rfl,
        CFSG.Quasithin.H13.KGSp6.coe_phi, hγe]
      rfl
    have h2 : ρ (u33GenPG i) = γ := by
      simp only [hρ, MonoidHom.comp_apply, CFSG.Quasithin.SzPS8.g2uRep_gen]
      exact (MulEquiv.symm_apply_eq Θ).mpr h1.symm
    rw [h2]
    exact hγ
  have hall : ∀ g, ρ g ∈ Γ := by
    have hle : (⊤ : Subgroup U33G) ≤ Γ.comap ρ := by
      rw [← u33Data.gen]
      refine (Subgroup.closure_le _).2 ?_
      rintro g (rfl | rfl | rfl | rfl | rfl)
      exacts [hgen 0, hgen 1, hgen 2, hgen 3, hgen 4]
    exact fun g => hle (Subgroup.mem_top g)
  have hKΓ : ρ.range ≤ Γ := by
    rintro _ ⟨g, rfl⟩
    exact hall g
  have hKcard : Nat.card ρ.range = 6048 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact card_u33Pres
  have hKcardΓ : Nat.card ↥(ρ.range.subgroupOf Γ) = 6048 := by
    rw [← hKcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKΓ).toEquiv
  have hKindex : (ρ.range.subgroupOf Γ).index = 2 := by
    have h1 := Subgroup.card_mul_index (ρ.range.subgroupOf Γ)
    rw [hKcardΓ, hΓcard] at h1
    omega
  have hKnorm : (ρ.range.subgroupOf Γ).Normal :=
    Subgroup.normal_of_index_eq_two hKindex
  have hKPSU : IsPSU 3 3 1 ↥(ρ.range.subgroupOf Γ) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hKΓ).trans (MonoidHom.ofInjective hρinj).symm).symm
      sixteenC8SpinG2_isPSU_u33G
  have hZK : Subgroup.center ↥(ρ.range.subgroupOf Γ) = ⊥ := by
    have hmap := Subgroup.map_center_eq
      ((Subgroup.subgroupOfEquivOfLe hKΓ).trans (MonoidHom.ofInjective hρinj).symm)
    rw [show Subgroup.center U33G = ⊥ from sixteenC8SpinG2_center_u33G] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).1 hmap
  have hcenter : Subgroup.center Γ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    haveI : (ρ.range.subgroupOf Γ).Normal := hKnorm
    have hzK : z ^ 2 ∈ ρ.range.subgroupOf Γ := by
      simpa [hKindex] using Subgroup.pow_index_mem (ρ.range.subgroupOf Γ) z
    have hz2 : z ^ 2 = 1 := by
      have hz2center : z ^ 2 ∈ Subgroup.center Γ := (Subgroup.center Γ).pow_mem hz 2
      have hz2Kcenter : (⟨z ^ 2, hzK⟩ : ↥(ρ.range.subgroupOf Γ)) ∈
          Subgroup.center ↥(ρ.range.subgroupOf Γ) := by
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext (Subgroup.mem_center_iff.1 hz2center (k : Γ))
      rw [hZK, Subgroup.mem_bot] at hz2Kcenter
      exact congrArg Subtype.val hz2Kcenter
    have hz2' : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hzpg : IsPGroup 2 ↥(Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2']; norm_num)
    obtain ⟨S, hSz⟩ := IsPGroup.exists_le_sylow hzpg
    have hScard : Nat.card ↥S = 64 := by
      have h := Sylow.card_eq_multiplicity S
      rw [hΓcard] at h
      rw [show (Nat.factorization 12096) 2 = 6 from by decide +kernel] at h
      norm_num at h
      exact h
    haveI : Fintype V := Fintype.ofFinite V
    have hVcard : 2 ∣ Nat.card V := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), hdim,
        ZMod.card]
      norm_num
    obtain ⟨b', hb'fix, hb'0⟩ := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      S.isPGroup' V hVcard (a := 0) (by simp)
    let S' : Subgroup (V ≃ₗ[ZMod 2] V) := S.map Γ.subtype
    let Z₀ : Subgroup (V ≃ₗ[ZMod 2] V) := Subgroup.zpowers (z : V ≃ₗ[ZMod 2] V)
    have hS'card : Nat.card S' = 64 := by
      change Nat.card ↥(S.map Γ.subtype) = 64
      rw [Subgroup.card_map_of_injective Γ.subtype_injective]
      exact hScard
    have hZ₀card : Nat.card Z₀ = 2 := by
      change Nat.card ↥(Subgroup.zpowers (z : V ≃ₗ[ZMod 2] V)) = 2
      rw [Nat.card_zpowers]
      rw [show orderOf (z : V ≃ₗ[ZMod 2] V) = orderOf z from
        orderOf_injective Γ.subtype Γ.subtype_injective z]
      exact hz2'
    have hZ₀le : Z₀ ≤ S' := by
      change Subgroup.zpowers (z : V ≃ₗ[ZMod 2] V) ≤ S'
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.2 ⟨z, hSz (Subgroup.mem_zpowers z), rfl⟩
    have hS'le : S' ≤ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) b' := by
      intro g hg
      refine ⟨Subgroup.map_subtype_le S hg, ?_⟩
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
      change (Γ.subtype s) • b' = b'
      have h := (MulAction.mem_fixedPoints.1 hb'fix) ⟨s, hs⟩
      rw [Subgroup.smul_def] at h
      exact h
    have hΓnorm : Γ ≤ Subgroup.normalizer (Z₀ : Set (V ≃ₗ[ZMod 2] V)) := by
      have hΓcent : Γ ≤ Subgroup.centralizer (Z₀ : Set (V ≃ₗ[ZMod 2] V)) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hh' : h ∈ Subgroup.zpowers (z : V ≃ₗ[ZMod 2] V) := hh
        rw [Subgroup.mem_zpowers_iff] at hh'
        obtain ⟨n, rfl⟩ := hh'
        have hc : g * (z : V ≃ₗ[ZMod 2] V) = (z : V ≃ₗ[ZMod 2] V) * g := by
          simpa only [Subgroup.coe_mul] using
            congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
        exact (Commute.zpow_right hc n).symm
      exact hΓcent.trans (Subgroup.centralizer_le_normalizer _)
    have hS'norm : S' ≤ Subgroup.normalizer (Z₀ : Set (V ≃ₗ[ZMod 2] V)) :=
      (Subgroup.map_subtype_le S).trans hΓnorm
    have hKGG22 : CFSG.Quasithin.H13.KGG22PointStab :=
      CFSG.Quasithin.H13.KGCert.kgG22PointStab
        (hO := CFSG.Quasithin.H13.KGCert.kgSp6Order12096)
    exact (hKGG22 V B hBalt hBnd hdim Γ hΓB hΓcard b' (Ne.symm hb'0) S' Z₀ hS'le hS'card
        hZ₀le hZ₀card hS'norm) (le_trans inf_le_left hΓnorm)
  let D : Subgroup Y := (ρ.range.subgroupOf Γ).map e.symm.toMonoidHom
  have hDnorm : D.Normal := hKnorm.map e.symm.toMonoidHom e.symm.surjective
  have hDindex : D.index = 2 :=
    (Subgroup.index_map_equiv (ρ.range.subgroupOf Γ) e.symm).trans hKindex
  have hDPSU : IsPSU 3 3 1 ↥D :=
    CFSG.Quasithin.IsPSU.of_mulEquiv
      ((ρ.range.subgroupOf Γ).equivMapOfInjective e.symm.toMonoidHom
        e.symm.injective) hKPSU
  have hcenterY : Subgroup.center Y = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hcenter] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
  exact ⟨hcenterY, D, hDnorm, hDindex, hDPSU⟩

theorem isG2Two_of_card_sp6
    {Y : Type} [Group Y] (ι : Y →* ↥(StatedSp 3 (ZMod 2))) (hι : Function.Injective ι)
    (hY : Nat.card Y = 12096) : IsG2Two Y := by
  classical
  let Γ : Subgroup (sixteenC8SpinG2V ≃ₗ[ZMod 2] sixteenC8SpinG2V) :=
    ι.range.map sixteenC8SpinG2Map
  have hΓcard : Nat.card Γ = 12096 := by
    rw [show Γ = ι.range.map sixteenC8SpinG2Map from rfl,
      Subgroup.card_map_of_injective sixteenC8SpinG2Map_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hY]
  have hBalt : ∀ v : sixteenC8SpinG2V, pairedSympForm (ZMod 2) 3 v v = 0 :=
    fun v => pairedSympForm_self v
  have hBnd : ∀ v : sixteenC8SpinG2V,
      (∀ w, pairedSympForm (ZMod 2) 3 v w = 0) → v = 0 :=
    pairedSympForm_nondegenerate.1
  have hdim : Module.finrank (ZMod 2) sixteenC8SpinG2V = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have hΓB : ∀ γ ∈ Γ, ∀ v w, pairedSympForm (ZMod 2) 3 (γ v) (γ w) =
      pairedSympForm (ZMod 2) 3 v w := by
    intro γ hγ v w
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
    obtain ⟨y, rfl⟩ := hx
    change pairedSympForm (ZMod 2) 3 (sixteenC8SpinG2ToLin _ v)
      (sixteenC8SpinG2ToLin _ w) = _
    rw [sixteenC8SpinG2ToLin_apply, sixteenC8SpinG2ToLin_apply]
    exact sixteenC8SpinG2_pairedSympForm_mulVec _ v w
  have eYΓ : Y ≃* Γ :=
    (MonoidHom.ofInjective hι).trans (ι.range.equivMapOfInjective sixteenC8SpinG2Map
      sixteenC8SpinG2Map_injective)
  obtain ⟨hcenterY, D, hDnorm, hDindex, hDPSU⟩ :=
    @sixteenC8SpinG2_g2_data




      sixteenC8SpinG2V Pi.addCommGroup
      (inferInstance : Module (ZMod 2) sixteenC8SpinG2V)
      (inferInstance : Finite sixteenC8SpinG2V) Y (inferInstance : Group Y)
      (pairedSympForm (ZMod 2) 3) hBalt hBnd hdim Γ hΓB hΓcard eYΓ
  exact ⟨hY, hcenterY, ⟨D, hDnorm, hDindex, hDPSU⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
