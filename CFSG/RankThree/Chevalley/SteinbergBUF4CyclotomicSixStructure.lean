module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2Sextic
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSixTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace SteinbergBN
open CFSG.RankThree.Classical Matrix

theorem inf_centralizer_eq_center_of_le {G : Type*} [Group G] {D R Z : Subgroup G} (hRD : R ≤ D)
    (hZ : ∀ z ∈ D ⊓ Subgroup.centralizer (R : Set G), z ∈ Z)
    (hc : ∀ z ∈ Z, ∀ d ∈ D, z * d = d * z) :
    D ⊓ Subgroup.centralizer (R : Set G) = (Subgroup.center D).map D.subtype := by
  apply le_antisymm
  · intro z hz
    have hzD := (Subgroup.mem_inf.1 hz).1
    refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
    exact (hc z (hZ z hz) d d.2).symm
  · rintro _ ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨r, hRD hr⟩)

theorem cyclotomic_six_levi_fixed_data (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (K₆ : Type) [Field K₆] [Algebra K K₆] [FiniteDimensional K K₆]
    (K₂ K₃ : IntermediateField K K₆) (h2 : Module.finrank K K₂ = 2)
    (h3 : Module.finrank K K₃ = 3) (σ : K₆ ≃+* K₆) (hσ : ∀ b, σ b = b ^ Nat.card K)
    (σ₂ : K₂ ≃+* K₂) (hσ₂ : ∀ b, σ₂ b = b ^ Nat.card K) (κ : F4A2Kind) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup .F4)
    (hv : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
        -(((simple .F4 κ.i * simple .F4 κ.j) ^ ε) • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)))
    (U : Subgroup (ModGL .F4 K₂))
    (hU : ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup .F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1) :
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
        ∃ g : subsystemGroup .F4 K₂ {κ.i, κ.j}, (g : ModGL .F4 K₂) ∈ U ∧
          f4A2Equiv K₂ κ g = A) ∧
    ∃ a ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓ (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v)
          σ.toRingHom).eqLocus (MonoidHom.id _) =
        U.map ((MulAut.conj (baseChangeGL (algebraMap K₃ K₆) a)).toMonoidHom.comp
          (baseChangeGL (algebraMap K₂ K₆))) ∧
      (∃ e : U ≃* ↥(subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _)),
        (∀ u : U, (e u : ModGL .F4 K₆) = baseChangeGL (algebraMap K₃ K₆) a *
          baseChangeGL (algebraMap K₂ K₆) u * (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) ∧
        ∀ (g : subsystemGroup .F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL .F4 K₂) ∈ U),
          e ⟨g, hg⟩ ∈ Subgroup.center _ ↔ ∃ t : K₂, t ^ (Nat.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
            (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = Matrix.scalar (Fin 3) t) ∧
      CFSG.IsQuasisimple ↥(subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
        (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
          (MonoidHom.id _)) ∧
      ⁅(torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j}) ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _),
        (torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j}) ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _)⁆ =
        subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _) ∧
      (∀ z ∈ torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j},
        (∀ r ∈ subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _), r * z = z * r) → z ∈ pairCharKernelTorus K₆ κ.i κ.j) ∧
      (∀ z ∈ pairCharKernelTorus K₆ κ.i κ.j,
        ∀ d ∈ torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j}, z * d = d * z) ∧
      Odd (Nat.card (pairCharKernelTorus K₆ κ.i κ.j)) ∧
      ∃ P : GL (Fin 2) K₂, ∀ A : SL2 K,
        baseChangeGL (algebraMap K₃ K₆) a *
          rootSL2 .F4 K₆ (Pi.single κ.i 1) (Matrix.SpecialLinearGroup.map (algebraMap K₂ K₆)
            (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A))) *
          (baseChangeGL (algebraMap K₃ K₆) a)⁻¹ ∈
        subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
          (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
            (MonoidHom.id _) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K₆ 2 := charP_of_injective_algebraMap (algebraMap K K₆).injective 2
  have hσ' : ∀ b, σ b = b ^ Fintype.card K := fun b => by rw [hσ, Nat.card_eq_fintype_card]
  have hσ₂' : ∀ b, σ₂ b = b ^ Fintype.card K := fun b => by
    rw [hσ₂, Nat.card_eq_fintype_card]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : WeylGroup Tag.F4, ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v :=
    ⟨CFSG.LieType.Ree.ReeTag.F4.negOne, CFSG.LieType.Ree.ReeTag.negOne_smul .F4⟩
  obtain ⟨hSU, a, ha, hF, ⟨e, he, hcen⟩, hqs, hcent, hcenter, hodd, P, hP⟩ :=
    even_F4_native_A2_sextic_unitary_permutation_descent K K₆ K₂ K₃ h2 h3 σ hσ' σ₂ hσ₂' κ ε hε
      w₀ hw₀ (twistedEntrywise ((weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
        canonicalRep (coxeterSystem Tag.F4) K₆ w₀) σ.toRingHom) (fun g => rfl) U hU
      (pairCharKernelTorus K₆ κ.i κ.j) _ mem_pairCharKernelTorus rfl
  have hv' : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
        ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ ε * w₀) • Pi.single k 1 := by
    intro k hk
    rw [hv k hk, mul_smul, hw₀, smul_neg]
  have hn' : canonicalRep (coxeterSystem Tag.F4) K₆
      ((simple Tag.F4 κ.i * simple Tag.F4 κ.j) ^ ε * w₀) =
        (weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
          canonicalRep (coxeterSystem Tag.F4) K₆ w₀ := by
    rw [EvenF4QPlus.canonicalRep_mul_of_charTwo, canonicalRep_simple_pair_zpow _ _ hε]
  have hagree : ∀ g ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j},
      twistedEntrywise (canonicalRep (coxeterSystem Tag.F4) K₆ v) σ.toRingHom g =
        twistedEntrywise ((weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
          canonicalRep (coxeterSystem Tag.F4) K₆ w₀) σ.toRingHom g := by
    intro g hg
    have hσg : Units.map (entrywiseHom σ.toRingHom) g ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j} := by
      rw [units_map_entrywiseHom_eq_baseChangeGL_self]
      exact baseChangeGL_mem_subsystemGroup _ hg
    rw [twistedEntrywise_apply, twistedEntrywise_apply, canonicalRep_conj_eq_of_smul_single hv' hσg,
      hn']
  have hF₀ : subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem Tag.F4) K₆ v) σ.toRingHom).eqLocus
        (MonoidHom.id _) =
      subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓
        (twistedEntrywise ((weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
          canonicalRep (coxeterSystem Tag.F4) K₆ w₀) σ.toRingHom).eqLocus (MonoidHom.id _) := by
    ext g
    constructor
    · intro hg'
      obtain ⟨hg, hfix⟩ := Subgroup.mem_inf.1 hg'
      exact Subgroup.mem_inf.2 ⟨hg, (hagree g hg).symm.trans hfix⟩
    · intro hg'
      obtain ⟨hg, hfix⟩ := Subgroup.mem_inf.1 hg'
      exact Subgroup.mem_inf.2 ⟨hg, (hagree g hg).trans hfix⟩
  have h4' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨hq, hp⟩ := hqs h4'
  let e₀ := MulEquiv.subgroupCongr hF₀
  have hq₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hp₀ := hq₀.1
  refine ⟨hSU, a, ha, hF₀.trans hF, ⟨e.trans e₀.symm, fun u => he u, fun g hg => ?_⟩, hq₀,
    levi_fixed_commutator_eq _ _ hp₀, fun z hzL hzc => ?_, fun z hz d hd => ?_, hodd, P,
    fun A => hF₀ ▸ hP A⟩
  · rw [MulEquiv.trans_apply, mulEquiv_apply_mem_center_iff, hcen g hg, Nat.card_eq_fintype_card]
  · rw [← hcent]
    refine Subgroup.mem_inf.2 ⟨hzL, Subgroup.mem_centralizer_iff.2 fun r hr => hzc r ?_⟩
    rw [hF₀]
    exact hr
  · rw [← hcenter] at hz
    obtain ⟨z₁, hz₁, rfl⟩ := hz
    have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz₁) ⟨d, hd⟩)
    exact hc.symm

theorem cyclotomic_six_D_structure (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (Ω : Type) [Field Ω] [Algebra K Ω] (K₆ : IntermediateField K Ω)
    (hK₆ : Module.finrank K K₆ = 6) (K₂ K₃ : IntermediateField K K₆)
    (h2 : Module.finrank K K₂ = 2) (h3 : Module.finrank K K₃ = 3) (σ : K₆ ≃+* K₆)
    (hσ : ∀ b, σ b = b ^ Nat.card K) (σ₂ : K₂ ≃+* K₂) (hσ₂ : ∀ b, σ₂ b = b ^ Nat.card K)
    (κ : F4A2Kind) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (v : WeylGroup .F4)
    (hv : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
        -(((simple .F4 κ.i * simple .F4 κ.j) ^ ε) • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)))
    (U : Subgroup (ModGL .F4 K₂))
    (hU : ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup .F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω))
    (hΓ₁ : ∀ z ∈ adjointGroup .F4 K₆, baseChangeGL (algebraMap K₆ Ω) z ∈ Γ₁ ↔
      canonicalRep (coxeterSystem .F4) K₆ v * Units.map (entrywiseHom σ.toRingHom) z *
        (canonicalRep (coxeterSystem .F4) K₆ v)⁻¹ = z)
    (hD : D = ((torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j}) ⊓
      ((MulAut.conj (canonicalRep (coxeterSystem .F4) K₆ v)).toMonoidHom.comp
        (Units.map (entrywiseHom σ.toRingHom))).eqLocus (MonoidHom.id _)).map
          (baseChangeGL (algebraMap K₆ Ω)))
    (hR : R = ⁅D, D⁆) :
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
        ∃ g : subsystemGroup .F4 K₂ {κ.i, κ.j}, (g : ModGL .F4 K₂) ∈ U ∧
          f4A2Equiv K₂ κ g = A) ∧
    ∃ a ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      R = (subsystemGroup .F4 K₆ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₆ Ω)) ⊓ Γ₁ ∧
      R = (U.map ((MulAut.conj (baseChangeGL (algebraMap K₃ K₆) a)).toMonoidHom.comp
        (baseChangeGL (algebraMap K₂ K₆)))).map (baseChangeGL (algebraMap K₆ Ω)) ∧
      (∃ e : U ≃* R,
        (∀ u : U, (e u : ModGL .F4 Ω) = baseChangeGL (algebraMap K₆ Ω)
          (baseChangeGL (algebraMap K₃ K₆) a * baseChangeGL (algebraMap K₂ K₆) u *
            (baseChangeGL (algebraMap K₃ K₆) a)⁻¹)) ∧
        ∀ (g : subsystemGroup .F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL .F4 K₂) ∈ U),
          e ⟨g, hg⟩ ∈ Subgroup.center R ↔ ∃ t : K₂, t ^ (Nat.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
            (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = Matrix.scalar (Fin 3) t) ∧
      CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤
        (torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ∧
      Odd (Nat.card (Subgroup.center D)) ∧
      ∃ P : GL (Fin 2) K₂, ∀ A : SL2 K,
        baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a *
          rootSL2 .F4 K₆ (Pi.single κ.i 1) (Matrix.SpecialLinearGroup.map (algebraMap K₂ K₆)
            (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A))) *
          (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) ∈ R := by
  classical
  have : FiniteDimensional K K₆ := Module.finite_of_finrank_eq_succ hK₆
  have hinj := baseChangeGL_injective (τ := Tag.F4) (algebraMap K₆ Ω)
  obtain ⟨hSU, a, ha, hF, ⟨e, he, hcen⟩, hq, hcomm, hcentZ, hZc, hodd, P, hP⟩ :=
    cyclotomic_six_levi_fixed_data K h4 K₆ K₂ K₃ h2 h3 σ hσ σ₂ hσ₂ κ ε hε v hv U hU
  have hD' : D = ((torusGroup .F4 K₆ ⊔ subsystemGroup .F4 K₆ {κ.i, κ.j}) ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
        (MonoidHom.id _)).map (baseChangeGL (algebraMap K₆ Ω)) := hD
  have hRF : R = (subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
        (MonoidHom.id _)).map (baseChangeGL (algebraMap K₆ Ω)) := by
    rw [hR, hD', ← Subgroup.map_commutator, hcomm]
  have hRQ : R = (subsystemGroup .F4 K₆ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₆ Ω)) ⊓ Γ₁ := by
    rw [hRF]
    ext z
    constructor
    · rintro ⟨z₀, hz₀, rfl⟩
      obtain ⟨hz₀Q, hz₀fix⟩ := Subgroup.mem_inf.1 hz₀
      refine Subgroup.mem_inf.2 ⟨⟨z₀, hz₀Q, rfl⟩, ?_⟩
      exact (hΓ₁ z₀ (EvenF4QPlus.subsystemGroup_le_adjointGroup' _ hz₀Q)).2 hz₀fix
    · intro hz
      obtain ⟨⟨z₀, hz₀Q, rfl⟩, hzΓ⟩ := Subgroup.mem_inf.1 hz
      exact ⟨z₀, Subgroup.mem_inf.2 ⟨hz₀Q,
        (hΓ₁ z₀ (EvenF4QPlus.subsystemGroup_le_adjointGroup' _ hz₀Q)).1 hzΓ⟩, rfl⟩
  let e₂ := ((subsystemGroup .F4 K₆ {κ.i, κ.j} ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₆ v) σ.toRingHom).eqLocus
        (MonoidHom.id _)).equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hRF.symm)
  have hRqs : CFSG.IsQuasisimple R := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂ hq
  have hRbot : R ≠ ⊥ := by
    have : Nontrivial (R ⧸ Subgroup.center R) := hRqs.2.1.toNontrivial
    have : Nontrivial R := (QuotientGroup.mk'_surjective (Subgroup.center R)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot R).1 this
  have hRD : R ≤ D := hR ▸ commutator_le_of_self D
  have hZD : ∀ z ∈ D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)),
      z ∈ (pairCharKernelTorus K₆ κ.i κ.j).map (baseChangeGL (algebraMap K₆ Ω)) := by
    intro z hz
    obtain ⟨hzD, hzc⟩ := Subgroup.mem_inf.1 hz
    rw [hD'] at hzD
    obtain ⟨z₀, hz₀, rfl⟩ := hzD
    refine ⟨z₀, hcentZ z₀ (Subgroup.mem_inf.1 hz₀).1 fun r hr => hinj ?_, rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.1 hzc) _ (by rw [hRF]; exact ⟨r, hr, rfl⟩)
  have hZc' : ∀ z ∈ (pairCharKernelTorus K₆ κ.i κ.j).map (baseChangeGL (algebraMap K₆ Ω)),
      ∀ d ∈ D, z * d = d * z := by
    rintro _ ⟨z₀, hz₀, rfl⟩ d hd
    rw [hD'] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    rw [← map_mul, ← map_mul, hZc z₀ hz₀ d₀ (Subgroup.mem_inf.1 hd₀).1]
  have hcentD := inf_centralizer_eq_center_of_le hRD hZD hZc'
  have hcenH : (Subgroup.center D).map D.subtype ≤
      (torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) := by
    rw [← hcentD]
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := hZD z hz
    exact ⟨z₀, ((mem_pairCharKernelTorus z₀).1 hz₀).1, rfl⟩
  have hoddD : Odd (Nat.card (Subgroup.center D)) := by
    have e1 : Nat.card (Subgroup.center D) = Nat.card ((Subgroup.center D).map D.subtype) :=
      (Subgroup.card_map_of_injective D.subtype_injective).symm
    have e2 : Nat.card ((Subgroup.center D).map D.subtype) ∣
        Nat.card ((pairCharKernelTorus K₆ κ.i κ.j).map (baseChangeGL (algebraMap K₆ Ω))) :=
      Subgroup.card_dvd_of_le (by rw [← hcentD]; exact fun z hz => hZD z hz)
    rw [Subgroup.card_map_of_injective hinj] at e2
    rw [e1]
    exact Odd.of_dvd_nat hodd e2
  refine ⟨hSU, a, ha, hRQ, hRF.trans (by rw [hF]), ⟨e.trans e₂, fun u => ?_, fun g hg => ?_⟩,
    hRqs, hRqs.1, CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hRqs, hRbot, hcentD,
    hcenH, hoddD, P, fun A => ?_⟩
  · change baseChangeGL (algebraMap K₆ Ω) (e u : ModGL Tag.F4 K₆) = _
    rw [he u]
  · rw [MulEquiv.trans_apply, mulEquiv_apply_mem_center_iff, hcen g hg]
  · rw [hRF]
    exact ⟨_, hP A, rfl⟩

end CFSG.RankThree.Chevalley
