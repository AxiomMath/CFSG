module

public import CFSG.Milestones.ASVolI.F429.bC4C2
public import CFSG.Milestones.ASVolI.F429.bC5
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

section Aut

variable {Y : Type} [Group Y]

theorem burnsideF429b_inner_conj_of_conj {α β ψ S : MulAut Y} {h : Y}
    (hψ : ψ = MulAut.conj h * S) (hSβ : S * β = β * S) (hconj : ψ * α * ψ⁻¹ = β) :
    α = MulAut.conj (S⁻¹ h⁻¹) * β * (MulAut.conj (S⁻¹ h⁻¹))⁻¹ := by
  have e1 : ψ⁻¹ = MulAut.conj (S⁻¹ h⁻¹) * S⁻¹ := by
    rw [hψ, mul_inv_rev, ← map_inv MulAut.conj h, burnsideF429b_mul_conj]
  have e2 : ψ = S * (MulAut.conj (S⁻¹ h⁻¹))⁻¹ := by
    rw [hψ, ← map_inv MulAut.conj, ← map_inv S⁻¹ h⁻¹, inv_inv, burnsideF429b_mul_conj,
      MulAut.apply_inv_self]
  have hSβ' : S⁻¹ * β * S = β := by
    rw [mul_assoc, ← hSβ, ← mul_assoc, inv_mul_cancel, one_mul]
  calc α = ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ := by group
    _ = ψ⁻¹ * β * ψ := by rw [hconj]
    _ = MulAut.conj (S⁻¹ h⁻¹) * (S⁻¹ * β * S) * (MulAut.conj (S⁻¹ h⁻¹))⁻¹ := by
        rw [e1, e2]
        simp only [mul_assoc]
    _ = _ := by rw [hSβ']

end Aut

variable {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal] {C : Type} [Group C]

theorem burnsideF429b_conjAut_apply (Ψ : C ≃* ↥Gp) (t : E) (x : C) :
    ((Ψ (((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm) x) : ↥Gp) : E) =
      t * ((Ψ x : ↥Gp) : E) * t⁻¹ := by
  show ((Ψ (Ψ.symm (burnsideF4d_rho Gp t (Ψ x))) : ↥Gp) : E) = _
  rw [MulEquiv.apply_symm_apply]
  exact burnsideF4d_rho_apply t (Ψ x)

theorem burnsideF429b_conjAut_sq (Ψ : C ≃* ↥Gp) {t : E} (ht : t * t = 1) :
    (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm *
      (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm = 1 := by
  refine MulEquiv.ext fun x => Ψ.injective (Subtype.ext ?_)
  rw [MulAut.mul_apply, burnsideF429b_conjAut_apply, burnsideF429b_conjAut_apply,
    MulAut.one_apply]
  calc t * (t * ((Ψ x : ↥Gp) : E) * t⁻¹) * t⁻¹ = (t * t) * ((Ψ x : ↥Gp) : E) * (t * t)⁻¹ := by
        group
    _ = ((Ψ x : ↥Gp) : E) := by rw [ht]; group

theorem burnsideF429b_conjAut_not_inner (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (Ψ : C ≃* ↥Gp) {t : E} (ht : t ∉ Gp) :
    (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
  rintro ⟨g, hg⟩
  apply ht
  have hρ : burnsideF4d_rho Gp t = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply, ← burnsideF429b_conjAut_apply Ψ t x, ← hg,
      MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  rw [burnsideF4d_rho_injective hc hρ]
  exact (Ψ g).2

theorem burnsideF429b_conjAut_rep (Ψ : C ≃* ↥Gp) {t : E} {β : MulAut C} {k : C}
    (hα : (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm =
      MulAut.conj k * β * (MulAut.conj k)⁻¹) (x : C) :
    ((MulAut.conj (Ψ k) (Ψ (β x)) : ↥Gp) : E) =
      t * ((MulAut.conj (Ψ k) (Ψ x) : ↥Gp) : E) * t⁻¹ := by
  have e : ∀ y, MulAut.conj (Ψ k) (Ψ y) = Ψ (k * y * k⁻¹) := fun y => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hx : (MulAut.conj k * β * (MulAut.conj k)⁻¹) (k * x * k⁻¹) = k * β x * k⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply,
      show k⁻¹ * (k * x * k⁻¹) * k = x by group, MulAut.conj_apply]
  rw [e, e, ← hx, ← hα]
  exact burnsideF429b_conjAut_apply Ψ t _

end Generic

section Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem burnsideF429b_G2_outer_involution {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .G2 K)) (hα2 : α * α = 1)
    (hαo : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K)) :
    Even f ∧ ∃ (δ : K →+* K) (β : MulAut (adjointGroup .G2 K)) (k : adjointGroup .G2 K),
      (∀ c, δ c = c ^ 2 ^ (f / 2)) ∧
      (∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K)) ∧
      α = MulAut.conj k * β * (MulAut.conj k)⁻¹ := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα1 : α ≠ 1 := fun h =>
    hαo (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  rcases CFSG.ComponentClassification.UnbalancedCatalog.even_G2_involution_inner_or_canonical_field
    hf K hK α hord with hin | ⟨hev, hall⟩
  · exact absurd hin hαo
  set δ : K →+* K := iterateFrobenius K 2 (f / 2) with hδdef
  have hδ : ∀ c, δ c = c ^ 2 ^ (f / 2) := fun c => by rw [hδdef, iterateFrobenius_def]
  obtain ⟨β, ψ, hβ, hψα, -⟩ := hall δ hδ
  obtain ⟨hNF, -⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
    hf K hK
  obtain ⟨⟨h, σ'⟩, hhσ, -⟩ := hNF ψ
  dsimp only at hhσ
  obtain ⟨S, hSdef⟩ : ∃ S : MulAut (adjointGroup .G2 K), S = MulAut.conj h⁻¹ * ψ := ⟨_, rfl⟩
  have hS : ∀ u, (S u : ModGL .G2 K) =
      Units.map (entrywiseHom σ'.toRingHom) (u : ModGL .G2 K) := by
    intro u
    rw [hSdef, MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hhσ u]
    group
  have hψS : ψ = MulAut.conj h * S := by
    rw [hSdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hcomm : σ'.toRingHom.comp δ = δ.comp σ'.toRingHom := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hδ, hδ, map_pow]
  have hSβ : S * β = β * S := by
    refine MulEquiv.ext fun u => Subtype.ext (Units.ext ?_)
    rw [MulAut.mul_apply, MulAut.mul_apply, hS, hβ, hβ, hS]
    simp only [Units.coe_map]
    show entrywise σ'.toRingHom (entrywise δ _) = entrywise δ (entrywise σ'.toRingHom _)
    rw [entrywise_entrywise, entrywise_entrywise, hcomm]
  exact ⟨hev, δ, β, S⁻¹ h⁻¹, hδ, hβ, burnsideF429b_inner_conj_of_conj hψS hSβ hψα⟩

theorem burnsideF429b_D4_outer_involution {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα2 : α * α = 1)
    (hαo : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Even f ∧ ∃ (δ : K ≃+* K) (k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ c, δ c = c ^ (2 ^ (3 * f / 2))) ∧
      (∀ g, ((fieldActor σ δ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) g) ∧
      α = MulAut.conj k * fieldActor σ δ * (MulAut.conj k)⁻¹ := by
  obtain ⟨hev, δ, hδ, hcoe, ψ, hψα, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ α (by rw [sq]; exact hα2) hαo
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  obtain ⟨⟨h, ε⟩, hhε, -⟩ := hNF ψ
  change ψ = MulAut.conj h * fieldActor σ ε at hhε
  have hcomm : fieldActor σ ε * fieldActor σ δ =
      fieldActor σ δ * fieldActor (t := TwistTag.D4) σ ε := by
    rw [← fieldActor_mul, ← fieldActor_mul,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K ε δ]
  exact ⟨hev, δ, (fieldActor σ ε)⁻¹ h⁻¹, hδ, hcoe,
    burnsideF429b_inner_conj_of_conj hhε hcomm hψα⟩

end Models

section C2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem burnsideF429b_c2c_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t := by
  haveI := hyp.normal
  intro t htT htS ht2
  have htG : t ∉ Gp := fun h =>
    htS (by rw [← burnsideF429_T_inf_Gp hyp hT]; exact ⟨htT, h⟩)
  refine ⟨htG, ht2, ?_⟩
  generalize hyp.toHypF_4_4g.chart.coordinatePayload = cp
  cases cp with
  | classical c hk mk => exact absurd hk (by cases c <;> decide)
  | g2 kind_eq prime_ok degree_pos K card ι =>
    let Ψ : adjointGroup .G2 K ≃* ↥Gp := (H13.F431.G2.mk K).trans ι
    obtain ⟨⟨e, he⟩, δ, β, k, hδ, hβ, hαk⟩ := burnsideF429b_G2_outer_involution hf K card _
      (burnsideF429b_conjAut_sq Ψ ht2)
      (burnsideF429b_conjAut_not_inner hyp.centralizer_trivial Ψ htG)
    refine ⟨e, by omega, by omega, MulAut.conj (Ψ k), ⟨Ψ k, rfl⟩, δ, fun c => ?_, ?_⟩
    · rw [hδ, show f / 2 = e by omega]
    · intro r
      refine ⟨β r, ?_, ?_⟩
      · show ((β r : ModGL .G2 K) : Module.End K (RootModule .G2 K)) =
          entrywise δ ((r : ModGL .G2 K) : Module.End K (RootModule .G2 K))
        rw [hβ r, Units.coe_map]
        rfl
      · exact burnsideF429b_conjAut_rep Ψ hαk r
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

theorem burnsideF429b_c2_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C2 .G2 f Gp M₁ M₂ hyp T := by
  obtain ⟨h1, h2⟩ := burnsideF429b_c2ab_G2 hyp hf hT
  exact ⟨h1, h2, fun t ht hS h2 => Or.inl (burnsideF429b_c2c_G2 hyp hf hT t ht hS h2)⟩

theorem burnsideF429b_c2c_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
      hyp.toHypF_4_4g.chart.IsFieldInv t := by
  haveI := hyp.normal
  intro t htT htS ht2
  have htG : t ∉ Gp := fun h =>
    htS (by rw [← burnsideF429_T_inf_Gp hyp hT]; exact ⟨htT, h⟩)
  refine ⟨htG, ht2, ?_⟩
  generalize hyp.toHypF_4_4g.chart.coordinatePayload = cp
  cases cp with
  | classical c hk mk => exact absurd hk (by cases c <;> decide)
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq K sigma scope ι =>
    obtain ⟨-, hf, hK, hσ⟩ := scope
    obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
      ⟨RingEquiv.ofBijective sigma
        ⟨sigma.injective, Finite.surjective_of_injective sigma.injective⟩, rfl⟩
    have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσ
    obtain ⟨-, -, -, -, -, hD, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ'
    obtain ⟨e, he⟩ := burnsideF4gD4_exists_derivedEquiv _ _ hD hZ
    let Ψ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* ↥Gp := e.symm.trans ι
    obtain ⟨⟨m, hm⟩, δ, k, hδ, hcoe, hαk⟩ := burnsideF429b_D4_outer_involution hf K hK σ hσ' _
      (burnsideF429b_conjAut_sq Ψ ht2)
      (burnsideF429b_conjAut_not_inner hyp.centralizer_trivial Ψ htG)
    refine ⟨m, by omega, by omega, MulAut.conj (Ψ k), ⟨Ψ k, rfl⟩, δ.toRingHom, fun c => ?_, ?_⟩
    · show δ c = _
      rw [hδ, show 3 * f / 2 = 3 * m by omega]
    · intro r
      have hcr : ((e (QuotientGroup.mk r) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) = (r : ModGL TwistTag.D4.tag K) := he r
      have hmem : ((fieldActor σ δ (e (QuotientGroup.mk r)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
          ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
            twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆ := by
        exact hD.ge (fieldActor σ δ (e (QuotientGroup.mk r))).2
      refine ⟨⟨_, hmem⟩, ?_, ?_⟩
      · show (((fieldActor σ δ (e (QuotientGroup.mk r)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) :
              Module.End K (RootModule TwistTag.D4.tag K)) =
          entrywise δ.toRingHom ((r : ModGL TwistTag.D4.tag K) :
            Module.End K (RootModule TwistTag.D4.tag K))
        rw [hcoe, Units.coe_map, hcr]
        rfl
      · have he' : e (QuotientGroup.mk ⟨_, hmem⟩) = fieldActor σ δ (e (QuotientGroup.mk r)) :=
          Subtype.ext (he _)
        have h1 : ι (QuotientGroup.mk ⟨_, hmem⟩) =
            Ψ (fieldActor σ δ (e (QuotientGroup.mk r))) :=
          congrArg ι (e.symm_apply_eq.2 he'.symm).symm
        have h2 : ι (QuotientGroup.mk r) = Ψ (e (QuotientGroup.mk r)) :=
          (congrArg ι (e.symm_apply_apply _)).symm
        show ((MulAut.conj (Ψ k) (ι (QuotientGroup.mk ⟨_, hmem⟩)) : ↥Gp) : E) =
          t * ((MulAut.conj (Ψ k) (ι (QuotientGroup.mk r)) : ↥Gp) : E) * t⁻¹
        rw [h1, h2]
        exact burnsideF429b_conjAut_rep Ψ hαk _
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

theorem burnsideF429b_c2_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    burnsideF429_C2 .D4tw f Gp M₁ M₂ hyp T := by
  obtain ⟨h1, h2⟩ := burnsideF429b_c2ab_D4tw hyp hT
  exact ⟨h1, h2, fun t ht hS h2 => Or.inl (burnsideF429b_c2c_D4tw hyp hT t ht hS h2)⟩

end C2

end CFSG.ASVolI
