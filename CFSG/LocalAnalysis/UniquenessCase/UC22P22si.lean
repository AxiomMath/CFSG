module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellImage
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.C118NoOuterAlg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender

namespace P22si

variable {G : Type} [Group G]

@[expose] noncomputable def act {R W₁ : Subgroup G} (h : R ≤ normalizer (W₁ : Set G)) : ↥R →* MulAut ↥W₁ :=
  W₁.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem act_coe {R W₁ : Subgroup G} (h : R ≤ normalizer (W₁ : Set G)) (g : ↥R) (u : ↥W₁) :
    ((act h g u : ↥W₁) : G) = (g : G) * u * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

end P22si

open P22si

theorem uc22p22si_inner {G : Type} [Group G] [Finite G] {R L W₁ W₀ : Subgroup G}
    {F : Type} [Field F] [Fintype F] {e : ℕ} (hF : Fintype.card F = 2 ^ e) (he : 2 ≤ e)
    (hR : IsPGroup 2 R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hRW₁ : R ≤ Subgroup.normalizer (W₁ : Set G)) (hRW₀ : R ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₁R : W₁ ≤ R) (hW₁e : CFSG.Open.IsElemAbelian 2 W₁)
    (hLW₁ : L ≤ Subgroup.normalizer (W₁ : Set G))
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : ↥W₁ →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβker : β.ker = W₀.subgroupOf W₁)
    (hβα : ∀ (l : ↥L) (u v : ↥W₁), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (α l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hfaith : ∀ r ∈ R, (∀ u v : ↥W₁, (v : G) = r * u * r⁻¹ → β v = β u) →
      r ∈ Subgroup.centralizer (W₁ : Set G))
    (hJ : ⁅CFSG.Quasithin.thompsonJ R, W₁⁆ ≠ ⊥) :
    ∀ b ∈ CFSG.Quasithin.baum R, ∃ l ∈ L, ∀ u v : ↥W₁,
      (v : G) = (l⁻¹ * b) * u * (l⁻¹ * b)⁻¹ → β v = β u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchp : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hcongr : ∀ (g : ↥R) (u v : ↥W₁), β u = β v → β (act hRW₁ g u) = β (act hRW₁ g v) := by
    intro g u v huv
    have h1 : u⁻¹ * v ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [hβker, Subgroup.mem_subgroupOf] at h1
    have h2 : (act hRW₁ g u)⁻¹ * (act hRW₁ g v) ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf]
      have h3 := (Subgroup.mem_normalizer_iff.mp (hRW₀ g.2) ((u⁻¹ * v : ↥W₁) : G)).mp h1
      have e : (act hRW₁ g u)⁻¹ * (act hRW₁ g v) = act hRW₁ g (u⁻¹ * v) := by
        simp [map_mul, map_inv]
      rw [e, act_coe hRW₁ g (u⁻¹ * v)]
      exact h3
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  obtain ⟨ρ, hadd, hact⟩ := exists_perm_action (act hRW₁) β hβ hcongr
  have hnorm : ∀ (g : ↥R) (A : Matrix.SpecialLinearGroup (Fin 2) F),
      ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v,
        ρ g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = (A' : Matrix (Fin 2) (Fin 2) F).mulVec (ρ g v) := by
    intro g A
    obtain ⟨l, rfl⟩ := hα A
    have hl' : (g : G) * l * (g : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRL g.2) l).mp l.2
    refine ⟨α ⟨_, hl'⟩, fun v => ?_⟩
    obtain ⟨u₀, hu₀⟩ := hβ (Multiplicative.ofAdd v)
    have hv : Multiplicative.toAdd (β u₀) = v := by rw [hu₀]; rfl
    have hm1 : (l : G) * u₀ * (l : G)⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hLW₁ l.2) u₀).mp u₀.2
    have hm2 : ((⟨_, hl'⟩ : ↥L) : G) * ((act hRW₁ g u₀ : ↥W₁) : G) * ((⟨_, hl'⟩ : ↥L) : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hLW₁ hl') _).mp (act hRW₁ g u₀).2
    rw [← hv, ← hβα l u₀ ⟨_, hm1⟩ rfl, hact, hact, ← hβα ⟨_, hl'⟩ (act hRW₁ g u₀) ⟨_, hm2⟩ rfl]
    congr 2
    apply Subtype.ext
    rw [act_coe]
    show (g : G) * ((l : G) * u₀ * (l : G)⁻¹) * (g : G)⁻¹ =
      ((g : G) * l * (g : G)⁻¹) * ((act hRW₁ g u₀ : ↥W₁) : G) * ((g : G) * l * (g : G)⁻¹)⁻¹
    rw [act_coe]
    group
  have hsem : ∀ g : ↥R, ∃ σ : F ≃+* F, IsSemilinearWith (ρ g) σ := fun g =>
    exists_semilinear_of_normalizes (ρ g) (hadd g) (hnorm g) (fun A => by
      rw [← map_inv]
      exact hnorm g⁻¹ A)
  obtain ⟨σ, hσ, hcocycle⟩ := exists_fieldHom ρ hadd hsem
  have hδ0 : ∀ p : ↥R, (semilinMatrix (ρ p)).det ≠ 0 :=
    fun p => semilinMatrix_det_ne_zero (hadd p) (hσ p)
  have hF1 : 1 < Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, hF]
    have : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  obtain ⟨u, hu⟩ := exists_rescale hR hF1 σ (fun p => (semilinMatrix (ρ p)).det) hδ0 hcocycle
  have hmem : ∀ p : ↥R, scalePerm u * ρ p * (scalePerm u)⁻¹ ∈ Gamma F :=
    fun p => scale_conj_mem_Gamma (hadd p) (hσ p) u (hu p)
  let ρ' : ↥R →* Gamma F :=
    (((MulAut.conj (scalePerm u : Equiv.Perm (Fin 2 → F))).toMonoidHom).comp ρ).codRestrict
      (Gamma F) hmem
  have hρ' : ∀ p : ↥R, ((ρ' p : Gamma F) : Equiv.Perm (Fin 2 → F)) =
      scalePerm u * ρ p * (scalePerm u)⁻¹ := fun p => rfl
  let V' : Subgroup ↥R := W₁.subgroupOf R
  have hVn : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hW₁R).mpr hRW₁
  have hVe : IsElementaryAbelian 2 V' :=
    BlueprintB2.isElementaryAbelian_subgroupOf
      ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mp hW₁e)
  let ι : ↥V' ≃* ↥W₁ := Subgroup.subgroupOfEquivOfLe hW₁R
  let sm : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    { toFun := fun x => Multiplicative.ofAdd ((u : F) • Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y => by simp [smul_add] }
  let φ : ↥V' →* Multiplicative (Fin 2 → F) := sm.comp (β.comp ι.toMonoidHom)
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨w, hw⟩ := hβ (Multiplicative.ofAdd (((u⁻¹ : Units F) : F) • Multiplicative.toAdd z))
    refine ⟨ι.symm w, ?_⟩
    show sm (β (ι (ι.symm w))) = z
    rw [MulEquiv.apply_symm_apply, hw]
    show Multiplicative.ofAdd ((u : F) • (((u⁻¹ : Units F) : F) • Multiplicative.toAdd z)) = z
    rw [smul_smul]
    simp
  have hφρ : ∀ (r : ↥R) (v v' : ↥V'), (v' : ↥R) = r * v * r⁻¹ →
      Multiplicative.toAdd (φ v') =
        ((ρ' r : Gamma F) : Equiv.Perm (Fin 2 → F)) (Multiplicative.toAdd (φ v)) := by
    intro r v v' hv
    have h1 : act hRW₁ r (ι v) = ι v' := by
      apply Subtype.ext
      rw [act_coe]
      have := congrArg (fun x : ↥R => (x : G)) hv
      have e1 : ((ι v : ↥W₁) : G) = ((v : ↥R) : G) := rfl
      have e2 : ((ι v' : ↥W₁) : G) = ((v' : ↥R) : G) := rfl
      rw [e1, e2]
      exact this.symm
    have h2 : ρ r (Multiplicative.toAdd (β (ι v))) = Multiplicative.toAdd (β (ι v')) := by
      rw [hact, h1]
    have e : ((u⁻¹ : Units F) : F) • ((u : F) • Multiplicative.toAdd (β (ι v))) =
        Multiplicative.toAdd (β (ι v)) := by
      rw [smul_smul, Units.inv_mul, one_smul]
    show (u : F) • Multiplicative.toAdd (β (ι v')) = _
    rw [hρ' r]
    simp only [Equiv.Perm.mul_apply, scalePerm_apply, scalePerm_inv_apply]
    show _ = (u : F) • ρ r (((u⁻¹ : Units F) : F) • ((u : F) • Multiplicative.toAdd (β (ι v))))
    rw [e, h2]
  have hρ1 : ∀ b : ↥R, ρ' b = 1 ↔ ρ b = 1 := by
    intro b
    constructor
    · intro h
      have h2 : scalePerm u * ρ b * (scalePerm u)⁻¹ = 1 := by
        rw [← hρ' b, h]
        rfl
      have h3 : scalePerm u * ρ b = scalePerm u := mul_inv_eq_one.mp h2
      exact mul_left_cancel (h3.trans (mul_one _).symm)
    · intro h
      apply Subtype.ext
      rw [hρ' b, h, mul_one, mul_inv_cancel]
      rfl
  have hker : ρ'.ker = Subgroup.centralizer (V' : Set ↥R) := by
    ext b
    rw [MonoidHom.mem_ker, hρ1, Subgroup.mem_centralizer_iff]
    constructor
    · intro hb v hv
      have h2 : (b : G) ∈ Subgroup.centralizer (W₁ : Set G) := by
        refine hfaith (b : G) b.2 fun u₁ v₁ huv => ?_
        have h3 := hact b u₁
        rw [hb, Equiv.Perm.one_apply] at h3
        have h4 : act hRW₁ b u₁ = v₁ := Subtype.ext (by rw [act_coe]; exact huv.symm)
        rw [h4] at h3
        exact Multiplicative.toAdd.injective h3.symm
      have hvW : (v : G) ∈ W₁ := Subgroup.mem_subgroupOf.mp hv
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h2 v hvW)
    · intro hb
      refine Equiv.ext fun x => ?_
      obtain ⟨w, hw⟩ := hβ (Multiplicative.ofAdd x)
      have hwx : Multiplicative.toAdd (β w) = x := by rw [hw]; rfl
      have hw' : act hRW₁ b w = w := by
        apply Subtype.ext
        rw [act_coe]
        have h3 := hb ⟨w, hW₁R w.2⟩ (Subgroup.mem_subgroupOf.mpr w.2)
        have h4 : (w : G) * b = b * w := congrArg (fun x : ↥R => (x : G)) h3
        calc (b : G) * w * (b : G)⁻¹ = ((w : G) * b) * (b : G)⁻¹ := by rw [h4]
          _ = w := by group
      rw [← hwx, hact, hw']
      rfl
  have hJ' : ⁅elemThompson ↥R 2, V'⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    have h1 := congrArg (Subgroup.map R.subtype) hbot
    rw [Subgroup.map_commutator, elemThompson_map_subtype_eq_thompsonJ R,
      Subgroup.map_subgroupOf_eq_of_le hW₁R, Subgroup.map_bot] at h1
    exact h1
  obtain ⟨ℓ, -, hBaum, -⟩ :=
    natural_quotient_internal_Thompson_Baumann_image hR V' hVe ρ' φ hφs hφρ hker hJ'
  intro b hb
  rw [← elemBaumann_map_subtype_eq_baum R] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  have hbR : ρ' b' ∈ (elemBaumann ↥R 2).map ρ' := ⟨b', hb', rfl⟩
  rw [hBaum] at hbR
  obtain ⟨A, hA⟩ := mem_slGamma_iff.mp (rootGamma_le_slGamma ℓ hbR)
  have hρbA : ∀ x, ρ b' x = (A : Matrix (Fin 2) (Fin 2) F).mulVec x := by
    intro x
    have hE : scalePerm u * ρ b' * (scalePerm u)⁻¹ = slPerm F A := (hρ' _).symm.trans hA
    have h1 := congrArg (fun g : Equiv.Perm (Fin 2 → F) => g ((u : F) • x)) hE
    simp only [Equiv.Perm.mul_apply, scalePerm_apply, scalePerm_inv_apply, slPerm_apply] at h1
    rw [smul_smul, Units.inv_mul, one_smul] at h1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_smul] at h1
    exact smul_right_injective _ (Units.ne_zero u) h1
  obtain ⟨l, hl⟩ := hα A
  refine ⟨(l : G), l.2, fun u₁ v₁ hv => ?_⟩
  have h1 : Multiplicative.toAdd (β (act hRW₁ b' u₁)) =
      (A : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u₁)) := by
    rw [← hact, hρbA]
  have h2 : (v₁ : G) = ((l⁻¹ : ↥L) : G) * ((act hRW₁ b' u₁ : ↥W₁) : G) * ((l⁻¹ : ↥L) : G)⁻¹ := by
    rw [hv, act_coe, Subgroup.coe_inv]
    simp only [Subgroup.coe_subtype]
    group
  have h3 := hβα l⁻¹ (act hRW₁ b' u₁) v₁ h2
  rw [map_inv, hl, h1, Matrix.mulVec_mulVec] at h3
  have h4 : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [h4, Matrix.one_mulVec] at h3
  exact Multiplicative.toAdd.injective h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
