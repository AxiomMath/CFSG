module

public import CFSG.Milestones.ASVolI.F429.bC2c
public import CFSG.Milestones.ASVolI.F429.C6Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOneCard
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Rank

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem burnsideF429b_isElemAbelian_of {R : Subgroup G}
    (hc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (h2 : ∀ x ∈ R, x * x = 1) : IsElemAbelian 2 R :=
  ⟨isMulCommutative_iff_of_setLike.mpr hc, fun x hx => by rw [sq]; exact h2 x hx⟩

theorem burnsideF429b_isElemAbelian_map {H : Type*} [Group H] (φ : G →* H) {R : Subgroup G}
    (hc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (h2 : ∀ x ∈ R, x * x = 1) :
    IsElemAbelian 2 (R.map φ) := by
  refine burnsideF429b_isElemAbelian_of ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h2 x hx, map_one]

theorem burnsideF429b_card_le_two_mul [Finite G] {A S : Subgroup G} {t : G} (ht : t ∈ A)
    (h : ∀ a ∈ A, a ∉ S → t * a ∈ S) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
  classical
  let φ : A → Bool × ↥(A ⊓ S) := fun a =>
    if ha : (a : G) ∈ S then (false, ⟨a, a.2, ha⟩)
    else (true, ⟨t * a, A.mul_mem ht a.2, h a a.2 ha⟩)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    by_cases ha : (a : G) ∈ S <;> by_cases hb : (b : G) ∈ S
    · have e := congrArg (fun p => (p.2 : G)) hab
      simpa [φ, ha, hb] using e
    · have e := congrArg Prod.fst hab
      simp [φ, ha, hb] at e
    · have e := congrArg Prod.fst hab
      simp [φ, ha, hb] at e
    · have e := congrArg (fun p => (p.2 : G)) hab
      simpa [φ, ha, hb] using e
  calc Nat.card A ≤ Nat.card (Bool × ↥(A ⊓ S)) := Nat.card_le_card_of_injective φ hφ
    _ = 2 * Nat.card ↥(A ⊓ S) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

end Generic

section Transport

variable {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal] {C : Type} [Group C]

theorem burnsideF429b_conjAut_mul (Ψ : C ≃* ↥Gp) (x y : E) :
    (Ψ.trans (burnsideF4d_rho Gp (x * y))).trans Ψ.symm =
      (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm *
        (Ψ.trans (burnsideF4d_rho Gp y)).trans Ψ.symm := by
  refine MulEquiv.ext fun c => Ψ.injective (Subtype.ext ?_)
  rw [MulAut.mul_apply, burnsideF429b_conjAut_apply, burnsideF429b_conjAut_apply,
    burnsideF429b_conjAut_apply]
  group

theorem burnsideF429b_mem_of_conjAut_inner (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (Ψ : C ≃* ↥Gp) {e : E}
    (h : (Ψ.trans (burnsideF4d_rho Gp e)).trans Ψ.symm ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner C) : e ∈ Gp := by
  by_contra hG
  exact burnsideF429b_conjAut_not_inner hc Ψ hG h

theorem burnsideF429b_conjAut_fix (Ψ : C ≃* ↥Gp) {e : E} {y : C}
    (h : e * ((Ψ y : ↥Gp) : E) = ((Ψ y : ↥Gp) : E) * e) :
    (Ψ.trans (burnsideF4d_rho Gp e)).trans Ψ.symm y = y := by
  refine Ψ.injective (Subtype.ext ?_)
  rw [burnsideF429b_conjAut_apply, h]
  group

end Transport

section G2Rank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem burnsideF429b_G2_exists_R0 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ R : Subgroup (H13.F431.G2.C K), R ≤ H13.F431.G2.U K ∧
      (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ (∀ x ∈ R, x * x = 1) ∧
      Nat.card K ^ 3 ≤ Nat.card R := by
  have hmul : ∀ ν β γ v b e : K, H13.F431.G2.nf 0 0 0 ν β γ * H13.F431.G2.nf 0 0 0 v b e =
      H13.F431.G2.nf 0 0 0 (ν + v) (β + b) (γ + e) := by
    intro ν β γ v b e
    rw [H13.F431.G2.nf_mul]
    exact H13.F431.G2.nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  let R : Subgroup (H13.F431.G2.C K) :=
    { carrier := {g | ∃ ν β γ : K, g = H13.F431.G2.nf 0 0 0 ν β γ}
      mul_mem' := by
        rintro _ _ ⟨ν, β, γ, rfl⟩ ⟨v, b, e, rfl⟩
        exact ⟨ν + v, β + b, γ + e, hmul ..⟩
      one_mem' := ⟨0, 0, 0, H13.F431.G2.nf_one.symm⟩
      inv_mem' := by
        rintro _ ⟨ν, β, γ, rfl⟩
        refine ⟨ν, β, γ, ?_⟩
        rw [H13.F431.G2.nf_inv]
        exact H13.F431.G2.nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) }
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨ν, β, γ, rfl⟩
    exact H13.F431.G2.nf_mem_U _ _ _ _ _ _
  · rintro _ ⟨ν, β, γ, rfl⟩ _ ⟨v, b, e, rfl⟩
    rw [hmul, hmul]
    exact H13.F431.G2.nf_congr rfl rfl rfl (add_comm _ _) (add_comm _ _) (add_comm _ _)
  · rintro _ ⟨ν, β, γ, rfl⟩
    rw [hmul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      H13.F431.G2.nf_one]
  · let φ : K × K × K → R := fun c =>
      ⟨H13.F431.G2.nf 0 0 0 c.1 c.2.1 c.2.2, c.1, c.2.1, c.2.2, rfl⟩
    have hφ : Function.Injective φ := by
      rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨-, -, -, h1, h2, h3⟩ := H13.F431.G2.nf_injective h'
      exact Prod.ext h1 (Prod.ext h2 h3)
    calc Nat.card K ^ 3 = Nat.card (K × K × K) := by rw [Nat.card_prod, Nat.card_prod]; ring
      _ ≤ Nat.card R := Nat.card_le_card_of_injective φ hφ

theorem burnsideF429b_G2_card_abelian_le_U {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Subgroup (H13.F431.G2.C F)} (hE : E ≤ H13.F431.G2.U F)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ Nat.card F ^ 4 := by
  haveI : Finite (ModGL Tag.G2 F) := finite_modGL
  have h1 : Nat.card ↥(H13.F431.G2.Q1 F ⊓ E) ≤ Nat.card F ^ 3 :=
    H13.F431.G2.card_abelian_le_Q1 inf_le_left (fun x hx y hy => hab x hx.2 y hy.2)
  have hQU : H13.F431.G2.Q1 F ≤ H13.F431.G2.U F := H13.F431.G2.Q1_le_U
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hidx : (H13.F431.G2.Q1 F).relIndex (H13.F431.G2.U F) = Nat.card F := by
    have e := Subgroup.relIndex_mul_card (H13.F431.G2.Q1 F) (H13.F431.G2.U F)
    rw [inf_eq_left.2 hQU, H13.F431.G2.card_Q1, H13.F431.G2.card_U] at e
    have hpos5 : 0 < Nat.card F ^ 5 := pow_pos hpos 5
    exact Nat.eq_of_mul_eq_mul_right hpos5 (e.trans (by ring))
  have hne : (H13.F431.G2.Q1 F).relIndex (H13.F431.G2.U F) ≠ 0 := by
    rw [hidx]
    exact hpos.ne'
  have h2 : (H13.F431.G2.Q1 F).relIndex E ≤ Nat.card F :=
    (Subgroup.relIndex_le_of_le_right hE hne).trans hidx.le
  calc Nat.card E = (H13.F431.G2.Q1 F).relIndex E * Nat.card ↥(H13.F431.G2.Q1 F ⊓ E) :=
        (Subgroup.relIndex_mul_card _ _).symm
    _ ≤ Nat.card F * Nat.card F ^ 3 := Nat.mul_le_mul h2 h1
    _ = Nat.card F ^ 4 := by ring

theorem burnsideF429b_G2_card_elemAb_le {F : Type} [Field F] [Finite F] [CharP F 2]
    (E : Subgroup (H13.F431.G2.C F)) (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card F ^ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL Tag.G2 F) := finite_modGL
  obtain ⟨-, hp, hi⟩ := CFSG.Quasithin.H13.Sec53F.G2.g2_sylow (K := F)
  have hi' : ¬ 2 ∣ (posUnipotentSub Tag.G2 F).index := by
    rw [← Subgroup.relIndex_top_right]
    exact hi
  refine CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.rank_le_of_sylow
    (hp.toSylow hi') (fun B hBc _ => ?_) E hab h2
  have h := burnsideF429b_G2_card_abelian_le_U
    (E := B.map (hp.toSylow hi' : Subgroup (H13.F431.G2.C F)).subtype) ?_ ?_
  · rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBc x hx y hy]

theorem burnsideF429b_G2_card_fixed_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (B : Subgroup (H13.F431.G2.C K)) (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ B, x * x = 1)
    (hfix : ∀ x ∈ B, Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.G2 K) = x) :
    Nat.card B ≤ Nat.card (fixSubfield σ) ^ 4 := by
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hι := adjointBaseChangeHom_injective Tag.G2 (fixSubfield σ).subtype
  have hrange : B ≤ (adjointBaseChangeHom Tag.G2 (fixSubfield σ).subtype).range := by
    intro x hx
    have hxJ : (x : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 σ := by
      rw [← CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage
        σ]
      exact mem_entrywiseFixedGroup.2 ⟨x.2, hfix x hx⟩
    obtain ⟨y, hy, hyx⟩ := hxJ
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hcard : Nat.card (B.comap (adjointBaseChangeHom Tag.G2 (fixSubfield σ).subtype)) =
      Nat.card B := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hrange]
  rw [← hcard]
  exact burnsideF429b_G2_card_elemAb_le _
    (fun x hx y hy => hι (by rw [map_mul, map_mul]; exact hab _ hx _ hy))
    (fun x hx => hι (by rw [map_mul, map_one]; exact h2 _ hx))

theorem burnsideF429b_G2_fieldAut_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {g : H13.F431.G2.C K}
    (hg : g ∈ Subgroup.normalizer (posUnipotentSub Tag.G2 K : Set (H13.F431.G2.C K)))
    (σ : K ≃+* K)
    (hfix : ∀ s : K, g * CFSG.Quasithin.H13.Sec53F.G2.fieldAut K σ (H13.F431.G2.xc s) * g⁻¹ =
      H13.F431.G2.xc s) : σ = 1 := by
  obtain ⟨u, hu, h, hh, rfl⟩ := CFSG.Quasithin.H13.Sec53F.G2.g2_B_eq g hg
  obtain ⟨l, -, hl⟩ : ((u * h : H13.F431.G2.C K) : ModGL Tag.G2 K) ∈
      H13.F431.G2.Cent.XcScalars K :=
    mul_mem (H13.F431.G2.Cent.posUnipotent_le_XcScalars hu)
      (H13.F431.G2.Cent.torusGroup_le_XcScalars hh)
  have hl' : ∀ s : K, u * h * H13.F431.G2.xc s * (u * h)⁻¹ = H13.F431.G2.xc (l * s) := fun s =>
    Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, H13.F431.G2.coe_xc] using hl s)
  have key : ∀ s : K, l * σ s = s := by
    intro s
    have e1 : CFSG.Quasithin.H13.Sec53F.G2.fieldAut K σ (H13.F431.G2.xc s) =
        H13.F431.G2.xc (σ s) := H13.F431.G2.fieldAut_xe σ _ s
    have e := hfix s
    rw [e1] at e
    exact H13.F431.G2.xc_injective ((hl' (σ s)).symm.trans e)
  have hl1 : l = 1 := by simpa using key 1
  exact RingEquiv.ext fun s => by simpa [hl1] using key s

end G2Rank

section C6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem burnsideF429b_c6_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .G2 f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, hcard, Ψ, -, hB⟩ := burnsideF429b_G2_chartB hyp.toHypF_4_4g
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set φ : H13.F431.G2.C K →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (borelSub Tag.G2 K).map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : S = (H13.F431.G2.U K).map φ := by
    rw [hSdef, hGB, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ hφ,
      burnsideF429b_G2_pCoreOf_borel]
  have hmemS : ∀ x, x ∈ T → x ∈ Gp → x ∈ S := fun x hx hg => by
    rw [hSdef, ← burnsideF429_T_inf_Gp hyp hT]
    exact ⟨hx, hg⟩
  have hc := hyp.centralizer_trivial
  obtain ⟨R₀, hR₀U, hR₀c, hR₀2, hR₀card⟩ := burnsideF429b_G2_exists_R0 K
  have hRcard : Nat.card K ^ 3 ≤ Nat.card ↥(R₀.map φ) := by
    rwa [Subgroup.card_map_of_injective hφ]
  refine burnsideF429_c6_of' (R := R₀.map φ) (W := (H13.F431.G2.Xc K).map φ)
    (burnsideF429_sbar_le hT) ?_ (burnsideF429b_isElemAbelian_map φ hR₀c hR₀2) ?_ ?_ ?_ ?_ ?_
  ·
    rw [← hSdef, hS]
    exact Subgroup.map_mono hR₀U
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.1 hAS
    have hinvA : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAe.2 a ha
    have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    have hnotG : ∀ a ∈ A, a ∉ S → a ∉ Gp := fun a ha haS haG => haS (hmemS a (hAT ha) haG)
    obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K
        hcard
    have hα2 : ∀ a ∈ A, ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) ^ 2 = 1 :=
      fun a ha => by rw [sq]; exact burnsideF429b_conjAut_sq Ψ (hinvA a ha)
    have hΘ : ∀ a ∈ A, a ∉ S →
        (∀ c, Θ ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) c = c ^ 2 ^ (f / 2)) ∧
        Nat.card (fixSubfield (Θ ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm))) =
          2 ^ (f / 2) := by
      intro a ha haS
      rcases hinv _ (hα2 a ha) with h1 | ⟨-, hc', hk⟩
      · exfalso
        apply burnsideF429b_conjAut_not_inner hc Ψ (hnotG a ha haS)
        show _ ∈ (MulAut.conj : H13.F431.G2.C K →* MulAut (H13.F431.G2.C K)).range
        rw [← hker]
        exact MonoidHom.mem_ker.2 h1
      · exact ⟨hc', hk⟩
    have h1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
      refine burnsideF429b_card_le_two_mul htA fun a ha haS => ?_
      refine hmemS _ (hAT (A.mul_mem htA ha)) (burnsideF429b_mem_of_conjAut_inner hc Ψ ?_)
      show _ ∈ (MulAut.conj : H13.F431.G2.C K →* MulAut (H13.F431.G2.C K)).range
      rw [← hker, MonoidHom.mem_ker, burnsideF429b_conjAut_mul, map_mul]
      have e : Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm) =
          Θ ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) :=
        RingEquiv.ext fun c => by rw [(hΘ t htA htS).1, (hΘ a ha haS).1]
      rw [e, ← map_mul, ← sq, hα2 a ha, map_one]
    obtain ⟨hev, δ, β, k, hδ, hβ, hαk⟩ := burnsideF429b_G2_outer_involution hf K hcard _
      (burnsideF429b_conjAut_sq Ψ (hinvA t htA))
      (burnsideF429b_conjAut_not_inner hc Ψ (hnotG t htA htS))
    have hσδ : (Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm)).toRingHom = δ :=
      RingHom.ext fun c => by
        show Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm) c = δ c
        rw [(hΘ t htA htS).1, hδ]
    have hle : A ⊓ S ≤ φ.range := fun y hy => by
      have hy' : y ∈ (H13.F431.G2.U K).map φ := hS ▸ hy.2
      obtain ⟨u, -, rfl⟩ := hy'
      exact ⟨u, rfl⟩
    have hBcard : Nat.card ↥(((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) =
        Nat.card ↥(A ⊓ S) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective,
        ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hle]
    have hB2 := burnsideF429b_G2_card_fixed_le (Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm))
      (((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) ?_ ?_ ?_
    · obtain ⟨m, hm⟩ := hev
      have hf2 : f / 2 = m := by omega
      calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := h1
        _ = 2 * Nat.card ↥(((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) := by
            rw [hBcard]
        _ ≤ 2 * Nat.card (fixSubfield (Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm))) ^ 4 :=
            Nat.mul_le_mul_left 2 hB2
        _ = 2 ^ (4 * m + 1) := by rw [(hΘ t htA htS).2, hf2]; ring
        _ < 2 ^ (6 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ = Nat.card K ^ 3 := by rw [hcard, hm]; ring
        _ ≤ Nat.card ↥(R₀.map φ) := hRcard
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact hφ (by rw [map_mul, map_mul]; exact hcommA _ hx.1 _ hy.1)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have hxx : x * x = 1 := hφ (by rw [map_mul, map_one]; exact hinvA _ hx.1)
      rw [hxx, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      have hty : (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm y = y :=
        burnsideF429b_conjAut_fix Ψ (by rw [← hφx]; exact hcommA t htA _ hy.1)
      have e : MulAut.conj k (β ((MulAut.conj k)⁻¹ y)) = y := by
        rw [hαk, MulAut.mul_apply, MulAut.mul_apply] at hty
        exact hty
      have hβy : β (MulAut.conj k⁻¹ y) = MulAut.conj k⁻¹ y := by
        rw [map_inv MulAut.conj k]
        calc β ((MulAut.conj k)⁻¹ y) =
            (MulAut.conj k)⁻¹ (MulAut.conj k (β ((MulAut.conj k)⁻¹ y))) := by
              rw [MulAut.inv_apply_self]
          _ = (MulAut.conj k)⁻¹ y := by rw [e]
      show Units.map (entrywiseHom (Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm)).toRingHom)
          ((MulAut.conj k⁻¹ y : H13.F431.G2.C K) : ModGL Tag.G2 K) =
          ((MulAut.conj k⁻¹ y : H13.F431.G2.C K) : ModGL Tag.G2 K)
      rw [hσδ, ← hβ, hβy]
  ·
    rw [← hSdef, hS]
    exact Subgroup.map_mono H13.F431.G2.Xc_le_U
  ·
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hSdef, hS] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨s, rfl⟩ := H13.F431.G2.mem_Xc_iff.1 hw
    rw [← map_mul, ← map_mul, ← H13.F431.G2.xc_comm_U hu s]
  ·
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨s, rfl⟩ := H13.F431.G2.mem_Xc_iff.1 hw
    rw [← map_pow, sq, H13.F431.G2.xc_mul_self, map_one]
  ·
    rintro x ⟨hxT, hxW⟩
    have hx12 : x ∈ M₁ ⊓ M₂ := hT.1 hxT
    have hrN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hx12
    have hmemU : ∀ y : H13.F431.G2.C K, y ∈ posUnipotentSub Tag.G2 K ↔ φ y ∈ S := by
      intro y
      rw [hS]
      exact (Subgroup.mem_map_iff_mem hφ).symm
    have h1 : ∀ y, (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm y ∈ posUnipotentSub Tag.G2 K ↔
        y ∈ posUnipotentSub Tag.G2 K := by
      intro y
      rw [hmemU, hmemU, hφx, hφx, burnsideF429b_conjAut_apply]
      exact ((Subgroup.mem_normalizer_iff.1 hrN) _).symm
    obtain ⟨g, hg, τ, ⟨σ, rfl⟩, hβ⟩ :=
      (CFSG.Quasithin.H13.Sec53F.G2.borelAutData_g2 hf hcard).normal_form _ h1
    have hfix : ∀ s : K, g * CFSG.Quasithin.H13.Sec53F.G2.fieldAut K σ (H13.F431.G2.xc s) * g⁻¹ =
        H13.F431.G2.xc s := by
      intro s
      have e : (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm (H13.F431.G2.xc s) =
          H13.F431.G2.xc s := by
        refine burnsideF429b_conjAut_fix Ψ ?_
        rw [← hφx]
        exact (Subgroup.mem_centralizer_iff.1 hxW _
          ⟨_, H13.F431.G2.xc_mem_Xc s, rfl⟩).symm
      rw [hβ, MulAut.mul_apply, MulAut.conj_apply] at e
      exact e
    have hσ1 := burnsideF429b_G2_fieldAut_eq_one hg σ hfix
    rw [hσ1, map_one, mul_one] at hβ
    exact hmemS x hxT (burnsideF429b_mem_of_conjAut_inner hc Ψ ⟨g, hβ.symm⟩)

end C6

end CFSG.ASVolI
