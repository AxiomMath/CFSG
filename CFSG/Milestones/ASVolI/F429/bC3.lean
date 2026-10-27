module

public import CFSG.Milestones.ASVolI.F429.Base
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

theorem burnsideF429b_of_model {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {P₁ P₂ U : Subgroup C}
    (h1 : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom) (h2 : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom)
    (hU1 : ChF.IsSylowOf 2 U P₁) (hU2 : ChF.IsSylowOf 2 U P₂) (hc1 : U ≤ perfectCore P₁)
    (hc2 : U ≤ perfectCore P₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  exact ⟨burnsideF429_le_perfectCore_of_model Ψ h1 hU1 hc1
      (hSB.trans (inf_le_inf_left Gp inf_le_left)) hS2,
    burnsideF429_le_perfectCore_of_model Ψ h2 hU2 hc2
      (hSB.trans (inf_le_inf_left Gp inf_le_right)) hS2⟩

end Generic

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2


theorem burnsideF429b_G2_point_eq {K : Type} [Field K] :
    ChF.G2Native.pointParabolic K = H13.F431.G2.Cent.Pr K := by
  unfold ChF.G2Native.pointParabolic
  rw [show (-ChF.G2Native.simpleVector 1 : ChF.G2Native.Lattice) =
    -Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 from rfl, burnsideF4gG2_eq_Pmin]
  rfl

theorem burnsideF429b_G2_line_eq {K : Type} [Field K] :
    ChF.G2Native.lineParabolic K = H13.F431.G2.Cent.Pa K := by
  unfold ChF.G2Native.lineParabolic
  rw [show (-ChF.G2Native.simpleVector 0 : ChF.G2Native.Lattice) =
    -Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 from rfl, burnsideF4gG2_eq_Pmin]
  rfl

theorem burnsideF429b_G2_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : H13.F431.G2.C K ≃* ↥Gp,
        M₁.subgroupOf Gp = (H13.F431.G2.Cent.Pr K).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (H13.F431.G2.Cent.Pa K).map Ψ.toMonoidHom := by
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 h
  letI := fK
  haveI := finK
  haveI : CharP K 2 := burnsideF4f_charP_of_card h.model.2.1 hcard
  let Ψ : H13.F431.G2.C K ≃* ↥Gp := (H13.F431.G2.mk K).trans marking
  have hΨ : ∀ L : Subgroup (G2Native.Parent K),
      G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
    intro L
    unfold G2Native.fullImage G2Native.fullLocal
    rw [Subgroup.map_map]
    exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
  refine ⟨K, fK, finK, inferInstance, hcard, Ψ, ?_, ?_⟩
  · rw [h1, hΨ, burnsideF429b_G2_point_eq]
  · rw [h2, hΨ, burnsideF429b_G2_line_eq]

theorem burnsideF429b_G2_model {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) :
    ChF.IsSylowOf 2 (H13.F431.G2.U K) (H13.F431.G2.Cent.Pr K) ∧
      ChF.IsSylowOf 2 (H13.F431.G2.U K) (H13.F431.G2.Cent.Pa K) ∧
      H13.F431.G2.U K ≤ perfectCore (H13.F431.G2.Cent.Pr K) ∧
      H13.F431.G2.U K ≤ perfectCore (H13.F431.G2.Cent.Pa K) := by
  have hc1 : H13.F431.G2.U K ≤ perfectCore (H13.F431.G2.Cent.Pr K) := fun x hx =>
    (H13.Sec53F.G2.mem_perfectCore_subgroupOf (parabolicSubgroup_le_adjointGroup _ _ _) x).2
      (H13.Sec53F.G2.posUnipotent_le_perfectCore_one hK4 hx)
  have hc0 : H13.F431.G2.U K ≤ perfectCore (H13.F431.G2.Cent.Pa K) := fun x hx =>
    (H13.Sec53F.G2.mem_perfectCore_subgroupOf (parabolicSubgroup_le_adjointGroup _ _ _) x).2
      (H13.Sec53F.G2.posUnipotent_le_perfectCore_zero hK4 hx)
  exact ⟨F7.isSylowTwoOf_mono_right H13.F431.G2.Cent.isSylowTwoOf_U_top
      (hc1.trans (perfectCore_le _)) le_top, H13.F431.G2.Cent.isSylowTwoOf_U_Pa, hc1, hc0⟩

theorem burnsideF429b_c3_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨K, fK, finK, cK, hcard, Ψ, h1, h2⟩ := burnsideF429b_G2_chart hyp.toHypF_4_4g
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hU1, hU2, hc1, hc2⟩ := burnsideF429b_G2_model hK4
  exact burnsideF429b_of_model Ψ h1 h2 hU1 hU2 hc1 hc2

end G2

section D4Fields

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem burnsideF429b_D4_four_le_card {K : Type} {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) : 4 ≤ Nat.card K := by
  rw [hK]
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h2 3

theorem burnsideF429b_D4_four_le_fixed {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, -, -, -, -, k, hk, hcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two (by omega : 1 ≤ f) K hK
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσq
  have hkeq : trialityFixedField K σ.toRingHom = k := by
    apply SetLike.ext'
    rw [hk]
    ext c
    simp [mem_trialityFixedField, hσ']
  rw [hkeq, hcard]
  exact hq4

end D4Fields

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Quasithin.H13.F431.D4q.Struct


theorem burnsideF429b_D4_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .D4tw 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K),
      (∀ c, σ (σ (σ c)) = c) ∧ 1 ≤ f ∧ Nat.card K = (2 ^ f) ^ 3 ∧
      (∀ c, σ.toRingHom c = c ^ (2 ^ f)) ∧
      ∃ Ψ : Cm σ ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pst0 σ).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pst1 σ).map Ψ.toMonoidHom := by
  obtain ⟨K, fK, finK, sigma, scope, marking, h1, h2⟩ := burnsideF4g_chart_D4tw h
  obtain ⟨-, hf, hK, hσ⟩ := scope
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
    ⟨RingEquiv.ofBijective sigma
      ⟨sigma.injective, Finite.surjective_of_injective sigma.injective⟩, rfl⟩
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσ
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ'
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI hCharP : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hΓ := twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 (Or.inl hchar)
  obtain ⟨-, -, -, -, -, hD, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ'
  obtain ⟨e, he⟩ := burnsideF4gD4_exists_derivedEquiv _ _ hD hZ
  let φ : Cm σ ≃* ↥Gp := e.symm.trans marking
  have hmap0 : ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
      ((derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map marking.toMonoidHom) =
        (P.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := by
    intro P
    have hcomp : φ.toMonoidHom.comp e.toMonoidHom = marking.toMonoidHom := by
      refine MonoidHom.ext fun q => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, φ]
    rw [← burnsideF4gD4_map_derivedImage _ _ P hD e he, Subgroup.map_map, hcomp]
  have h0 := burnsideF4gD4_trialityParabolic_zero σ.toRingHom hΓ
  have h1' := burnsideF4gD4_trialityParabolic_one σ.toRingHom hΓ
  refine ⟨K, fK, finK, hCharP, σ, hσ3, hf, hK, hσ, φ, ?_, ?_⟩
  · calc M₁.subgroupOf Gp = _ := h1
      _ = ((trialityParabolic K σ.toRingHom 0).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := hmap0 _
      _ = (Pst0 σ).map φ.toMonoidHom := by rw [h0]; rfl
  · calc M₂.subgroupOf Gp = _ := h2
      _ = ((trialityParabolic K σ.toRingHom 1).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom := hmap0 _
      _ = (Pst1 σ).map φ.toMonoidHom := by rw [h1']; rfl

theorem burnsideF429b_D4_model {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f)) :
    ChF.IsSylowOf 2 (Ust σ) (Pst0 σ) ∧ ChF.IsSylowOf 2 (Ust σ) (Pst1 σ) ∧
      Ust σ ≤ perfectCore (Pst0 σ) ∧ (2 ≤ f → Ust σ ≤ perfectCore (Pst1 σ)) := by
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    RingHom.ext fun c => (ringHom_pow_three_apply σ.toRingHom c).trans (hσ c)
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK hσq
  have hP0C : graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
  have hP1C : graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedParabolic_le _ _ _ _
  have hUP0 : Ust σ ≤ Pst0 σ := hS.le₀.trans' Subgroup.le_normalizer
  have hUP1 : Ust σ ≤ Pst1 σ := hS.le₁.trans' Subgroup.le_normalizer
  refine ⟨burnsideF4gD4Inv_isSylowTwoOf_of_le hS.sylow hUP0,
    burnsideF4gD4Inv_isSylowTwoOf_of_le hS.sylow hUP1, ?_, ?_⟩
  · exact fun x hx => (CFSG.Quasithin.H13.Sec53F.TriD4.mem_perfectCore_subgroupOf hP0C x).2
      (CFSG.Quasithin.H13.Sec53F.TriD4.posUnipotent_le_perfectCore_P0 σ hσ3
        (burnsideF429b_D4_four_le_card hf hK) (Subgroup.mem_subgroupOf.1 hx))
  · exact fun hf2 x hx => (CFSG.Quasithin.H13.Sec53F.TriD4.mem_perfectCore_subgroupOf hP1C x).2
      (CFSG.Quasithin.H13.Sec53F.TriD4.posUnipotent_le_perfectCore_P1 σ hσ3
        (burnsideF429b_D4_four_le_fixed σ hf2 hK hσq) (Subgroup.mem_subgroupOf.1 hx))

theorem burnsideF429b_c3_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  obtain ⟨hU0, hU1, hc0, hc1⟩ := burnsideF429b_D4_model σ hσ3 hf1 hK hσq
  exact burnsideF429b_of_model Ψ h1 h2 hU0 hU1 hc0 (hc1 hf)

theorem burnsideF429b_c8_D4tw_left {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) := by
  haveI := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, -⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  obtain ⟨hU0, -, hc0, -⟩ := burnsideF429b_D4_model σ hσ3 hf1 hK hσq
  exact burnsideF429_le_perfectCore_of_model Ψ h1 hU0 hc0
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_inf_left Gp inf_le_left))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem burnsideF429b_c8_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∨
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  Or.inl (burnsideF429b_c8_D4tw_left hyp)

end D4

section F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4


theorem burnsideF429b_F4_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .F4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime) (a : ℕ), 1 ≤ a ∧
      Nat.card K = 2 ^ (2 * a + 1) ∧
      ∃ Ψ : Gm K a ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pg K a ⟨1, by decide⟩).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pg K a ⟨0, by decide⟩).map Ψ.toMonoidHom := by
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, h1, h2⟩ := burnsideF4g_chart_F4tw h
  letI := fK
  haveI := finK
  have ha : 1 ≤ a := by omega
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Inv_exists_iso ha hK marking
  refine ⟨K, fK, finK, inferInstance, a, ha, hK, Φ, h1.trans (hΦ _ _ fun y => ?_),
    h2.trans (hΦ _ _ fun y => ?_)⟩
  · rw [burnsideF4gF4Inv_reeParabolic_one_eq]
    exact Subgroup.mem_subgroupOf
  · rw [burnsideF4gF4Inv_reeParabolic_zero_eq]
    exact Subgroup.mem_subgroupOf

theorem burnsideF429b_F4_model {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ChF.IsSylowOf 2 (Ug K a) (Pg K a ⟨1, by decide⟩) ∧
      ChF.IsSylowOf 2 (Ug K a) (Pg K a ⟨0, by decide⟩) ∧
      Ug K a ≤ perfectCore (Pg K a ⟨1, by decide⟩) ∧
      Ug K a ≤ perfectCore (Pg K a ⟨0, by decide⟩) := by
  have hc : ∀ j : Fin F4.fixedOrbitCount,
      F4.reeFixedPosUnipotent K a ≤ perfectCore (F4.reeLocalParabolic K a j) →
        Ug K a ≤ perfectCore (Pg K a j) := fun j h x hx =>
    (CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma j) x).2
      (h (Subgroup.mem_subgroupOf.1 hx))
  have hc1 := hc _ (CFSG.Quasithin.H13.Sec53F.ReeF4.reeFixedPosUnipotent_le_perfectCore_one ha hK)
  have hc0 := hc _ (CFSG.Quasithin.H13.Sec53F.ReeF4.reeFixedPosUnipotent_le_perfectCore_zero ha hK)
  exact ⟨F7.isSylowTwoOf_mono_right (isSylowTwoOf_Ug hK) (hc1.trans (perfectCore_le _)) le_top,
    F7.isSylowTwoOf_mono_right (isSylowTwoOf_Ug hK) (hc0.trans (perfectCore_le _)) le_top, hc1, hc0⟩

theorem burnsideF429b_c3_F4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨K, fK, finK, cK, a, ha, hK, Ψ, h1, h2⟩ := burnsideF429b_F4_chart hyp.toHypF_4_4g hf
  obtain ⟨hU1, hU0, hc1, hc0⟩ := burnsideF429b_F4_model ha hK
  exact burnsideF429b_of_model Ψ h1 h2 hU1 hU0 hc1 hc0

end F4

end CFSG.ASVolI
