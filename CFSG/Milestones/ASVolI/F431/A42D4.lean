module

public import CFSG.Milestones.ASVolI.F431.A42Engine
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qYam
public import CFSG.LieType.BorelTits.AllModels
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutSection
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Complete
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section D4

set_option linter.unusedSectionVars false


section Chart

open CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots

theorem burnsideF4m_A42_chart_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (chart : NativeChart .D4tw 2 f Gp) (hm : chart.Matches M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K)
      (hσ3 : ∀ c, σ (σ (σ c)) = c), 1 ≤ f ∧ Nat.card K = (2 ^ f) ^ 3 ∧
      (∀ c, σ.toRingHom c = c ^ (2 ^ f)) ∧
      ∃ φ : Cm σ ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pst0 σ).map φ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pst1 σ).map φ.toMonoidHom ∧
        chart.shortRoot = ((burnsideF4gD4Inv_SC σ).map φ.toMonoidHom).map Gp.subtype := by
  rcases chart.coordinates with
    ⟨c, hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, -, -, K, fK, finK, sigma, scope, marking, -, h2, h3, h4, h5⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · cases c <;> simp [classicalKind] at hk
  · cases hk
  · cases hk
  · obtain ⟨-, hf, hK, hσ⟩ := scope
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
    have hmap : ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
        ((derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map marking.toMonoidHom) =
          (P.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            (e.symm.trans marking).toMonoidHom := by
      intro P
      have hcomp : (e.symm.trans marking).toMonoidHom.comp e.toMonoidHom =
          marking.toMonoidHom := by
        refine MonoidHom.ext fun q => ?_
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [← burnsideF4gD4_map_derivedImage _ _ P hD e he, Subgroup.map_map, hcomp]
    have h0 := burnsideF4gD4_trialityParabolic_zero σ.toRingHom hΓ
    have h1 := burnsideF4gD4_trialityParabolic_one σ.toRingHom hΓ
    refine ⟨K, fK, finK, hCharP, σ, hσ3, hf, hK, hσ, e.symm.trans marking, ?_, ?_, ?_⟩
    · have h : Gp ⊓ M₁ = (((trialityParabolic K σ.toRingHom 0).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            (e.symm.trans marking).toMonoidHom).map Gp.subtype := by
        rw [hm.2.1, h2]
        exact congrArg (Subgroup.map Gp.subtype) (hmap _)
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, h, h0]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have h : Gp ⊓ M₂ = (((trialityParabolic K σ.toRingHom 1).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
            (e.symm.trans marking).toMonoidHom).map Gp.subtype := by
        rw [hm.2.2, h3]
        exact congrArg (Subgroup.map Gp.subtype) (hmap _)
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, h, h1]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · rw [h5]
      exact congrArg (Subgroup.map Gp.subtype) (hmap _)
  · cases hk
  · cases hk

end Chart

theorem burnsideF4m_A42_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .D4tw Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε) ∧
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  haveI := hyp.amalgam.finite
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  obtain ⟨K, _, _, _, σ, hσ3, -, hK, hσq, φ, hP1, hP2, hS⟩ := burnsideF4m_A42_chart_D4 chart hm
  have S1 := CFSG.Quasithin.H13.F431.D4q.Loc.stdTwo_d4 σ hσ3 (by omega) hK hσq
  obtain ⟨V, L, S2⟩ := CFSG.Quasithin.H13.F431.D4q.StdLoc.stdLoc_d4 σ hσ3 hf hK hσq
  have S3 := CFSG.Quasithin.H13.F431.D4q.Loc.stdOrient_d4 σ hσ3 (by omega) hK hσq
  have YS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ (by omega) hK hσq
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel (burnsideF4g_lieModel_D4tw hyp.amalgam.model)
      (by decide)
  obtain ⟨hcent, hlieK⟩ := burnsideF4m_A42_engine hyp (by decide) hodd hZ1 S1 S2 S3
    YS.isYAmalgamPair YS.above φ hP1 hP2 hBT
  have htP : CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3 ∈
      CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ := S3.U_le_P' S1.t_mem
  have ht : ((φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) : ↥Gp) : E) ∈ M₂ := by
    have h : φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) ∈ M₂.subgroupOf Gp := by
      rw [hP2]
      exact ⟨_, htP, rfl⟩
    exact h
  refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
  ·
    have hGM : Gp ⊓ M₂ = ((CFSG.Quasithin.H13.F431.D4q.Struct.Pst1 σ).map
        φ.toMonoidHom).map Gp.subtype := by
      rw [← hP2, Subgroup.subgroupOf_map_subtype, inf_comm]
    show ((φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ φ.injective]
    exact ⟨φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3),
      ⟨CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3, burnsideF4gD4Inv_t_core σ hσ3, rfl⟩, rfl⟩
  ·
    obtain ⟨b, hbS, hb1⟩ := burnsideF4gD4Inv_S_ne σ hσ3
    obtain ⟨c, hc⟩ := isConj_iff.mp (burnsideF4gD4Inv_S_conj σ hσ3 b hbS hb1)
    have ht1 : CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3 ≠ 1 :=
      CFSG.Quasithin.H13.F431.D4q.Loc.tC_ne_one σ hσ3
    refine ⟨f, chart, hm, (φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3)).2, ?_, ?_,
      fun h => absurd h (by decide), ((φ c : ↥Gp) : E), (φ c).2, ?_⟩
    · intro h
      have h1 : φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) = φ 1 := by
        rw [map_one]
        exact Subtype.ext h
      exact ht1 (φ.injective h1)
    · show ((φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) *
        φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) : ↥Gp) : E) = 1
      rw [← map_mul, CFSG.Quasithin.H13.F431.D4q.Loc.tC_mul_self σ hσ3, map_one]
      rfl
    · rw [if_pos rfl, hS]
      refine ⟨φ b, ⟨b, hbS, rfl⟩, ?_⟩
      show (φ b : E) = (φ c : E) * (φ (CFSG.Quasithin.H13.F431.D4q.Loc.tC σ hσ3) : E) *
        ((φ c : E))⁻¹
      rw [← hc]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end D4

end CFSG.ASVolI
