module

public import CFSG.Milestones.ASVolI.F431.A42Engine
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2NFLieStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2StdLoc

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Blueprint.Chevalley

section G2

set_option linter.unusedSectionVars false


theorem burnsideF4m_A42_chart_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (chart : NativeChart .G2 2 f Gp) (hm : chart.Matches M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : G2Native.Parent K ≃* ↥Gp,
        M₁.subgroupOf Gp = (G2Native.pointParabolic K).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (G2Native.lineParabolic K).map Ψ.toMonoidHom ∧
        chart.shortRoot = ((G2Native.shortRoot K).map Ψ.toMonoidHom).map Gp.subtype := by
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, hcard, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c <;> decide)
  · haveI charK : CharP K 2 := burnsideF4f_charP_of_card hd hcard
    let Ψ : G2Native.Parent K ≃* ↥Gp := (CFSG.Quasithin.H13.F431.G2.mk K).trans marking
    have hΨ : ∀ L : Subgroup (G2Native.Parent K),
        G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
      intro L
      unfold G2Native.fullImage G2Native.fullLocal
      rw [Subgroup.map_map]
      exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
    refine ⟨K, fK, finK, charK, hcard, Ψ, ?_, ?_, ?_⟩
    · have h : Gp ⊓ M₁ =
          (G2Native.fullImage K marking (G2Native.pointParabolic K)).map Gp.subtype :=
        hm.2.1.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, h, ← hΨ]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have h : Gp ⊓ M₂ =
          (G2Native.fullImage K marking (G2Native.lineParabolic K)).map Gp.subtype :=
        hm.2.2.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, h, ← hΨ]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · rw [h5, hΨ]
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem burnsideF4m_A42_yam_G2 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    IsYAmalgamPair (CFSG.Quasithin.H13.F431.G2.U K)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩) ∧
      ∀ B : Subgroup (CFSG.Quasithin.H13.F431.G2.C K),
        Subgroup.normalizer ((CFSG.Quasithin.H13.F431.G2.U K : Subgroup _) :
          Set (CFSG.Quasithin.H13.F431.G2.C K)) ≤ B → B ≠ ⊤ →
        B ≤ CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩ ∨
          B ≤ CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩ := by
  have YS := CFSG.Quasithin.H13.Sec53F.G2.g2_yamStd hK hf
  have fin2 : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have hne01 : Setup.X6.g2Index 0 ≠ Setup.X6.g2Index 1 := fun h =>
    absurd (Setup.X6.g2Index_injective h) (by decide)
  have hidx : (Setup.X6.g2Index 0 = ⟨0, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨1, by decide⟩) ∨
      (Setup.X6.g2Index 0 = ⟨1, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨0, by decide⟩) := by
    rcases fin2 (Setup.X6.g2Index 0) with h0 | h0 <;>
      rcases fin2 (Setup.X6.g2Index 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) hne01
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne01
  rcases hidx with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [e0, e1] at YS
    have hY : IsYAmalgamPair (CFSG.Quasithin.H13.F431.G2.U K)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩) := YS.isYAmalgamPair
    refine ⟨⟨hY.1, hY.2.1.symm, fun B => (hY.2.2 B).trans or_comm⟩, fun B hB hB' => ?_⟩
    exact (YS.above B hB hB').symm
  · rw [e0, e1] at YS
    have hY : IsYAmalgamPair (CFSG.Quasithin.H13.F431.G2.U K)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩)
        (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩) := YS.isYAmalgamPair
    exact ⟨hY, fun B hB hB' => YS.above B hB hB'⟩

theorem burnsideF4m_A42_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .G2 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .G2 Gp M₁ M₂ (t : E) ∧
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
  obtain ⟨K, _, _, _, hcard, Ψ, hP1, hP2, hS⟩ := burnsideF4m_A42_chart_G2 chart hm
  rw [burnsideF4gG2Inv_point_eq] at hP1
  rw [burnsideF4gG2Inv_line_eq] at hP2
  rw [burnsideF4gG2Inv_shortRoot_eq] at hS
  have hK3 : 3 ≤ Nat.card K := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hP1' : M₁.subgroupOf Gp =
      (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩).map Ψ.toMonoidHom := hP1
  have hP2' : M₂.subgroupOf Gp =
      (CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩).map Ψ.toMonoidHom := hP2
  have S1 := CFSG.Quasithin.H13.F431.G2.g2_stdTwo hf hcard
  have S2 := CFSG.Quasithin.H13.F431.G2.g2_stdLoc hf hcard
  have S3 := CFSG.Quasithin.H13.F431.G2.NFLie.stdOrient_g2 hf hcard
  obtain ⟨hYam, habove⟩ := burnsideF4m_A42_yam_G2 hcard hf
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel (burnsideF4g_lieModel_G2 hf hyp.amalgam.model)
      (by decide)
  obtain ⟨hcent, hlieK⟩ :=
    burnsideF4m_A42_engine hyp (by decide) hodd hZ1 S1 S2 S3 hYam habove Ψ hP1' hP2' hBT
  have htP : CFSG.Quasithin.H13.F431.G2.xv (1 : K) ∈
      CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩ := S3.U_le_P' S1.t_mem
  have ht : ((Ψ (CFSG.Quasithin.H13.F431.G2.xv 1) : ↥Gp) : E) ∈ M₂ := by
    have h : Ψ (CFSG.Quasithin.H13.F431.G2.xv 1) ∈ M₂.subgroupOf Gp := by
      rw [hP2']
      exact ⟨_, htP, rfl⟩
    exact h
  refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
  ·
    have hGM : Gp ⊓ M₂ = ((CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩).map
        Ψ.toMonoidHom).map Gp.subtype := by
      rw [← hP2', Subgroup.subgroupOf_map_subtype, inf_comm]
    show ((Ψ (CFSG.Quasithin.H13.F431.G2.xv 1) : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Ψ.injective]
    refine ⟨Ψ (CFSG.Quasithin.H13.F431.G2.xv 1), ⟨CFSG.Quasithin.H13.F431.G2.xv 1, ?_, rfl⟩, rfl⟩
    have h := burnsideF4gG2Inv_pCoreOf_Pa (K := K) hK3
    show CFSG.Quasithin.H13.F431.G2.xv 1 ∈
      pCoreOf 2 (CFSG.Quasithin.H13.F431.G2.Cent.Pa K)
    rw [h]
    exact CFSG.Quasithin.H13.F431.G2.xv_mem_Q2 1
  ·
    refine ⟨f, chart, hm, (Ψ (CFSG.Quasithin.H13.F431.G2.xv 1)).2, ?_, ?_,
      fun h => absurd h (by decide), 1, Gp.one_mem, ?_⟩
    · intro h
      have h1 : Ψ (CFSG.Quasithin.H13.F431.G2.xv (1 : K)) = Ψ 1 := by
        rw [map_one]
        exact Subtype.ext h
      exact one_ne_zero (CFSG.Quasithin.H13.F431.G2.xv_eq_one_iff.1 (Ψ.injective h1))
    · show ((Ψ (CFSG.Quasithin.H13.F431.G2.xv 1) * Ψ (CFSG.Quasithin.H13.F431.G2.xv 1) :
        ↥Gp) : E) = 1
      rw [← map_mul, CFSG.Quasithin.H13.F431.G2.xv_mul_self, map_one]
      rfl
    · rw [if_pos rfl, one_mul, inv_one, mul_one, hS]
      exact ⟨Ψ (CFSG.Quasithin.H13.F431.G2.xv 1),
        ⟨CFSG.Quasithin.H13.F431.G2.xv 1, CFSG.Quasithin.H13.F431.G2.xv_mem_Xv 1, rfl⟩, rfl⟩

end G2

end CFSG.ASVolI
