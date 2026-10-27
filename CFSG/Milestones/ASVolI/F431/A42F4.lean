module

public import CFSG.Milestones.ASVolI.F431.A42Engine3
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwo

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F4

set_option linter.unusedSectionVars false


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4
  CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF4m_A42_F4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .F4tw f Gp M₁ M₂ β ε z) (hf : 3 ≤ f) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .F4tw Gp M₁ M₂ (t : E) ∧
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
  obtain ⟨K, fK, finK, charK, a, ha, hKsc, marking, h2, h3, -, h5⟩ :=
    burnsideF4gF4Inv_chart_data hf chart
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hKsc
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hK
  haveI : Finite (Gm K a) := finite_gm K a
  obtain ⟨Φ, hΦ⟩ := burnsideF4gF4Inv_exists_iso ha hK marking
  have hP1 : M₁.subgroupOf Gp = (Pg K a ⟨1, by decide⟩).map Φ.toMonoidHom := by
    have h : Gp ⊓ M₁ = ((Pg K a ⟨1, by decide⟩).map Φ.toMonoidHom).map Gp.subtype := by
      rw [hm.2.1, h2, hΦ _ _ (burnsideF4gF4Inv_mem_P₁_iff hK), burnsideF4gF4Inv_Pg_one_eq hK]
    rw [← Subgroup.inf_subgroupOf_left M₁ Gp, h]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hP2 : M₂.subgroupOf Gp = (Pg K a ⟨0, by decide⟩).map Φ.toMonoidHom := by
    have h : Gp ⊓ M₂ = ((Pg K a ⟨0, by decide⟩).map Φ.toMonoidHom).map Gp.subtype := by
      rw [hm.2.2, h3, hΦ _ _ (burnsideF4gF4Inv_mem_P₂_iff hK), burnsideF4gF4Inv_Pg_zero_eq hK]
    rw [← Subgroup.inf_subgroupOf_left M₂ Gp, h]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hS : chart.shortRoot =
      (((reeShortRoot K a).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom).map Gp.subtype := by
    rw [h5]
    exact congrArg (Subgroup.map Gp.subtype) (hΦ _ _ (fun y => Subgroup.mem_subgroupOf))
  have S1 := f4_stdTwo ha hK
  have S2 := f4_stdLoc ha hK
  have S3 := stdOrient3_twoF4 ha hK
  have hF3 := commutator_mem_inner_gm ha hK
  have YS : CFSG.Quasithin.H13.Sec53F.Yam.YamStd (Gm K a) (Ug K a) (Pg K a ⟨0, by decide⟩)
      (Pg K a ⟨1, by decide⟩) := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  have hY := YS.isYAmalgamPair
  have hYam : IsYAmalgamPair (Ug K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) :=
    ⟨hY.1, hY.2.1.symm, fun B => (hY.2.2 B).trans or_comm⟩
  have habove : ∀ B : Subgroup (Gm K a), Subgroup.normalizer (Ug K a : Set (Gm K a)) ≤ B →
      B ≠ ⊤ → B ≤ Pg K a ⟨1, by decide⟩ ∨ B ≤ Pg K a ⟨0, by decide⟩ :=
    fun B hB hB' => (YS.above B hB hB').symm
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel (burnsideF4g_lieModel_F4tw hf hyp.amalgam.model)
      (by decide)
  obtain ⟨hcent, hlieK⟩ := burnsideF4m_A42_engine3 hyp (by decide) hodd hZ1 S1 S2 S3 hF3 hYam
    habove Φ hP1 hP2 hBT
  have htP : tg hK ∈ Pg K a ⟨0, by decide⟩ :=
    S3.ct (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have ht : ((Φ (tg hK) : ↥Gp) : E) ∈ M₂ := by
    have h : Φ (tg hK) ∈ M₂.subgroupOf Gp := by
      rw [hP2]
      exact ⟨_, htP, rfl⟩
    exact h
  refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
  ·
    have hGM : Gp ⊓ M₂ = ((Pg K a ⟨0, by decide⟩).map Φ.toMonoidHom).map Gp.subtype := by
      rw [← hP2, Subgroup.subgroupOf_map_subtype, inf_comm]
    show ((Φ (tg hK) : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
    rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
      CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Φ.injective]
    have hcore := burnsideF4gF4Inv_tg_core ha hK
    rw [← burnsideF4gF4Inv_Pg_zero_eq hK] at hcore
    exact ⟨Φ (tg hK), ⟨tg hK, hcore, rfl⟩, rfl⟩
  ·
    refine ⟨f, chart, hm, (Φ (tg hK)).2, ?_, ?_, fun h => absurd h (by decide), 1,
      Gp.one_mem, ?_⟩
    · intro h
      have h1 : Φ (tg hK) = Φ 1 := by
        rw [map_one]
        exact Subtype.ext h
      have ht1 : tg hK ≠ 1 := fun h0 => by
        have h3 := S1.t_two
        rw [h0, orderOf_one] at h3
        exact absurd h3 (by decide)
      exact ht1 (Φ.injective h1)
    · show ((Φ (tg hK) * Φ (tg hK) : ↥Gp) : E) = 1
      have h2t : tg hK * tg hK = 1 := by
        have := pow_orderOf_eq_one (tg hK)
        rwa [S1.t_two, pow_two] at this
      rw [← map_mul, h2t, map_one]
      rfl
    · rw [if_pos rfl, one_mul, inv_one, mul_one, hS]
      exact ⟨Φ (tg hK), ⟨tg hK, burnsideF4gF4Inv_tg_SR hK, rfl⟩, rfl⟩

end F4

end CFSG.ASVolI
