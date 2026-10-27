module

public import CFSG.Milestones.ASVolI.F48.Six
public import CFSG.Milestones.ASVolI.F48.Bn
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideF48_chart_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : ChF.HypF_4_4g .G2 p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      ∃ marking : ChF.G2Native.FullModel K ≃* ↥Gp,
        M₁.subgroupOf Gp = ChF.G2Native.fullImage K marking (ChF.G2Native.pointParabolic K) ∧
        M₂.subgroupOf Gp = ChF.G2Native.fullImage K marking (ChF.G2Native.lineParabolic K) := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, h1, h2, h3, h4, h5⟩ |
      ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · refine ⟨K, fK, finK, card, marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ =
          (ChF.G2Native.fullImage K marking (ChF.G2Native.pointParabolic K)).map Gp.subtype :=
        hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ =
          (ChF.G2Native.fullImage K marking (ChF.G2Native.lineParabolic K)).map Gp.subtype :=
        hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by decide)

theorem burnsideF48_isSylowOf_of_equiv_top {p : ℕ} {E : Type} [Group E] {Gp : Subgroup E}
    {G' : Type} [Group G'] (ε : G' ≃* ↥Gp) {U : Subgroup G'} (hU : ChF.IsSylowOf p U ⊤) :
    ChF.IsSylowOf p ((U.map ε.toMonoidHom).map Gp.subtype) Gp := by
  refine ⟨Subgroup.map_subtype_le _, (hU.2.1.map ε.toMonoidHom).map Gp.subtype, ?_⟩
  have h1 : ((U.map ε.toMonoidHom).map Gp.subtype).subgroupOf Gp = U.map ε.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have h2 := hU.2.2
  rw [Subgroup.relIndex_top_right] at h2
  rw [Subgroup.relIndex, h1]
  change ¬ p ∣ (U.map (ε : G' →* ↥Gp)).index
  rw [Subgroup.index_map_equiv]
  exact h2

theorem burnsideF48_mem_map_equiv {G' G'' : Type} [Group G'] [Group G''] (ε : G' ≃* G'')
    (P : Subgroup G') (g : G') : ε g ∈ P.map ε.toMonoidHom ↔ g ∈ P := by
  rw [Subgroup.mem_map_equiv]
  simp

section G2Core


set_option linter.unusedSectionVars false

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.H13.F431.G2 CFSG.Quasithin.H13.F431.G2.F48
  CFSG.Quasithin.H13.F431.BN in
theorem burnsideF48_g2_cartan_data {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) :
    ∃ n w h : AdjointQuotient Tag.G2 K,
      n ∈ (burnsideF4h_g2_sys K).P₁ ∧ n ∉ (burnsideF4h_g2_sys K).P₂ ∧
      h ∈ (burnsideF4h_g2_sys K).P₁ ∧ h ∈ (burnsideF4h_g2_sys K).P₂ ∧
      n⁻¹ * h * n ∈ (burnsideF4h_g2_sys K).P₂ ∧ w⁻¹ * h * w ∈ (burnsideF4h_g2_sys K).P₁ ∧
      (¬ ∃ k ∈ (burnsideF4h_g2_sys K).P₁, ∃ l ∈ (burnsideF4h_g2_sys K).P₂,
        ∃ k' ∈ (burnsideF4h_g2_sys K).P₁, ∃ l' ∈ (burnsideF4h_g2_sys K).P₂,
        ∃ k'' ∈ (burnsideF4h_g2_sys K).P₁, w = k * l * k' * l' * k'') ∧
      ∀ q ∈ (burnsideF4h_g2_sys K).U, n⁻¹ * q * n ∈ (burnsideF4h_g2_sys K).U →
        h * q * h⁻¹ = q → q = 1 := by
  have hK3 : 3 ≤ Nat.card K := by omega
  obtain ⟨u, hu, hu2⟩ := exists_unit_sq_ne_one hK4
  have hcart : hexProj ↥(adjointGroup Tag.G2 K) (torG2 u) ∈
      (burnsideF4h_g2_sys K).B ⊓ (burnsideF4h_g2_sys K).N := torG2_mem_cartan hK3 u
  set D := burnsideF4h_g2_sys K with hD
  have hBP₁ : D.B ≤ D.P₁ := B_le_P D true
  have hBP₂ : D.B ≤ D.P₂ := B_le_P D false
  have hmiN : mi D true ∈ D.N := (D.lift (gen D.w₁ D.w₂ true)).2
  have hwN : ((D.lift D.w₀ : D.N) : AdjointQuotient Tag.G2 K) ∈ D.N := (D.lift D.w₀).2
  refine ⟨(mi D true)⁻¹, ((D.lift D.w₀ : D.N) : AdjointQuotient Tag.G2 K),
    hexProj ↥(adjointGroup Tag.G2 K) (torG2 u), D.P₁.inv_mem (mi_mem_P D true), ?_,
    hBP₁ hcart.1, hBP₂ hcart.1, ?_, ?_, burnsideF48_w₀_not_mem_five D (by norm_num), ?_⟩
  · intro h
    exact burnsideF48_bn_mi_not_mem_P₂ D (by simpa using D.P₂.inv_mem h)
  · rw [inv_inv]
    exact hBP₂ (burnsideF48_bn_conj_mem_B D hmiN hcart)
  · have := burnsideF48_bn_conj_mem_B D (D.N.inv_mem hwN) hcart
    rw [inv_inv] at this
    exact hBP₁ this
  · intro q hq hq' hc
    have hq'' : mi D true * q * (mi D true)⁻¹ ∈ D.U := by simpa [inv_inv] using hq'
    exact burnsideF48_centralizer_Uplus D hcart
      (fun k hk x hx hf => g2Model_fix_root hK3 u hu hu2 (mem_intList_iff.1 hk).1
        (by have := (mem_intList_iff.1 hk).2; omega) hx hf)
      ((mem_Uplus_iff D).2 ⟨hq, hq''⟩) hc

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.GH74.BNPair CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint CFSG.Quasithin.H13.F431.BN in
theorem burnsideF48_cartanFPF_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.G2.m)
    (hq : 4 ≤ p ^ f) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 6) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF48_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hK4 : 4 ≤ Nat.card K := by rw [hcard]; exact hq
  obtain ⟨n, w, h, hn1, hn2, hh1, hh2, hh3, hh4, hw, hQ⟩ := burnsideF48_g2_cartan_data hK4
  refine burnsideF48_cartanFPF_of_data_six hyp hp hm rfl hpoly marking
    (burnsideF4h_g2_sys K).P₁ (burnsideF4h_g2_sys K).P₂ (burnsideF4h_g2_sys K).U ?_ ?_
    (burnsideF48_isSylowOf_of_equiv_top marking (burnsideF4h_g2_sys_U_sylow p)) ?_
    n w h hn1 hn2 hh1 hh2 hh3 hh4 hw hQ
  · intro g
    have e : ((marking g : ↥Gp) : E) ∈ M₁ ↔ marking g ∈ M₁.subgroupOf Gp := Subgroup.mem_subgroupOf.symm
    rw [e, h1, ChF.G2Native.fullImage, ← burnsideF4h_g2_fullLocal_point]
    exact burnsideF48_mem_map_equiv marking _ g
  · intro g
    have e : ((marking g : ↥Gp) : E) ∈ M₂ ↔ marking g ∈ M₂.subgroupOf Gp := Subgroup.mem_subgroupOf.symm
    rw [e, h2, ChF.G2Native.fullImage, ← burnsideF4h_g2_fullLocal_line]
    exact burnsideF48_mem_map_equiv marking _ g
  · exact (burnsideF4h_g2_sys K).U_le_B.trans (B_le_P _ true)

theorem burnsideF48_simple_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) : IsSimpleGroup ↥Gp := by
  obtain ⟨K, fK, finK, hcard, marking, -, -⟩ := burnsideF48_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI := CFSG.GH74.GLS.Stage4.Hex.isSimpleGroup_g2Model (F := K) (by rw [hcard]; exact hq)
  exact marking.symm.isSimpleGroup

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_G2 (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .G2 p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) : ChF.F48Concl .G2 p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .G2
  have hL : ChF.GLKind.G2.IsLie :=
    show ChF.GLKind.G2 ≠ ChF.GLKind.G2d ∧ ChF.GLKind.G2 ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_G2 hyp (by omega)) hP ?_
  exact burnsideF48_cartanFPF_G2 hyp hp hm hq (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

end G2Core

end CFSG.ASVolI
