module

public import CFSG.Milestones.ASVolI.F431.A42U4
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Std
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Extend

theorem burnsideF4m_A42_chart_extend_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (χ : NativeChart .U5 2 f (⊤ : Subgroup ↥Gp))
    (hχ : χ.Matches ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp)) :
    ∃ chart : NativeChart .U5 2 f Gp, chart.Matches M₁ M₂ ∧
      ∀ (b : Bool) (x : ↥Gp), χ.RootInvolution b x → chart.RootInvolution b (x : E) := by
  let e : ↥(⊤ : Subgroup ↥Gp) ≃* ↥Gp := Subgroup.topEquiv
  have he : ∀ X : Subgroup ↥(⊤ : Subgroup ↥Gp),
      (X.map (⊤ : Subgroup ↥Gp).subtype).map Gp.subtype = (X.map e.toMonoidHom).map Gp.subtype :=
    fun X => rfl
  rcases χ.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · refine ⟨⟨χ.borel.map Gp.subtype, χ.points.map Gp.subtype, χ.lines.map Gp.subtype,
      χ.longRoot.map Gp.subtype, χ.shortRoot.map Gp.subtype,
      Or.inl ⟨c, hk, burnsideF4j_markingMap marking e, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
    · rw [h1, burnsideF4j_markingMap_borel]
      exact he _
    · rw [h2, burnsideF4j_markingMap_parabolic]
      exact he _
    · rw [h3, burnsideF4j_markingMap_parabolic]
      exact he _
    · rw [h4, burnsideF4j_markingMap_root]
      exact he _
    · rw [h5, burnsideF4j_markingMap_root]
      exact he _
    ·
      obtain ⟨hb, hp, hl⟩ := hχ
      refine ⟨?_, ?_, ?_⟩
      · show Gp ⊓ (M₁ ⊓ M₂) = χ.borel.map Gp.subtype
        rw [← hb]
        ext x
        constructor
        · rintro ⟨hG, h1', h2'⟩
          exact ⟨⟨x, hG⟩, ⟨Subgroup.mem_top _, ⟨hG, h1'⟩, ⟨hG, h2'⟩⟩, rfl⟩
        · rintro ⟨y, ⟨-, ⟨-, hy1⟩, ⟨-, hy2⟩⟩, rfl⟩
          exact ⟨y.2, hy1, hy2⟩
      · show Gp ⊓ M₁ = χ.points.map Gp.subtype
        rw [← hp, top_inf_eq, Subgroup.subgroupOf_map_subtype, inf_comm (Gp ⊓ M₁) Gp,
          ← inf_assoc, inf_idem]
      · show Gp ⊓ M₂ = χ.lines.map Gp.subtype
        rw [← hl, top_inf_eq, Subgroup.subgroupOf_map_subtype, inf_comm (Gp ⊓ M₂) Gp,
          ← inf_assoc, inf_idem]
    ·
      rintro b x ⟨-, h1', h2', h3', c', -, hc'⟩
      refine ⟨x.2, fun h => h1' (Subtype.ext h), congrArg Subtype.val h2', h3', (c' : E), c'.2, ?_⟩
      cases b
      · rw [if_neg (by decide)] at hc' ⊢
        exact ⟨_, hc', rfl⟩
      · rw [if_pos rfl] at hc' ⊢
        exact ⟨_, hc', rfl⟩
  all_goals exact absurd hk (by decide)

end Extend

section U5

set_option linter.unusedSectionVars false


open CFSG.LieType.Universal.Unitary in
theorem burnsideF4m_A42_U5 {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .U5 2 Gp M₁ M₂ β ε z) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .U5 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε) ∧
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp.amalgam
  have h27 := as_F_4_27 .U5 2 ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨hχm, -, -, h3, h4, -⟩ := h27
  obtain ⟨-, ⟨C, ⟨-, -⟩, hCu⟩, hls, hliff, -⟩ := h3 ⟨by decide, by decide, by decide⟩
  have h4' := (h4 (by decide)).1
  have hM1' : (Gp ⊓ M₁).subgroupOf Gp = M₁.subgroupOf Gp := Subgroup.inf_subgroupOf_left M₁ Gp
  have hM2' : (Gp ⊓ M₂).subgroupOf Gp = M₂.subgroupOf Gp := Subgroup.inf_subgroupOf_left M₂ Gp
  obtain ⟨w, hwZ, hw1⟩ : ∃ w : ↥Gp, w ∈ ctr (oPPrime 2 (M₁.subgroupOf Gp)) ∧ w ≠ 1 := by
    have hz := hyp.z_mem.1 (by decide)
    rw [burnsideF4j_Z1_eq hyp] at hz
    obtain ⟨x, hx1, hxZ, hxz⟩ := mem_subImg.mp hz
    have hmap : ctr (oPPrime 2 (Gp ⊓ M₁)) =
        (ctr (oPPrime 2 (M₁.subgroupOf Gp))).map Gp.subtype := by
      have e : (M₁.subgroupOf Gp).map Gp.subtype = Gp ⊓ M₁ := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      rw [← e, burnsideF4d_oPPrime_map _ Gp.subtype_injective,
        burnsideF4j_ctr_map _ Gp.subtype_injective]
    rw [hmap] at hxZ
    obtain ⟨w, hw, rfl⟩ := hxZ
    refine ⟨w, hw, fun h => hyp.z_inv.1 ?_⟩
    subst h
    rw [← hxz]
    have e : (⟨Gp.subtype 1, hx1⟩ : ↥M₁) = 1 := Subtype.ext (map_one Gp.subtype)
    rw [e, map_one]
  have hwZ' : w ∈ ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf Gp)) := by
    rw [hM1']
    exact hwZ
  obtain ⟨hwRI, -, hwC, -⟩ := h4' w hwZ' hw1
  have hwL := hwRI (by decide)
  have hw2 : w * w = 1 := hwL.2.2.1
  have hwC' : Subgroup.centralizer ({w} : Set ↥Gp) ≤ M₁.subgroupOf Gp := hM1' ▸ hwC
  have hmodel := burnsideF4g_lieModel_U5 hyp.amalgam.model
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := Un.un5_model_equiv hmodel
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  haveI := Un.isSimpleGroup_un5 hF
  haveI := Finite.of_equiv (↥Gp) e.symm.toEquiv
  have hU0 := Un.isSylowTwoOf_un5System hF ζ
  obtain ⟨P, P', z₀, t₀, V4, V, Uc, R, K, hPP, S1, SV, SL⟩ := Un.un5StdDatum F hF ζ
  obtain ⟨marking, hm1, hm2⟩ := burnsideF4g_marking (c := .U5) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD₀, hTD₀⟩ := burnsideF4g_yamU5 marking
  rw [← hm1, ← hm2] at hTD₀
  obtain ⟨ψ, -, hψP⟩ := BN.exists_iso_of_yam (Un.un5System hF ζ) hU0 e
    (burnsideF4d_amalgamExt hyp.amalgam.toHypF_4_4g TD₀ hTD₀)
  have YS := BN.yamStd (Un.un5System hF ζ) hU0
  have hY' := YS.isYAmalgamPair
  have hUP1 : (Un.un5System hF ζ).U ≤ (Un.un5System hF ζ).P₁ :=
    Subgroup.le_normalizer.trans YS.le₀
  have hUP2 : (Un.un5System hF ζ).U ≤ (Un.un5System hF ζ).P₂ :=
    Subgroup.le_normalizer.trans YS.le₁
  have hYam : IsYAmalgamPair (Un.un5System hF ζ).U P P' := by
    rcases hPP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hY'
    · exact ⟨hY'.1, hY'.2.1.symm, fun B => (hY'.2.2 B).trans or_comm⟩
  have habove : ∀ B, Subgroup.normalizer ((Un.un5System hF ζ).U : Set _) ≤ B → B ≠ ⊤ →
      B ≤ P ∨ B ≤ P' := by
    intro B hB hB'
    rcases YS.above B hB hB' with h | h <;> rcases hPP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
  have hUP : (Un.un5System hF ζ).U ≤ P := by
    rcases hPP with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hUP1
    · exact hUP2
  have hUP' : (Un.un5System hF ζ).U ≤ P' := by
    rcases hPP with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hUP2
    · exact hUP1
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel hmodel (by decide)
  have hlab : (M₁.subgroupOf Gp = P.map ψ.toMonoidHom ∧
      M₂.subgroupOf Gp = P'.map ψ.toMonoidHom) ∨
      (M₁.subgroupOf Gp = P'.map ψ.toMonoidHom ∧ M₂.subgroupOf Gp = P.map ψ.toMonoidHom) := by
    rcases hψP with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hPP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    obtain ⟨hcent, hlieK⟩ := burnsideF4m_A42_engineU hyp (Or.inr rfl) hodd hZ1 S1 SV SL hYam
      habove ψ h1 h2 hBT
    obtain ⟨g, -, hgz⟩ := burnsideF4m_A42_center_conj ψ S1 hU0
      (by rw [h1]; exact Subgroup.map_mono hUP) hwZ hw1 hw2
    have ht₀1 : t₀ ≠ 1 := fun h0 => by
      have h3 := S1.t_two
      rw [h0, orderOf_one] at h3
      exact absurd h3 (by decide)
    have ht₀2 : t₀ * t₀ = 1 := by
      have := pow_orderOf_eq_one t₀
      rwa [S1.t_two, pow_two] at this
    have htQ : t₀ ∈ pCoreOf 2 P' := by
      have h := SV.V4_zt.2
      rw [SV.V4_eq] at h
      exact h.1
    have htP : t₀ ∈ P' := CFSG.LieType.BorelTits.pCoreOf_le 2 _ htQ
    have ht : ((ψ t₀ : ↥Gp) : E) ∈ M₂ := by
      have h : ψ t₀ ∈ M₂.subgroupOf Gp := by
        rw [h2]
        exact ⟨_, htP, rfl⟩
      exact h
    have hψt1 : ψ t₀ ≠ 1 := fun h => ht₀1 (ψ.injective (h.trans (map_one ψ).symm))
    have hψt2 : ψ t₀ * ψ t₀ = 1 := by rw [← map_mul, ht₀2, map_one]
    refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
    ·
      have hGM : Gp ⊓ M₂ = (P'.map ψ.toMonoidHom).map Gp.subtype := by
        rw [← h2, Subgroup.subgroupOf_map_subtype, inf_comm]
      show ((ψ t₀ : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
      rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
        CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ ψ.injective]
      exact ⟨ψ t₀, ⟨t₀, htQ, rfl⟩, rfl⟩
    ·
      have hmem : ∀ x : ↥Gp, x ≠ 1 → x * x = 1 →
          ConjClasses.mk x ∈ InvClasses ↥Gp := fun x hx1 hx2 =>
        ⟨x, ConjClasses.mem_carrier_mk, hx1, hx2⟩
      have hlongC : ∀ x : ↥Gp, x ≠ 1 → x * x = 1 →
          hyp'.toHypF_4_4g.chart.RootInvolution false x → ConjClasses.mk x = C := by
        intro x hx1 hx2 hxL
        obtain ⟨c, -, hc⟩ := ((hliff x hx1 hx2).mp hxL)
        refine hCu _ ⟨hmem x hx1 hx2, c * x * c⁻¹, ?_, hc⟩
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
        exact (isConj_iff.mpr ⟨c, rfl⟩).symm
      rcases hls (ψ t₀) hψt1 hψt2 with htL | htS
      · exfalso
        have hcl := (hlongC _ hψt1 hψt2 htL).trans (hlongC w hw1 hw2 hwL).symm
        have h1c : IsConj (ψ t₀) w := ConjClasses.mk_eq_mk_iff_isConj.mp hcl
        have h3c : IsConj w (ψ z₀) := by
          refine isConj_iff.mpr ⟨(ψ g)⁻¹, ?_⟩
          have e1 : w = ψ (g * z₀ * g⁻¹) := by rw [hgz, MulEquiv.apply_symm_apply]
          rw [e1, map_mul, map_mul, map_inv]
          group
        have h4c := ψ.symm.toMonoidHom.map_isConj (h1c.trans h3c)
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4c
        obtain ⟨c₀, hc₀⟩ := isConj_iff.mp h4c.symm
        exact S1.noconj (MulAut.conj c₀) (by rw [MulAut.conj_apply]; exact hc₀)
      · obtain ⟨chartE, hEm, hEri⟩ := burnsideF4m_A42_chart_extend_U5 _ hχm
        exact ⟨2, chartE, hEm, hEri true _ htS⟩
  ·
    exfalso
    obtain ⟨g, hg, hgz⟩ := burnsideF4m_A42_center_conj ψ S1 hU0
      (by rw [h1]; exact Subgroup.map_mono hUP') hwZ hw1 hw2
    apply SV.nz
    intro c hc
    have hc' : c * z₀ = z₀ * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hgc : ψ (g * c * g⁻¹) ∈ Subgroup.centralizer ({w} : Set ↥Gp) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : w = ψ (g * z₀ * g⁻¹) := by rw [hgz, MulEquiv.apply_symm_apply]
      rw [e1, ← map_mul, ← map_mul]
      congr 1
      calc g * c * g⁻¹ * (g * z₀ * g⁻¹) = g * (c * z₀) * g⁻¹ := by group
        _ = g * (z₀ * c) * g⁻¹ := by rw [hc']
        _ = g * z₀ * g⁻¹ * (g * c * g⁻¹) := by group
    have hgcP : g * c * g⁻¹ ∈ P' := by
      have h := hwC' hgc
      rw [h1] at h
      exact (Subgroup.mem_map_iff_mem ψ.injective).mp h
    have hgP : g ∈ P' := hg.2
    have e2 : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [e2]
    exact P'.mul_mem (P'.mul_mem (P'.inv_mem hgP) hgcP) hgP

end U5

end CFSG.ASVolI
