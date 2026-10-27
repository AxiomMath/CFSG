module

public import CFSG.Milestones.ASVolI.F431.A42EngineU
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDatumFour
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Orient

theorem burnsideF4m_A42_center_conj {D C : Type} [Group D] [Group C] [Finite C]
    (ψ : C ≃* D) {U P P' : Subgroup C} {z₀ t₀ : C} (S1 : Lift.StdTwo C U P P' z₀ t₀)
    (hU : IsSylowTwoOf U ⊤) {Q : Subgroup D} (hUQ : U.map ψ.toMonoidHom ≤ Q)
    {w : D} (hw : w ∈ ctr (oPPrime 2 Q)) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    ∃ h ∈ P ⊓ P', h * z₀ * h⁻¹ = ψ.symm w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ u ∈ U, ψ u * w = w * ψ u := by
    intro u hu
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU.2.1) ⟨u, hu⟩
    have hk' : orderOf (ψ u) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_mk u hu]
      exact hk
    have hmem : ψ u ∈ oPPrime 2 Q := burnsideF4gG2Inv_mem_oPPrime (hUQ ⟨u, hu, rfl⟩) hk'
    exact (Subgroup.mem_centralizer_iff.mp hw.2) _ hmem
  have hu₀c : ∀ u ∈ U, u * ψ.symm w = ψ.symm w * u := by
    intro u hu
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcomm u hu
  have hu₀2 : ψ.symm w * ψ.symm w = 1 := by rw [← map_mul, hw2, map_one]
  have hu₀U : ψ.symm w ∈ U := by
    have hK := burnsideF4ja_isPGroup_zpowers hu₀2
    have hle : Subgroup.zpowers (ψ.symm w) ≤ Subgroup.normalizer (U : Set C) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h := hu₀c x hx
        have e : ψ.symm w * x * (ψ.symm w)⁻¹ = x := by
          rw [← h, mul_assoc, mul_inv_cancel, mul_one]
        rw [e]
        exact hx
      · intro hx
        have h := hu₀c _ hx
        have e : x = ψ.symm w * x * (ψ.symm w)⁻¹ := by
          calc x = (ψ.symm w)⁻¹ * (ψ.symm w * x * (ψ.symm w)⁻¹ * ψ.symm w) := by group
            _ = (ψ.symm w)⁻¹ * (ψ.symm w * (ψ.symm w * x * (ψ.symm w)⁻¹)) := by rw [h]
            _ = ψ.symm w * x * (ψ.symm w)⁻¹ := by group
        rw [e]
        exact hx
    have hsup := IsPGroup.to_sup_of_normal_left' hU.2.1 hK hle
    have heq := CFSG.Quasithin.F1.eq_of_isSylowTwoOf_le hU le_top hsup le_sup_left
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hu₀1 : ψ.symm w ≠ 1 := fun h => hw1 (by
    rw [← MulEquiv.apply_symm_apply ψ w, h, map_one])
  exact S1.center _ hu₀U (fun y hy => hu₀c y hy) hu₀1

end Orient

section U4

set_option linter.unusedSectionVars false


open CFSG.ASVolI.ChF.ClassicalRoots CFSG.Quasithin.H13.U4Par CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary in
theorem burnsideF4m_A42_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) (hodd : Odd Gp.index)
    (hZ1 : burnsideF4m_Core1 Gp M₁) :
    (∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .U4 Gp M₁ M₂ (t : E) ∧
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
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  obtain ⟨marking, hpts, hlines, -, hshort⟩ := burnsideF4gU4Inv_marking chart
  obtain ⟨Φ, e0, e1, -, e3⟩ := burnsideF4gU4Inv_equiv_roots marking
  have hM1 : M₁.subgroupOf Gp = marking.parabolic false := by
    rw [← Subgroup.inf_subgroupOf_left M₁ Gp, hm.2.1, hpts]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hM2 : M₂.subgroupOf Gp = marking.parabolic true := by
    rw [← Subgroup.inf_subgroupOf_left M₂ Gp, hm.2.2, hlines]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  have hY := burnsideF4gU4Inv_Data_Y (burnsideF4gU4_fieldData marking)
    (fun x hx1 hx2 => by
      rw [← burnsideF4gU4Inv_shortRad_eq]
      exact burnsideF4gU4InvW_invol_cases _ hx1 hx2)
    (fun z hz hz1 z' hz' hz1' => burnsideF4gU4InvW_zRad_conj _ hz hz1 hz' hz1')
    (fun t ht ht1 t' ht' ht1' => by
      rw [← burnsideF4gU4Inv_shortRad_eq] at ht ht'
      exact burnsideF4gU4InvW_short_conj _ ht ht1 ht' ht1')
    (fun z hz hz1 t ht ht1 => by
      rw [← burnsideF4gU4Inv_shortRad_eq] at ht
      exact burnsideF4gU4InvW_not_conj _ hz hz1 ht ht1)
  have D := burnsideF4gU4Inv_Data_map Φ hY
  rw [← e0, ← e1, ← hM1, ← hM2] at D
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
  have hwL := D.ctr_oPPrime hwZ
  have hw2 := D.sq_long w hwL
  have hwC := D.centralizer_long w hwL hw1
  have hmodel := burnsideF4g_lieModel_U4 hyp.amalgam.model
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := Un.un_model_equiv hmodel
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  haveI := Un.isSimpleGroup_unSU hF
  haveI := Finite.of_equiv (↥Gp) e.symm.toEquiv
  obtain ⟨z₀, t₀, V4, V, Uc, R, K, S1, SV, SL⟩ := Un.unStdDatum_four f hf F hF ζ
  obtain ⟨TD₀, hTD₀⟩ := burnsideF4g_yamU4 marking
  rw [← hM1, ← hM2] at hTD₀
  obtain ⟨ψ, -, hψP⟩ := BN.exists_iso_of_yam (Un.unSystem hF ζ) (Un.isSylowTwoOf_unU hF) e
    (burnsideF4d_amalgamExt hyp.amalgam.toHypF_4_4g TD₀ hTD₀)
  have YS := BN.yamStd (Un.unSystem hF ζ) (Un.isSylowTwoOf_unU hF)
  have hY' := YS.isYAmalgamPair
  have hYam : IsYAmalgamPair (Un.unSystem hF ζ).U (Un.unSystem hF ζ).P₂
      (Un.unSystem hF ζ).P₁ := ⟨hY'.1, hY'.2.1.symm, fun B => (hY'.2.2 B).trans or_comm⟩
  have habove : ∀ B, Subgroup.normalizer ((Un.unSystem hF ζ).U : Set _) ≤ B →
        B ≠ ⊤ → B ≤ (Un.unSystem hF ζ).P₂ ∨ B ≤ (Un.unSystem hF ζ).P₁ :=
    fun B hB hB' => (YS.above B hB hB').symm
  have hUP1 : (Un.unSystem hF ζ).U ≤ (Un.unSystem hF ζ).P₁ :=
    Subgroup.le_normalizer.trans YS.le₀
  have hUP2 : (Un.unSystem hF ζ).U ≤ (Un.unSystem hF ζ).P₂ :=
    Subgroup.le_normalizer.trans YS.le₁
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel hmodel (by decide)
  rcases hψP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    exfalso
    have h1' : M₁.subgroupOf Gp = (Un.unSystem hF ζ).P₁.map ψ.toMonoidHom := h1
    obtain ⟨g, hg, hgz⟩ := burnsideF4m_A42_center_conj ψ S1 (Un.isSylowTwoOf_unU hF)
      (by rw [h1']; exact Subgroup.map_mono hUP1) hwZ hw1 hw2
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
    have hgcP : g * c * g⁻¹ ∈ (Un.unSystem hF ζ).P₁ := by
      have h := hwC hgc
      rw [h1'] at h
      exact (Subgroup.mem_map_iff_mem ψ.injective).mp h
    have hgP : g ∈ (Un.unSystem hF ζ).P₁ := hg.2
    have e2 : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [e2]
    exact (Un.unSystem hF ζ).P₁.mul_mem
      ((Un.unSystem hF ζ).P₁.mul_mem ((Un.unSystem hF ζ).P₁.inv_mem hgP) hgcP) hgP
  ·
    have h1' : M₁.subgroupOf Gp = (Un.unSystem hF ζ).P₂.map ψ.toMonoidHom := h1
    have h2' : M₂.subgroupOf Gp = (Un.unSystem hF ζ).P₁.map ψ.toMonoidHom := h2
    obtain ⟨hcent, hlieK⟩ := burnsideF4m_A42_engineU hyp (Or.inl rfl) hodd hZ1 S1 SV SL hYam
      habove ψ h1' h2' hBT
    obtain ⟨g, -, hgz⟩ := burnsideF4m_A42_center_conj ψ S1 (Un.isSylowTwoOf_unU hF)
      (by rw [h1']; exact Subgroup.map_mono hUP2) hwZ hw1 hw2
    have ht₀1 : t₀ ≠ 1 := fun h0 => by
      have h3 := S1.t_two
      rw [h0, orderOf_one] at h3
      exact absurd h3 (by decide)
    have ht₀2 : t₀ * t₀ = 1 := by
      have := pow_orderOf_eq_one t₀
      rwa [S1.t_two, pow_two] at this
    have htQ : t₀ ∈ pCoreOf 2 (Un.unSystem hF ζ).P₁ := by
      have h := SV.V4_zt.2
      rw [SV.V4_eq] at h
      exact h.1
    have htP : t₀ ∈ (Un.unSystem hF ζ).P₁ :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ htQ
    have ht : ((ψ t₀ : ↥Gp) : E) ∈ M₂ := by
      have h : ψ t₀ ∈ M₂.subgroupOf Gp := by
        rw [h2']
        exact ⟨_, htP, rfl⟩
      exact h
    have hψt1 : ψ t₀ ≠ 1 := fun h => ht₀1 (ψ.injective (h.trans (map_one ψ).symm))
    have hψt2 : ψ t₀ * ψ t₀ = 1 := by rw [← map_mul, ht₀2, map_one]
    refine ⟨⟨⟨_, ht⟩, ?_, ?_, hcent ht⟩, hlieK⟩
    ·
      have hGM : Gp ⊓ M₂ = (((Un.unSystem hF ζ).P₁).map ψ.toMonoidHom).map Gp.subtype := by
        rw [← h2', Subgroup.subgroupOf_map_subtype, inf_comm]
      show ((ψ t₀ : ↥Gp) : E) ∈ pCoreOf 2 (Gp ⊓ M₂)
      rw [hGM, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Gp.subtype_injective,
        CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ ψ.injective]
      exact ⟨ψ t₀, ⟨t₀, htQ, rfl⟩, rfl⟩
    ·
      rcases D.cases (ψ t₀) hψt1 hψt2 with ⟨c, hc⟩ | ⟨c, hc⟩
      · exfalso
        have hℓ1 : c * ψ t₀ * c⁻¹ ≠ 1 := fun h => hψt1 (by
          have : ψ t₀ = c⁻¹ * (c * ψ t₀ * c⁻¹) * c := by group
          rw [this, h]
          group)
        have h1c : IsConj (ψ t₀) (c * ψ t₀ * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
        have h2c := D.conj_long _ hc hℓ1 w hwL hw1
        have h3c : IsConj w (ψ z₀) := by
          refine isConj_iff.mpr ⟨(ψ g)⁻¹, ?_⟩
          have e1 : w = ψ (g * z₀ * g⁻¹) := by rw [hgz, MulEquiv.apply_symm_apply]
          rw [e1, map_mul, map_mul, map_inv]
          group
        have h4c := ψ.symm.toMonoidHom.map_isConj ((h1c.trans h2c).trans h3c)
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4c
        obtain ⟨c₀, hc₀⟩ := isConj_iff.mp h4c.symm
        exact S1.noconj (MulAut.conj c₀) (by rw [MulAut.conj_apply]; exact hc₀)
      · refine ⟨f, chart, hm, (ψ t₀).2, fun h => hψt1 (Subtype.ext h),
          congrArg Subtype.val hψt2, fun h => absurd h (by decide), (c : E), c.2, ?_⟩
        rw [if_pos rfl, hshort, e3]
        refine ⟨c * ψ t₀ * c⁻¹, hc, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

end U4

end CFSG.ASVolI
