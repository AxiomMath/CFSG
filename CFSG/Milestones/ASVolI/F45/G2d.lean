module

public import CFSG.Milestones.ASVolI.F45.ExcDefs
public import CFSG.Milestones.ASVolI.F45.G2dSix
public import CFSG.Milestones.ASVolI.F45.G2dModel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

attribute [local instance 10000] burnsideF45_cosetAct burnsideF45_cosetSMul


theorem burnsideF45_g2d_iso {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2d 2 1 (⊤ : Subgroup E) M₁ M₂) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (π : E ≃* G2Native.SmallModel K)
    (h1 : ∀ e, e ∈ M₁ ↔ π e ∈ G2Native.smallLocal K (G2Native.pointParabolic K))
    (h2 : ∀ e, e ∈ M₂ ↔ π e ∈ G2Native.smallLocal K (G2Native.lineParabolic K)) :
    ∃ e : (incl M₁ M₂).Γ ≃ V (burnsideF4h_g2_sys K),
      e (incl M₁ M₂).xv = v (burnsideF4h_g2_sys K) true ∧
      e (incl M₁ M₂).lv = v (burnsideF4h_g2_sys K) false ∧
      (∀ (g : (incl M₁ M₂).G0) (a : (incl M₁ M₂).Γ),
        e ((g • a : (incl M₁ M₂).Γ)) =
          ((burnsideF4h_g2_incl K hK).comp π.toMonoidHom (burnsideF45_eIso hyp g)) • e a) ∧
      ∀ a b, (incl M₁ M₂).graph.Adj a b ↔ (Γ (burnsideF4h_g2_sys K)).Adj (e a) (e b) := by
  haveI := hyp.finite
  set D := burnsideF4h_g2_sys K with hD
  let j : E →* G2Native.FullModel K := (burnsideF4h_g2_incl K hK).comp π.toMonoidHom
  have hj : ∀ y, j y = burnsideF4h_g2_incl K hK (π y) := fun _ => rfl
  have hm1 : ∀ y, y ∈ M₁ ↔ j y ∈ D.P₁ := fun y => by
    rw [hD, ← burnsideF4h_g2_fullLocal_point, hj, burnsideF4h_g2_incl_mem hK]
    exact h1 y
  have hm2 : ∀ y, y ∈ M₂ ↔ j y ∈ D.P₂ := fun y => by
    rw [hD, ← burnsideF4h_g2_fullLocal_line, hj, burnsideF4h_g2_incl_mem hK]
    exact h2 y
  letI actE : MulAction E (V D) := MulAction.compHom (V D) j
  have hsmulE : ∀ (y : E) (a : V D), y • a = j y • a := fun _ _ => rfl
  haveI : GraphAction E (Γ D) := ⟨fun y a b => by
    rw [hsmulE, hsmulE]
    exact GraphAction.adj_smul (j y) a b⟩
  let θ : E ≃* ↥(⊤ : Subgroup E) := Subgroup.topEquiv.symm
  have hθ : ∀ y : E, ((θ y : ↥(⊤ : Subgroup E)) : E) = y := fun _ => rfl
  have XD := burnsideF45_xdatum_of_model hyp Nat.prime_two (burnsideF45_three_le_m _) θ
    (v₁ := v D true) (v₂ := v D false)
    (fun y => by rw [hθ, hm1, hsmulE]; exact (smul_v_true_eq_iff (j y)).symm)
    (fun y => by rw [hθ, hm2, hsmulE]; exact (smul_v_false_eq_iff (j y)).symm)
    (fun y z => by rw [hsmulE, hsmulE]; exact disj D (j y) (j z))
    (fun y z => by rw [hsmulE, hsmulE]; exact noadj_true D (j y) (j z))
    (fun y z => by rw [hsmulE, hsmulE]; exact noadj_false D (j y) (j z))
    (adj_v D)
  have hcover : ∀ x : G2Native.FullModel K, ∃ y : E, ∃ b ∈ D.B, x = j y * b := fun x => by
    obtain ⟨s, b, hb, hx⟩ := burnsideF4h_g2_incl_cover hK x
    refine ⟨π.symm s, b, ?_, ?_⟩
    · rw [hD, ← burnsideF4h_g2_fullLocal_borel]
      exact hb
    · rw [hj, MulEquiv.apply_symm_apply]
      exact hx
  have hcov : ∀ a : V D, ∃ y : E, y • v D true = a ∨ y • v D false = a := by
    intro a
    obtain ⟨i, x, rfl⟩ := CFSG.GH74.BNPair.exists_vtx a
    obtain ⟨y, b, hb, hxb⟩ := hcover x⁻¹
    refine ⟨y, ?_⟩
    have key : y • v D i = vtx D.B D.N D.w₁ D.w₂ i x := by
      have hjy : j y = x⁻¹ * b⁻¹ := by rw [hxb]; group
      rw [hsmulE, hjy, mul_smul, smul_v_of_mem_B D i (D.B.inv_mem hb), v_eq_vt, smul_vt]
      simp only [one_mul, inv_inv]
      rfl
    cases i
    · exact Or.inr key
    · exact Or.inl key
  have hflag : ∀ a, (Γ D).Adj (v D true) a →
      ∃ y : E, y • v D true = v D true ∧ y • v D false = a := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := flag_true D a ha
    obtain ⟨y, b, hb, hpb⟩ := hcover p
    have hjy : j y = p * b⁻¹ := by rw [hpb]; group
    refine ⟨y, ?_, ?_⟩
    · rw [hsmulE, smul_v_true_eq_iff, hjy]
      exact D.P₁.mul_mem hp (B_le_P D true (D.B.inv_mem hb))
    · rw [hsmulE, hjy, mul_smul, smul_v_of_mem_B D false (D.B.inv_mem hb), hpa]
  obtain ⟨e, he1, he2, heq, hadj⟩ := XD.exists_equiv hcov hflag
  refine ⟨e, he1, he2, fun g a => ?_, hadj⟩
  have hΦ : burnsideF45_Phi hyp θ (burnsideF45_eIso hyp g) = g := by
    apply (burnsideF45_eIso hyp).injective
    rw [burnsideF45_eIso_Phi]
    rfl
  have := heq (burnsideF45_eIso hyp g) a
  rw [hΦ] at this
  exact this

theorem burnsideF45_excKind_G2d : burnsideF45_ExcKind .G2d := by
  intro p f E _ Gp M₁ M₂ hyp
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2 hf1
  have hGp : Gp = ⊤ := hyp.canonical (Or.inl rfl)
  subst hGp
  obtain ⟨K, fK, finK, hK, π, h1, h2⟩ := burnsideF45_g2d_chart hyp.toHypF_4_4g
  letI := fK
  haveI := hyp.finite
  have hP := burnsideF45_g2d_isLie hK π h1 h2
  have hB := burnsideF45_g2d_borel_pGroup hK π h1 h2
  obtain ⟨e, he1, he2, heq, hadj⟩ := burnsideF45_g2d_iso hyp hK π h1 h2
  let J : (incl M₁ M₂).G0 →* G2Native.FullModel K :=
    ((burnsideF4h_g2_incl K hK).comp π.toMonoidHom).comp (burnsideF45_eIso hyp).toMonoidHom
  letI actX : MulAction (G2Native.FullModel K) (incl M₁ M₂).Γ := burnsideF45_transAct e
  haveI : GraphAction (G2Native.FullModel K) (incl M₁ M₂).graph := burnsideF45_transAct_graph e hadj
  have hJrange : J.range = (burnsideF4h_g2_incl K hK).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (burnsideF45_eIso hyp).surjective,
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 π.surjective,
      ← MonoidHom.range_eq_map]
  have hmodel := burnsideF45_hexModel_transport e hadj (burnsideF45_g2d_hexModel hK)
  have hx0 : e.symm (v (burnsideF4h_g2_sys K) true) = (incl M₁ M₂).xv := by
    rw [← he1, Equiv.symm_apply_apply]
  have hl0 : e.symm (v (burnsideF4h_g2_sys K) false) = (incl M₁ M₂).lv := by
    rw [← he2, Equiv.symm_apply_apply]
  rw [hx0, hl0, ← hJrange] at hmodel
  have H : burnsideF45_G2dHex (incl M₁ M₂).graph J (incl M₁ M₂).xv (incl M₁ M₂).lv :=
    { compat := fun g w => by
        show e.symm (J g • e w) = g • w
        rw [show J g • e w = e (g • w) from (heq g w).symm, Equiv.symm_apply_apply]
      inj := (burnsideF4h_g2_incl_injective hK).comp
        (π.injective.comp (burnsideF45_eIso hyp).injective)
      index := by
        rw [hJrange]
        exact burnsideF4h_g2_incl_index hK
      poly := burnsideF4gG2Two_polygon_derived hyp
      three := burnsideF45_g2d_three hyp
      col := ⟨CosetGeom.vtype, fun a b h => CosetGeom.vtype_ne_of_adj h,
        fun g => by rw [CosetGeom.vtype_smul]; rfl, fun g => by rw [CosetGeom.vtype_smul]; rfl⟩
      vert := fun w => by
        obtain ⟨g, hg⟩ := exists_smul_eq_baseVert (incl M₁ M₂) w
        cases hv : CosetGeom.vtype w
        · rw [hv] at hg
          exact ⟨g, Or.inl hg⟩
        · rw [hv] at hg
          exact ⟨g, Or.inr hg⟩
      flag := fun u w h => CosetGeom.exists_smul_edge h
      qfix := fun u h hh a ha => by
        obtain ⟨w, hw⟩ := CosetGeom.exists_adj u
        have := (burnsideF45_C6_abe hyp Nat.prime_two (burnsideF45_three_le_m _) hP hw).2.1
        rw [burnsideF45_g2d_Qu hyp] at this
        exact this a ha h hh
      model := hmodel }
  refine ⟨burnsideF45_g2d_C6 hyp hP hB, ?_, ?_⟩
  · exact ⟨H.pathTrans_x, H.pathTrans_l, H.orbits_l,
      fun v hv q₁ hq₁ h₁ q₂ hq₂ h₂ hq r₁ hr₁ h₁' r₂ hr₂ h₂' hr =>
        H.twoTrans_l hv hq₁ h₁ hq₂ h₂ hq hr₁ h₁' hr₂ h₂' hr⟩
  · intro u v huv
    refine ⟨fun hu => ?_, fun hu => Or.inr ?_⟩
    · obtain ⟨g, hg⟩ := exists_smul_eq_baseVert (incl M₁ M₂) u
      rw [hu] at hg
      rw [burnsideF45_g2d_Qu hyp]
      exact H.complement_line ⟨g, hg⟩ huv
    · obtain ⟨g, hg⟩ := exists_smul_eq_baseVert (incl M₁ M₂) u
      rw [hu] at hg
      exact H.point_iso ⟨g, hg⟩ huv

end CFSG.ASVolI
