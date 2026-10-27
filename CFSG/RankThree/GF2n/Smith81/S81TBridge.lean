module

public import CFSG.RankThree.GF2n.Smith81.S81TModelDef
public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Smith81.S81UTheta
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.E3LCond
open scoped commutatorElement

theorem mem_closure_symm_E {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (f : A ≃+ A')
    {S : Set A} {S' : Set A'} (hS : ∀ b ∈ S', f.symm b ∈ S) {b : A'}
    (hb : b ∈ AddSubgroup.closure S') : f.symm b ∈ AddSubgroup.closure S := by
  induction hb using AddSubgroup.closure_induction with
  | mem b hb => exact AddSubgroup.subset_closure (hS b hb)
  | zero => rw [map_zero]; exact zero_mem _
  | add b c _ _ hb hc => rw [map_add]; exact add_mem hb hc
  | neg b _ hb => rw [map_neg]; exact neg_mem hb

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {E' : Type} [AddCommGroup E'] [Module K E'] {ψ : M₀.E ≃ₗ[K] E'}
  {φ : Lgen M (LB M Q B) →* (E' ≃ₗ[K] E')} {Γ : Subgroup (E' ≃ₗ[K] E')} {p₀ : E'}
  {U₀ : Subgroup (E' ≃ₗ[K] E')} {X : Subgroup G} {x : G}

theorem exists_lift_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {g : E' ≃ₗ[K] E'} (hg : g ∈ Γ) :
    ∃ s : Lgen M (LB M Q B), φ s = g := by
  rw [← d.range] at hg
  obtain ⟨s, hs⟩ := hg
  exact ⟨s, hs⟩

theorem psi_T_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G} (hxL : x ∈ Lgen M (LB M Q B))
    (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t) (e' : M₀.E) :
    ψ (Tx.T e') = t (ψ e') := by
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj e'
  rw [← Tx.hπ y hy, d.equivariant ⟨x, hxL⟩ y hy, hφ]

theorem mem_Cs_iff_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G} (hxL : x ∈ Lgen M (LB M Q B))
    (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t) {e' : M₀.E} :
    e' ∈ Cs Tx ↔ ψ e' ∈ CwE t := by
  rw [mem_Cs, ← ψ.injective.eq_iff, psi_T_E d hxL Tx hφ]
  exact Iff.rfl

theorem mem_Rs_iff_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G} (hxL : x ∈ Lgen M (LB M Q B))
    (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t) {r : M₀.E} :
    r ∈ Rs Tx ↔ ψ r ∈ RwE t := by
  rw [mem_Rs]
  constructor
  · rintro ⟨e', he'⟩
    refine ⟨ψ e', ?_⟩
    have h1 : ψ (Tx.T e' - e') = ψ r := by rw [he']
    rw [map_sub, psi_T_E d hxL Tx hφ] at h1
    exact h1.symm
  · rintro ⟨w, hw⟩
    refine ⟨ψ.symm w, ψ.injective ?_⟩
    rw [map_sub, psi_T_E d hxL Tx hφ, LinearEquiv.apply_symm_apply]
    exact hw.symm

theorem comm_mem_Q_of_lift_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x u : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (hu : u ∈ Lgen M (LB M Q B)) {t g : E' ≃ₗ[K] E'}
    (hφx : φ ⟨x, hxL⟩ = t) (hφu : φ ⟨u, hu⟩ = g) (hcomm : g * t = t * g) : ⁅u, x⁆ ∈ Q := by
  have h1 : φ (⟨u, hu⟩ * ⟨x, hxL⟩ * ⟨u, hu⟩⁻¹ * ⟨x, hxL⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφx, hφu, hcomm]
    group
  have := (d.ker _).mp h1
  simpa [commutatorElement_def] using this

theorem rootPt_of_orbit (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (Hs : StrothHyp M Q Z) {v : E'}
    (hv0 : v ≠ 0) (hv : ∃ g ∈ Γ, ∃ c : K, v = c • g p₀) : RootPt M₀ (ψ.symm v) := by
  obtain ⟨g, hg, c, rfl⟩ := hv
  obtain ⟨A₀, hctx₀⟩ := exists_ctx_of_strothHyp Hs
  obtain ⟨g₀, hg₀, himg₀, -⟩ := d.point A₀ hctx₀.conj hctx₀.le hctx₀.ne
  have hmem : c • g₀ p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (A₀ : Set G) := by
    rw [himg₀]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hmem
  obtain ⟨s, hs⟩ := exists_lift_E d (mul_mem hg (inv_mem hg₀))
  obtain ⟨g', hg'⟩ := hctx₀.conj
  have hsQ : ∀ y ∈ Q, (s : G) * y * (s : G)⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (d.le_normalizer s.2) y).mp hy
  have hA₀Q : a₀ ∈ Q := hctx₀.le ha₀
  have haA : (s : G) * a₀ * (s : G)⁻¹ ∈ conjSubgroup (s : G) A₀ := by
    rw [mem_conjSubgroup]
    have e' : (s : G)⁻¹ * ((s : G) * a₀ * (s : G)⁻¹) * (s : G) = a₀ := by group
    rw [e']
    exact ha₀
  have hψa : ψ (M₀.π ((s : G) * a₀ * (s : G)⁻¹)) = c • g p₀ := by
    have ha₀eq' : ψ (M₀.π a₀) = c • g₀ p₀ := ha₀eq
    rw [d.equivariant s a₀ hA₀Q, ha₀eq', hs, LinearEquiv.map_smul]
    rw [← LinearEquiv.mul_apply, mul_assoc, inv_mul_cancel, mul_one]
  have haQ : (s : G) * a₀ * (s : G)⁻¹ ∈ Q := hsQ a₀ hA₀Q
  refine Or.inr ⟨conjSubgroup (s : G) A₀, ⟨(s : G) * g', by rw [hg', conjSubgroup_mul]⟩, ?_, ?_,
    _, haA, by rw [← hψa, LinearEquiv.symm_apply_apply]⟩
  · intro y hy
    have h1 : (s : G)⁻¹ * y * (s : G) ∈ Q := hctx₀.le (mem_conjSubgroup.mp hy)
    have e' : y = (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ := by group
    rw [e']
    exact hsQ _ h1
  · intro hAZ
    have haZ : (s : G) * a₀ * (s : G)⁻¹ ∈ Z := hAZ ▸ haA
    apply hv0
    rw [← hψa, (M₀.π_ker _ haQ).mpr haZ, map_zero]

theorem covC_transport_E (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t)
    (hC : ∀ c ∈ CwE t, ∃ r ∈ RwE t, c - r ∈
      AddSubgroup.closure {v | ∃ g ∈ GcentE Γ t, ∃ c' ∈ CwE t, v = g c' - c'}) :
    ∀ c ∈ Cs Tx, c ∈ (Rs Tx).toAddSubgroup ⊔ AddSubgroup.closure
      {f | ∃ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ GcentE Γ t, φ ⟨u, hu⟩ = g},
        ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧ f = M₀.π (u * w * u⁻¹) - M₀.π w} := by
  intro c hcCs
  have hcw : ψ c ∈ CwE t := (mem_Cs_iff_E d hxL Tx hφ).mp hcCs
  obtain ⟨r, hr, hb⟩ := hC _ hcw
  have hr' : ψ.symm r ∈ Rs Tx := by
    rw [mem_Rs_iff_E d hxL Tx hφ, LinearEquiv.apply_symm_apply]
    exact hr
  have hS : ∀ b ∈ {v : E' | ∃ g ∈ GcentE Γ t, ∃ c' ∈ CwE t, v = g c' - c'},
      ψ.toAddEquiv.symm b ∈ {f : M₀.E | ∃ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B),
        ∃ g ∈ GcentE Γ t, φ ⟨u, hu⟩ = g}, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧
          f = M₀.π (u * w * u⁻¹) - M₀.π w} := by
    rintro b ⟨g, hg, c', hc', rfl⟩
    obtain ⟨s, hs⟩ := exists_lift_E d hg.1
    obtain ⟨a, ha, hpa⟩ := M₀.π_surj (ψ.symm c')
    have hψa : ψ (M₀.π a) = c' := by rw [hpa, LinearEquiv.apply_symm_apply]
    have hacs : M₀.π a ∈ Cs Tx := by
      rw [mem_Cs_iff_E d hxL Tx hφ, hψa]
      exact hc'
    refine ⟨(s : G), ⟨s.2, g, hg, hs⟩, a, ha, hacs, ?_⟩
    refine (LinearEquiv.symm_apply_eq (e := ψ)).mpr ?_
    rw [map_sub, d.equivariant s a ha, hs, hψa]
  have hbS : ψ c - r ∈ AddSubgroup.closure
      {v : E' | ∃ g ∈ GcentE Γ t, ∃ c' ∈ CwE t, v = g c' - c'} := hb
  have hz := mem_closure_symm_E ψ.toAddEquiv hS hbS
  have h2 : ψ.toAddEquiv.symm (ψ c - r) = c - ψ.symm r := by
    show ψ.symm (ψ c - r) = _
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [AddSubgroup.mem_sup]
  exact ⟨ψ.symm r, hr', c - ψ.symm r, h2 ▸ hz, by abel⟩

theorem P3_transport_E (hc : Ctx M Q Z B) (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t)
    (U : Set (E' ≃ₗ[K] E')) (hUc : ∀ u ∈ U, u ∈ GcentE Γ t)
    (hUC : ∀ u ∈ U, ∀ c ∈ CwE t, u c - c ∈ RwE t)
    (hUfix : ∀ c ∈ CwE t, (∀ u ∈ U, u c = c) → c ∈ RwE t) :
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = g}, u ∈ H0 M Z) ∧
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = g}, ⁅u, x⁆ ∈ Q) ∧
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = g},
      ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx) ∧
    (∀ e' ∈ Cs Tx, (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U,
        φ ⟨u, hu⟩ = g}, ∀ w ∈ Q, M₀.π w = e' → M₀.π (u * w * u⁻¹) = e') → e' ∈ Rs Tx) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  · rintro u ⟨hu, g, hg, hφu⟩
    exact comm_mem_Q_of_lift_E d hxL hu hφ hφu (hUc g hg).2
  · rintro u ⟨hu, g, hg, hφu⟩ w hw hwC
    have hψ : ψ (M₀.π (u * w * u⁻¹)) = g (ψ (M₀.π w)) := by
      have := d.equivariant ⟨u, hu⟩ w hw
      rw [hφu] at this
      exact this
    have hsub : ψ (M₀.π (u * w * u⁻¹) - M₀.π w) = g (ψ (M₀.π w)) - ψ (M₀.π w) := by
      rw [map_sub, hψ]
    rw [mem_Rs_iff_E d hxL Tx hφ, hsub]
    exact hUC g hg _ ((mem_Cs_iff_E d hxL Tx hφ).mp hwC)
  · intro e' he' hfix
    rw [mem_Rs_iff_E d hxL Tx hφ]
    refine hUfix (ψ e') ((mem_Cs_iff_E d hxL Tx hφ).mp he') (fun u₀ hu₀ => ?_)
    obtain ⟨su, hsu⟩ := exists_lift_E d (hUc u₀ hu₀).1
    obtain ⟨w, hw, hwe⟩ := M₀.π_surj e'
    have h1 := hfix (su : G) ⟨su.2, u₀, hu₀, hsu⟩ w hw hwe
    have h2 := d.equivariant su w hw
    rw [hsu, hwe, h1] at h2
    exact h2.symm

theorem P2_transport_E (hc : Ctx M Q Z B) (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t)
    (hP2 : ∀ S : AddSubgroup E', S ≠ ⊥ → (∀ s ∈ S, s ∈ RwE t) →
      (∀ a ∈ GcentE Γ t, ∀ b ∈ GcentE Γ t, ∀ s ∈ S, (a * b * a⁻¹ * b⁻¹) s ∈ S) →
      ∃ p ∈ S, p ≠ 0 ∧ ∃ g ∈ Γ, ∃ c : K, p = c • g p₀) :
    ∀ S : AddSubgroup M₀.E, S ≠ ⊥ → (∀ s ∈ S, s ∈ Rs Tx) →
      (∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ S → M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ S) →
      ∃ e' ∈ S, e' ≠ 0 ∧ RootPt M₀ e' := by
  intro S hS hSR hSstab
  let f : M₀.E →+ E' := ψ.toLinearMap.toAddMonoidHom
  have hS' : (S.map f : AddSubgroup E') ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff]
    intro v hv
    have h1 : f v ∈ (S.map f : AddSubgroup E') := ⟨v, hv, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h1
    have h2 : ψ v = 0 := h1
    have h3 : v = 0 := ψ.injective (h2.trans (map_zero ψ).symm)
    simp [h3]
  have hR' : ∀ s ∈ (S.map f : AddSubgroup E'), s ∈ RwE t := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_Rs_iff_E d hxL Tx hφ).mp (hSR v hv)
  have hstab : ∀ a ∈ GcentE Γ t, ∀ b ∈ GcentE Γ t, ∀ s ∈ (S.map f : AddSubgroup E'),
      (a * b * a⁻¹ * b⁻¹) s ∈ (S.map f : AddSubgroup E') := by
    intro a ha b hb s hs
    obtain ⟨v, hv, rfl⟩ := hs
    obtain ⟨sa, hsa⟩ := exists_lift_E d ha.1
    obtain ⟨sb, hsb⟩ := exists_lift_E d hb.1
    have hax : ⁅(sa : G), x⁆ ∈ Q := comm_mem_Q_of_lift_E d hxL sa.2 hφ hsa ha.2
    have hbx : ⁅(sb : G), x⁆ ∈ Q := comm_mem_Q_of_lift_E d hxL sb.2 hφ hsb hb.2
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj v
    have key := hSstab (sa : G) (sb : G) (Lgen_le_H0 hc sa.2) (Lgen_le_H0 hc sb.2) hax hbx y hy hv
    refine ⟨M₀.π (⁅(sa : G), (sb : G)⁆ * y * ⁅(sa : G), (sb : G)⁆⁻¹), key, ?_⟩
    have h1 := d.equivariant ⁅sa, sb⁆ y hy
    have h2 : φ ⁅sa, sb⁆ = a * b * a⁻¹ * b⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv, hsa, hsb]
    have h3 : ((⁅sa, sb⁆ : Lgen M (LB M Q B)) : G) = ⁅(sa : G), (sb : G)⁆ := by
      simp [commutatorElement_def]
    rw [h2, h3] at h1
    exact h1
  obtain ⟨p, hpS, hp0, hpP⟩ := hP2 (S.map f : AddSubgroup E') hS' hR' hstab
  obtain ⟨v, hv, rfl⟩ := hpS
  refine ⟨v, hv, fun h => hp0 (by rw [h]; exact map_zero f), ?_⟩
  have hr := rootPt_of_orbit d hc.hyp hp0 hpP
  have hfv : f v = ψ v := rfl
  rw [hfv, LinearEquiv.symm_apply_apply] at hr
  exact hr

theorem e28_of_involK12 {β' : E' → E' → K} (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {lam : K}
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β' (ψ e) (ψ f)) (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t)
    (hM : InvolK12 Γ p₀ β' t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  obtain ⟨U, hUc, hUC, hUfix⟩ := hM.P3
  obtain ⟨hU0, hUx, hUCG, hUfixG⟩ := P3_transport_E hc d hxL Tx hφ U hUc hUC hUfix
  have hV0 : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ GcentE Γ t, φ ⟨u, hu⟩ = g},
      u ∈ H0 M Z := by
    rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  have hVx : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ GcentE Γ t, φ ⟨u, hu⟩ = g},
      ⁅u, x⁆ ∈ Q := by
    rintro u ⟨hu, g, hg, hφu⟩
    exact comm_mem_Q_of_lift_E d hxL hu hφ hφu hg.2
  have hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0 := by
    intro r hr
    obtain ⟨e', rfl⟩ := mem_Rs.mp hr
    rw [Qf_sub hs Tx e', hform, psi_T_E d hxL Tx hφ, hM.qfR, mul_zero]
  exact e3l28_root_of_coinv hs hD Tx hQf _ hV0 hVx (covC_transport_E d hxL Tx hφ hM.covC)
    _ hU0 hUx hUCG hUfixG (P2_transport_E hc d hxL Tx hφ hM.P2) hne

theorem e28_of_involK3 {β' : E' → E' → K} (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β' (ψ e) (ψ f)) (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) {t : E' ≃ₗ[K] E'} (hφ : φ ⟨x, hxL⟩ = t)
    (hM : InvolK3 Γ β' t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  refine e3l28_root_of_k3 hs hD Tx ?_ ?_ hne
  · intro e' he'
    rw [mem_Rs_iff_E d hxL Tx hφ]
    exact hM.CR _ ((mem_Cs_iff_E d hxL Tx hφ).mp he')
  · obtain ⟨v, hv⟩ := hM.qf_ne
    refine ⟨Tx.T (ψ.symm v) - ψ.symm v, mem_Rs.mpr ⟨_, rfl⟩, ?_⟩
    rw [Qf_sub hs Tx, hform, psi_T_E d hxL Tx hφ, LinearEquiv.apply_symm_apply]
    exact mul_ne_zero hlam hv

end CFSG.RankThree.GF2n.Smith81.MinuscT
