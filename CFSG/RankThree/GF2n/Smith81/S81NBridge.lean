module

public import CFSG.RankThree.GF2n.Smith81.S81NThmA
public import CFSG.RankThree.GF2n.Smith81.S81NModelDef
public import CFSG.RankThree.GF2n.Smith81.S81LRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LBridge

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LCond
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ψ : M₀.E ≃ₗ[K] Cube K} {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}

theorem exists_lift (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {g : GL (Fin 6) K}
    (hg : (g : Matrix (Fin 6) (Fin 6) K).det = 1) :
    ∃ s : Lgen M (LB M Q B), φ s = rhoEquiv K g := by
  have hgG : rhoEquiv K g ∈ Gam K :=
    Subgroup.mem_map_of_mem _ (CFSG.Open.StatedAPI.mem_statedSL_of_det hg)
  rw [← d.range] at hgG
  obtain ⟨s, hs⟩ := hgG
  exact ⟨s, hs⟩

theorem psi_T (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) (e : M₀.E) : ψ (Tx.T e) = rho K t (ψ e) := by
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
  rw [← Tx.hπ y hy, d.equivariant ⟨x, hxL⟩ y hy, hφ]
  rfl

theorem mem_Cs_iff (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) {e : M₀.E} :
    e ∈ Cs Tx ↔ ψ e ∈ LinearMap.ker (rho K t - 1) := by
  rw [mem_Cs, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    ← psi_T d hxL Tx hφ, ψ.injective.eq_iff]

theorem mem_Rs_iff (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) {r : M₀.E} :
    r ∈ Rs Tx ↔ ψ r ∈ LinearMap.range (rho K t - 1) := by
  rw [mem_Rs]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨ψ e, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, ← psi_T d hxL Tx hφ, ← map_sub, he]
  · rintro ⟨ξ, hξ⟩
    refine ⟨ψ.symm ξ, ψ.injective ?_⟩
    rw [map_sub, psi_T d hxL Tx hφ, LinearEquiv.apply_symm_apply, ← hξ,
      LinearMap.sub_apply, Module.End.one_apply]

theorem rootPt_of_pure (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (H : StrothHyp M Q Z) {ξ : Cube K} (hξ : IsPure K ξ) : RootPt M₀ (ψ.symm ξ) := by
  by_cases h0 : ξ = 0
  · left
    rw [h0, map_zero]
  · obtain ⟨A, hA, hAQ, hAZ, a, haA, ha⟩ := d.exists_root_group H hξ h0
    right
    exact ⟨A, hA, hAQ, hAZ, a, haA, by rw [← ha, LinearEquiv.symm_apply_apply]⟩

theorem comm_mem_Q_of_lift (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {x u : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (hu : u ∈ Lgen M (LB M Q B)) {t u₀ : GL (Fin 6) K}
    (hφx : φ ⟨x, hxL⟩ = rhoEquiv K t) (hφu : φ ⟨u, hu⟩ = rhoEquiv K u₀)
    (hcomm : u₀ * t = t * u₀) : ⁅u, x⁆ ∈ Q := by
  have h1 : φ (⟨u, hu⟩ * ⟨x, hxL⟩ * ⟨u, hu⟩⁻¹ * ⟨x, hxL⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφx, hφu]
    have : rhoEquiv K u₀ * rhoEquiv K t = rhoEquiv K t * rhoEquiv K u₀ := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [this]
    group
  have := (d.ker _).mp h1
  simpa [commutatorElement_def] using this

section Main

variable {X : Subgroup G} {x : G}

theorem qf_zero_of_QfR (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) {lam : K}
    (hB : ∀ e f : M₀.E, M₀.B e f = lam * beta K (ψ e) (ψ f))
    (hQ : LinearMap.range (rho K t - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K t - 1) ∧
        ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂}) :
    ∀ r ∈ Rs Tx, M₀.Qf r = 0 := by
  have H : StrothHyp M Q Z := hs.hyp
  have hspan : Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K t - 1) ∧
        ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂} ≤
      LinearMap.range (rho K t - 1) :=
    Submodule.span_le.mpr fun ξ hξ => hξ.1
  have key : ∀ ξ ∈ Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K t - 1) ∧
        ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂},
      M₀.Qf (ψ.symm ξ) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, p₁, p₂, h1, h2, hβ, rfl⟩ := hx
      rw [map_add, M₀.Qf_add, Qf_RootPt hD (rootPt_of_pure d H h1),
        Qf_RootPt hD (rootPt_of_pure d H h2), hB]
      simp [hβ]
    | zero => simp [Tim79.QuadModel.Qf_zero]
    | add x y hxs hys hx hy =>
      have hxR : ψ.symm x ∈ Rs Tx := by
        rw [mem_Rs_iff d hxL Tx hφ]; simpa using hspan hxs
      have hyR : ψ.symm y ∈ Rs Tx := by
        rw [mem_Rs_iff d hxL Tx hφ]; simpa using hspan hys
      rw [map_add, M₀.Qf_add, hx, hy, B_Rs_Rs hs Tx hxR hyR]
      simp
    | smul a x hxs hx =>
      rw [map_smul, M₀.Qf_smul, hx]
      simp
  intro r hr
  have h1 : ψ r ∈ LinearMap.range (rho K t - 1) := (mem_Rs_iff d hxL Tx hφ).mp hr
  have := key (ψ r) (hQ h1)
  simpa using this

theorem e3l28_of_involModel12 (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (hform : ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * beta K (ψ e) (ψ f))
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) (hM : InvolModel12 K t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have H : StrothHyp M Q Z := hs.hyp
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  have hCs : ∀ {e : M₀.E}, e ∈ Cs Tx ↔ ψ e ∈ LinearMap.ker (rho K t - 1) :=
    fun {e} => mem_Cs_iff d hxL Tx hφ
  have hRs : ∀ {r : M₀.E}, r ∈ Rs Tx ↔ ψ r ∈ LinearMap.range (rho K t - 1) :=
    fun {r} => mem_Rs_iff d hxL Tx hφ
  obtain ⟨lam, hlam, hB⟩ := hform
  obtain ⟨U, hUdet, hUcomm, hUCm, hUfixm⟩ := hM.P3
  obtain ⟨P, hPcomm, hP2m⟩ := hM.P2
  have hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e} := by
    intro e he
    have h1 : ψ e ∈ Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K t - 1) ∧ IsPure K ξ} :=
      hM.P1 (hCs.mp he)
    have h2 := Submodule.mem_map_of_mem (f := (ψ.symm : Cube K →ₗ[K] M₀.E)) h1
    rw [Submodule.map_span] at h2
    have h3 : e ∈ Submodule.span K ((ψ.symm : Cube K →ₗ[K] M₀.E) ''
        {ξ | ξ ∈ LinearMap.ker (rho K t - 1) ∧ IsPure K ξ}) := by
      simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h2
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨ξ, ⟨hξC, hξP⟩, rfl⟩
    refine ⟨?_, rootPt_of_pure d H hξP⟩
    rw [hCs]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hξC
  have hQf := qf_zero_of_QfR hD d hs hxL Tx hφ hB hM.QfR
  refine e3l28_root_of_model12 hs hD Tx hP1 hQf
    {u | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ u₀ ∈ U, φ ⟨u, hu⟩ = rhoEquiv K u₀} ?_ ?_ ?_ ?_ ?_ hne
  · rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  · rintro u ⟨hu, u₀, hu₀, hφu⟩
    exact comm_mem_Q_of_lift d hxL hu hφ hφu (hUcomm u₀ hu₀)
  · rintro u ⟨hu, u₀, hu₀, hφu⟩ w hw hwC
    have hψ : ψ (M₀.π (u * w * u⁻¹)) = rho K u₀ (ψ (M₀.π w)) := by
      have := d.equivariant ⟨u, hu⟩ w hw
      rw [hφu] at this
      exact this
    rw [hRs, map_sub, hψ]
    exact hUCm u₀ hu₀ (ψ (M₀.π w)) (hCs.mp hwC)
  · intro e he hfix
    rw [hRs]
    refine hUfixm (ψ e) (hCs.mp he) fun u₀ hu₀ => ?_
    obtain ⟨su, hsu⟩ := exists_lift d (hUdet u₀ hu₀)
    obtain ⟨w, hw, hwe⟩ := M₀.π_surj e
    have h1 := hfix (su : G) ⟨su.2, u₀, hu₀, hsu⟩ w hw hwe
    have h2 := d.equivariant su w hw
    rw [hsu, hwe, h1] at h2
    exact h2.symm
  · intro S hS hSR hSstab
    let f : M₀.E →+ Cube K := ψ.toLinearMap.toAddMonoidHom
    have hS' : S.map f ≠ ⊥ := by
      intro h
      apply hS
      rw [eq_bot_iff]
      intro e he
      have h1 : f e ∈ S.map f := ⟨e, he, rfl⟩
      rw [h, AddSubgroup.mem_bot] at h1
      have : e = 0 := ψ.injective (by simpa [f] using h1)
      simp [this]
    have hR' : ∀ s ∈ S.map f, s ∈ LinearMap.range (rho K t - 1) := by
      rintro _ ⟨e, heS, rfl⟩
      exact hRs.mp (hSR e heS)
    have hstab : ∀ u ∈ P, ∀ s ∈ S.map f, rho K u s ∈ S.map f := by
      intro u hu s hs
      obtain ⟨a₀, b₀, ha0, hb0, hat, hbt, rfl⟩ := hPcomm u hu
      obtain ⟨e, heS, rfl⟩ := hs
      obtain ⟨sa, hsa⟩ := exists_lift d ha0
      obtain ⟨sb, hsb⟩ := exists_lift d hb0
      have hax := comm_mem_Q_of_lift d hxL sa.2 hφ hsa hat
      have hbx := comm_mem_Q_of_lift d hxL sb.2 hφ hsb hbt
      obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
      have key := hSstab (sa : G) (sb : G) (Lgen_le_H0 hc sa.2) (Lgen_le_H0 hc sb.2) hax hbx y hy heS
      refine ⟨M₀.π (⁅(sa : G), (sb : G)⁆ * y * ⁅(sa : G), (sb : G)⁆⁻¹), key, ?_⟩
      have h1 := d.equivariant ⁅sa, sb⁆ y hy
      have h2 : φ ⁅sa, sb⁆ = rhoEquiv K ⁅a₀, b₀⁆ := by
        rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
          map_inv, map_mul, map_mul, map_mul, map_inv, map_inv, hsa, hsb]
      have h3 : ((⁅sa, sb⁆ : Lgen M (LB M Q B)) : G) = ⁅(sa : G), (sb : G)⁆ := by
        simp [commutatorElement_def]
      rw [h2, h3] at h1
      exact h1
    obtain ⟨p, hpS, hp0, hpP⟩ := hP2m (S.map f) hS' hR' hstab
    obtain ⟨e, heS, rfl⟩ := hpS
    refine ⟨e, heS, fun h => hp0 (by simp [f, h]), ?_⟩
    have := rootPt_of_pure d H hpP
    simpa [f] using this

theorem e3l28_of_involModel3 (hD : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K))
    (hform : ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * beta K (ψ e) (ψ f))
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) {t : GL (Fin 6) K}
    (hφ : φ ⟨x, hxL⟩ = rhoEquiv K t) (hM : InvolModel3 K t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have H : StrothHyp M Q Z := hs.hyp
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  have hCs : ∀ {e : M₀.E}, e ∈ Cs Tx ↔ ψ e ∈ LinearMap.ker (rho K t - 1) :=
    fun {e} => mem_Cs_iff d hxL Tx hφ
  have hRs : ∀ {r : M₀.E}, r ∈ Rs Tx ↔ ψ r ∈ LinearMap.range (rho K t - 1) :=
    fun {r} => mem_Rs_iff d hxL Tx hφ
  obtain ⟨lam, hlam, hB⟩ := hform
  refine e3l28_root_of_k3 hs hD Tx ?_ ?_ hne
  · intro e he
    rw [hRs]
    exact hM.CR (hCs.mp he)
  · obtain ⟨p₁, p₂, h1, h2, hR, hβ⟩ := hM.beta_ne
    refine ⟨ψ.symm (p₁ + p₂), ?_, ?_⟩
    · rw [hRs]
      simpa only [LinearEquiv.apply_symm_apply] using hR
    · rw [map_add, M₀.Qf_add, Qf_RootPt hD (rootPt_of_pure d H h1),
        Qf_RootPt hD (rootPt_of_pure d H h2), hB]
      simp only [LinearEquiv.apply_symm_apply, zero_add]
      exact mul_ne_zero hlam hβ

end Main

end CFSG.RankThree.GF2n.Smith81.E3LBridge
