module

public import CFSG.RankThree.GF2n.Smith81.S81RFrame
public import CFSG.RankThree.GF2n.Smith81.S81RIrred
public import CFSG.RankThree.GF2n.Smith81.S81NMain
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Core
public import CFSG.RankThree.GF2n.Smith81.S81LFusion
public import CFSG.RankThree.GF2n.Smith81.S81LModel
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] {M Q Z X : Subgroup G} {x : G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

section CaseII
variable [Finite G] [CharP K 2]

private theorem x_mul_Z_comm' (hs : Sit M Q Z X x) {z : G} (hz : z ∈ Z) : x * z = z * x :=
  mul_inv_eq_iff_eq_mul.mp (hs.x_cent (smith_1_12 hs) z hz)

theorem caseII_of_nf (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    (hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e})
    (hNF : ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)) : CaseII Q Z x := by
  rcases theta_dichotomy hD hs Tx hP1 with hI | hII
  · exfalso
    obtain ⟨w, hw, hw1, -⟩ := exists_mem_Z_ne hs.hyp (1 : G)
    obtain ⟨q, hq, hqw⟩ := hI w hw
    apply hNF w hw hw1
    refine isConj_iff.mpr ⟨q, ?_⟩
    have hxw : x * w = w * x := x_mul_Z_comm' hs hw
    calc q * x * q⁻¹ = ⁅q, x⁆ * x := by rw [commutatorElement_def]; group
      _ = w * x := by rw [hqw]
      _ = x * w := hxw.symm
  · exact hII

theorem conj_eq_of_comm_mem_Q (hD : GlobalModelData M Q Z γ M₀) (hs : Sit M Q Z X x)
    (Tx : XAct M₀ x) (hII : CaseII Q Z x)
    (hNF : ∀ y : G, IsConj x y → y ∈ M → y ∉ Q → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj y (y * w))
    {u : G} (hu0 : u ∈ H0 M Z) (hux : ⁅u, x⁆ ∈ Q) :
    ∃ q ∈ Q, u * x * u⁻¹ = q * x * q⁻¹ := by
  obtain ⟨z, hzZ, q, hq, hz⟩ :=
    zetaRel_of_piComm hs Tx hu0 hux (caseII_piComm_mem_Rs hD hs Tx hII hu0 hux)
  by_cases hz1 : z = 1
  · exact ⟨q, hq, by rw [hz, hz1, mul_one]⟩
  · exfalso
    have H := hs.hyp
    have hqM : q ∈ M := H.Q_normal.1 hq
    have hyM : q * x * q⁻¹ ∈ M := M.mul_mem (M.mul_mem hqM hs.memM) (M.inv_mem hqM)
    have hyQ : q * x * q⁻¹ ∉ Q := by
      intro hyQ
      apply hs.notQ
      have h1 : q⁻¹ * (q * x * q⁻¹) * q ∈ Q := Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hyQ) hq
      simpa [mul_assoc] using h1
    have hyc : IsConj x (q * x * q⁻¹) := isConj_iff.mpr ⟨q, rfl⟩
    apply hNF _ hyc hyM hyQ z hzZ hz1
    have hxu : IsConj x (u * x * u⁻¹) := isConj_iff.mpr ⟨u, rfl⟩
    rw [← hz]
    exact hyc.symm.trans hxu

end CaseII

section Frame
variable [Finite G] [CharP K 2]

private theorem transvGL_comm_tInv1' (i j : Fin 6) (hij : i ≠ j) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (c : K) : transvGL K i j hij c * tInv1 K = tInv1 K * transvGL K i j hij c := by
  apply Units.ext
  simp only [Units.val_mul, transvGL_val, tInv1, Matrix.transvection]
  have h1 : Matrix.single i j c * Matrix.single (0 : Fin 6) (1 : Fin 6) (1 : K) = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    · intro h; omega
  have h2 : Matrix.single (0 : Fin 6) (1 : Fin 6) (1 : K) * Matrix.single i j c = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    · intro h; omega
  simp only [add_mul, mul_add, mul_one, one_mul, h1, h2, add_zero]
  abel

theorem phi_eq_of_mul_mem_Q {B : Subgroup G} {ψ : M₀.E ≃ₗ[K] Cube K}
    {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)}
    (d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)) {s : Lgen M (LB M Q B)}
    (hsx : (s : G) * x⁻¹ ∈ Q) :
    ∃ hxL : x ∈ Lgen M (LB M Q B), φ ⟨x, hxL⟩ = φ s := by
  have hxs : x * (s : G)⁻¹ ∈ Q := by
    have := Q.inv_mem hsx
    simpa [mul_inv_rev] using this
  have hxL : x ∈ Lgen M (LB M Q B) := by
    have h1 : x * (s : G)⁻¹ ∈ Lgen M (LB M Q B) := Q_le_Lgen M Q B hxs
    have h2 := (Lgen M (LB M Q B)).mul_mem h1 s.2
    simpa using h2
  refine ⟨hxL, ?_⟩
  have h : φ (⟨x, hxL⟩ * s⁻¹) = 1 := (d.ker _).mpr (by simpa using hxs)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

end Frame

section Main

theorem smith212E3LRoot_of_inputs (hFE1 : Smith24E3LUniformStatement)
    (hFE2 : E3LRootEltStatement) (hNF : Smith212ENonfusedE3LStatement) :
    Smith212E3LRootStatement := by
  intro G _ _ M Q Z B IH hrem hc z hz hz1 x hxM hxQ hxc X hX hxX
  have hc3 : InCaseE3L M Q Z B := hc
  obtain ⟨t, ht, hL⟩ := hc
  have hSE : SmithECfg M Q Z B :=
    ⟨hrem.toCfg, t, ht, Or.inl ((caseE3_iff M Q Z B).mpr (Or.inr hL))⟩
  have H : StrothHyp M Q Z := hrem.ctx.hyp
  have hs : Sit M Q Z X x := ⟨H, hX, hxX, ne_one_of_isConj_Z hz1 hxc, hxM, hxQ⟩
  have h12 := smith_1_12 hs
  have hNFx : ∀ y : G, IsConj x y → y ∈ M → y ∉ Q → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj y (y * w) :=
    fun y hyc hyM hyQ w hw hw1 =>
      hNF G M Q Z B IH hSE hc3 z hz hz1 y hyM hyQ (hxc.trans hyc) w hw hw1
  have hne : Q ⊓ QB X ≠ ⊥ :=
    smith28aE3L_of_normQuot (normQuotE3L_of_uniform hFE1) (elemBoundE3L_of_uniform hFE1)
      G M Q Z B IH hSE hc3 X x hs
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hrem hc3 K γ M₀ hD
  obtain ⟨s, hsq, g, hg, hφs⟩ := hFE2 G M Q Z B IH hrem hc3 K γ M₀ hD ψ φ d z hz hz1 x hxc hxM hxQ
  obtain ⟨hxL, hφx⟩ := phi_eq_of_mul_mem_Q (x := x) d hsq
  obtain ⟨c, hcdet, hcg⟩ := exists_conj_tInv1 hg
  have d' := d.transport hcdet
  have hφ' : ((MulAut.conj (rhoEquiv K c)).toMonoidHom.comp φ) ⟨x, hxL⟩ =
      rhoEquiv K (tInv1 K) := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφx, hφs,
      ← map_inv, ← map_mul, ← map_mul, hcg]
  generalize hψ'e : ψ.trans (rhoEquiv K c) = ψ' at d'
  generalize hφ'e : (MulAut.conj (rhoEquiv K c)).toMonoidHom.comp φ = φ' at d' hφ'
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  have hCs : ∀ {e : M₀.E}, e ∈ Cs Tx ↔ ψ' e ∈ LinearMap.ker (rho K (tInv1 K) - 1) :=
    fun {e} => mem_Cs_iff d' hxL Tx hφ'
  have hRs : ∀ {r : M₀.E}, r ∈ Rs Tx ↔ ψ' r ∈ LinearMap.range (rho K (tInv1 K) - 1) :=
    fun {r} => mem_Rs_iff d' hxL Tx hφ'
  have hP1 : Cs Tx ≤ Submodule.span K {e | e ∈ Cs Tx ∧ RootPt M₀ e} := by
    intro e he
    have h1 : ψ' e ∈ Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1) ∧
        IsPure K ξ} := model1_P1 (hCs.mp he)
    have h2 := Submodule.mem_map_of_mem (f := (ψ'.symm : Cube K →ₗ[K] M₀.E)) h1
    rw [Submodule.map_span] at h2
    have h3 : e ∈ Submodule.span K ((ψ'.symm : Cube K →ₗ[K] M₀.E) ''
        {ξ | ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1) ∧ IsPure K ξ}) := by
      simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h2
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨ξ, ⟨hξC, hξP⟩, rfl⟩
    refine ⟨?_, rootPt_of_pure d' H hξP⟩
    rw [hCs]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hξC
  have hII : CaseII Q Z x :=
    caseII_of_nf hD hs Tx hP1 (fun w hw hw1 => hNFx x (IsConj.refl x) hxM hxQ w hw hw1)
  obtain ⟨⟨d₁, hd₁⟩, hd₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hd₁1' : d₁ ≠ 1 := fun h => hd₁1 (Subtype.ext h)
  have hd₁0 : M₀.π d₁ ≠ 0 := fun h0 => hd₁1' (D_eq_one_of_pi_eq_zero hs hd₁ h0)
  have hS0 : piSub M₀ (Q ⊓ QB X) inf_le_left ≠ ⊥ := by
    intro hS
    have hmem : M₀.π d₁ ∈ piSub M₀ (Q ⊓ QB X) inf_le_left := mem_piSub.mpr ⟨d₁, hd₁, rfl⟩
    rw [hS, AddSubgroup.mem_bot] at hmem
    exact hd₁0 hmem
  have hSR : ∀ e ∈ piSub M₀ (Q ⊓ QB X) inf_le_left, e ∈ Rs Tx := by
    intro e he
    obtain ⟨d₀, hd₀, rfl⟩ := mem_piSub.mp he
    exact caseII_piD_le_R hD hs Tx hII hd₀
  let f : M₀.E →+ Cube K := ψ'.toLinearMap.toAddMonoidHom
  have hS' : (piSub M₀ (Q ⊓ QB X) inf_le_left).map f ≠ ⊥ := by
    intro h
    apply hS0
    rw [eq_bot_iff]
    intro e he
    have h1 : f e ∈ (piSub M₀ (Q ⊓ QB X) inf_le_left).map f := ⟨e, he, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h1
    have : e = 0 := ψ'.injective (by simpa [f] using h1)
    simp [this]
  have hSR' : ∀ e ∈ (piSub M₀ (Q ⊓ QB X) inf_le_left).map f,
      e ∈ LinearMap.range (rho K (tInv1 K) - 1) := by
    rintro _ ⟨e, heS, rfl⟩
    exact hRs.mp (hSR e heS)
  have hstab : ∀ (i j : Fin 6) (hij : i ≠ j) (c : K), 2 ≤ i.val → 2 ≤ j.val →
      ∀ e ∈ (piSub M₀ (Q ⊓ QB X) inf_le_left).map f,
        rho K (transvGL K i j hij c) e ∈ (piSub M₀ (Q ⊓ QB X) inf_le_left).map f := by
    intro i j hij c hi hj e he
    obtain ⟨e₀, he₀S, rfl⟩ := he
    obtain ⟨d₀, hd₀, rfl⟩ := mem_piSub.mp he₀S
    obtain ⟨u, hu⟩ := exists_lift d' (det_transvGL i j hij c)
    have hux : ⁅(u : G), x⁆ ∈ Q :=
      comm_mem_Q_of_lift d' hxL u.2 hφ' hu (transvGL_comm_tInv1' i j hij hi hj c)
    obtain ⟨q, hq, hqe⟩ :=
      conj_eq_of_comm_mem_Q hD hs Tx hII hNFx (Lgen_le_H0 hrem.ctx u.2) hux
    obtain ⟨dd, hddD, hddπ⟩ := piD_conj_mem (M₀ := M₀) hs (Lgen_le_H0 hrem.ctx u.2) hq hqe hd₀
    refine ⟨M₀.π dd, mem_piSub.mpr ⟨dd, hddD, rfl⟩, ?_⟩
    have hev := d'.equivariant u d₀ (Subgroup.mem_inf.mp hd₀).1
    rw [hu] at hev
    simp only [f, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
    rw [hddπ, hev]
    rfl
  have key := irred_range_tInv1 _ hS' hSR' hstab
  have hRS : ∀ r ∈ Rs Tx, ∃ d₀ ∈ Q ⊓ QB X, M₀.π d₀ = r := by
    intro r hr
    obtain ⟨e, heS, he⟩ := key (ψ' r) (hRs.mp hr)
    have : e = r := ψ'.injective he
    subst this
    exact mem_piSub.mp heS
  have hneg : ∀ v : M₀.E, -v = v := fun v => by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hv : v + v = 0 := by rw [← two_smul K v, h2, zero_smul]
    exact neg_eq_of_add_eq_zero_left hv
  apply le_antisymm
  · refine sup_le (fun d hd => ?_) le_sup_right
    have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
    obtain ⟨d₂, hd₂, z', hz', hdz⟩ :=
      exists_comm_of_mem_Rs hs Tx hdQ (caseII_piD_le_R hD hs Tx hII hd)
    rw [hdz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator hd₂ (Subgroup.mem_zpowers x)))
      (Subgroup.mem_sup_right hz')
  · refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases eq_one_or_eq_of_mem_zpowers hs.x_sq hb with rfl | rfl
    · simp only [commutatorElement_def, inv_one, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hcQ : ⁅a, b⁆ ∈ Q := comm_mem_Q H hs.memM ha
      have hmem : M₀.π ⁅a, b⁆ ∈ Rs Tx := by
        rw [Tx.pi_comm H hs.memM ha]
        refine mem_Rs.mpr ⟨M₀.π a, ?_⟩
        rw [← hneg (M₀.π a - Tx.T (M₀.π a)), neg_sub]
      obtain ⟨d₀, hd₀, hπd⟩ := hRS _ hmem
      have hd₀Q : d₀ ∈ Q := (Subgroup.mem_inf.mp hd₀).1
      have hZ : d₀⁻¹ * ⁅a, b⁆ ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hd₀Q hcQ).mp hπd
      have h := Subgroup.mul_mem_sup hd₀ hZ
      rwa [mul_inv_cancel_left] at h

end Main

end CFSG.RankThree.GF2n.Smith81.E3LRoot
