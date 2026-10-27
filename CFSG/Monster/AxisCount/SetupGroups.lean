module

public import CFSG.Monster.AxisCount.FrameStab
public import CFSG.Monster.B.TwoA.Triality.PermLift
public import CFSG.Monster.Visible.Faithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.Generated CFSG.Monster.B

open CFSG.Monster.B.TwoA (hE0 e0Cls)

@[expose] noncomputable def wFrame : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv wQ

@[expose] noncomputable def Nfr' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Gvis ⊓ Subgroup.centralizer {wFrame}

theorem wFrame_eq_zB : wFrame = zB := rhoEquiv_wQ

theorem wFrame_eq_xmatTau2 : wFrame = xmatTau2 := by
  rw [wFrame_eq_zB, xmatTau2_eq]

theorem wFrame_eq_conj : wFrame = tauB⁻¹ * xB * tauB := by
  have h := conj_tauB_zB
  rw [wFrame_eq_zB]
  calc zB = tauB⁻¹ * (tauB * zB * tauB⁻¹) * tauB := by group
    _ = tauB⁻¹ * xB * tauB := by rw [h]

theorem wFrame_mem_Gvis : wFrame ∈ Gvis := rhoEquiv_mem_Gvis wQ

theorem wFrame_mul_self : wFrame * wFrame = 1 := by
  rw [wFrame_eq_zB]
  exact zB_mul_self

theorem mem_Nfr'_iff {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ Nfr' ↔ g ∈ Gvis ∧ g * wFrame * g⁻¹ = wFrame := by
  rw [Nfr', Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem Nfr'_le_Gvis : Nfr' ≤ Gvis := inf_le_left

theorem phi0_wQ_eq_twoΩCls : phi0 (coordOf wQ) = twoΩCls := by
  rw [← toAdd_phi_mk wQ, phi_wQ, Griess.classOf_eq_cls two_omega_mem]
  rfl

private theorem coordOf_wQ_fst_aux : (coordOf wQ).1 = Spin.ΩC := by
  change (spinEquiv.symm wQ).a = Spin.ΩC
  rw [symm_wQ]

theorem mul_xB_comm_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) :
    g * xB = xB * g := by
  have h : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} := by
    rw [Gmat_inf_centralizer_xmat]
    exact hg
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 h.2
  rwa [xmat_eq_xB] at h2

theorem conj_xB_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) : g * xB * g⁻¹ = xB := by
  rw [mul_xB_comm_of_mem_Gvis hg, mul_inv_cancel_right]

theorem phi0_coordOf_conjQ (p : Pvis) (t : Q) :
    phi0 (coordOf (conjQ p t)) = modTwoEnd p.1.2 (phi0 (coordOf t)) := by
  rw [← toAdd_phi_mk (conjQ p t), phi_conjQ, toAdd_phi_mk]

theorem thetaEquiv_mem_Nfr_iff (p : Pvis) :
    thetaEquiv p ∈ Nfr ↔ modTwoEnd p.1.2 twoΩCls = twoΩCls := by
  rw [mem_Nfr]
  constructor
  · rintro ⟨_, h⟩
    rwa [psiVis_smul_thetaEquiv] at h
  · intro h
    exact ⟨thetaEquiv_mem_Gvis p, by rw [psiVis_smul_thetaEquiv]; exact h⟩

theorem conj_wFrame_cases {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Nfr) :
    g * wFrame * g⁻¹ = wFrame ∨ g * wFrame * g⁻¹ = wFrame * xB := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 (Nfr_le_Gvis hg)
  have hfix := (thetaEquiv_mem_Nfr_iff p).1 hg
  have hco : coordOf (conjQ p wQ) = coordOf wQ := by
    apply phi0_injective
    rw [phi0_coordOf_conjQ, phi0_wQ_eq_twoΩCls, hfix]
  have e : thetaEquiv p * wFrame * (thetaEquiv p)⁻¹ = rhoEquiv (conjQ p wQ) :=
    Visible.thetaEquiv_conj_rhoEquiv p wQ
  rw [e]
  rcases B.Short.eq_or_eq_zQ_mul_of_coordOf_eq hco with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h, rhoEquiv_mul, rhoEquiv_zQ]
    rfl

theorem mem_Nfr_of_conj_eq {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis)
    (h : g * wFrame * g⁻¹ = wFrame) : g ∈ Nfr := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  rw [thetaEquiv_mem_Nfr_iff]
  have e : rhoEquiv (conjQ p wQ) = rhoEquiv wQ :=
    (Visible.thetaEquiv_conj_rhoEquiv p wQ).symm.trans h
  have e' : conjQ p wQ = wQ := rhoEquiv_injective e
  have h2 := phi0_coordOf_conjQ p wQ
  rw [e', phi0_wQ_eq_twoΩCls] at h2
  exact h2.symm

theorem Nfr'_le_Nfr : Nfr' ≤ Nfr := fun _ hg =>
  let h := mem_Nfr'_iff.1 hg
  mem_Nfr_of_conj_eq h.1 h.2

theorem rhoEquiv_mem_Nfr (r : Q) : rhoEquiv r ∈ Nfr := by
  refine (thetaEquiv_mem_Nfr_iff (rhoPair r)).2 ?_
  show modTwoEnd 1 twoΩCls = twoΩCls
  rw [modTwoEnd_one]
  rfl

theorem hE0_eq_hCocode : hE0 = hCocode e0Cls := rfl

theorem hE0_mem_Gvis : hE0 ∈ Gvis := rhoEquiv_mem_Gvis _

theorem hE0_mem_Nfr : hE0 ∈ Nfr := rhoEquiv_mem_Nfr _

theorem hE0_mul_self : hE0 * hE0 = 1 := OddCocode.hCocode_mul_self e0Cls

theorem hE0_inv : hE0⁻¹ = hE0 := inv_eq_of_mul_eq_one_right hE0_mul_self

theorem hE0_inv_mul_tauB_mul_hE0 : hE0⁻¹ * tauB * hE0 = tauB⁻¹ := by
  rw [hE0_inv]
  exact OddCocode.hCocode_mul_tauB_mul pair_ΩC_mk_single

private theorem rhoEquiv_inv' (q : Q) : rhoEquiv q⁻¹ = (rhoEquiv q)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    ((rhoEquiv_mul q q⁻¹).symm.trans ((congrArg rhoEquiv (mul_inv_cancel q)).trans
      OddCocode.rhoEquiv_one))

theorem hE0_conj_wFrame : hE0 * wFrame * hE0⁻¹ = wFrame * xB := by
  have hΩ : pair Spin.ΩC e0Cls = 1 := pair_ΩC_mk_single
  have h1 : (DQ e0Cls)⁻¹ * wQ * DQ e0Cls = zQ * wQ := by
    apply spinEquiv.symm.injective
    rw [OddCocode.symm_conj_DQ, coordOf_wQ_fst_aux, hΩ, symm_zQ_mul]
    rfl
  calc hE0 * wFrame * hE0⁻¹
      = rhoEquiv (DQ e0Cls) * rhoEquiv wQ * rhoEquiv (DQ e0Cls)⁻¹ := by
        rw [wFrame, hE0, rhoEquiv_inv']
    _ = rhoEquiv ((DQ e0Cls)⁻¹ * (wQ * DQ e0Cls)) := by
        rw [← rhoEquiv_mul, ← rhoEquiv_mul]
    _ = rhoEquiv (zQ * wQ) := by rw [← mul_assoc, h1]
    _ = wFrame * xB := by rw [rhoEquiv_mul, rhoEquiv_zQ]; rfl

theorem hE0_notMem_Nfr' : hE0 ∉ Nfr' := by
  intro h
  have h1 := (mem_Nfr'_iff.1 h).2
  rw [hE0_conj_wFrame] at h1
  have h2 : xB = 1 := by
    have := congrArg (wFrame⁻¹ * ·) h1
    simpa using this
  exact one_ne_xB h2.symm

theorem relIndex_Nfr'_Nfr : Nfr'.relIndex Nfr = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨hE0, hE0_mem_Nfr, fun b hb => ?_⟩
  have hbG : b ∈ Gvis := Nfr_le_Gvis hb
  have hbh : b * hE0 ∈ Gvis := Gvis.mul_mem hbG hE0_mem_Gvis
  have hx : xB ≠ 1 := one_ne_xB.symm
  have hconj : (b * hE0) * wFrame * (b * hE0)⁻¹ = (b * wFrame * b⁻¹) * xB := by
    calc (b * hE0) * wFrame * (b * hE0)⁻¹ = b * (hE0 * wFrame * hE0⁻¹) * b⁻¹ := by group
      _ = b * (wFrame * xB) * b⁻¹ := by rw [hE0_conj_wFrame]
      _ = (b * wFrame * b⁻¹) * (b * xB * b⁻¹) := by group
      _ = (b * wFrame * b⁻¹) * xB := by rw [conj_xB_of_mem_Gvis hbG]
  have hcancel : ∀ w : SpaceB ≃ₗ[ℚ] SpaceB, w * xB = w → False := fun w h => by
    have h2 : xB = 1 := by
      have := congrArg (w⁻¹ * ·) h
      simpa using this
    exact hx h2
  rcases conj_wFrame_cases hb with h | h
  · right
    refine ⟨mem_Nfr'_iff.2 ⟨hbG, h⟩, fun h' => ?_⟩
    have := (mem_Nfr'_iff.1 h').2
    rw [hconj, h] at this
    exact hcancel _ this
  · left
    refine ⟨mem_Nfr'_iff.2 ⟨hbh, ?_⟩, fun h' => ?_⟩
    · rw [hconj, h, mul_assoc, xB_mul_self, mul_one]
    · have := (mem_Nfr'_iff.1 h').2
      rw [h] at this
      exact hcancel _ this

private theorem conj_commute {G : Type*} [Group G] {c n a b : G} (hab : c * a * c⁻¹ = b)
    (h : n * a = a * n) : (c * n * c⁻¹) * b = b * (c * n * c⁻¹) := by
  rw [← hab]
  calc (c * n * c⁻¹) * (c * a * c⁻¹) = c * (n * a) * c⁻¹ := by group
    _ = c * (a * n) * c⁻¹ := by rw [h]
    _ = (c * a * c⁻¹) * (c * n * c⁻¹) := by group

private theorem inv_conj_eq_of_conj_eq' {G : Type*} [Group G] {c a b : G} (h : c * a * c⁻¹ = b) :
    c⁻¹ * b * c = a := by
  rw [← h]
  group

theorem tauB_inv_conj_yB : tauB⁻¹ * yB * tauB = xB := inv_conj_eq_of_conj_eq' conj_tauB_xB

theorem tauB_inv_conj_zB : tauB⁻¹ * zB * tauB = yB := inv_conj_eq_of_conj_eq' conj_tauB_yB

theorem tauB_inv_conj_xB : tauB⁻¹ * xB * tauB = zB := inv_conj_eq_of_conj_eq' conj_tauB_zB

theorem commute_of_mem_Nfr' {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Nfr') :
    n * xB = xB * n ∧ n * yB = yB * n ∧ n * zB = zB * n := by
  have hnG := (mem_Nfr'_iff.1 hn).1
  have hx := mul_xB_comm_of_mem_Gvis hnG
  have hz : n * zB = zB * n := by
    have := (mem_Nfr'_iff.1 hn).2
    rw [wFrame_eq_zB, mul_inv_eq_iff_eq_mul] at this
    exact this
  refine ⟨hx, ?_, hz⟩
  rw [← xB_mul_zB, ← mul_assoc, hx, mul_assoc, hz, mul_assoc]

theorem mem_Nfr'_iff_commute {n : SpaceB ≃ₗ[ℚ] SpaceB} :
    n ∈ Nfr' ↔ n ∈ Gmat ∧ n * xB = xB * n ∧ n * zB = zB * n := by
  constructor
  · intro hn
    obtain ⟨hx, -, hz⟩ := commute_of_mem_Nfr' hn
    exact ⟨Hmat_le_Gmat (mem_Nfr'_iff.1 hn).1, hx, hz⟩
  · rintro ⟨hG, hx, hz⟩
    have hG' : n ∈ Gvis := by
      have h : n ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
        ⟨hG, Subgroup.mem_centralizer_singleton_iff.2 (by rw [xmat_eq_xB]; exact hx)⟩
      rw [Gmat_inf_centralizer_xmat] at h
      exact h
    refine mem_Nfr'_iff.2 ⟨hG', ?_⟩
    rw [wFrame_eq_zB, hz, mul_inv_cancel_right]

theorem Nfr'_eq_Gmat_inf_centralizer_Vmat :
    Nfr' = Gmat ⊓ Subgroup.centralizer (Vmat : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
  ext n
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn
    obtain ⟨hx, hy, hz⟩ := commute_of_mem_Nfr' hn
    refine ⟨Hmat_le_Gmat (mem_Nfr'_iff.1 hn).1, fun v hv => ?_⟩
    rcases mem_Vmat.1 hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · rw [xmat_eq_xB]
      exact hx.symm
    · rw [xmatTau_eq]
      exact hy.symm
    · rw [xmatTau2_eq]
      exact hz.symm
  · rintro ⟨hG, hc⟩
    have hx := hc xmat (mem_Vmat.2 (.inr (.inl rfl)))
    have hz := hc xmatTau2 (mem_Vmat.2 (.inr (.inr (.inr rfl))))
    rw [xmat_eq_xB] at hx
    rw [xmatTau2_eq] at hz
    exact mem_Nfr'_iff_commute.2 ⟨hG, hx.symm, hz.symm⟩

theorem tauB_conj_mem_Nfr' {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Nfr') :
    tauB * n * tauB⁻¹ ∈ Nfr' := by
  obtain ⟨hx, hy, hz⟩ := commute_of_mem_Nfr' hn
  refine mem_Nfr'_iff_commute.2 ⟨?_, ?_, ?_⟩
  · exact Gmat.mul_mem (Gmat.mul_mem tauB_mem_Gmat (Hmat_le_Gmat (mem_Nfr'_iff.1 hn).1))
      (Gmat.inv_mem tauB_mem_Gmat)
  · exact conj_commute conj_tauB_zB hz
  · exact conj_commute conj_tauB_yB hy

theorem tauB_inv_conj_mem_Nfr' {n : SpaceB ≃ₗ[ℚ] SpaceB} (hn : n ∈ Nfr') :
    tauB⁻¹ * n * tauB ∈ Nfr' := by
  obtain ⟨hx, hy, hz⟩ := commute_of_mem_Nfr' hn
  have key : ∀ {a b : SpaceB ≃ₗ[ℚ] SpaceB}, tauB⁻¹ * a * tauB = b → n * a = a * n →
      (tauB⁻¹ * n * tauB) * b = b * (tauB⁻¹ * n * tauB) := fun {a b} hab h => by
    have := conj_commute (c := tauB⁻¹) (n := n) (a := a) (b := b) (by simpa using hab) h
    simpa using this
  refine mem_Nfr'_iff_commute.2 ⟨?_, ?_, ?_⟩
  · exact Gmat.mul_mem (Gmat.mul_mem (Gmat.inv_mem tauB_mem_Gmat)
      (Hmat_le_Gmat (mem_Nfr'_iff.1 hn).1)) tauB_mem_Gmat
  · exact key tauB_inv_conj_yB hy
  · exact key tauB_inv_conj_xB hx

instance finite_Gvis : Finite Gvis :=
  Finite.of_injective (Subgroup.inclusion (Hmat_le_Gmat : Gvis ≤ Gmat))
    (Subgroup.inclusion_injective _)

theorem index_comap_psiVis :
    ((MulAction.stabilizer GLV twoΩCls).comap psiVis).index = 8292375 := by
  rw [Subgroup.index_comap, range_psiVis]
  have h : (MulAction.stabilizer GLV twoΩCls).subgroupOf Hvis =
      MulAction.stabilizer Hvis fDelta := by
    ext u
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_fDelta]
    rfl
  rw [Subgroup.relIndex, h, MulAction.index_stabilizer_of_transitive, natCard_deltaSub]

theorem natCard_Gvis_eq :
    Nat.card Gvis = 8292375 * Nat.card Nfr := by
  have h := Subgroup.index_mul_card ((MulAction.stabilizer GLV twoΩCls).comap psiVis)
  rw [index_comap_psiVis] at h
  have e : Nat.card Nfr = Nat.card ((MulAction.stabilizer GLV twoΩCls).comap psiVis) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [e, ← h]

theorem two_mul_natCard_Gvis :
    2 * Nat.card Gvis = Nat.card Nfr * 16584750 := by
  rw [natCard_Gvis_eq]
  ring

instance finite_Nfr : Finite Nfr :=
  Finite.of_injective (Subgroup.inclusion Nfr_le_Gvis) (Subgroup.inclusion_injective _)

theorem two_mul_natCard_Gvis_div :
    2 * Nat.card Gvis / Nat.card Nfr = 16584750 := by
  rw [two_mul_natCard_Gvis]
  exact Nat.mul_div_cancel_left _ Nat.card_pos

end CFSG.Monster.AxisCount
