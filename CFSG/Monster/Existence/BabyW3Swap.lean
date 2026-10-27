module

public import CFSG.Monster.Existence.BabyW3Cent
public import CFSG.Monster.Existence.BabyW3Quot
public import CFSG.Monster.AxisCount.HSCount
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.Existence.Census.TwoClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.Spin CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Census CFSG.Monster.Existence.Census MulOpposite

theorem natCard_op_inf_centralizer_dvd {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    Nat.card ↥(H.op ⊓ Subgroup.centralizer ({op t} : Set Gᵐᵒᵖ)) ∣
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) := by
  have h : H.op ⊓ Subgroup.centralizer ({op t} : Set Gᵐᵒᵖ) =
      (H ⊓ Subgroup.centralizer ({t} : Set G)).op := by
    ext u
    simp only [Subgroup.mem_inf, Subgroup.mem_op, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := congrArg MulOpposite.unop h2
      simp only [unop_mul, unop_op] at this
      exact this.symm
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      apply MulOpposite.unop_injective
      simp only [unop_mul, unop_op]
      exact h2.symm
  rw [h, Nat.card_congr (H ⊓ Subgroup.centralizer ({t} : Set G)).equivOp.symm]
  exact Subgroup.card_dvd_of_le inf_le_right

@[expose] noncomputable def dW3 :
    SpaceB ≃ₗ[ℚ] SpaceB :=
  Classical.choose
    (shortInv_transitive rhoEquiv_qP_zero_three_sixty_mem_shortInv tStar_mem_shortInv)

theorem dW3_spec :
    dW3 ∈ Gvis ∧ dW3 * rhoEquiv (qP 0 3 60) * dW3⁻¹ = tStar :=
  Classical.choose_spec
    (shortInv_transitive rhoEquiv_qP_zero_three_sixty_mem_shortInv tStar_mem_shortInv)

@[expose] noncomputable def gW3 :
    SpaceB ≃ₗ[ℚ] SpaceB := dW3 * tauB ^ 2

theorem gW3_mem_Gmat : gW3 ∈ Gmat :=
  mul_mem (Hmat_le_Gmat dW3_spec.1) (pow_mem tauB_mem_Gmat 2)

theorem gW3_conj_h1 :
    gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * gW3⁻¹ = tStar := by
  calc gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * gW3⁻¹ =
      dW3 * (tauB ^ 2 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (tauB ^ 2)⁻¹) * dW3⁻¹ := by
        unfold gW3
        group
    _ = tStar := by rw [trialityWitness_one]; exact dW3_spec.2

@[expose] noncomputable def yW3 :
    SpaceB ≃ₗ[ℚ] SpaceB := gW3 * xmat * gW3⁻¹

theorem yW3_eq :
    yW3 = dW3 * rhoEquiv wQ * dW3⁻¹ := by
  have h : tauB ^ 2 * xmat * (tauB ^ 2)⁻¹ = rhoEquiv wQ := by
    rw [tauB_pow_two_eq_inv, inv_inv]
    exact tauB_inv_mul_xmat_mul
  calc yW3 = dW3 * (tauB ^ 2 * xmat * (tauB ^ 2)⁻¹) * dW3⁻¹ := by
        unfold yW3 gW3
        group
    _ = dW3 * rhoEquiv wQ * dW3⁻¹ := by rw [h]

theorem cosetRep_one_comm_xmat :
    (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = xmat * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have h := Gvis_conj_xmat (cosetRep 1).2
  calc (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
        (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by group
    _ = xmat * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [h]

theorem tStar_comm_yW3 :
    tStar * yW3 = yW3 * tStar := by
  calc tStar * yW3 = (gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * gW3⁻¹) * (gW3 * xmat * gW3⁻¹) := by
        rw [gW3_conj_h1]
        rfl
    _ = gW3 * ((cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat) * gW3⁻¹ := by group
    _ = gW3 * (xmat * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * gW3⁻¹ := by
        rw [cosetRep_one_comm_xmat]
    _ = (gW3 * xmat * gW3⁻¹) * (gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * gW3⁻¹) := by group
    _ = yW3 * tStar := by
        rw [gW3_conj_h1]
        rfl

theorem yW3_mem_rhoCQ :
    yW3 ∈ rhoCQ := by
  obtain ⟨p, hp, -⟩ := Gvis_conj_rho dW3_spec.1 wQ
  have h := tStar_comm_yW3
  rw [yW3_eq, hp] at h
  rw [yW3_eq, hp]
  refine mem_rhoCQ.2 ⟨conjQ p wQ, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply rhoEquiv_injective
  rw [rhoEquiv_mul, rhoEquiv_mul]
  exact h

@[expose] noncomputable def y3C :
    Cgen := ⟨yW3, rhoCQ_le_Cgen yW3_mem_rhoCQ⟩

@[expose] noncomputable def y3Bar :
    Cbar := kappa y3C

theorem y3Bar_mem_Ebar :
    y3Bar ∈ Ebar :=
  ⟨y3C, (Subgroup.mem_subgroupOf).2 yW3_mem_rhoCQ, rfl⟩

theorem yW3_mul_self :
    yW3 * yW3 = 1 := by
  calc yW3 * yW3 = gW3 * (xmat * xmat) * gW3⁻¹ := by
        unfold yW3
        group
    _ = 1 := by
        rw [xmat_eq_xB, xB_mul_self]
        group

theorem trace_yW3 :
    LinearMap.trace ℚ SpaceB (yW3 : SpaceB →ₗ[ℚ] SpaceB) = 276 :=
  (CFSG.Monster.B.trace_conj gW3 xmat).trans trace_xmat

theorem y3C_mul_self :
    y3C * y3C = 1 := Subtype.ext yW3_mul_self

theorem y3C_ne_one :
    y3C ≠ 1 := by
  intro h
  have h1 : yW3 = 1 := congrArg Subtype.val h
  have h2 : xmat = 1 := conj_eq_one_iff.1 h1
  have h3 := orderOf_xmat
  rw [h2, orderOf_one] at h3
  omega

theorem y3C_ne_tStarC :
    y3C ≠ tStarC := by
  intro h
  have h1 : yW3 = tStar := congrArg Subtype.val h
  have h2 := trace_yW3
  rw [h1, trace_tStar] at h2
  norm_num at h2

theorem y3C_ne_tStarC_mul_xC :
    y3C ≠ tStarC * xC := by
  intro h
  have h1 : yW3 = tStar * xmat := congrArg Subtype.val h
  have h2 := trace_yW3
  rw [h1, tStar_mul_xmat, trace_rho_short isShortCoord_zQ_mul_rStar] at h2
  norm_num at h2

theorem wQ_ne_zQ : wQ ≠ zQ := by
  intro h
  have h1 : CFSG.Monster.B.Rep4371.pauliQ (false, 63, 0) =
      CFSG.Monster.B.Rep4371.pauliQ (true, 0, 0) := by
    rw [pauliQ_omega, pauliQ_z]
    exact h
  have h2 := pauliQ_inj (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1
  exact Bool.false_ne_true (congrArg Prod.fst h2)

theorem y3C_ne_xC :
    y3C ≠ xC := by
  intro h
  have h1 : yW3 = xmat := congrArg Subtype.val h
  obtain ⟨p, hp, -⟩ := Gvis_conj_rho dW3_spec.1 wQ
  rw [yW3_eq, hp] at h1
  have h2 : conjQ p wQ = conjQ p zQ := by
    rw [conjQ_zQ]
    exact rhoEquiv_injective h1
  exact wQ_ne_zQ ((conjQ p).injective h2)

theorem y3Bar_mul_self :
    y3Bar * y3Bar = 1 := by
  rw [y3Bar, ← map_mul, y3C_mul_self, map_one]

theorem y3Bar_ne_one :
    y3Bar ≠ 1 := by
  intro h
  rcases (kappa_eq_one_iff y3C).1 h with h | h
  · exact y3C_ne_one h
  · exact y3C_ne_tStarC h

theorem y3Bar_ne_xbar :
    y3Bar ≠ xbar := by
  intro h
  have hx : xC⁻¹ = xC := inv_eq_of_mul_eq_one_right xC_mul_self
  have h1 : kappa (y3C * xC) = 1 := by
    rw [map_mul]
    change y3Bar * xbar = 1
    rw [h]
    exact xbar_mul_self
  rcases (kappa_eq_one_iff _).1 h1 with h2 | h2
  · apply y3C_ne_xC
    calc y3C = y3C * xC * xC⁻¹ := by group
      _ = xC := by rw [h2, hx, one_mul]
  · apply y3C_ne_tStarC_mul_xC
    calc y3C = y3C * xC * xC⁻¹ := by group
      _ = tStarC * xC := by rw [h2, hx]

theorem mem_Gvis_conj_of_comm_y
    {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ Cgen)
    (hcy : c * yW3 = yW3 * c) : gW3⁻¹ * c * gW3 ∈ Gvis := by
  refine mem_Gvis_of_comm_xmat (mul_mem (mul_mem (inv_mem gW3_mem_Gmat) (Cgen_le_Gmat hc))
    gW3_mem_Gmat) ?_
  have : gW3⁻¹ * c * gW3 * xmat = xmat * (gW3⁻¹ * c * gW3) := by
    calc gW3⁻¹ * c * gW3 * xmat = gW3⁻¹ * (c * (gW3 * xmat * gW3⁻¹)) * gW3 := by group
      _ = gW3⁻¹ * ((gW3 * xmat * gW3⁻¹) * c) * gW3 := by
          rw [show gW3 * xmat * gW3⁻¹ = yW3 from rfl, hcy]
      _ = xmat * (gW3⁻¹ * c * gW3) := by group
  exact this

theorem conj_comm_h1_of_mem_Cgen
    {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ Cgen) :
    gW3⁻¹ * c * gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3⁻¹ * c * gW3) := by
  have hct := commute_tStar_of_mem_Cgen hc
  have hh : (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = gW3⁻¹ * tStar * gW3 := by
    rw [← gW3_conj_h1]
    group
  calc gW3⁻¹ * c * gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = gW3⁻¹ * (c * tStar) * gW3 := by
        rw [hh]
        group
    _ = gW3⁻¹ * (tStar * c) * gW3 := by rw [hct]
    _ = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3⁻¹ * c * gW3) := by
        rw [hh]
        group

theorem conj_mem_Cgen_of_comm_h1
    {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ Gvis)
    (hch : c * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * c) :
    gW3 * c * gW3⁻¹ ∈ Cgen := by
  refine AxisCount.HS.centralizer_tStar_le_Cgen _
    (mul_mem (mul_mem gW3_mem_Gmat (Hmat_le_Gmat hc)) (inv_mem gW3_mem_Gmat)) ?_
  calc gW3 * c * gW3⁻¹ * tStar = gW3 * (c * (gW3⁻¹ * tStar * gW3)) * gW3⁻¹ := by group
    _ = gW3 * (c * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * gW3⁻¹ := by
        rw [← gW3_conj_h1]
        group
    _ = gW3 * ((cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * c) * gW3⁻¹ := by rw [hch]
    _ = tStar * (gW3 * c * gW3⁻¹) := by
        rw [← gW3_conj_h1]
        group

theorem conj_comm_y_of_mem_Gvis
    {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ Gvis) :
    gW3 * c * gW3⁻¹ * yW3 = yW3 * (gW3 * c * gW3⁻¹) := by
  have h := Gvis_conj_xmat hc
  have hcx : c * xmat = xmat * c := by
    calc c * xmat = c * xmat * c⁻¹ * c := by group
      _ = xmat * c := by rw [h]
  calc gW3 * c * gW3⁻¹ * yW3 = gW3 * (c * xmat) * gW3⁻¹ := by
        unfold yW3
        group
    _ = gW3 * (xmat * c) * gW3⁻¹ := by rw [hcx]
    _ = yW3 * (gW3 * c * gW3⁻¹) := by
        unfold yW3
        group

theorem natCard_centralizer_y3C :
    Nat.card ↥(Subgroup.centralizer ({y3C} : Set Cgen)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  rw [← natCard_centralizer_cosetRep_one]
  have hfwd : ∀ c : ↥(Subgroup.centralizer ({y3C} : Set Cgen)),
      gW3⁻¹ * (c.1 : Cgen).1 * gW3 ∈ Gvis ∧
        gW3⁻¹ * (c.1 : Cgen).1 * gW3 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
          (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3⁻¹ * (c.1 : Cgen).1 * gW3) := by
    intro c
    have hcy : (c.1 : Cgen).1 * yW3 = yW3 * (c.1 : Cgen).1 :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2)
    exact ⟨mem_Gvis_conj_of_comm_y c.1.2 hcy, conj_comm_h1_of_mem_Cgen c.1.2⟩
  have hbwd : ∀ c' : ↥(Subgroup.centralizer ({cosetRep 1} : Set Gvis)),
      gW3 * (c'.1 : Gvis).1 * gW3⁻¹ ∈ Cgen ∧
        gW3 * (c'.1 : Gvis).1 * gW3⁻¹ * yW3 = yW3 * (gW3 * (c'.1 : Gvis).1 * gW3⁻¹) := by
    intro c'
    have hch : (c'.1 : Gvis).1 * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
        (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (c'.1 : Gvis).1 :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c'.2)
    exact ⟨conj_mem_Cgen_of_comm_h1 c'.1.2 hch, conj_comm_y_of_mem_Gvis c'.1.2⟩
  refine Nat.card_congr
    { toFun := fun c => ⟨⟨_, (hfwd c).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hfwd c).2)⟩
      invFun := fun c' => ⟨⟨_, (hbwd c').1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hbwd c').2)⟩
      left_inv := fun c => ?_
      right_inv := fun c' => ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    show gW3 * (gW3⁻¹ * (c.1 : Cgen).1 * gW3) * gW3⁻¹ = (c.1 : Cgen).1
    group
  · apply Subtype.ext
    apply Subtype.ext
    show gW3⁻¹ * (gW3 * (c'.1 : Gvis).1 * gW3⁻¹) * gW3 = (c'.1 : Gvis).1
    group

theorem tStarC_mul_self : tStarC * tStarC = 1 := Subtype.ext tStar_mul_self

theorem tStarC_ne_one : tStarC ≠ 1 := fun h => tStar_ne_one (congrArg Subtype.val h)

theorem two_mul_natCard_centralizer_y3Bar :
    ∃ o : ℕ, 1 ≤ o ∧ o ≤ 2 ∧ (o = 2 → ∃ c : Cgen, c * y3C * c⁻¹ = tStarC * y3C) ∧
      2 * Nat.card ↥(Subgroup.centralizer ({y3Bar} : Set Cbar)) =
        o * (2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7) := by
  obtain ⟨o, h1, h2, h3, h4⟩ := centralizer_card_of_central_quotient kappa kappa_surjective
    tStarC_mem_center tStarC_mul_self tStarC_ne_one ker_kappa y3C
  exact ⟨o, h1, h2, h3, by rw [← natCard_centralizer_y3C]; exact h4⟩

theorem natCard_jbarOp :
    Nat.card ↥(Jbar.op) = 354883595661213696000 :=
  (Nat.card_congr Jbar.equivOp.symm).trans natCard_Jbar

theorem y3Bar_census :
    (∃ c : Cgen, c * y3C * c⁻¹ = tStarC * y3C) ∧
      Nat.card ↥(Subgroup.centralizer ({y3Bar} : Set Cbar)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 ∧
      IsConj (CTIB.rs 3) (op y3Bar) := by
  obtain ⟨o, ho1, ho2, hsw, hcard⟩ := two_mul_natCard_centralizer_y3Bar
  set cbar := Nat.card ↥(Subgroup.centralizer ({y3Bar} : Set Cbar)) with hcbar
  have hdvd := natCard_op_inf_centralizer_dvd Jbar y3Bar
  have horb := ncard_conj_mul_natCard_inf_centralizer (Jbar.op) (op y3Bar)
  rw [natCard_jbarOp] at horb
  have hinv : op y3Bar ∈ {t | t ∈ CTIB.Qs ∧ t * t = 1 ∧ t ≠ 1} :=
    ⟨Subgroup.mem_op.2 y3Bar_mem_Ebar, by rw [← op_mul, y3Bar_mul_self, op_one],
      fun h => y3Bar_ne_one (op_injective (h.trans op_one.symm))⟩
  rw [CTIB.invs_eq] at hinv
  have hclass : ∀ i : ℕ, op y3Bar ∈ CTIB.jClass (CTIB.rs i) →
      (CTIB.jClass (CTIB.rs i)).ncard * Nat.card ↥(Jbar.op ⊓ Subgroup.centralizer
        ({op y3Bar} : Set Cbarᵐᵒᵖ)) = 354883595661213696000 := by
    intro i hi
    have h := horb
    have e : {u : Sbp | ∃ g ∈ Jbar.op, u = g⁻¹ * op y3Bar * g} = CTIB.jClass (op y3Bar) := rfl
    rw [e, CTIB.jClass_eq_of_mem hi] at h
    exact h
  have hN : (2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 : ℕ) = 11689182992793600 := by norm_num
  rw [hN] at hcard
  rcases hinv with ((h | h) | h) | h
  ·
    exfalso
    rw [CTIB.rs0_eq, CTIB.jClass_xs] at h
    exact y3Bar_ne_xbar (op_injective (Set.mem_singleton_iff.1 h))
  ·
    exfalso
    have h1 := hclass 1 h
    rw [CTIB.ncard_jClass_rs1] at h1
    obtain ⟨k, hk⟩ := hdvd
    have hc : Nat.card ↥(Jbar.op ⊓ Subgroup.centralizer ({op y3Bar} : Set Cbarᵐᵒᵖ)) =
        77148607752437760 := by omega
    rw [hc] at hk
    omega
  · exfalso
    have h1 := hclass 2 h
    rw [CTIB.ncard_jClass_rs2] at h1
    obtain ⟨k, hk⟩ := hdvd
    have hc : Nat.card ↥(Jbar.op ⊓ Subgroup.centralizer ({op y3Bar} : Set Cbarᵐᵒᵖ)) =
        3809807790243840 := by omega
    rw [hc] at hk
    omega
  ·
    have h1 := hclass 3 h
    rw [CTIB.ncard_jClass_rs3] at h1
    obtain ⟨k, hk⟩ := hdvd
    have hc : Nat.card ↥(Jbar.op ⊓ Subgroup.centralizer ({op y3Bar} : Set Cbarᵐᵒᵖ)) =
        86586540687360 := by omega
    rw [hc] at hk
    have ho : o = 2 := by omega
    subst ho
    refine ⟨hsw rfl, by rw [hN]; omega, ?_⟩
    obtain ⟨g, hg, hgt⟩ := h
    exact isConj_iff.2 ⟨g⁻¹, by rw [hgt, inv_inv]⟩

end CFSG.Monster.Existence
