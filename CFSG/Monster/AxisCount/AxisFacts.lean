module

public import CFSG.Monster.AxisCount.TraceInv
public import CFSG.Monster.B.Cbar.Fusion
public import CFSG.Monster.B.Cbar.GenData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short

@[expose] noncomputable def aStarMinus : SpaceB := axis (zQ * rStar)

private theorem isShortCoord_zQ_mul_rStar' : IsShortCoord (coordOf (zQ * rStar)) :=
  isShortCoord_zQ_mul isShortCoord_rStar

theorem rhoEquiv_apply_aStar_of_conj {q : Q} (hq : q⁻¹ * rStar * q = zQ * rStar) :
    rhoEquiv q aStar = aStarMinus := by
  have h := thetaEquiv_axis (rhoPair q) isShortCoord_rStar
  rw [conjQ_rhoPair, hq] at h
  exact h

theorem aStarMinus_mem_axisOrbit : aStarMinus ∈ axisOrbit := by
  obtain ⟨q, hq⟩ := exists_conj_eq_zQ_mul (not_mem_center_of_isShortCoord isShortCoord_rStar)
  exact ⟨rhoEquiv q, Hmat_le_Gmat (rhoEquiv_mem_Gvis q), rhoEquiv_apply_aStar_of_conj hq⟩

theorem tAxis_aStarMinus :
    tAxis aStarMinus = (rhoEquiv (zQ * rStar) : SpaceB →ₗ[ℚ] SpaceB) :=
  tAxis_axis isShortCoord_zQ_mul_rStar'

theorem rhoEquiv_zQ_mul_rStar : rhoEquiv (zQ * rStar) = tStar * xmat := by
  rw [rhoEquiv_mul, xmat_eq_xB, rhoEquiv_zQ]
  rfl

theorem mul_tStar_comm_iff {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) :
    g * tStar = tStar * g ↔ g aStar = aStar :=
  commute_iff_of_eq_tAxis aStar_mem_axisOrbit tAxis_aStar.symm hg

theorem mul_rhoEquiv_zQ_mul_comm_iff {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) :
    g * rhoEquiv (zQ * rStar) = rhoEquiv (zQ * rStar) * g ↔ g aStarMinus = aStarMinus :=
  commute_iff_of_eq_tAxis aStarMinus_mem_axisOrbit tAxis_aStarMinus.symm hg

theorem mem_Jstar_of_fix {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (h : g aStar = aStar) :
    g ∈ Jstar :=
  ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ((mul_tStar_comm_iff (Hmat_le_Gmat hg)).2 h)⟩

theorem fix_aStar_of_mem_Jstar {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Jstar) : g aStar = aStar :=
  (mul_tStar_comm_iff (Hmat_le_Gmat hg.1)).1 (Subgroup.mem_centralizer_singleton_iff.1 hg.2)

theorem Gvis_inf_stabilizer_aStar :
    Gvis ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar = Jstar := by
  ext g
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => mem_Jstar_of_fix h.1 h.2, fun h => ⟨h.1, fix_aStar_of_mem_Jstar h⟩⟩

theorem mem_Jstar_of_fix_of_fix {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) (h₁ : g aStar = aStar)
    (h₂ : g aStarMinus = aStarMinus) : g ∈ Jstar := by
  have c₁ : Commute g tStar := (mul_tStar_comm_iff hg).2 h₁
  have c₂ : Commute g (rhoEquiv (zQ * rStar)) := (mul_rhoEquiv_zQ_mul_comm_iff hg).2 h₂
  rw [rhoEquiv_zQ_mul_rStar] at c₂
  have c₃ : Commute g xmat := by
    have h : Commute g (tStar⁻¹ * (tStar * xmat)) := c₁.inv_right.mul_right c₂
    rwa [inv_mul_cancel_left] at h
  have hx : g ∈ Gvis := by
    have h : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
      ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 c₃.eq⟩
    rw [Gmat_inf_centralizer_xmat] at h
    exact h
  exact mem_Jstar_of_fix hx h₁

theorem fix_aStar_of_mem_Cgen {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Cgen) : g aStar = aStar :=
  (mul_tStar_comm_iff (Cgen_le_Gmat hg)).1 (commute_tStar_of_mem_Cgen hg)

theorem Cgen_le_stabilizer : Cgen ≤ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar :=
  fun _ hg => MulAction.mem_stabilizer_iff.2 (fix_aStar_of_mem_Cgen hg)

theorem Cgen_le_inf_stabilizer :
    Cgen ≤ Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar :=
  le_inf Cgen_le_Gmat Cgen_le_stabilizer

theorem mem_Cgen_of_fix_of_apply_eq {σ c : SpaceB ≃ₗ[ℚ] SpaceB} (hσ : σ ∈ Gmat)
    (h₁ : σ aStar = aStar) (hc : c ∈ Cgen) (h₂ : σ aStarMinus = c aStarMinus) : σ ∈ Cgen := by
  have hc' : c⁻¹ ∈ Cgen := Cgen.inv_mem hc
  have hJ : c⁻¹ * σ ∈ Jstar := by
    refine mem_Jstar_of_fix_of_fix (Gmat.mul_mem (Cgen_le_Gmat hc') hσ) ?_ ?_
    · rw [LinearEquiv.mul_apply, h₁]
      exact fix_aStar_of_mem_Cgen hc'
    · rw [LinearEquiv.mul_apply, h₂]
      exact (LinearEquiv.mul_apply c⁻¹ c aStarMinus).symm.trans (by rw [inv_mul_cancel]; rfl)
  have e : σ = c * (c⁻¹ * σ) := by group
  rw [e]
  exact Cgen.mul_mem hc (Jstar_le_Cgen hJ)

theorem Gmat_inf_centralizer_tStar :
    Gmat ⊓ Subgroup.centralizer {tStar} =
      Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulAction.mem_stabilizer_iff]
  exact and_congr_right fun hg => mul_tStar_comm_iff hg

theorem tauB_apply_aStar : tauB aStar = aStar := fix_aStar_of_mem_Cgen tauB_mem_Cgen

theorem Gmat_inf_centralizer_tStar_eq_Cgen
    (h : Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar ≤ Cgen) :
    Gmat ⊓ Subgroup.centralizer {tStar} = Cgen := by
  rw [Gmat_inf_centralizer_tStar]
  exact le_antisymm h Cgen_le_inf_stabilizer

theorem axisOrbit_eq_orbit_Gmat : axisOrbit = MulAction.orbit Gmat aStar := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem natCard_stabilizer_subgroup {G X : Type*} [Group G] [MulAction G X] (K : Subgroup G)
    (x : X) :
    Nat.card (MulAction.stabilizer K x) = Nat.card (K ⊓ MulAction.stabilizer G x : Subgroup G) :=
  Nat.card_congr
    { toFun := fun g => ⟨(g : K), g.1.2, MulAction.mem_stabilizer_iff.2 g.2⟩
      invFun := fun g => ⟨⟨g, g.2.1⟩, MulAction.mem_stabilizer_iff.1 g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_orbit_mul_card_stabilizer_Gmat :
    Nat.card (MulAction.orbit Gmat aStar) * Nat.card (MulAction.stabilizer Gmat aStar) =
      Nat.card Gmat :=
  card_orbit_mul_card_stabilizer aStar

theorem card_orbit_mul_card_inf_stabilizer :
    Nat.card axisOrbit *
      Nat.card (Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar : Subgroup _) =
      Nat.card Gmat := by
  rw [axisOrbit_eq_orbit_Gmat, ← natCard_stabilizer_subgroup]
  exact card_orbit_mul_card_stabilizer_Gmat

theorem natCard_Gmat_eq_of_stabilizer_le
    (h : Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar ≤ Cgen) :
    Nat.card Gmat = Nat.card (MulAction.orbit Gmat aStar) * Nat.card Cgen := by
  have e : Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar = Cgen :=
    le_antisymm h Cgen_le_inf_stabilizer
  rw [← card_orbit_mul_card_inf_stabilizer, axisOrbit_eq_orbit_Gmat, e]

theorem orbit_Gvis_aStar_eq :
    MulAction.orbit Gvis aStar = axis '' {r : Q | IsShortCoord (coordOf r)} := by
  ext a
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
    exact ⟨conjQ p rStar, isShortCoord_conjQ p isShortCoord_rStar,
      (thetaEquiv_axis p isShortCoord_rStar).symm⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨g, hg, -, hga⟩ := exists_Gvis_conj_short isShortCoord_rStar hr
    exact ⟨⟨g, hg⟩, hga⟩

theorem axis_injOn_short : Set.InjOn axis {r : Q | IsShortCoord (coordOf r)} := by
  intro r hr r' hr' h
  have h1 := congrArg tAxis h
  rw [tAxis_axis hr, tAxis_axis hr'] at h1
  exact rhoEquiv_injective (LinearEquiv.toLinearMap_injective h1)

theorem natCard_orbit_Gvis_aStar :
    Nat.card (MulAction.orbit Gvis aStar) = 196560 := by
  rw [Nat.card_coe_set_eq, orbit_Gvis_aStar_eq, axis_injOn_short.ncard_image]
  have h := ncard_shortInv
  rwa [shortInv, Set.ncard_image_of_injective _ rhoEquiv_injective] at h

theorem natCard_Gvis_eq_mul_Jstar :
    Nat.card Gvis = 196560 * Nat.card Jstar := by
  have h := card_orbit_mul_card_stabilizer (K := Gvis) aStar
  rw [natCard_stabilizer_subgroup, Gvis_inf_stabilizer_aStar, natCard_orbit_Gvis_aStar] at h
  exact h.symm

theorem trA2_aStar : trA2 aStar = trA2Values 0 := by
  have h : (aStar.1 : Matrix (Fin 24) (Fin 24) ℚ) = (2 : ℚ) • projMat (vMinus 0 1) := by
    rw [aStar_eq]
    simp only [Prod.fst_sub, Prod.smul_fst, Submodule.coe_sub, Submodule.coe_smul]
    rw [coe_axisE_rStar]
    simp
  set c : Fin 24 → ℚ := fun i => (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0) with hc
  have hent : ∀ i j, ((2 : ℚ) • projMat (vMinus 0 1)) i j = c i * c j := by
    intro i j
    simp only [projMat, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, vMinus_zero_one,
      hc, Griess.ratVec, Code.eℤ, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> norm_num
  have hc2 : ∑ i, c i ^ 2 = 2 := by
    have h2 : ∀ i : Fin 24, c i ^ 2 = (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
      intro i
      simp only [hc]
      by_cases h0 : i = 0
      · subst h0
        simp
      · by_cases h1 : i = 1
        · subst h1
          simp
        · simp [h0, h1]
    simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num
  rw [trA2, h]
  simp only [hent, mul_pow]
  rw [← Finset.sum_mul_sum, hc2]
  norm_num [trA2Values, trA2Num, trA2Exp]

end CFSG.Monster.AxisCount
