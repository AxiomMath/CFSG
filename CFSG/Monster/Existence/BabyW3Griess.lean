module

public import CFSG.Monster.Existence.BabyW3Swap
public import CFSG.Monster.GMS.Facts.TableV

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.Spin CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Census CFSG.Monster.Existence.Census
  CFSG.Monster.GMS

theorem exists_swap_cosetRep_one :
    ∃ c ∈ Gmat, c * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * c ∧
      c * xmat * c⁻¹ = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat := by
  obtain ⟨c₀, hc₀⟩ := y3Bar_census.1
  have h1 : (c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * yW3 * (c₀ : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = tStar * yW3 :=
    congrArg Subtype.val hc₀
  have hh : (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = gW3⁻¹ * tStar * gW3 := by
    rw [← gW3_conj_h1]
    group
  refine ⟨gW3⁻¹ * (c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * gW3,
    mul_mem (mul_mem (inv_mem gW3_mem_Gmat) (Cgen_le_Gmat c₀.2)) gW3_mem_Gmat,
    conj_comm_h1_of_mem_Cgen c₀.2, ?_⟩
  calc gW3⁻¹ * (c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 * xmat *
        (gW3⁻¹ * (c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * gW3)⁻¹ =
      gW3⁻¹ * ((c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3 * xmat * gW3⁻¹) *
        (c₀ : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) * gW3 := by group
    _ = gW3⁻¹ * (tStar * yW3) * gW3 := by
        rw [show gW3 * xmat * gW3⁻¹ = yW3 from rfl, h1]
    _ = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat := by
        rw [hh]
        unfold yW3
        group

theorem trace_cosetRep_one_mul_xmat :
    LinearMap.trace ℚ SpaceB (((cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * xmat : SpaceB ≃ₗ[ℚ] SpaceB) :
      SpaceB →ₗ[ℚ] SpaceB) = 276 := by
  obtain ⟨c, -, -, hc⟩ := exists_swap_cosetRep_one
  rw [← hc]
  exact (CFSG.Monster.B.trace_conj c xmat).trans trace_xmat

theorem coe_rhoGvis_zQ : ((rhoGvis zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xmat := rfl

theorem rhoGvis_zQ_comm (g : Gvis) : g * rhoGvis zQ = rhoGvis zQ * g := by
  apply Subtype.ext
  have h := Gvis_conj_xmat g.2
  show (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)
  calc (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat =
      (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
        (g : SpaceB ≃ₗ[ℚ] SpaceB) := by group
    _ = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [h]

theorem rhoGvis_zQ_mul_self : rhoGvis zQ * rhoGvis zQ = 1 := by
  apply Subtype.ext
  show xmat * xmat = 1
  rw [xmat_eq_xB]
  exact xB_mul_self

theorem mem_cosetInv_one_mul_zQ :
    cosetRep 1 * rhoGvis zQ ∈ cosetInv 1 := by
  refine ⟨?_, ?_⟩
  · rw [mem_cosetR_iff, map_mul]
    have : piVis (rhoGvis zQ) = 1 := by
      rw [← MonoidHom.mem_ker, ker_piVis]
      exact rhoGvis_mem zQ
    rw [this, mul_one]
  · calc cosetRep 1 * rhoGvis zQ * (cosetRep 1 * rhoGvis zQ) =
        cosetRep 1 * (rhoGvis zQ * cosetRep 1) * rhoGvis zQ := by group
      _ = cosetRep 1 * (cosetRep 1 * rhoGvis zQ) * rhoGvis zQ := by
          rw [← rhoGvis_zQ_comm (cosetRep 1)]
      _ = (cosetRep 1 * cosetRep 1) * (rhoGvis zQ * rhoGvis zQ) := by group
      _ = 1 := by rw [cosetRep_one_mul_self, rhoGvis_zQ_mul_self, one_mul]

theorem qmatClass_mul_zQ (f : Gvis) :
    qmatClass (f * rhoGvis zQ) = (fun v => v * rhoGvis zQ) '' qmatClass f := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u⁻¹ * f * u, ⟨u, hu, rfl⟩, ?_⟩
    show u⁻¹ * f * u * rhoGvis zQ = u⁻¹ * (f * rhoGvis zQ) * u
    calc u⁻¹ * f * u * rhoGvis zQ = u⁻¹ * f * (u * rhoGvis zQ) := by group
      _ = u⁻¹ * f * (rhoGvis zQ * u) := by rw [rhoGvis_zQ_comm u]
      _ = u⁻¹ * (f * rhoGvis zQ) * u := by group
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    show u⁻¹ * f * u * rhoGvis zQ = u⁻¹ * (f * rhoGvis zQ) * u
    calc u⁻¹ * f * u * rhoGvis zQ = u⁻¹ * f * (u * rhoGvis zQ) := by group
      _ = u⁻¹ * f * (rhoGvis zQ * u) := by rw [rhoGvis_zQ_comm u]
      _ = u⁻¹ * (f * rhoGvis zQ) * u := by group

theorem cosetRep_one_mul_rhoGvis_zQ_mem_class_four :
    cosetRep 1 * rhoGvis zQ ∈ qmatClass (classRep 4) := by
  obtain ⟨k, hk, hfk⟩ := mem_qmatClass_of_mem_cosetInv_one mem_cosetInv_one_mul_zQ
  have hcard : (qmatClass (classRep k)).ncard = 256 := by
    rw [← qmatClass_eq_of_mem hfk, qmatClass_mul_zQ,
      Set.ncard_image_of_injective _ (fun a b h => mul_right_cancel h),
      ncard_qmatClass_h1]
  rw [ncard_qmatClass_classRep hk, classSize_eq k hk] at hcard
  have hk04 : k = 0 ∨ k = 4 := by
    by_contra hne
    have h512 : (if k = 0 ∨ k = 4 then 256 else 512) = 512 := by simp [hne]
    rw [h512] at hcard
    omega
  rcases hk04 with rfl | rfl
  · exfalso
    rw [classRep_zero_eq] at hfk
    have h1 := mem_qmatClass_trVis hfk
    have h2 : trVis (cosetRep 1 * rhoGvis zQ) = 276 := trace_cosetRep_one_mul_xmat
    rw [h2, trVis_cosetRep_one] at h1
    norm_num at h1
  · exact hfk

@[expose] noncomputable def uW3 :
    MGriess := ⟨yW3, Gmat_le_AutO (Cgen_le y3C.2).1⟩

theorem coe_uW3 :
    ((uW3 : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = yW3 := rfl

theorem uW3_mem_cent :
    uW3 ∈ cent tGriess :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext tStar_comm_yW3.symm)

theorem orderOf_uW3 :
    orderOf uW3 = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext yW3_mul_self) (fun h => y3C_ne_one
    (Subtype.ext (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h)))

theorem uW3_ne_tGriess :
    uW3 ≠ tGriess := fun h => y3C_ne_tStarC
  (Subtype.ext (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB)) h))

theorem exists_swap_uW3 :
    ∃ g ∈ cent tGriess, g * uW3 * g⁻¹ = tGriess * uW3 := by
  obtain ⟨c₀, hc₀⟩ := y3Bar_census.1
  refine ⟨⟨(c₀ : SpaceB ≃ₗ[ℚ] SpaceB), Gmat_le_AutO (Cgen_le c₀.2).1⟩,
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (commute_tStar_of_mem_Cgen c₀.2)),
    Subtype.ext (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB)) hc₀)⟩

theorem isConj_xGriess_uW3 :
    IsConj xGriess uW3 :=
  isConj_iff.2 ⟨⟨gW3, Gmat_le_AutO gW3_mem_Gmat⟩, Subtype.ext rfl⟩

theorem isConj_xGriess_tGriess_mul_uW3 :
    IsConj xGriess (tGriess * uW3) := by
  obtain ⟨g, -, hg⟩ := exists_swap_uW3
  exact isConj_xGriess_uW3.trans (isConj_iff.2 ⟨g, hg⟩)

theorem mem_Cgen_of_mem_cent2_uW3
    {v : MGriess} (hv : v ∈ cent2 tGriess uW3) :
    (v : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen := by
  have hvu : (v : SpaceB ≃ₗ[ℚ] SpaceB) * yW3 = yW3 * (v : SpaceB ≃ₗ[ℚ] SpaceB) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv.2)
  have hvt : (v : SpaceB ≃ₗ[ℚ] SpaceB) * tStar = tStar * (v : SpaceB ≃ₗ[ℚ] SpaceB) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv.1)
  have hgA : gW3 ∈ AutO := Gmat_le_AutO gW3_mem_Gmat
  have hw : (⟨gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3,
      mul_mem (mul_mem (inv_mem hgA) v.2) hgA⟩ : MGriess) ∈ cent xGriess := by
    refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    show gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 * xmat =
      xmat * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3)
    calc gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 * xmat =
        gW3⁻¹ * ((v : SpaceB ≃ₗ[ℚ] SpaceB) * (gW3 * xmat * gW3⁻¹)) * gW3 := by group
      _ = gW3⁻¹ * ((gW3 * xmat * gW3⁻¹) * (v : SpaceB ≃ₗ[ℚ] SpaceB)) * gW3 := by
          rw [show gW3 * xmat * gW3⁻¹ = yW3 from rfl, hvu]
      _ = xmat * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3) := by group
  have hwG : gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3 ∈ Gvis := by
    rw [← map_cent_xGriess]
    exact ⟨_, hw, rfl⟩
  have hvG : (v : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := by
    have := mul_mem (mul_mem gW3_mem_Gmat (Hmat_le_Gmat hwG)) (inv_mem gW3_mem_Gmat)
    have e : gW3 * (gW3⁻¹ * (v : SpaceB ≃ₗ[ℚ] SpaceB) * gW3) * gW3⁻¹ =
        (v : SpaceB ≃ₗ[ℚ] SpaceB) := by group
    rwa [e] at this
  exact AxisCount.HS.centralizer_tStar_le_Cgen _ hvG hvt

theorem natCard_cent2_tGriess_uW3 :
    Nat.card ↥(cent2 tGriess uW3) = tableVOrderU := by
  rw [show tableVOrderU = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 from rfl, ← natCard_centralizer_y3C]
  refine Nat.card_congr
    { toFun := fun v => ⟨⟨(v.1 : SpaceB ≃ₗ[ℚ] SpaceB), mem_Cgen_of_mem_cent2_uW3 v.2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (congrArg (fun g : MGriess => (g : SpaceB ≃ₗ[ℚ] SpaceB))
            (Subgroup.mem_centralizer_singleton_iff.1 v.2.2)))⟩
      invFun := fun c => ⟨⟨(c.1 : Cgen).1, Gmat_le_AutO (Cgen_le c.1.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (commute_tStar_of_mem_Cgen c.1.2)),
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (congrArg (fun g : Cgen => (g : SpaceB ≃ₗ[ℚ] SpaceB))
            (Subgroup.mem_centralizer_singleton_iff.1 c.2)))⟩
      left_inv := fun v => rfl
      right_inv := fun c => rfl }

theorem exists_uW3 :
    ∃ u : MGriess, u ∈ cent tGriess ∧ orderOf u = 2 ∧ u ≠ tGriess ∧
      (∃ g ∈ cent tGriess, g * u * g⁻¹ = tGriess * u) ∧
      Nat.card ↥(cent2 tGriess u) = tableVOrderU :=
  ⟨uW3, uW3_mem_cent, orderOf_uW3, uW3_ne_tGriess, exists_swap_uW3,
    natCard_cent2_tGriess_uW3⟩

end CFSG.Monster.Existence
