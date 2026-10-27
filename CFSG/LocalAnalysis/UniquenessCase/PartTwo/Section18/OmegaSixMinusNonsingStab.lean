module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusNonsingStabHom
public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSingStab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

section Orbit

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem statedQuadMinus_three_kOmMVec :
    StatedQuadMinus 3 F b c (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = 1 :=
  CFSG.SeitzReduction.SymplecticPilot.kOmM_statedQuadMinus_vec F b c

noncomputable local instance nonsingStabMulAction :
    MulAction (StatedOmega (StatedQuadMinus 3 F b c)) (SixMinusIdx → F) where
  smul g x := ((g : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ x
  one_smul x := by
    simp [Matrix.one_mulVec]
  mul_smul g h x := by
    change (((g * h : StatedOmega (StatedQuadMinus 3 F b c)) : GL SixMinusIdx F) :
        Matrix SixMinusIdx SixMinusIdx F) *ᵥ x =
      ((g : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ
        (((h : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ x)
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mul_mem_statedOmega_of_not_mem (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g h : GL SixMinusIdx F}
    (hgO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F g ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 3 F b c))
    (hhO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F h ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 3 F b c))
    (hg : g ∉ StatedOmega (StatedQuadMinus 3 F b c))
    (hh : h ∉ StatedOmega (StatedQuadMinus 3 F b c)) :
    g * h ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  rw [CFSG.LocalAnalysis.RankThreeUC.mem_statedOmega_iff] at hg hh ⊢
  set O := TauCeti.QuadraticMap.orthogonalGroup
    (CFSG.LieType.Universal.Spin.quadMinus 3 F b c)
  set D := ⁅O, O⁆
  have hidx : (D.subgroupOf O).index = 2 := by
    have h := (CFSG.LocalAnalysis.RankThreeUC.quadMinus_three_derived (F := F) (b := b) (c := c)
      hirr).1
    simpa [D, O, Subgroup.relIndex] using h
  have hg' : (⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F g, hgO⟩ : O) ∉
      D.subgroupOf O := by
    simpa [Subgroup.mem_subgroupOf] using hg
  have hh' : (⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F h, hhO⟩ : O) ∉
      D.subgroupOf O := by
    simpa [Subgroup.mem_subgroupOf] using hh
  have hm : (⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F g, hgO⟩ : O) *
      (⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F h, hhO⟩ : O) ∈ D.subgroupOf O := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hg' hh'
  simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using hm

theorem orbit_nonsing_eq (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    MulAction.orbit (StatedOmega (StatedQuadMinus 3 F b c))
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) =
      {x : SixMinusIdx → F | StatedQuadMinus 3 F b c x = 1} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    change StatedQuadMinus 3 F b c (((g : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ
      CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = 1
    rw [CFSG.SeitzReduction.F4Pilot.isometry_of_mem_statedOmega g.2,
      statedQuadMinus_three_kOmMVec]
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h1 : (0 : F) = 1 := by
        have h2 : StatedQuadMinus 3 F b c (0 : SixMinusIdx → F) = 0 :=
          CFSG.LocalAnalysis.RankThreeUC.stated_quad_zero
        have h3 : StatedQuadMinus 3 F b c (0 : SixMinusIdx → F) = 1 := hx
        rw [h2] at h3
        exact h3
      exact zero_ne_one h1
    have hv0 : CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 ≠ 0 := by
      intro h0
      have h1 := statedQuadMinus_three_kOmMVec (F := F) (b := b) (c := c)
      rw [h0] at h1
      have h2 : StatedQuadMinus 3 F b c (0 : SixMinusIdx → F) = 0 :=
        CFSG.LocalAnalysis.RankThreeUC.stated_quad_zero
      rw [h2] at h1
      exact zero_ne_one h1
    obtain ⟨gO₀, hgO₀, hgv₀⟩ := CFSG.LocalAnalysis.RankThreeUC.exists_isometry_apply_eq
      (F := F) (b := b) (c := c) hirr hv0 hx0 (by rw [statedQuadMinus_three_kOmMVec, hx])
    let gO : (SixMinusIdx → F) ≃ₗ[F] (SixMinusIdx → F) := gO₀
    have hgO : gO ∈ TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) := hgO₀
    have hgv : gO (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = x := hgv₀
    obtain ⟨G, hG⟩ : ∃ G : GL SixMinusIdx F,
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F G = gO :=
      ⟨(CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F).symm gO,
        MulEquiv.apply_symm_apply _ _⟩
    have hGv : ((G : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 = x := by
      rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hG, hgv]
    by_cases hGΩ : G ∈ StatedOmega (StatedQuadMinus 3 F b c)
    · exact ⟨⟨G, hGΩ⟩, hGv⟩
    · have hxO : gO ∈ TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) := hgO
      let Sx : GL SixMinusIdx F := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F).symm
        (CFSG.ClassicalGroups.Orthogonal.reflect
          (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) x)
      have hSxlin : CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F Sx =
          CFSG.ClassicalGroups.Orthogonal.reflect
            (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) x :=
        MulEquiv.apply_symm_apply _ _
      have hQx : CFSG.LieType.Universal.Spin.quadMinus 3 F b c x ≠ 0 := by
        rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
        rw [hx]; exact one_ne_zero
      have hSxO : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F Sx) ∈
          TauCeti.QuadraticMap.orthogonalGroup
            (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) := by
        rw [hSxlin]
        exact CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _
      have hSxΩ : Sx ∉ StatedOmega (StatedQuadMinus 3 F b c) := by
        intro hmem
        rw [CFSG.LocalAnalysis.RankThreeUC.mem_statedOmega_iff] at hmem
        rw [hSxlin] at hmem
        rw [← Subgroup.map_subtype_commutator] at hmem
        obtain ⟨cO, hcO, hcval⟩ := Subgroup.mem_map.mp hmem
        have hceq : cO = (⟨CFSG.ClassicalGroups.Orthogonal.reflect
            (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) x,
            CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _⟩ :
              ↥(TauCeti.QuadraticMap.orthogonalGroup
                (CFSG.LieType.Universal.Spin.quadMinus 3 F b c))) := by
          apply Subtype.ext
          exact hcval
        rw [hceq] at hcO
        exact CFSG.RankThree.PartOne.reflect_not_mem_commutator
          (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
          hQx hcO
      have hGO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F G ∈
          TauCeti.QuadraticMap.orthogonalGroup
            (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) := by
        rw [hG]; exact hgO
      have hSxGΩ : Sx * G ∈ StatedOmega (StatedQuadMinus 3 F b c) :=
        mul_mem_statedOmega_of_not_mem hirr hSxO hGO hSxΩ hGΩ
      have hxfix : CFSG.ClassicalGroups.Orthogonal.reflect
          (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) x x = x := by
        rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero]
        rw [show QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadMinus 3 F b c) x x = 0 from by
          rw [QuadraticMap.polar_self, nsmul_eq_mul]
          simp [CharTwo.two_eq_zero]]
      refine ⟨⟨Sx * G, hSxGΩ⟩, ?_⟩
      change ((Sx * G : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 = x
      rw [Units.val_mul]
      rw [show ((↑Sx : Matrix SixMinusIdx SixMinusIdx F) *
          (↑G : Matrix SixMinusIdx SixMinusIdx F)) *ᵥ
          CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 =
          (↑Sx : Matrix SixMinusIdx SixMinusIdx F) *ᵥ ((↑G : Matrix SixMinusIdx SixMinusIdx F) *ᵥ
            CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) from
        (Matrix.mulVec_mulVec
          (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)
          (↑Sx : Matrix SixMinusIdx SixMinusIdx F) (↑G : Matrix SixMinusIdx SixMinusIdx F)).symm]
      rw [hGv, ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hSxlin]
      exact hxfix

end Orbit

section Count

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem arith_norm_one (q S N : ℤ) (hq : q - 1 ≠ 0)
    (hpart : S + (q - 1) * N = q ^ 6)
    (hsing : S = 1 + (q ^ 3 + 1) * (q ^ 2 - 1)) :
    N = q ^ 2 * (q ^ 3 + 1) := by
  have h1 : (q - 1) * N = q ^ 6 - S := by linarith
  rw [hsing] at h1
  have h2 : (q - 1) * (q ^ 2 * (q ^ 3 + 1)) = q ^ 6 - (1 + (q ^ 3 + 1) * (q ^ 2 - 1)) := by
    ring
  exact mul_left_cancel₀ hq (h1.trans h2.symm)

theorem card_norm_one_statedQuadMinus_three (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} =
      Nat.card F ^ 2 * (Nat.card F ^ 3 + 1) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hbij : Function.Bijective fun p :
      Fˣ × {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} =>
      (⟨(p.1 : F) • (p.2 : SixMinusIdx → F), by
        rw [statedQuadMinus_three_smul, p.2.2, mul_one]
        exact pow_ne_zero 2 p.1.ne_zero⟩ :
          {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x ≠ 0}) := by
    constructor
    · rintro ⟨cc, x⟩ ⟨cc', x'⟩ hh
      have h' : (cc : F) • (x : SixMinusIdx → F) =
          (cc' : F) • (x' : SixMinusIdx → F) := congrArg Subtype.val hh
      have hQ := congrArg (StatedQuadMinus 3 F b c) h'
      rw [statedQuadMinus_three_smul, statedQuadMinus_three_smul, x.2, x'.2, mul_one, mul_one] at hQ
      have hcc : (cc : F) = (cc' : F) := CharTwo.sq_inj.mp hQ
      have hcc' : cc = cc' := Units.ext hcc
      subst hcc'
      exact Prod.ext rfl (Subtype.ext (smul_right_injective (SixMinusIdx → F) cc.ne_zero h'))
    · rintro ⟨y, hy⟩
      obtain ⟨cc, hc⟩ := CFSG.Timmesfeld.ClassicalOrders.exists_sq_eq_of_charTwo
        (StatedQuadMinus 3 F b c y)
      have hc0 : cc ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : 2 ≠ 0)] at hc
        exact hy hc.symm
      refine ⟨(Units.mk0 cc hc0, ⟨cc⁻¹ • y, ?_⟩), Subtype.ext ?_⟩
      · rw [statedQuadMinus_three_smul, ← hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc0)]
      · change cc • cc⁻¹ • y = y
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_units] at hcard
  have hpart : Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} +
      Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x ≠ 0} =
        Nat.card (SixMinusIdx → F) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (fun x : SixMinusIdx → F => StatedQuadMinus 3 F b c x = 0))
  have hV : Nat.card (SixMinusIdx → F) = Nat.card F ^ 6 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_coord_fun,
      show Fintype.card SixMinusIdx = 6 by simp [SixMinusIdx]]
  have hsingZ := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus
    (K := F) (b := b) (c := c) 2 hirr).1
  have hsing : (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 3 + 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    have h1 : Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} =
        Nat.card {v // CFSG.LieType.Universal.Spin.quadMinus 3 F b c v = 0} :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => by
        rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]
        rfl))
    rw [h1]
    exact hsingZ
  have hcardZ : (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x ≠ 0} : ℤ) =
      ((Nat.card F : ℤ) - 1) *
        (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) := by
    have hq1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr (Finite.card_pos).ne'
    have h := hcard.symm
    zify [hq1] at h
    exact h
  have hpartZ : (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} : ℤ) +
      (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x ≠ 0} : ℤ) =
      (Nat.card F : ℤ) ^ 6 := by
    have h := hpart
    rw [hV] at h
    exact_mod_cast h
  have hq1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr (Finite.card_pos).ne'
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq : (Nat.card F : ℤ) - 1 ≠ 0 := by omega
  have hpartN : ((Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} : ℤ)) +
      ((Nat.card F : ℤ) - 1) *
        (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) =
      (Nat.card F : ℤ) ^ 6 := by
    have h := hpartZ
    rw [hcardZ] at h
    exact h
  have hN : (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) =
      (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1) :=
    arith_norm_one (Nat.card F : ℤ)
      (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 0} : ℤ)
      (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) hq hpartN hsing
  exact_mod_cast hN

end Count

section Cardinality

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem arith_stab_sp (q st sp N : ℤ) (hN : N = q ^ 2 * (q ^ 3 + 1)) (hN0 : N ≠ 0)
    (h1 : st * N = q ^ 6 * (q ^ 3 + 1) * (q ^ 2 - 1) * (q ^ 4 - 1))
    (h2 : sp * N = q ^ 6 * (q ^ 3 + 1) * (q ^ 2 - 1) * (q ^ 4 - 1)) : st = sp := by
  exact mul_right_cancel₀ hN0 (h1.trans h2.symm)

theorem card_vecStab_eq_card_statedSp (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) =
      Nat.card ↥(StatedSp 2 F) := by
  classical
  letI : MulAction (StatedOmega (StatedQuadMinus 3 F b c)) (SixMinusIdx → F) := nonsingStabMulAction
  have hidx := MulAction.index_stabilizer (StatedOmega (StatedQuadMinus 3 F b c))
    (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)
  have hcard := Subgroup.card_mul_index
    (MulAction.stabilizer (StatedOmega (StatedQuadMinus 3 F b c))
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2))
  rw [hidx, orbit_nonsing_eq hirr, ← Nat.card_coe_set_eq] at hcard
  have hstab : Nat.card (MulAction.stabilizer (StatedOmega (StatedQuadMinus 3 F b c))
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) =
      Nat.card ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) := rfl
  rw [hstab] at hcard
  have hNZ : (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) =
      (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1) := by
    rw [card_norm_one_statedQuadMinus_three hirr]; push_cast; ring
  have hΩZ := CFSG.RankThree.GF2n.Smith81.card_statedOmega_minus_eq_of_two_le
    (K := F) (m := 3) (by norm_num) (b := b) (c := c) hirr
  rw [show (3 : ℕ) * (3 - 1) = 6 by norm_num,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num)] at hΩZ
  norm_num at hΩZ
  have hSpZ : (Nat.card ↥(StatedSp 2 F) : ℤ) =
      (Nat.card F : ℤ) ^ 4 * ((Nat.card F : ℤ) ^ 2 - 1) * ((Nat.card F : ℤ) ^ 4 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ (by exact_mod_cast Finite.card_pos)
    have h2 : 1 ≤ Nat.card F ^ 4 := Nat.one_le_pow 4 _ (by exact_mod_cast Finite.card_pos)
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  have hcardZ : (Nat.card ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) : ℤ) *
      (Nat.card {x : SixMinusIdx → F // StatedQuadMinus 3 F b c x = 1} : ℤ) =
      (Nat.card ↥(StatedOmega (StatedQuadMinus 3 F b c)) : ℤ) := by
    exact_mod_cast hcard
  have hN0 : ((Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1)) ≠ 0 := by
    have hq : (0 : ℤ) < Nat.card F := by exact_mod_cast Finite.card_pos
    positivity
  have h1 : (Nat.card ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) : ℤ) *
      ((Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1)) =
      (Nat.card F : ℤ) ^ 6 * ((Nat.card F : ℤ) ^ 3 + 1) *
        ((Nat.card F : ℤ) ^ 2 - 1) * ((Nat.card F : ℤ) ^ 4 - 1) := by
    rw [← hNZ, hcardZ, hΩZ]
    ring
  have h2 : (Nat.card ↥(StatedSp 2 F) : ℤ) *
      ((Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1)) =
      (Nat.card F : ℤ) ^ 6 * ((Nat.card F : ℤ) ^ 3 + 1) *
        ((Nat.card F : ℤ) ^ 2 - 1) * ((Nat.card F : ℤ) ^ 4 - 1) := by
    rw [hSpZ]; ring
  have hfinal := arith_stab_sp (Nat.card F : ℤ)
    (Nat.card ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)))
    (Nat.card ↥(StatedSp 2 F))
    ((Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 3 + 1)) rfl hN0 h1 h2
  exact_mod_cast hfinal

end Cardinality

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem nonempty_vecStab_kOmMVec_equiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) ≃* ↥(StatedSp 2 F)) := by
  refine ⟨MulEquiv.ofBijective (nonsingStabRes hirr) ?_⟩
  exact (nonsingStabRes_injective hirr).bijective_of_nat_card_le
    (by rw [card_vecStab_eq_card_statedSp hirr])

end Main

section Final

theorem exists_vecStab_OmegaMinus6_nonsing_equiv {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F}
    (hw : StatedQuadMinus 3 F b c w ≠ 0) :
    Nonempty (↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype w) ≃*
      ↥(StatedSp 2 F)) := by
  classical
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  obtain ⟨s, hs⟩ := CFSG.Timmesfeld.ClassicalOrders.exists_sq_eq_of_charTwo
    (StatedQuadMinus 3 F b c w)
  have hw0 : w ≠ 0 := by
    intro h0
    apply hw
    rw [h0]
    exact CFSG.LocalAnalysis.RankThreeUC.stated_quad_zero
  have hs0 : s ≠ 0 := by
    intro h0
    apply hw
    rw [← hs, h0]
    norm_num
  let v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F :=
    CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2
  let w₀ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F := s • v
  have hQv : StatedQuadMinus 3 F b c v = 1 :=
    CFSG.SeitzReduction.SymplecticPilot.kOmM_statedQuadMinus_vec F b c
  have hQw₀ : StatedQuadMinus 3 F b c w₀ = StatedQuadMinus 3 F b c w := by
    change StatedQuadMinus 3 F b c (s • v) = StatedQuadMinus 3 F b c w
    rw [statedQuadMinus_three_smul, hQv, mul_one, hs]
  have hw₀0 : w₀ ≠ 0 := by
    intro h0
    apply hw
    rw [← hQw₀, h0]
    exact CFSG.LocalAnalysis.RankThreeUC.stated_quad_zero
  have hstab : KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype (s • v) =
      KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype v := by
    ext g
    rw [KTabC.mem_vecStab, KTabC.mem_vecStab]
    constructor
    · intro h
      rw [Matrix.mulVec_smul] at h
      exact smul_right_injective _ hs0 h
    · intro h
      rw [Matrix.mulVec_smul, h]
  obtain ⟨e₁⟩ := nonempty_vecStab_omegaSixMinus_equiv
    (F := F) (b := b) (c := c) hirr hw₀0 hw0 hQw₀.symm
  obtain ⟨e₂⟩ := nonempty_vecStab_kOmMVec_equiv (F := F) (b := b) (c := c) hirr
  exact ⟨(e₁.trans (MulEquiv.subgroupCongr hstab)).trans e₂⟩

end Final

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
