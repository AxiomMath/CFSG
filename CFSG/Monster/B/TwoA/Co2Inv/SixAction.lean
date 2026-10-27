
module

public import CFSG.Monster.B.TwoA.Co2Inv.SixActionBase

public import CFSG.Monster.B.TwoA.Co2Inv.SixCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

theorem Zsp_diff_zero :

    (Zsp : Set (Wv v0)) \ {0} = {x | ∃ k ∈ Cr, wAct v0 k wFr = x} := by
  rw [orbit_Cr_wFr]
  ext x
  simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hx0⟩
    obtain ⟨c, hc, rfl⟩ := mem_Zsp_iff.1 hx
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · exact absurd (by rw [zBasis_comb_zero, decW_zero]) hx0
      · exact h
    obtain ⟨i, hi, e⟩ := zBasis_comb_frame c hc hc0
    exact ⟨i, hi, by rw [e]⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨c, hc, hc0, e⟩ := frame_zBasis_comb i hi
    refine ⟨mem_Zsp_iff.2 ⟨c, hc, by rw [e]⟩, ?_⟩
    exact decW_ne_zero (frameOrbit_bounds i hi).1 (frameOrbit_bounds i hi).2

theorem wAct_cGen_zComb
    (k : Fin 21) {c : ℕ} (hc : c < 64) :
    wAct v0 (cGen k) (decW (Native.actD 6 zBasis c)) =
      decW (Native.actD 6 zBasis (Native.actD 6 (sixRows[(k : ℕ)]!) c)) := by
  rw [wAct_cGen, rowsEnd_decW, (sixRows_spec k k.2 c hc).2]

theorem cGen_mem_wSetStab
    (k : Fin 21) : cGen k ∈ wSetStab Zsp := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_Zsp_iff.1 hx
  rw [wAct_cGen_zComb k hc]
  exact zComb_mem _

theorem Cr_le_wSetStab :
    Cr ≤ wSetStab Zsp := by
  rw [← G21_eq_Cr, G21_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact cGen_mem_wSetStab k

@[expose] def cGenZ
    (k : Fin 21) : wSetStab Zsp := ⟨cGen k, cGen_mem_wSetStab k⟩

theorem wAct_cGen_zB
    (k : Fin 21) (i : Fin 6) : wAct v0 (cGen k) (zB i : Wv v0) =
    decW (Native.actD 6 zBasis (sixRows[(k : ℕ)]!)[(i : ℕ)]!) := by
  rw [coe_zB, zVec, ← (zBasis_comb_single i i.2).2,
    wAct_cGen_zComb k (zBasis_comb_single i i.2).1, sixRows_single k k.2 i i.2]

theorem resGL_inv_cGenZ_zB
    (k : Fin 21) (i : Fin 6) :
    resGL (cGenZ k)⁻¹ (zB i) = ⟨_, zComb_mem (sixRows[(k : ℕ)]!)[(i : ℕ)]!⟩ := by
  apply Subtype.ext
  rw [coe_resGL_apply, show ((((cGenZ k)⁻¹ : wSetStab Zsp) : Kstab v0))⁻¹ = cGen k from
    inv_inv (cGen k)]
  exact wAct_cGen_zB k i

theorem resGL_cGenZ_mem
    (k : Fin 21) :
    resGL (cGenZ k) ∈ TauCeti.BilinForm.isometryGroup bZ := by
  rw [← inv_mem_iff, ← map_inv, TauCeti.BilinForm.mem_isometryGroup_iff]
  refine bZ_map_eq_of_basis _ fun i j => ?_
  calc bZ (resGL (cGenZ k)⁻¹ (zB i)) (resGL (cGenZ k)⁻¹ (zB j))
      = bZ ⟨_, zComb_mem (sixRows[(k : ℕ)]!)[(i : ℕ)]!⟩
          ⟨_, zComb_mem (sixRows[(k : ℕ)]!)[(j : ℕ)]!⟩ :=
        congrArg₂ (fun a b => bZ a b) (resGL_inv_cGenZ_zB k i) (resGL_inv_cGenZ_zB k j)
    _ = bZ (zB i) (zB j) := by
        rw [bZ_comb, bZ_zB]
        exact gramMat_invariant k k.2 i j

theorem cGen_mem_map_comap
    (j : Fin 21) :
    cGen j ∈ ((TauCeti.BilinForm.isometryGroup bZ).comap resGL).map (wSetStab Zsp).subtype :=
  Subgroup.mem_map.2 ⟨cGenZ j, Subgroup.mem_comap.2 (resGL_cGenZ_mem j), rfl⟩

theorem Cr_le_map_comap :
    Cr ≤ ((TauCeti.BilinForm.isometryGroup bZ).comap resGL).map (wSetStab Zsp).subtype := by
  rw [← G21_eq_Cr, G21_eq, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact cGen_mem_map_comap j

set_option maxHeartbeats 1000000 in
theorem resGL_mem_isometryGroup
    (k : Cr) :
    resGL (Subgroup.inclusion Cr_le_wSetStab k) ∈ TauCeti.BilinForm.isometryGroup bZ := by
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 (Cr_le_map_comap k.2)
  have hk : Subgroup.inclusion Cr_le_wSetStab k = g := Subtype.ext e.symm
  rw [hk]
  exact Subgroup.mem_comap.1 hg

@[expose] def resZ :
    Cr →* TauCeti.BilinForm.isometryGroup bZ :=
  (resGL.comp (Subgroup.inclusion Cr_le_wSetStab)).codRestrict _ resGL_mem_isometryGroup

theorem coe_resZ_apply
    (k : Cr) (x : Zsp) :
    (((resZ k : TauCeti.BilinForm.isometryGroup bZ) : Zsp ≃ₗ[ZMod 2] Zsp) x : Wv v0) =
      wAct v0 (k : Kstab v0)⁻¹ x := rfl

theorem Mr_le_Cr :
    Mr ≤ Cr := fun _ hk => (mem_Mr'.1 hk).2

theorem ker_resZ_le :
    resZ.ker ≤ Mr.subgroupOf Cr := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hw := congrArg (fun φ : TauCeti.BilinForm.isometryGroup bZ =>
    (((φ : Zsp ≃ₗ[ZMod 2] Zsp) ⟨wFr, wFr_mem_Zsp⟩ : Zsp) : Wv v0)) hk
  have hinv : (k : Kstab v0)⁻¹ ∈ Mfr := hw
  rw [Subgroup.mem_subgroupOf]
  refine mem_Mr'.2 ⟨?_, k.2⟩
  rw [← inv_inv (k : Kstab v0)]
  exact Mfr.inv_mem hinv

@[expose] def resMr :
    Mr.subgroupOf Cr →* TauCeti.BilinForm.isometryGroup bZ :=
  resZ.comp (Mr.subgroupOf Cr).subtype

theorem natCard_ker_resMr :
    Nat.card resMr.ker = Nat.card resZ.ker :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
      invFun := fun y => ⟨⟨y.1, ker_resZ_le y.2⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem natCard_range_resMr_ge :
    23040 ≤ Nat.card resMr.range := by
  have hsub : MulAction.orbit Mr zVec ⊆
      (fun φ : TauCeti.BilinForm.isometryGroup bZ =>
        fun t => (((φ : Zsp ≃ₗ[ZMod 2] Zsp) (zB t) : Zsp) : Wv v0)) '' (resMr.range : Set _) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨resMr ⟨⟨g, Mr_le_Cr g.2⟩, Subgroup.mem_subgroupOf.2 g.2⟩, ⟨_, rfl⟩, ?_⟩
    funext t
    change wAct v0 (g : Kstab v0)⁻¹ (zB t : Wv v0) = wAct v0 (g : Kstab v0)⁻¹ (zVec t)
    rw [coe_zB]
  have hfin : (resMr.range : Set (TauCeti.BilinForm.isometryGroup bZ)).Finite := Set.toFinite _
  calc 23040 = (MulAction.orbit Mr zVec).ncard := ncard_orbit_zVec.symm
    _ ≤ _ := Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (resMr.range : Set (TauCeti.BilinForm.isometryGroup bZ)).ncard := Set.ncard_image_le hfin
    _ = Nat.card resMr.range := (Nat.card_coe_set_eq _).symm

theorem resZ_surjective_natCard_ker :
    Function.Surjective resZ ∧ Nat.card resZ.ker = 512 ∧
    Nat.card resZ.range = 1451520 := by
  have h1 : Nat.card resZ.ker * Nat.card resZ.range = 743178240 :=
    (natCard_ker_mul_range resZ).trans natCard_Cr
  have h2 : Nat.card resZ.ker * Nat.card resMr.range = 11796480 :=
    (congrArg (· * Nat.card resMr.range) natCard_ker_resMr.symm).trans
      ((natCard_ker_mul_range resMr).trans
        ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe Mr_le_Cr).toEquiv).trans M20_eq_Mr.2))
  have h3 := natCard_range_resMr_ge
  have h4 : Nat.card resZ.range ≤ 1451520 :=
    (Subgroup.card_le_card_group _).trans_eq natCard_isometryGroup_bZ
  have hk : Nat.card resZ.ker ≤ 512 := by
    have h7 : Nat.card resZ.ker * 23040 ≤ 512 * 23040 :=
      calc Nat.card resZ.ker * 23040 ≤ Nat.card resZ.ker * Nat.card resMr.range :=
            Nat.mul_le_mul_left _ h3
        _ = 512 * 23040 := h2.trans (by norm_num)
    exact Nat.le_of_mul_le_mul_right h7 (by norm_num)
  have hk' : Nat.card resZ.ker = 512 := by
    have h8 : 512 * 1451520 ≤ Nat.card resZ.ker * 1451520 :=
      calc 512 * 1451520 = Nat.card resZ.ker * Nat.card resZ.range := (h1.trans (by norm_num)).symm
        _ ≤ Nat.card resZ.ker * 1451520 := Nat.mul_le_mul_left _ h4
    exact le_antisymm hk (Nat.le_of_mul_le_mul_right h8 (by norm_num))
  have hr : Nat.card resZ.range = 1451520 := by
    have h9 : 512 * Nat.card resZ.range = 512 * 1451520 :=
      ((congrArg (· * Nat.card resZ.range) hk'.symm).trans h1).trans (by norm_num)
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h9
  exact ⟨MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ (hr.trans
    natCard_isometryGroup_bZ.symm)), hk', hr⟩

theorem nonempty_range_resZ_equiv :
    Nonempty (resZ.range ≃* CFSG.Assembly.LowTwoRank.StatedSp 3 (ZMod 2)) :=
  nonempty_isometryGroup_bZ_equiv.map fun e =>
    ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.2 resZ_surjective_natCard_ker.1)).trans
      Subgroup.topEquiv).trans e

theorem native_Co2_central_involution_symplectic_six_action :
    zBasis = #[31, 12319, 20511, 36895, 6145, 69663] ∧
    (∀ t : Fin 6, zVec t = decW zBasis[(t : ℕ)]!) ∧
    LinearIndependent (ZMod 2) zVec ∧ (∀ t, (zB t : Wv v0) = zVec t) ∧
    Module.finrank (ZMod 2) Zsp = 6 ∧
    (Zsp : Set (Wv v0)) \ {0} = {x | ∃ k ∈ Cr, wAct v0 k wFr = x} ∧
    gramSix = #[16, 44, 42, 54, 41, 30] ∧
    (∀ i j : Fin 6, bZ (zB i) (zB j) = bvec 6 gramSix[(i : ℕ)]! j) ∧
    bZ.IsAlt ∧ bZ.Nondegenerate ∧
    (∀ (k : Cr) (x : Zsp),
      (((resZ k : TauCeti.BilinForm.isometryGroup bZ) : Zsp ≃ₗ[ZMod 2] Zsp) x : Wv v0) =
        wAct v0 (k : Kstab v0)⁻¹ x) ∧
    Function.Surjective resZ ∧ Nat.card resZ.ker = 512 ∧
    Nat.card (TauCeti.BilinForm.isometryGroup bZ) = 1451520 ∧
    Nonempty (resZ.range ≃* CFSG.Assembly.LowTwoRank.StatedSp 3 (ZMod 2)) ∧
    Nat.card resZ.range = 1451520 := by
  exact ⟨rfl, fun _ => rfl, linearIndependent_zVec, coe_zB, finrank_Zsp, Zsp_diff_zero, rfl,
    bZ_zB, bZ_isAlt, bZ_nondegenerate, coe_resZ_apply, resZ_surjective_natCard_ker.1,
    resZ_surjective_natCard_ker.2.1, natCard_isometryGroup_bZ, nonempty_range_resZ_equiv,
    resZ_surjective_natCard_ker.2.2⟩

end CFSG.Monster.B.TwoA.Co2Inv
