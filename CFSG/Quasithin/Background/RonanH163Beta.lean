module

public import CFSG.Quasithin.Background.RonanH163Gen

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def betaCols : List ℕ := [30, 0, 6, 0, 0, 0, 23, 0, 10, 0]

@[expose] def betaLin : (Fin 10 → ZMod 2) →+ (Fin 5 → ZMod 2) where
  toFun v i := ∑ j : Fin 10, v j * bvec 5 (betaCols.getD j 0) i
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp [add_mul, Finset.sum_add_distrib]

theorem betaLin_cols : ∀ j < 10, betaLin (bvec 10 (2 ^ j)) = bvec 5 (betaCols.getD j 0) := by
  decide +kernel

@[expose] def betaHom : W10 →* G6.PermMod 5 := AddMonoidHom.toMultiplicative betaLin

theorem betaHom_toW (k : ℕ) : betaHom (toW 10 k) = toW 5 (actM betaCols k) :=
  congrArg Multiplicative.ofAdd (addHom_bvec betaLin betaCols rfl betaLin_cols k)

@[expose] def betaU : ↥U4 →* G6.PermMod 5 := betaHom.comp U4.subtype

theorem betaCols_lt : ∀ c ∈ betaCols, c < 2 ^ 5 := by
  decide +kernel

theorem betaCols_inj : ∀ m ∈ combos b4, actM betaCols m = 0 → m = 0 := by
  decide +kernel

theorem betaCols_range : ∀ y : Fin 5 → ZMod 2,
    (∑ i, y i = 0) ↔ ∃ m ∈ combos b4, bvec 5 (actM betaCols m) = y := by
  decide +kernel

theorem betaCols_sig1 : ∀ m ∈ combos b4,
    bvec 5 (actM betaCols (actC10 g1Arr m)) = fun i => bvec 5 (actM betaCols m) (sig1⁻¹ i) := by
  decide +kernel

theorem betaCols_sig2 : ∀ m ∈ combos b4,
    bvec 5 (actM betaCols (actC10 g2Arr m)) = fun i => bvec 5 (actM betaCols m) (sig2⁻¹ i) := by
  decide +kernel

theorem betaU_range : betaU.range = G6.coreMod 5 := by
  ext x
  rw [MonoidHom.mem_range, G6.mem_coreMod]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨m, hm, hmu⟩ := mem_maskSub.1 u.2
    have h1 : betaU u = toW 5 (actM betaCols m) := by
      change betaHom (u : W10) = _
      rw [← hmu, betaHom_toW]
    rw [h1]
    exact (betaCols_range (bvec 5 (actM betaCols m))).2 ⟨m, hm, rfl⟩
  · intro hx
    obtain ⟨m, hm, hmx⟩ := (betaCols_range (Multiplicative.toAdd x)).1 hx
    have hmem : toW 10 m ∈ U4 := mem_maskSub.2 ⟨m, hm, rfl⟩
    refine ⟨⟨toW 10 m, hmem⟩, ?_⟩
    change betaHom (toW 10 m) = x
    rw [betaHom_toW]
    exact congrArg Multiplicative.ofAdd hmx

theorem betaU_eq_one (u : ↥U4) : betaU u = 1 ↔ (u : W10) ∈ (⊥ : Subgroup W10) := by
  rw [Subgroup.mem_bot]
  change betaHom (u : W10) = 1 ↔ (u : W10) = 1
  constructor
  · intro h
    obtain ⟨m, hm, hmu⟩ := mem_maskSub.1 u.2
    rw [← hmu, betaHom_toW] at h
    have hlt : actM betaCols m < 2 ^ 5 := actM_lt betaCols_lt m
    have h2 : actM betaCols m = 0 := toW_inj hlt (by norm_num) (by rw [h, toW_zero])
    rw [← hmu, betaCols_inj m hm h2, toW_zero]
  · intro h
    rw [h, map_one]

@[expose] def EqvU4 (g : P24) : Prop :=
  ∀ hg : g ∈ MY mog22plus Qstd, ∀ w : W10, w ∈ U4 →
    betaHom (R ⟨g, (mem_MY_iff.1 hg).1⟩ w) = G6.permAct 5 (piQ mog22plus ⟨g, hg⟩) (betaHom w)

theorem eqvU4_NQ2 {x : P24}
    (hx : x ∈ NQ2) : EqvU4 x := by
  intro hgM w hw
  have h1 : (⟨x, hgM⟩ : ↥(MY mog22plus Qstd)) ∈ (piQ mog22plus).ker := by
    rw [ker_piQ_L2]
    exact Subgroup.mem_subgroupOf.2 hx
  have hpiQ : piQ mog22plus ⟨x, hgM⟩ = 1 := MonoidHom.mem_ker.1 h1
  have hmem : R ⟨x, (mem_MY_iff.1 hgM).1⟩ ∈ rImg R NQ2 :=
    Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 hx)
  have hw' : w ∈ fixV (rImg R NQ2) := by
    rw [fixV_NQ2]
    exact hw
  have hfix : R ⟨x, (mem_MY_iff.1 hgM).1⟩ w = w := mem_fixV.1 hw' _ hmem
  rw [hfix, hpiQ, map_one, MulAut.one_apply]

theorem eqvU4_g1 :
    EqvU4 g1Perm := by
  intro hgM w hw
  have hpiQ : piQ mog22plus ⟨g1Perm, hgM⟩ = sig1 := piQ_eq_of_smul _ sig1 g1_smul_Zq
  have hR : R ⟨g1Perm, (mem_MY_iff.1 hgM).1⟩ = R g1Elt := rfl
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
  rw [hpiQ, hR, R_g1, betaHom_toW, betaHom_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact congrFun (betaCols_sig1 m hm) i

theorem eqvU4_g2 :
    EqvU4 g2Perm := by
  intro hgM w hw
  have hpiQ : piQ mog22plus ⟨g2Perm, hgM⟩ = sig2 := piQ_eq_of_smul _ sig2 g2_smul_Zq
  have hR : R ⟨g2Perm, (mem_MY_iff.1 hgM).1⟩ = R g2Elt := rfl
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
  rw [hpiQ, hR, R_g2, betaHom_toW, betaHom_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact congrFun (betaCols_sig2 m hm) i

theorem eqvU4_one : EqvU4 1 := by
  intro hg w _
  have h1 : R ⟨1, (mem_MY_iff.1 hg).1⟩ = 1 := map_one R
  have h2 : piQ mog22plus ⟨1, hg⟩ = 1 := map_one (piQ mog22plus)
  rw [h1, h2, map_one, MulAut.one_apply, MulAut.one_apply]

theorem eqvU4_mul {x y : P24}
    (hx : x ∈ MY mog22plus Qstd) (hy : y ∈ MY mog22plus Qstd) (ihx : EqvU4 x) (ihy : EqvU4 y) :
    EqvU4 (x * y) := by
  intro hxy w hw
  have hx1 : x ∈ mog22plus := (mem_MY_iff.1 hx).1
  have hy1 : y ∈ mog22plus := (mem_MY_iff.1 hy).1
  have hv : R ⟨y, hy1⟩ w ∈ U4 :=
    inv_U4 (R ⟨y, hy1⟩) (Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 hy)) w hw
  have hab : (⟨x * y, (mem_MY_iff.1 hxy).1⟩ : ↥mog22plus) = ⟨x, hx1⟩ * ⟨y, hy1⟩ := rfl
  have hab' : (⟨x * y, hxy⟩ : ↥(MY mog22plus Qstd)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hab, hab', map_mul R ⟨x, hx1⟩ ⟨y, hy1⟩,
    MulAut.mul_apply W10 (R ⟨x, hx1⟩) (R ⟨y, hy1⟩) w,
    map_mul (piQ mog22plus) ⟨x, hx⟩ ⟨y, hy⟩,
    map_mul (G6.permAct 5) (piQ mog22plus ⟨x, hx⟩) (piQ mog22plus ⟨y, hy⟩),
    MulAut.mul_apply (G6.PermMod 5) (G6.permAct 5 (piQ mog22plus ⟨x, hx⟩))
      (G6.permAct 5 (piQ mog22plus ⟨y, hy⟩)) (betaHom w),
    ihx hx _ hv, ihy hy w hw]

theorem permAct_inv_apply
    {x : P24} (hx : x ∈ MY mog22plus Qstd) (b B : G6.PermMod 5)
    (h3 : b = G6.permAct 5 (piQ mog22plus ⟨x, hx⟩) B) :
    G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ b = B := by
  calc G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ b
      = G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ (G6.permAct 5 (piQ mog22plus ⟨x, hx⟩) B) :=
        congrArg (fun z => G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ z) h3
    _ = (G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ * G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)) B :=
        (MulAut.mul_apply (G6.PermMod 5) _ _ B).symm
    _ = G6.permAct 5 ((piQ mog22plus ⟨x, hx⟩)⁻¹ * piQ mog22plus ⟨x, hx⟩) B :=
        congrArg (fun f : MulAut (G6.PermMod 5) => f B)
          (map_mul (G6.permAct 5) (piQ mog22plus ⟨x, hx⟩)⁻¹ (piQ mog22plus ⟨x, hx⟩)).symm
    _ = G6.permAct 5 1 B :=
        congrArg (fun τ : Equiv.Perm (Fin 5) => G6.permAct 5 τ B)
          (inv_mul_cancel (piQ mog22plus ⟨x, hx⟩))
    _ = (1 : MulAut (G6.PermMod 5)) B :=
        congrArg (fun f : MulAut (G6.PermMod 5) => f B) (map_one (G6.permAct 5))
    _ = B := MulAut.one_apply (G6.PermMod 5) B

theorem perm_inv_eq
    {x : P24} (hx : x ∈ MY mog22plus Qstd) (hgM : x⁻¹ ∈ MY mog22plus Qstd) (b B : G6.PermMod 5)
    (hA : G6.permAct 5 (piQ mog22plus ⟨x, hx⟩)⁻¹ B = b) :
    b = G6.permAct 5 (piQ mog22plus ⟨x⁻¹, hgM⟩) B := by
  have hpiQ : piQ mog22plus ⟨x⁻¹, hgM⟩ = (piQ mog22plus ⟨x, hx⟩)⁻¹ :=
    map_inv (piQ mog22plus) ⟨x, hx⟩
  exact hA.symm.trans (congrArg (fun τ : Equiv.Perm (Fin 5) => G6.permAct 5 τ B) hpiQ.symm)

theorem eqvU4_inv {x : P24}
    (hx : x ∈ MY mog22plus Qstd) (ihx : EqvU4 x) : EqvU4 x⁻¹ := by
  intro hgM w hw
  have hx1 : x ∈ mog22plus := (mem_MY_iff.1 hx).1
  have hi1 : x⁻¹ ∈ mog22plus := (mem_MY_iff.1 hgM).1
  have hv : R ⟨x⁻¹, hi1⟩ w ∈ U4 :=
    inv_U4 (R ⟨x⁻¹, hi1⟩) (Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 hgM)) w hw
  have h1 := ihx hx _ hv
  have hm : (⟨x, hx1⟩ : ↥mog22plus) * ⟨x⁻¹, hi1⟩ = 1 := Subtype.ext (mul_inv_cancel x)
  have hm1 : R ⟨x, hx1⟩ * R ⟨x⁻¹, hi1⟩ = 1 := by
    rw [← map_mul R ⟨x, hx1⟩ ⟨x⁻¹, hi1⟩, hm, map_one R]
  have h2 : R ⟨x, hx1⟩ (R ⟨x⁻¹, hi1⟩ w) = w :=
    (MulAut.mul_apply W10 (R ⟨x, hx1⟩) (R ⟨x⁻¹, hi1⟩) w).symm.trans
      ((congrArg (fun f : MulAut W10 => f w) hm1).trans (MulAut.one_apply W10 w))
  have h3 : betaHom w = G6.permAct 5 (piQ mog22plus ⟨x, hx⟩) (betaHom (R ⟨x⁻¹, hi1⟩ w)) :=
    (congrArg betaHom h2.symm).trans h1
  exact perm_inv_eq hx hgM _ _ (permAct_inv_apply hx _ _ h3)

theorem eqvU4_closure :
    ∀ g ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}), EqvU4 g := by
  have hMY : Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) ≤ MY mog22plus Qstd := by
    rw [Subgroup.closure_le]
    rintro x (hx | rfl | rfl)
    · exact NQ2_le_MY_Q hx
    · exact g1Perm_mem_MY g1Perm_mem_mog22plus
    · exact g2Perm_mem_MY g2Perm_mem_mog22plus
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => EqvU4 g) ?_ ?_ ?_ ?_ hg
  · rintro x (hx | rfl | rfl)
    · exact eqvU4_NQ2 hx
    · exact eqvU4_g1
    · exact eqvU4_g2
  · exact eqvU4_one
  · intro x y hx hy ihx ihy
    exact eqvU4_mul (hMY hx) (hMY hy) ihx ihy
  · intro x hx ihx
    exact eqvU4_inv (hMY hx) ihx

theorem betaHom_R {g : P24}
    (hg : g ∈ MY mog22plus Qstd) {w : W10} (hw : w ∈ U4) :
    betaHom (R ⟨g, (mem_MY_iff.1 hg).1⟩ w) = G6.permAct 5 (piQ mog22plus ⟨g, hg⟩) (betaHom w) :=
  eqvU4_closure g (MQ_le_closure hg) hg w hw

theorem induces_std :
    InducesOnSub (rImg R (MY mog22plus Qstd)) (fixV (rImg R (KY mog22plus Qstd))) ⊥
      (G6.PermMod 5) (G6.coreMod 5) (G6.permAct 5).range := by
  rw [KY_Q_L2, fixV_NQ2]
  unfold InducesOnSub
  refine ⟨bot_le, fun g hg u hu => inv_U4 g hg u hu, ?_, betaU, betaU_range, betaU_eq_one, ?_, ?_⟩
  · intro g _ z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact MulEquiv.map_one g
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    have hxM : (x : P24) ∈ MY mog22plus Qstd := Subgroup.mem_subgroupOf.1 hx
    refine ⟨G6.permAct 5 (piQ mog22plus ⟨(x : P24), hxM⟩), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    intro u u' huu'
    change betaHom (u' : W10) = G6.permAct 5 (piQ mog22plus ⟨(x : P24), hxM⟩) (betaHom (u : W10))
    rw [huu']
    exact betaHom_R hxM u.2
  · intro γ hγ
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.1 hγ
    have hσ : σ ∈ (piQ mog22plus).range := by
      rw [piQ_range_top_L2]
      exact Subgroup.mem_top σ
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hσ
    refine ⟨R ⟨(y : P24), (mem_MY_iff.1 y.2).1⟩,
      Subgroup.mem_map_of_mem R (Subgroup.mem_subgroupOf.2 y.2), ?_⟩
    intro u u' huu'
    change betaHom (u' : W10) = G6.permAct 5 (piQ mog22plus y) (betaHom (u : W10))
    rw [huu']
    exact betaHom_R y.2 u.2

end CFSG.Quasithin.RonanH163
