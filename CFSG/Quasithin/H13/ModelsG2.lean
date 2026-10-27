module

public import CFSG.Quasithin.H13.ModelsG2Hom
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.Quasithin.Background.G2UAdjoint

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U
open scoped Matrix

abbrev zornStab : Subgroup (GL (Fin 14) (ZMod 3)) :=
  compressStab zornE zornF zornF_mul_zornE_mul_zornF

@[expose] noncomputable def zornCompress : zornStab →* GL (Fin 8) (ZMod 3) :=
  (compressHom zornE zornF zornJ zornJ_mul_zornE zornF_mul_zornJ
    zornJ_add_zornE_mul_zornF).toHomUnits

theorem coe_zornCompress (g : zornStab) :
    ((zornCompress g : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      zornJ + zornE * ((g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) * zornF :=
  rfl

variable {K : Type} [Field K]

theorem coe_inv_of_coe_eq {g : GL (Fin 14) (ZMod 3)} {A B : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (hg : (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = A) (hAB : A * B = 1) :
    ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = B := by
  calc ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3))
      = ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) * (A * B) := by
        rw [hAB, Matrix.mul_one]
    _ = B := by
        rw [← hg, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]

theorem coe_glHom_of_gen (σ : K ≃+* ZMod 3) {g : ModGL .G2 K} {i : Fin Tag.G2.rank} {c : K}
    (h : (g : Module.End K (RootModule .G2 K)) = xOp .G2 K i c ∨
      (g : Module.End K (RootModule .G2 K)) = yOp .G2 K i c) :
    ((glHom σ g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
        XMat (ZMod 3) i (σ c) ∨
      ((glHom σ g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
        YMat (ZMod 3) i (σ c) := by
  rw [glHom_apply, coe_glEquiv]
  rcases h with h | h
  · exact Or.inl (by rw [h, endEquiv_xOp])
  · exact Or.inr (by rw [h, endEquiv_yOp])

theorem map_adjointGroup_le_zornStab (σ : K ≃+* ZMod 3) :
    (adjointGroup .G2 K).map (glHom σ) ≤ zornStab := by
  rw [adjointGroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, c, h⟩, rfl⟩
  rw [SetLike.mem_coe, mem_compressStab]
  rcases coe_glHom_of_gen σ h with h | h
  · rw [coe_inv_of_coe_eq h (XMat_mul_neg i (σ c)).1, h]
    exact ⟨(XMat_compress i (σ c)).1, (XMat_compress i (-σ c)).1⟩
  · rw [coe_inv_of_coe_eq h (XMat_mul_neg i (σ c)).2, h]
    exact ⟨(XMat_compress i (σ c)).2, (XMat_compress i (-σ c)).2⟩

@[expose] noncomputable def adjointToZornStab (σ : K ≃+* ZMod 3) :
    adjointGroup .G2 K →* zornStab :=
  ((glHom σ).comp (adjointGroup .G2 K).subtype).codRestrict zornStab fun g =>
    map_adjointGroup_le_zornStab σ ⟨g.1, g.2, rfl⟩

@[expose] noncomputable def g2ZornHom (σ : K ≃+* ZMod 3) :
    adjointGroup .G2 K →* (quasithinZorn (ZMod 3) ≃ₗ[ZMod 3] quasithinZorn (ZMod 3)) :=
  ((zornMatHom (ZMod 3)).comp zornCompress).comp (adjointToZornStab σ)

theorem g2ZornHom_apply (σ : K ≃+* ZMod 3) (g : adjointGroup .G2 K) :
    g2ZornHom σ g = zornMatHom (ZMod 3) (zornCompress (adjointToZornStab σ g)) :=
  rfl

theorem coe_adjointToZornStab (σ : K ≃+* ZMod 3) (g : adjointGroup .G2 K) :
    ((adjointToZornStab σ g : zornStab) : GL (Fin 14) (ZMod 3)) = glHom σ g :=
  rfl

theorem g2ZornHom_mem_zornAut (σ : K ≃+* ZMod 3) (g : adjointGroup .G2 K) :
    g2ZornHom σ g ∈ zornAut (ZMod 3) := by
  have hgen : Subgroup.closure (((↑) : adjointGroup .G2 K → ModGL .G2 K) ⁻¹'
      {g | ∃ (i : Fin Tag.G2.rank) (c : K),
        (g : Module.End K (RootModule .G2 K)) = xOp .G2 K i c ∨
          (g : Module.End K (RootModule .G2 K)) = yOp .G2 K i c}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have htop : (zornAut (ZMod 3)).comap (g2ZornHom σ) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro ⟨x, hx⟩ ⟨i, c, h⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, g2ZornHom_apply]
    apply zornMatHom_mem_zornAut
    rw [coe_zornCompress, coe_adjointToZornStab]
    rcases coe_glHom_of_gen σ h with h | h
    · rw [h]
      exact (XMat_isZornAutoMat i (σ c)).1
    · rw [h]
      exact (XMat_isZornAutoMat i (σ c)).2
  have hg : g ∈ (zornAut (ZMod 3)).comap (g2ZornHom σ) := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hg

variable [Finite K]

theorem isSimpleGroup_adjointGroup_G2
    (hK : 3 ≤ Nat.card K) :
    IsSimpleGroup (adjointGroup .G2 K) := by
  have h := (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite K] in
theorem exists_mem_adjointGroup_glHom (σ : K ≃+* ZMod 3) :
    ∃ g : adjointGroup .G2 K, ((glHom σ g : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = XMat (ZMod 3) (ix 0) 1 := by
  have h1 := (XMat_mul_neg (ix 0) 1).1
  have h2 : XMat (ZMod 3) (ix 0) (-1) * XMat (ZMod 3) (ix 0) 1 = 1 := by
    decide +kernel
  let u : GL (Fin 14) (ZMod 3) := ⟨XMat (ZMod 3) (ix 0) 1, XMat (ZMod 3) (ix 0) (-1), h1, h2⟩
  let y : ModGL .G2 K := (glEquiv σ).symm u
  have hy : (y : Module.End K (RootModule .G2 K)) = xOp .G2 K (ix 0) (σ.symm 1) := by
    apply (endEquiv σ).injective
    rw [← coe_glEquiv, MulEquiv.apply_symm_apply, endEquiv_xOp, RingEquiv.apply_symm_apply]
  refine ⟨⟨y, Subgroup.subset_closure ⟨ix 0, σ.symm 1, Or.inl hy⟩⟩, ?_⟩
  change ((glHom σ ((glEquiv σ).symm u) : GL (Fin 14) (ZMod 3)) :
    Matrix (Fin 14) (Fin 14) (ZMod 3)) = _
  rw [glHom_apply, MulEquiv.apply_symm_apply]

theorem g2ZornHom_injective
    (σ : K ≃+* ZMod 3) (hK : 3 ≤ Nat.card K) :
    Function.Injective (g2ZornHom σ) := by
  have := isSimpleGroup_adjointGroup_G2 hK
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g2ZornHom σ).ker with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := exists_mem_adjointGroup_glHom σ
    have h1 : g2ZornHom σ g = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top g)
    apply compress_XMat_ne
    have h2 := LinearEquiv.congr_fun h1 (zornBasisVec 2)
    rw [g2ZornHom_apply] at h2
    rw [← hg, ← coe_adjointToZornStab, ← coe_zornCompress]
    exact h2

theorem card_adjointGroup_G2_three
    (hK : Nat.card K = 3) :
    Nat.card (adjointGroup .G2 K) = 4245696 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  decide

noncomputable def adjointGroupG2EquivZornAut
    (σ : K ≃+* ZMod 3) (hK : Nat.card K = 3) :
    adjointGroup .G2 K ≃* zornAut (ZMod 3) := by
  have hinj := g2ZornHom_injective σ (by omega)
  have hle : (g2ZornHom σ).range ≤ zornAut (ZMod 3) := by
    rintro _ ⟨g, rfl⟩
    exact g2ZornHom_mem_zornAut σ g
  have hcard : Nat.card (zornAut (ZMod 3)) ≤ Nat.card (g2ZornHom σ).range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_adjointGroup_G2_three hK]
    exact card_zornAut_three_le
  exact (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (Subgroup.eq_of_le_of_card_ge hle hcard))

noncomputable def adjointQuotientG2EquivQuasithinG2
    (σ : K ≃+* ZMod 3) (hK : Nat.card K = 3) :
    AdjointQuotient .G2 K ≃* quasithinG2 (ZMod 3) :=
  ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot).trans
    ((adjointGroupG2EquivZornAut σ hK).trans (MulEquiv.subgroupCongr quasithinG2_eq_zornAut.symm))

noncomputable def adjointQuotientG2ZModThreeEquiv
    :
    AdjointQuotient .G2 (ZMod 3) ≃* quasithinG2 (ZMod 3) :=
  adjointQuotientG2EquivQuasithinG2 (RingEquiv.refl _) (Nat.card_zmod 3)

theorem lieModel_of_mulEquiv_quasithinG2
    {X : Type} [Group X] (e : X ≃* quasithinG2 (ZMod 3)) :
    CFSG.Blueprint.LieModel X .G2 0 3 1 :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, ZMod 3,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans adjointQuotientG2ZModThreeEquiv.symm⟩⟩)

theorem lieModel_quasithinG2
    : CFSG.Blueprint.LieModel (quasithinG2 (ZMod 3)) .G2 0 3 1 :=
  lieModel_of_mulEquiv_quasithinG2 (MulEquiv.refl _)

end CFSG.Quasithin.H13
