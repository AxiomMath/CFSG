module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.Quasithin.Background.HTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

def intModIncl {A W : Subgroup G} (hA : IsElemAbelian 2 A) (hW : IsElemAbelian 2 W)
    (hWA : W ≤ A) : IntMod W hW →* IntMod A hA where
  toFun x := IntMod.mk hA ⟨x.val, hWA x.val_mem⟩
  map_one' := IntMod.val_injective rfl
  map_mul' _ _ := IntMod.val_injective rfl

private theorem mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y h
  rw [mkTil_eq_iff] at h
  exact IntMod.val_injective (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h))

private theorem modNull_bot {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    modNull (⊥ : Subgroup G) V hV = ⊥ := by
  rw [modNull, intSub, Subgroup.bot_subgroupOf]
  rfl

noncomputable def intModEquiv {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IntMod V hV ≃* (↥V) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable def tilBotEquiv {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    (↥V) ≃* Vtil (⊥ : Subgroup G) V hV :=
  (intModEquiv hV).symm.trans <|
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (modNull_bot hV).symm)

theorem tilBotEquiv_apply {V : Subgroup G} (hV : IsElemAbelian 2 V) (x : ↥V) :
    tilBotEquiv hV x = mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV x) := by
  have h0 : (intModEquiv hV).symm x = IntMod.mk hV x := rfl
  rw [tilBotEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h0,
    QuotientGroup.quotientBot_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

noncomputable def imgTilEquiv {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hWA : W ≤ A) : ↥(W.subgroupOf A) ≃* ↥(imgTil (⊥ : Subgroup G) A hA W) :=
  Subgroup.equivMapOfInjective (W.subgroupOf A) (mkTil (⊥ : Subgroup G) A hA)
    (mkTil_bot_injective hA)

theorem imgTilEquiv_apply {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hWA : W ≤ A) (y : ↥(W.subgroupOf A)) :
    imgTilEquiv hA hWA y =
      ⟨mkTil (⊥ : Subgroup G) A hA y.val,
        (mem_imgTil (⊥ : Subgroup G) A hA W _).2 ⟨y.val, y.2, rfl⟩⟩ :=
  Subtype.ext (Subgroup.coe_equivMapOfInjective_apply _ _ _ y)

noncomputable def restrictEquiv {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A) :
    ↥(imgTil (⊥ : Subgroup G) A hA W) ≃* Vtil (⊥ : Subgroup G) W hW :=
  (imgTilEquiv hA hWA).symm.trans
    ((Subgroup.subgroupOfEquivOfLe hWA).trans (tilBotEquiv hW))

theorem restrictEquiv_apply {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A) (y : ↥(W.subgroupOf A)) :
    restrictEquiv hA hW hWA
        ⟨mkTil (⊥ : Subgroup G) A hA y.val,
          (mem_imgTil (⊥ : Subgroup G) A hA W _).2 ⟨y.val, y.2, rfl⟩⟩ =
      mkTil (⊥ : Subgroup G) W hW
        (IntMod.mk hW (Subgroup.subgroupOfEquivOfLe hWA y)) := by
  have h1 : (imgTilEquiv hA hWA).symm
      ⟨mkTil (⊥ : Subgroup G) A hA y.val,
        (mem_imgTil (⊥ : Subgroup G) A hA W _).2 ⟨y.val, y.2, rfl⟩⟩ = y := by
    rw [MulEquiv.symm_apply_eq]
    exact (imgTilEquiv_apply hA hWA y).symm
  rw [restrictEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, tilBotEquiv_apply]

theorem restrictEquiv_symm_apply {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A) (x : IntMod W hW) :
    (restrictEquiv hA hW hWA).symm (mkTil (⊥ : Subgroup G) W hW x) =
      ⟨mkTil (⊥ : Subgroup G) A hA (intModIncl hA hW hWA x),
        (mem_imgTil (⊥ : Subgroup G) A hA W _).2
          ⟨intModIncl hA hW hWA x, by
            change x.val ∈ W
            exact x.val_mem, rfl⟩⟩ := by
  rw [MulEquiv.symm_apply_eq]
  rw [restrictEquiv_apply hA hW hWA
    (⟨intModIncl hA hW hWA x, x.val_mem⟩ : ↥(W.subgroupOf A))]
  exact congrArg (mkTil (⊥ : Subgroup G) W hW) (IntMod.val_injective rfl)

theorem actTil_mem_stabSub_imgTil {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A) {g : G}
    (hgA : g ∈ stabTil (⊥ : Subgroup G) A) (hgW : g ∈ stabTil (⊥ : Subgroup G) W) :
    actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩ ∈ stabSub (imgTil (⊥ : Subgroup G) A hA W) := by
  rw [mem_stabSub]
  have forward : ∀ {h : G} (hhA : h ∈ stabTil (⊥ : Subgroup G) A)
      (hhW : h ∈ stabTil (⊥ : Subgroup G) W) {u : Vtil (⊥ : Subgroup G) A hA},
      u ∈ imgTil (⊥ : Subgroup G) A hA W →
      actTil (⊥ : Subgroup G) A hA ⟨h, hhA⟩ u ∈ imgTil (⊥ : Subgroup G) A hA W := by
    intro h hhA hhW u hu
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) A hA W u).1 hu
    rw [actTil_mk]
    exact (mem_imgTil (⊥ : Subgroup G) A hA W _).2
      ⟨actStab (⊥ : Subgroup G) A hA ⟨h, hhA⟩ x, by
        rw [actStab_apply_val]
        exact (Subgroup.mem_normalizer_iff.mp (stabTil_le_normalizer (⊥) W hhW) x.val).1 hx, rfl⟩
  intro u
  constructor
  · intro hu
    have hmem : actTil (⊥ : Subgroup G) A hA ⟨g⁻¹, (stabTil (⊥) A).inv_mem hgA⟩
        (actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩ u) ∈ imgTil (⊥ : Subgroup G) A hA W :=
      forward ((stabTil (⊥) A).inv_mem hgA) ((stabTil (⊥) W).inv_mem hgW) hu
    have heq : actTil (⊥ : Subgroup G) A hA ⟨g⁻¹, (stabTil (⊥) A).inv_mem hgA⟩
        (actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩ u) = u := by
      calc actTil (⊥ : Subgroup G) A hA ⟨g⁻¹, _⟩ (actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩ u)
          = (actTil (⊥ : Subgroup G) A hA ⟨g⁻¹, _⟩ *
              actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩) u := rfl
        _ = actTil (⊥ : Subgroup G) A hA (⟨g⁻¹, _⟩ * ⟨g, hgA⟩) u := by rw [map_mul]
        _ = u := by
          rw [show (⟨g⁻¹, _⟩ * ⟨g, hgA⟩ : ↥(stabTil (⊥) A)) = 1 by
            apply Subtype.ext
            simp, map_one, MulAut.one_apply]
    rwa [heq] at hmem
  · exact forward hgA hgW

theorem congrHom_restrictEquiv_actTil {A W : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A) {g : G}
    (hgA : g ∈ stabTil (⊥ : Subgroup G) A) (hgW : g ∈ stabTil (⊥ : Subgroup G) W)
    (hgstab : actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩ ∈
      stabSub (imgTil (⊥ : Subgroup G) A hA W)) :
    CFSG.Quasithin.H.congrHom (restrictEquiv hA hW hWA)
      (resHom (imgTil (⊥ : Subgroup G) A hA W)
        ⟨actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩, hgstab⟩) =
      actTil (⊥ : Subgroup G) W hW ⟨g, hgW⟩ := by
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) W hW q
  rw [CFSG.Quasithin.H.congrHom_apply, restrictEquiv_symm_apply hA hW hWA x]
  have hmem : (actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩
      (intModIncl hA hW hWA x)).val ∈ W := by
    rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (stabTil_le_normalizer (⊥) W hgW) x.val).1 x.val_mem
  have hres : resHom (imgTil (⊥ : Subgroup G) A hA W)
      ⟨actTil (⊥ : Subgroup G) A hA ⟨g, hgA⟩, hgstab⟩
      ⟨mkTil (⊥ : Subgroup G) A hA (intModIncl hA hW hWA x),
        (mem_imgTil (⊥ : Subgroup G) A hA W _).2
          ⟨intModIncl hA hW hWA x, x.val_mem, rfl⟩⟩ =
      ⟨mkTil (⊥ : Subgroup G) A hA
        (actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩ (intModIncl hA hW hWA x)),
        (mem_imgTil (⊥ : Subgroup G) A hA W _).2
          ⟨actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩ (intModIncl hA hW hWA x), hmem, rfl⟩⟩ := by
    refine Subtype.ext ?_
    rw [resHom_apply, actTil_mk]
  rw [hres, restrictEquiv_apply hA hW hWA
    (⟨actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩ (intModIncl hA hW hWA x), hmem⟩), actTil_mk]
  apply congrArg (mkTil (⊥ : Subgroup G) W hW)
  apply IntMod.val_injective
  change ((Subgroup.subgroupOfEquivOfLe hWA)
    ⟨actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩ (intModIncl hA hW hWA x), hmem⟩ : ↥W).val =
      (actStab (⊥ : Subgroup G) W hW ⟨g, hgW⟩ x).val
  rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
  change (actStab (⊥ : Subgroup G) A hA ⟨g, hgA⟩ (intModIncl hA hW hWA x)).val =
    (actStab (⊥ : Subgroup G) W hW ⟨g, hgW⟩ x).val
  rw [actStab_apply_val, actStab_apply_val]
  simp [intModIncl]
  rfl

private theorem mem_stabTil_bot_of_le_normalizer {A H : Subgroup G}
    (hHA : H ≤ Subgroup.normalizer (A : Set G)) {g : G} (hg : g ∈ H) :
    g ∈ stabTil (⊥ : Subgroup G) A :=
  Subgroup.mem_inf.mpr
    ⟨hHA hg, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g⟩

theorem Mbar_eq_autSub_map {A W H : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A)
    (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) :
    ∃ e : ↥(imgTil (⊥ : Subgroup G) A hA W) ≃* Vtil (⊥ : Subgroup G) W hW,
      Mbar H (⊥ : Subgroup G) W hW =
        (autSub (barSub (⊥ : Subgroup G) A hA H) (imgTil (⊥ : Subgroup G) A hA W)).map
          (CFSG.Quasithin.H.congrHom e) := by
  classical
  refine ⟨restrictEquiv hA hW hWA, ?_⟩
  ext φ
  constructor
  · intro hφ
    obtain ⟨gW, hgH, hgWval⟩ := (mem_barSub (⊥ : Subgroup G) W hW H φ).1 hφ
    have hgA : (gW : G) ∈ stabTil (⊥ : Subgroup G) A :=
      mem_stabTil_bot_of_le_normalizer hHA hgH
    have hgW : (gW : G) ∈ stabTil (⊥ : Subgroup G) W := by
      simpa using (mem_stabTil_bot_of_le_normalizer hHW hgH)
    have hgstab : actTil (⊥ : Subgroup G) A hA ⟨(gW : G), hgA⟩ ∈
        stabSub (imgTil (⊥ : Subgroup G) A hA W) :=
      actTil_mem_stabSub_imgTil hA hW hWA hgA hgW
    have hnat := congrHom_restrictEquiv_actTil hA hW hWA hgA hgW hgstab
    have hnat' : CFSG.Quasithin.H.congrHom (restrictEquiv hA hW hWA)
        (resHom (imgTil (⊥ : Subgroup G) A hA W)
          ⟨actTil (⊥ : Subgroup G) A hA ⟨(gW : G), hgA⟩, hgstab⟩) = φ := by
      rw [hnat]
      have hgg : (⟨(gW : G), hgW⟩ : ↥(stabTil (⊥) W)) = gW := Subtype.ext rfl
      rw [hgg]
      exact hgWval
    refine Subgroup.mem_map.mpr ⟨resHom (imgTil (⊥ : Subgroup G) A hA W)
      ⟨actTil (⊥ : Subgroup G) A hA ⟨(gW : G), hgA⟩, hgstab⟩, ?_, hnat'⟩
    refine mem_autSub.mpr ⟨⟨actTil (⊥ : Subgroup G) A hA ⟨(gW : G), hgA⟩, hgstab⟩,
      ?_, rfl⟩
    exact (mem_barSub (⊥ : Subgroup G) A hA H _).2
      ⟨⟨(gW : G), hgA⟩, hgH, rfl⟩
  · intro hφ
    obtain ⟨ψ, hψ, hψφ⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨gA, hgAbar, hgAres⟩ := mem_autSub.mp hψ
    obtain ⟨g, hgH, hgg⟩ := (mem_barSub (⊥ : Subgroup G) A hA H _).1 hgAbar
    have hgW : (g : G) ∈ stabTil (⊥ : Subgroup G) W := by
      simpa using (mem_stabTil_bot_of_le_normalizer hHW hgH)
    have hgA' : (g : G) ∈ stabTil (⊥ : Subgroup G) A := g.2
    have hgstab : actTil (⊥ : Subgroup G) A hA ⟨(g : G), hgA'⟩ ∈
        stabSub (imgTil (⊥ : Subgroup G) A hA W) := by
      rw [hgg]
      exact gA.2
    have hnat := congrHom_restrictEquiv_actTil hA hW hWA hgA' hgW hgstab
    have hgAeq : gA = ⟨actTil (⊥ : Subgroup G) A hA ⟨(g : G), hgA'⟩, hgstab⟩ :=
      Subtype.ext hgg.symm
    refine (mem_barSub (⊥ : Subgroup G) W hW H φ).2 ⟨⟨(g : G), hgW⟩, hgH, ?_⟩
    rw [← hnat, ← hgAeq, hgAres, hψφ]

theorem barSub_sup {A H₁ H₂ : Subgroup G} (hA : IsElemAbelian 2 A)
    (hH₁ : H₁ ≤ stabTil (⊥ : Subgroup G) A) (hH₂ : H₂ ≤ stabTil (⊥ : Subgroup G) A) :
    barSub (⊥ : Subgroup G) A hA (H₁ ⊔ H₂) =
      barSub (⊥ : Subgroup G) A hA H₁ ⊔ barSub (⊥ : Subgroup G) A hA H₂ := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hH₁ hH₂, Subgroup.map_sup]

theorem Mbar_sup_eq_autSub_map {A W H₁ H₂ : Subgroup G} (hA : IsElemAbelian 2 A)
    (hW : IsElemAbelian 2 W) (hWA : W ≤ A)
    (hH₁A : H₁ ≤ Subgroup.normalizer (A : Set G))
    (hH₂A : H₂ ≤ Subgroup.normalizer (A : Set G))
    (hH₁W : H₁ ≤ Subgroup.normalizer (W : Set G))
    (hH₂W : H₂ ≤ Subgroup.normalizer (W : Set G)) :
    ∃ e : ↥(imgTil (⊥ : Subgroup G) A hA W) ≃* Vtil (⊥ : Subgroup G) W hW,
      Mbar (H₁ ⊔ H₂) (⊥ : Subgroup G) W hW =
        (autSub (barSub (⊥ : Subgroup G) A hA H₁ ⊔ barSub (⊥ : Subgroup G) A hA H₂)
          (imgTil (⊥ : Subgroup G) A hA W)).map (CFSG.Quasithin.H.congrHom e) := by
  obtain ⟨e, he⟩ := Mbar_eq_autSub_map hA hW hWA (sup_le hH₁A hH₂A) (sup_le hH₁W hH₂W)
  refine ⟨e, ?_⟩
  rw [he, barSub_sup hA
    (le_inf hH₁A (by rw [Subgroup.normalizer_eq_top]; exact le_top))
    (le_inf hH₂A (by rw [Subgroup.normalizer_eq_top]; exact le_top))]

end CFSG.LocalAnalysis.UniquenessCase.UC22
