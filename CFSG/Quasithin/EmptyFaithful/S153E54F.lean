module

public import CFSG.Quasithin.EmptyFaithful.S153E54E
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.G2Omega4Plus

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

abbrev Zp54 {G : Type} [Group G] (T M V₁ Mc : Subgroup G) : Subgroup G :=
  VZ T M ⊓ UH153 T M V₁ Mc

section Hyp

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem conjClosure_Zp_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    conjClosure (Zp54 T M V₁ Mc) Mc = UH153 T M V₁ Mc := by
  apply le_antisymm
  · exact conjClosure_le fun h hh z hz => U_conj_mem hh hz.2
  · exact conjClosure_mono (le_inf (ZS_le_V cx) (ZS_le_U cx)) le_rfl

theorem T_le_normalizer_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (UH153 T M V₁ Mc : Set G) :=
  (cx.hF.almostSpecialHyp.g22.three.2)

theorem base54 (cx : Ctx15350 T Mc M V₁ V₂ t) :
    AlmostSpecialBase (Zp54 T M V₁ Mc) (quasithinOmegaOneCenter T) (Y153 Mc M) T Mc := by
  have hb := cx.hF.almostSpecialHyp.toBase
  exact
    { elemAbelian := F7.isElemAbelian_mono cx.c.hyp.elemAbelian inf_le_left
      ne_bot := hb.ne_bot
      le_V := le_inf ((Z_le_ZS cx).trans (ZS_le_V cx)) ((Z_le_ZS cx).trans (ZS_le_U cx))
      oTwo_eq := hb.oTwo_eq
      V_le_T := inf_le_right.trans (U_le_T cx)
      T_le_normV₁ := hb.T_le_normV₁
      T_le_normV := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨T_le_N cx hx, T_le_normalizer_U cx hx⟩
      T_le_normL := hb.T_le_normL
      sylow_LT := hb.sylow_LT
      H_le := hb.H_le
      lOne_sup_le := hb.lOne_sup_le
      sylow_H := hb.sylow_H
      charTwo := hb.charTwo }

theorem g22_54 (cx : Ctx15350 T Mc M V₁ V₂ t) :
    G22Conclusion (Zp54 T M V₁ Mc) (quasithinOmegaOneCenter T) T Mc := by
  have hg := cx.hF.almostSpecialHyp.g22
  have hcc := conjClosure_Zp_eq cx
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hcc]
    exact secImg_mono (inf_le_right)
  · rw [hcc]
    exact hg.one.2
  · rw [hcc]
    exact hg.two
  · rw [hcc]
    exact hg.three
  · rw [hcc]
    exact hg.four

theorem mem_pCoreOf_YT_iff (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G}
    (hy : y ∈ Y153 Mc M) : y ∈ pCoreOf 2 (Y153 Mc M ⊔ T) ↔ y ∈ pCoreOf 2 (Y153 Mc M) := by
  constructor
  · intro h
    rw [Hyp153.lemma_15_3_7_pCore h113 cx.c.hyp] at h
    rw [cx.r49.case_one.1]
    exact ⟨hy, h.2⟩
  · intro h
    rw [Hyp153.lemma_15_3_7_pCore h113 cx.c.hyp]
    refine ⟨pCoreOf_Y_le_T cx h, ?_⟩
    rw [cx.r49.case_one.1] at h
    exact h.2

@[expose] def pi2Equiv :
    Multiplicative (Fin 2 → ZMod 3) ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3) where
  toFun f := (Multiplicative.ofAdd (Multiplicative.toAdd f 0),
    Multiplicative.ofAdd (Multiplicative.toAdd f 1))
  invFun p := Multiplicative.ofAdd ![Multiplicative.toAdd p.1, Multiplicative.toAdd p.2]
  left_inv f := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' f g := rfl

theorem exists_starImg_equiv (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Nonempty (↥(starImg (Y153 Mc M) T (Y153 Mc M)) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  obtain ⟨e⟩ := cx.r49.case_one.2
  let Φ : ↥(Y153 Mc M) →* Multiplicative (ZMod 3) × Multiplicative (ZMod 3) :=
    (pi2Equiv : _ ≃* _).toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(Y153 Mc M))))
  have hΦ : Function.Surjective Φ := by
    intro p
    obtain ⟨q, hq⟩ := pi2Equiv.surjective p
    obtain ⟨r, hr⟩ := e.surjective q
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective r
    refine ⟨y, ?_⟩
    show pi2Equiv (e (QuotientGroup.mk y)) = p
    rw [hy, hr, hq]
  obtain ⟨E, -⟩ := secImg_equiv_of_hom (A := Y153 Mc M ⊔ T) (B := pCoreOf 2 (Y153 Mc M ⊔ T))
    (X := Y153 Mc M) le_sup_left Φ hΦ (fun x => by
      rw [mem_pCoreOf_YT_iff h113 cx x.2]
      show pi2Equiv (e (QuotientGroup.mk x)) = 1 ↔ _
      rw [map_eq_one_iff _ pi2Equiv.injective, map_eq_one_iff _ e.injective,
        QuotientGroup.eq_one_iff]
      have h : (pCoreOf 2 (Y153 Mc M)).subgroupOf (Y153 Mc M) = CFSG.Open.pCore 2 ↥(Y153 Mc M) :=
        map_subtype_subgroupOf' _
      rw [← h, Subgroup.mem_subgroupOf])
  exact ⟨E⟩

theorem isPerp_Zp (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    IsPerp153 cx.c (quasithinOmegaOneCenter T) (Zp54 T M V₁ Mc) := by
  obtain ⟨P, hP, -, hVU, -⟩ := c.h53two.perp
  have : Zp54 T M V₁ Mc = P := hVU
  rw [this]
  exact hP

theorem om4Data_aux (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) (S : Setup54 cx) {A VL K : Subgroup G}
    (hA : A = Y153 Mc M ⊔ UH153 T M V₁ Mc) (hVL : VL = VZ T M)
    (hK : K = pCoreOf 2 (Y153 Mc M ⊔ T)) :
    ∃ D : Om4Data A K VL, ∀ v w : ↥VL, (w : G) ∈ quasithinOmegaOneCenter T → (w : G) ≠ 1 →
      ((v : G) ∈ Zp54 T M V₁ Mc ↔
        polarDet (Multiplicative.toAdd (D.ψ v)) (Multiplicative.toAdd (D.ψ w)) = 0) := by
  subst hA hVL hK
  have hperp := isPerp_Zp cx c
  obtain ⟨z, hz, hz1, hzgen⟩ := exists_Z_gen cx
  have hker : S.α.ker = (pCoreOf 2 (Y153 Mc M ⊔ T)).subgroupOf
      (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Hyp153.lemma_15_3_7_pCore h113 cx.c.hyp]
    constructor
    · intro h1
      exact ⟨mem_T_of_alpha_eq_one h113 cx S x.2 h1, (S.ker x).1 h1⟩
    · rintro ⟨-, hC⟩
      exact (S.ker x).2 hC
  refine ⟨⟨YU_le_normalizer cx, S.α, S.ψ, S.surj, hker, fun a v => S.equiv a v⟩, ?_⟩
  · intro v w hw hw1
    have hwz : (w : G) = z := (hzgen _ hw).resolve_left hw1
    have hq1 := (qW_spec cx).1
    refine (hperp (v : G)).trans ?_
    have h1 : (∀ a ∈ quasithinOmegaOneCenter T, Orth153 cx.c a (v : G)) ↔
        Orth153 cx.c (w : G) (v : G) := by
      constructor
      · intro h
        exact h _ hw
      · intro h a ha
        rcases hzgen a ha with rfl | rfl
        · refine ⟨(1 : VZ T M).2, v.2, ?_⟩
          exact quadPolar_one_left hq1 _
        · rw [hwz] at h
          exact h
    have h2 : Orth153 cx.c (w : G) (v : G) ↔ quadPolar (qW cx) w v = 0 := by
      constructor
      · rintro ⟨ha, hb, h⟩
        exact h
      · intro h
        exact ⟨w.2, v.2, h⟩
    rw [and_iff_right v.2, h1, h2, S.polar w v, polarDet_comm]
    exact Iff.rfl

theorem hyp54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    AlmostSpecialOm4Hyp (Zp54 T M V₁ Mc) (quasithinOmegaOneCenter T) (Y153 Mc M) T Mc where
  base := base54 cx
  g22 := g22_54 cx
  card_V₁ := cx.hF.card_V₁
  L_star := exists_starImg_equiv h113 cx
  V_le_VL := by
    rw [conjClosure_Z_Y h113 cx c]
    exact inf_le_left
  module := by
    obtain ⟨S⟩ := nonempty_setup cx c
    exact om4Data_aux h113 cx c S (by rw [conjClosure_Zp_eq cx]) (conjClosure_Z_Y h113 cx c) rfl

end Hyp

end S153E54

end CFSG.Quasithin
