module

public import CFSG.Timmesfeld.Transvection.PresSURankOne
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne
import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) {G : Type*} [Group G] (R : SURelations (m / 2) σ G) (he : Even m)

section Short

variable {i : Fin (m / 2)} (hk : i.val + 1 < m / 2)

@[expose] def SURelations.shortRels : RankOneRels G F where
  x := R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩)
  y := R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i)
  x_add := R.add _ _ (idx_short hk)
  y_add := R.add _ _ (idx_short' hk)
  conj_x _ ht a := R.shortB hσ he hk ht a

omit [Finite F] in
theorem rankOneShortHom_pos {x : SU σ m} (hx : x ∈ rootGroup σ hσ m (Pi.single i 1)) {c : F}
    (hc : suElt σ hσ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) c = x) :
    rankOneShortHom hk ⟨x, Subgroup.mem_sup_left hx⟩ = sl2Upper c := by
  apply Subtype.ext
  rw [coe_rankOneShortHom, toBlock_of_mem_pos hk hx, coe_sl2Upper, ← hc]
  congr
  exact mat_suElt_apply hσ (idx_short hk) c

omit [Finite F] in
theorem rankOneShortHom_neg {y : SU σ m} (hy : y ∈ rootGroup σ hσ m (-Pi.single i 1)) {c : F}
    (hc : suElt σ hσ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) c = y) :
    rankOneShortHom hk ⟨y, Subgroup.mem_sup_right hy⟩ = sl2Lower c := by
  apply Subtype.ext
  rw [coe_rankOneShortHom, toBlock_of_mem_neg hk hy, coe_sl2Lower, ← hc]
  congr
  exact mat_suElt_apply hσ (idx_short' hk) c

include hk in
theorem SURelations.extendsToHom_short :
    ExtendsToHom (rootGroup σ hσ m) {Pi.single i 1, -Pi.single i 1}
      (fun γ x => suPsi hσ R he γ x) := by
  obtain ⟨Θ, hΘx, hΘy⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (R.shortRels hσ he hk)
  have hαe := toStd_single_short (m := m) hk
  have hαe' : toStd m (-Pi.single i 1) = rt (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) := by
    rw [toStd_neg, hαe, rt_inl_inr, rt_inl_inr, neg_sub]
  refine ⟨CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ m) i, Θ.comp (rankOneShortHom hk), ?_⟩
  rintro γ (rfl | rfl) x
  · obtain ⟨c, hc⟩ := (mem_rootGroup_iff_suElt hσ he (idx_short hk) hαe x).1 x.2
    have hv := relValid_short (σ := σ) (idx_short hk) c
    have hx : x = ⟨_, eval_mem_rootGroup hσ hv hαe⟩ := Subtype.ext (by
      dsimp only
      rw [SURelations.eval_short _ (ne_of_idx_ne (idx_short hk)), suRelationsModel_ξ, hc])
    refine ⟨Subgroup.mem_sup_left x.2, ?_⟩
    dsimp only
    rw [MonoidHom.comp_apply, rankOneShortHom_pos hσ hk x.2 hc, hΘx, hx, suPsi_eval hσ R he hv hαe,
      R.eval_short (ne_of_idx_ne (idx_short hk))]
    rfl
  · obtain ⟨c, hc⟩ := (mem_rootGroup_iff_suElt hσ he (idx_short' hk) hαe' x).1 x.2
    have hv := relValid_short (σ := σ) (idx_short' hk) c
    have hx : x = ⟨_, eval_mem_rootGroup hσ hv hαe'⟩ := Subtype.ext (by
      dsimp only
      rw [SURelations.eval_short _ (ne_of_idx_ne (idx_short' hk)), suRelationsModel_ξ, hc])
    refine ⟨Subgroup.mem_sup_right x.2, ?_⟩
    dsimp only
    rw [MonoidHom.comp_apply, rankOneShortHom_neg hσ hk x.2 hc, hΘy, hx,
      suPsi_eval hσ R he hv hαe', R.eval_short (ne_of_idx_ne (idx_short' hk))]
    rfl

end Short

section Long

omit [Finite F] [CharP F 2] in
variable (σ) in
@[expose] def Pres.sigmaFixedField : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F)

omit [Finite F] [CharP F 2] in
theorem Pres.mem_sigmaFixedField {c : F} : c ∈ sigmaFixedField σ ↔ σ c = c := Iff.rfl

variable {i : Fin (m / 2)} (hk : ¬i.val + 1 < m / 2)

include hk he in
theorem toStd_neg_single_last :
    toStd m (-Pi.single i 1) = rt (Sum.inr i) (Sum.inr i) := by
  rw [toStd_neg, toStd_single_last_even hk he, rt_inl_inl, rt_inr_inr]

@[expose] noncomputable def longModelRels :
    RankOneRels (CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ m) i) (sigmaFixedField σ) where
  x c := ⟨suLong σ (Sum.inl i) c,
    Subgroup.mem_sup_left (suLong_mem hσ _ (toStd_single_last_even hk he) c)⟩
  y c := ⟨suLong σ (Sum.inr i) c,
    Subgroup.mem_sup_right (suLong_mem hσ _ (toStd_neg_single_last he hk) c)⟩
  x_add a b := Subtype.ext (suLong_add _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 a.2))
    (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 b.2)))
  y_add a b := Subtype.ext (suLong_add _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 a.2))
    (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 b.2)))
  conj_x t ht a := Subtype.ext (by
    have ht' : (t : F) ≠ 0 := by exact_mod_cast ht
    have h := longWeyl_conj_x hk
      (z := ⟨(t : F), add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 t.2)⟩) ht'
      (a := (a : F)) (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 a.2))
    rw [← longWeyl_eq] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    push_cast
    exact h)

@[expose] def SURelations.longRels (hm : 4 ≤ m) (htr : ∀ c, σ c = c → ∃ s, s + σ s = c) :
    RankOneRels G (sigmaFixedField σ) where
  x c := R.ξL (Sum.inl i) c
  y c := R.ξL (Sum.inr i) c
  x_add a b := R.addL _ _ _ a.2 b.2
  y_add a b := R.addL _ _ _ a.2 b.2
  conj_x t ht a := by
    have ht' : (t : F) ≠ 0 := by exact_mod_cast ht
    have h := R.longB hσ he hk hm htr t.2 ht' a.2
    push_cast
    exact h

include hk in
theorem SURelations.extendsToHom_long (hm : 4 ≤ m) (htr : ∀ c, σ c = c → ∃ s, s + σ s = c) :
    ExtendsToHom (rootGroup σ hσ m) {Pi.single i 1, -Pi.single i 1}
      (fun γ x => suPsi hσ R he γ x) := by
  obtain ⟨Θ, hΘx, hΘy⟩ :=
    CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (R.longRels hσ he hk hm htr)
  obtain ⟨Θ₀, hΘ₀x, hΘ₀y⟩ :=
    CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (longModelRels hσ he hk)
  have hαe := toStd_single_last_even hk he
  have hαe' := toStd_neg_single_last he hk
  have hp : lowIdx (n := m) i ≠ Fin.rev (lowIdx i) := lowIdx_ne_rev i i
  have hblock : ((SU σ 2).subtype.comp (rankOneLastEvenHom σ hσ he hk)).comp Θ₀ =
      SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype) := by
    refine CFSG.SectionRank.EvenCover.sl2_hom_ext (fun c => Units.ext ?_) (fun c => Units.ext ?_)
    · change mat σ 2 (rankOneLastEvenHom σ hσ he hk (Θ₀ (sl2Upper c))) =
        ((SpecialLinearGroup.map (sigmaFixedField σ).subtype (sl2Upper c) :
          SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      rw [mat_rankOneLastEvenHom, hΘ₀x, SpecialLinearGroup.map_apply_coe, coe_sl2Upper]
      change SUExtras.toBlock _ _ (mat σ m (suLong σ (Sum.inl i) c)) = _
      rw [mat_suLong _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 c.2))]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SUExtras.toBlock, hp, Ne.symm hp]
    · change mat σ 2 (rankOneLastEvenHom σ hσ he hk (Θ₀ (sl2Lower c))) =
        ((SpecialLinearGroup.map (sigmaFixedField σ).subtype (sl2Lower c) :
          SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      rw [mat_rankOneLastEvenHom, hΘ₀y, SpecialLinearGroup.map_apply_coe, coe_sl2Lower]
      change SUExtras.toBlock _ _ (mat σ m (suLong σ (Sum.inr i) c)) = _
      rw [mat_suLong _ (add_map_eq_zero_iff.2 (mem_sigmaFixedField.1 c.2))]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SUExtras.toBlock, hp, Ne.symm hp]
  have hinj : Function.Injective Θ₀ := by
    intro g g' h
    have h' := congrArg ((SU σ 2).subtype.comp (rankOneLastEvenHom σ hσ he hk)) h
    have h'' : SpecialLinearGroup.toGL (SpecialLinearGroup.map (sigmaFixedField σ).subtype g) =
        SpecialLinearGroup.toGL (SpecialLinearGroup.map (sigmaFixedField σ).subtype g') := by
      change (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype)) g =
        (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (sigmaFixedField σ).subtype)) g'
      rw [← hblock]
      exact h'
    have h3 := SpecialLinearGroup.toGL_injective h''
    ext a b
    have h4 := congrArg
      (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) a b) h3
    simpa using h4
  have hsurj : Function.Surjective Θ₀ := by
    have hle : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ m) i ≤
        Θ₀.range.map (CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ m) i).subtype := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨c, hc0, rfl⟩ := (mem_rootGroup_iff_suLong hσ he _ hαe x).1 hx
        refine Subgroup.mem_map.2 ⟨Θ₀ (sl2Upper ⟨c, mem_sigmaFixedField.2
          (add_map_eq_zero_iff.1 hc0)⟩), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
        rw [hΘ₀x]
        rfl
      · obtain ⟨c, hc0, rfl⟩ := (mem_rootGroup_iff_suLong hσ he _ hαe' x).1 hx
        refine Subgroup.mem_map.2 ⟨Θ₀ (sl2Lower ⟨c, mem_sigmaFixedField.2
          (add_map_eq_zero_iff.1 hc0)⟩), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
        rw [hΘ₀y]
        rfl
    intro g
    obtain ⟨g₁, hg₁, hg⟩ := Subgroup.mem_map.1 (hle g.2)
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.1 hg₁
    exact ⟨g', Subtype.ext hg⟩
  let e := MulEquiv.ofBijective Θ₀ ⟨hinj, hsurj⟩
  refine ⟨CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ m) i, Θ.comp e.symm.toMonoidHom, ?_⟩
  rintro γ (rfl | rfl) x
  · obtain ⟨c, hc0, hc⟩ := (mem_rootGroup_iff_suLong hσ he _ hαe x).1 x.2
    have hfix := add_map_eq_zero_iff.1 hc0
    have hv := relValid_long (σ := σ) (Sum.inl i) hfix
    have hx : (⟨_, eval_mem_rootGroup hσ hv hαe⟩ : rootGroup σ hσ m _) = x := Subtype.ext (by
      dsimp only
      rw [SURelations.eval_long, suRelationsModel_ξL, hc])
    have he' : e.symm ⟨x, Subgroup.mem_sup_left x.2⟩ =
        sl2Upper ⟨c, mem_sigmaFixedField.2 hfix⟩ :=
      e.symm_apply_eq.2 (Subtype.ext (by
        exact hc.symm.trans
          (congrArg Subtype.val (hΘ₀x ⟨c, mem_sigmaFixedField.2 hfix⟩)).symm))
    refine ⟨Subgroup.mem_sup_left x.2, ?_⟩
    dsimp only
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he', hΘx, ← hx,
      suPsi_eval hσ R he hv hαe, R.eval_long]
    rfl
  · obtain ⟨c, hc0, hc⟩ := (mem_rootGroup_iff_suLong hσ he _ hαe' x).1 x.2
    have hfix := add_map_eq_zero_iff.1 hc0
    have hv := relValid_long (σ := σ) (Sum.inr i) hfix
    have hx : (⟨_, eval_mem_rootGroup hσ hv hαe'⟩ : rootGroup σ hσ m _) = x := Subtype.ext (by
      dsimp only
      rw [SURelations.eval_long, suRelationsModel_ξL, hc])
    have he' : e.symm ⟨x, Subgroup.mem_sup_right x.2⟩ =
        sl2Lower ⟨c, mem_sigmaFixedField.2 hfix⟩ :=
      e.symm_apply_eq.2 (Subtype.ext (by
        exact hc.symm.trans
          (congrArg Subtype.val (hΘ₀y ⟨c, mem_sigmaFixedField.2 hfix⟩)).symm))
    refine ⟨Subgroup.mem_sup_right x.2, ?_⟩
    dsimp only
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he', hΘy, ← hx,
      suPsi_eval hσ R he hv hαe', R.eval_long]
    rfl

end Long

end CFSG.Timmesfeld.Transvection
