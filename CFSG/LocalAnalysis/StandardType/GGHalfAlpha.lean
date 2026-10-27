module

public import CFSG.LocalAnalysis.StandardType.GGHalfConj
public import CFSG.LocalAnalysis.StandardType.GGHalfAlphaPre
public import CFSG.LocalAnalysis.StandardType.GGHalfAlphaMat
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphExcl
public import CFSG.LocalAnalysis.StandardType.GGHalfAux
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

private theorem sigmaPerm_apply_four {m : ℕ} (hm : 3 ≤ m) :
    sigmaPerm m (4 : Fin (m + 1 + 1 + 1)) = 4 := by
  have h0 : (4 : Fin (m + 1 + 1 + 1)) ≠ (0 : Fin (m + 1 + 1 + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.coe_ofNat_eq_mod] at hv
    change 4 % (m + 1 + 1 + 1) = 0 % (m + 1 + 1 + 1) at hv
    rw [Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1), Nat.zero_mod] at hv
    omega
  have h1 : (4 : Fin (m + 1 + 1 + 1)) ≠ (1 : Fin (m + 1 + 1 + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.coe_ofNat_eq_mod] at hv
    change 4 % (m + 1 + 1 + 1) = 1 % (m + 1 + 1 + 1) at hv
    rw [Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1),
      Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)] at hv
    omega
  have h2 : (4 : Fin (m + 1 + 1 + 1)) ≠ (2 : Fin (m + 1 + 1 + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.coe_ofNat_eq_mod] at hv
    change 4 % (m + 1 + 1 + 1) = 2 % (m + 1 + 1 + 1) at hv
    rw [Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1),
      Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)] at hv
    omega
  have h3 : (4 : Fin (m + 1 + 1 + 1)) ≠ (3 : Fin (m + 1 + 1 + 1)) := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.coe_ofNat_eq_mod] at hv
    change 4 % (m + 1 + 1 + 1) = 3 % (m + 1 + 1 + 1) at hv
    rw [Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1),
      Nat.mod_eq_of_lt (by omega : 3 < m + 1 + 1 + 1)] at hv
    omega
  exact sigmaPerm_apply_of_fixed m h0 h1 h2 h3

theorem exists_alpha (hm : 4 ≤ m) :
    ∃ α : MulAut (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2), ∀ s,
      hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ := by
  let ψ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G :=
    (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂
  let ψ' : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G :=
    (MulAut.conj (hElt φ₂)).toMonoidHom.comp φ₁
  have hψ : Function.Injective ψ := by
    intro a b hab
    exact h.coords.inj₂ ((MulEquiv.injective (MulAut.conj (gElt φ₁))) hab)
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    exact h.coords.inj₁ ((MulEquiv.injective (MulAut.conj (hElt φ₂))) hab)
  have hrange : ψ.range = ψ'.range := by
    simp only [ψ, ψ', MonoidHom.range_comp, h.coords.range₂, h.coords.range₁]
    exact h.conj_eq hm
  obtain ⟨α, hα⟩ := exists_mulAut_of_range_eq hψ hψ' hrange
  refine ⟨α, fun s => ?_⟩
  have hs := hα s
  simp only [ψ, ψ'] at hs
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hs

theorem alphaInner_of_six_le (hm : 4 ≤ m) : GGHalfAlphaInner φ₁ φ₂ := by
  obtain ⟨α, hα⟩ := h.exists_alpha hm
  obtain ⟨c, ε, hε, hαc⟩ := aut_sl_gf2 (d := m + 1 + 1 + 1) (by omega) α
  interval_cases ε
  · refine ⟨c, fun s => ?_⟩
    have hα' : α = MulAut.conj c := by rw [hαc, pow_zero, mul_one]
    have hs : α s = c * s * c⁻¹ := by rw [hα', MulAut.conj_apply]
    rw [← hα s, hs]
  · exfalso
    refine not_conj_graph_shift hm c (fun s hs => ?_)
    have h1 := h.alpha_lower s hs
    have h2 := hα (slUpper2Hom m s)
    have heq : α (slUpper2Hom m s) = slLower2Hom m s :=
      h.coords.inj₁ (mul_left_cancel (mul_right_cancel (h2.trans h1)))
    have hα' : α = MulAut.conj c *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (m + 1 + 1 + 1) F2 := by
      rw [hαc, pow_one]
    rw [hα'] at heq
    simpa only [MulAut.mul_apply, MulAut.conj_apply] using heq

theorem alphaInner_props_of_three_le (hm : 3 ≤ m) {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (ha : ∀ s, gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ = hElt φ₂ * φ₁ (a * s * a⁻¹) * (hElt φ₂)⁻¹) :
    (∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
        a * slUpper2Hom m s * a⁻¹ = slLower2Hom m s) ∧
      a * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * a⁻¹ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ∧
      a * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ * a⁻¹ =
        omegaBlock (m + 1 + 1) ⟨2, by omega⟩ := by
  have cancel : ∀ {X Y : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2},
      hElt φ₂ * φ₁ X * (hElt φ₂)⁻¹ = hElt φ₂ * φ₁ Y * (hElt φ₂)⁻¹ → X = Y :=
    fun hh => h.coords.inj₁ (mul_left_cancel (mul_right_cancel hh))
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · apply cancel
    rw [← ha (slUpper2Hom m s), h.alpha_lower s hs]
  · apply cancel
    rw [← ha (omegaBlock (m + 1 + 1) ⟨0, by omega⟩), h.alpha_v]
  · apply cancel
    rw [← ha (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩), h.alpha_w]

theorem conj_map_slOn012_of_three_le (hm : 3 ≤ m) :
    ((slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map φ₂).map
        (MulAut.conj (gElt φ₁)).toMonoidHom =
      (slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1)))).map φ₁ := by
  have hcastU : (fun i : Fin (m + 1) => i.castSucc.castSucc) ''
      ({0, 1, 2} : Set (Fin (m + 1))) = ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) := by
    ext i
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases hj with rfl | rfl | rfl
      · left; apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      · right; left; apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1),
          Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
      · right; right; apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 2 < m + 1),
          Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)]
    · rintro (rfl | rfl | rfl)
      · refine ⟨0, by left; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      · refine ⟨1, by right; left; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1),
          Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
      · refine ⟨2, by right; right; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 2 < m + 1),
          Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)]
  have hcastL : (fun i : Fin (m + 1) => i.succ.succ) ''
      ({0, 1, 2} : Set (Fin (m + 1))) = ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1))) := by
    ext i
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases hj with rfl | rfl | rfl
      · left; apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 0 < m + 1),
          Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)]
      · right; left; apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1),
          Nat.mod_eq_of_lt (by omega : 3 < m + 1 + 1 + 1)]
      · right; right; apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 2 < m + 1),
          Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1)]
    · rintro (rfl | rfl | rfl)
      · refine ⟨0, by left; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 0 < m + 1),
          Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)]
      · refine ⟨1, by right; left; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1),
          Nat.mod_eq_of_lt (by omega : 3 < m + 1 + 1 + 1)]
      · refine ⟨2, by right; right; rfl, ?_⟩
        apply Fin.ext
        simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod]
        rw [Nat.mod_eq_of_lt (by omega : 2 < m + 1),
          Nat.mod_eq_of_lt (by omega : 4 < m + 1 + 1 + 1)]
  have hSigmaSet : sigmaPerm m '' ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1))) =
      ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) := by
    ext i
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases hj with rfl | rfl | rfl
      · rw [sigmaPerm_apply_two m (by omega)]; left; rfl
      · rw [sigmaPerm_apply_three m (by omega)]; right; left; rfl
      · rw [h.sigmaPerm_apply_four hm]; right; right; rfl
    · rintro (rfl | rfl | rfl)
      · refine ⟨2, by left; rfl, ?_⟩
        rw [sigmaPerm_apply_two m (by omega)]
      · refine ⟨3, by right; left; rfl, ?_⟩
        rw [sigmaPerm_apply_three m (by omega)]
      · refine ⟨4, by right; right; rfl, ?_⟩
        exact h.sigmaPerm_apply_four hm
  have hU : slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1))) =
      (slOn (m + 1) ({0, 1, 2} : Set (Fin (m + 1)))).map (slUpper2Hom m) := by
    rw [← hcastU, ← slUpper2Hom_map_slOn]
  have hL : slOn (m + 1 + 1 + 1) ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1))) =
      (slOn (m + 1) ({0, 1, 2} : Set (Fin (m + 1)))).map (slLower2Hom m) := by
    rw [← hcastL, ← slLower2Hom_map_slOn]
  have hUpper : (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map φ₂ =
      (slOn (m + 1 + 1 + 1) ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1)))).map φ₁ := by
    rw [hU, hL]
    simp only [Subgroup.map_map, h.coords.agree]
  have hcomp : (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₁ =
      φ₁.comp (MulAut.conj (slPerm gf2_two (sigmaPerm m))).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, gElt,
      map_mul, map_inv]
  have hconj : ((slOn (m + 1 + 1 + 1) ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1)))).map φ₁).map
        (MulAut.conj (gElt φ₁)).toMonoidHom =
      ((slOn (m + 1 + 1 + 1) ({2, 3, 4} : Set (Fin (m + 1 + 1 + 1)))).map
        (MulAut.conj (slPerm gf2_two (sigmaPerm m))).toMonoidHom).map φ₁ := by
    simp only [Subgroup.map_map, hcomp]
  rw [hUpper, hconj, slOn_map_conj_slPerm, hSigmaSet]

theorem normSL014_of_alphaInner_of_three_le (hm : 3 ≤ m) (hα : GGHalfAlphaInner φ₁ φ₂) :
    GGHalfNormSL014 φ₁ φ₂ := by
  obtain ⟨a, ha⟩ := hα
  obtain ⟨h1, h2, h3⟩ := h.alphaInner_props_of_three_le hm ha
  have hmap : (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
        (MulAut.conj a).toMonoidHom =
      slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) :=
    map_conj_slOn012 (m := m) (by omega) h1 h2 h3
  have hcomp : (MulAut.conj (hElt φ₂)).toMonoidHom.comp
        (φ₁.comp (MulAut.conj a).toMonoidHom) =
      (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂ := by
    ext x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using (ha x).symm
  show ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁).map
        (MulAut.conj (hElt φ₂)).toMonoidHom =
      (slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁
  calc
    ((slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1)))).map φ₁).map
        (MulAut.conj (hElt φ₂)).toMonoidHom
        = (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
            ((MulAut.conj (hElt φ₂)).toMonoidHom.comp
              (φ₁.comp (MulAut.conj a).toMonoidHom)) := by
          rw [← hmap]
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map
            ((MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂) := by rw [hcomp]
    _ = ((slOn (m + 1 + 1 + 1) ({0, 1, 2} : Set (Fin (m + 1 + 1 + 1)))).map φ₂).map
            (MulAut.conj (gElt φ₁)).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = (slOn (m + 1 + 1 + 1) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1)))).map φ₁ :=
          h.conj_map_slOn012_of_three_le hm

theorem normSL014_of_alphaInner (hm : 4 ≤ m) (hα : GGHalfAlphaInner φ₁ φ₂) :
    GGHalfNormSL014 φ₁ φ₂ :=
  h.normSL014_of_alphaInner_of_three_le (by omega) hα

end GGHalfCtx

end CFSG.StandardType

end
