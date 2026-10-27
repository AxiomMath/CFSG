module

public import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup
public import CFSG.LocalAnalysis.StandardType.GGF4CrossPair
import CFSG.LocalAnalysis.StandardType.GGF4CommPair
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.StandardType.F4Model

@[expose] def frameIdxAll (A B : M4) : List ℕ :=
  (List.range 24).filter fun x => (Rm x != A) && (Rm x != B) && commb (Rm x) A && commb (Rm x) B

@[expose] def pairFrameOrd (A B : M4) : Bool :=
  (frameIdxAll A B).all fun x => (frameIdxAll A B).all fun y =>
    x == y || (if commb (Rm x) (Rm y) then T1 x == T1 y else ord4b (Rm x) (Rm y))

theorem pairFrameOrd_long : pairFrameOrd (Sm 1) ((Sm 2).mul ((Sm 1).mul (Sm 2))) = true := by
  decide +kernel

theorem pairFrameOrd_short : pairFrameOrd (Sm 2) ((Sm 1).mul ((Sm 2).mul (Sm 1))) = true := by
  decide +kernel

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

private theorem commb_of_commute'' {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : Commute u v) : commb x y = true := by
  rw [commb_iff x y]
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_mul, ← hu, ← hv, ← map_mul, ← map_mul, h.eq]

private theorem commute_of_commb'' {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : commb x y = true) : Commute u v := by
  rw [commute_iff_eq]
  apply R.inj
  rw [map_mul, map_mul, hu, hv, ← M4.toMat_mul, ← M4.toMat_mul, (commb_iff x y).1 h]

private theorem bne_of_ne'' {u v : W} {x y : M4} (hu : R.ρ u = x.toMat) (hv : R.ρ v = y.toMat)
    (h : u ≠ v) : (x != y) = true := by
  rw [bne_iff_ne]
  intro hxy
  apply h
  apply R.inj
  rw [hu, hv, hxy]

private theorem pairFrameOrd_std {A B : M4} (hok : pairFrameOrd A B = true) {a b c d : W}
    (haρ : R.ρ a = A.toMat) (hbρ : R.ρ b = B.toMat) (hc : R.IsRefl c) (hd : R.IsRefl d)
    (hca : Commute c a) (hcb : Commute c b) (hda : Commute d a) (hdb : Commute d b)
    (hcna : c ≠ a) (hcnb : c ≠ b) (hdna : d ≠ a) (hdnb : d ≠ b) (hcd : c ≠ d) :
    (Commute c d → R.cls c = R.cls d) ∧ (¬ Commute c d → orderOf (c * d) = 4) := by
  obtain ⟨xc, hxc, hxcρ⟩ := R.refl_rep hc
  obtain ⟨xd, hxd, hxdρ⟩ := R.refl_rep hd
  have hmem : ∀ {u : W} {xu : ℕ}, xu < 24 → R.ρ u = (Rm xu).toMat → Commute u a →
      Commute u b → u ≠ a → u ≠ b → xu ∈ frameIdxAll A B := by
    intro u xu hxu hxuρ hua hub huna hunb
    unfold frameIdxAll
    rw [List.mem_filter, List.mem_range]
    refine ⟨hxu, ?_⟩
    have h1 := R.bne_of_ne'' hxuρ haρ huna
    have h2 := R.bne_of_ne'' hxuρ hbρ hunb
    have h3 := R.commb_of_commute'' hxuρ haρ hua
    have h4 := R.commb_of_commute'' hxuρ hbρ hub
    simp only [h1, h2, h3, h4, Bool.and_self]
  have hmc := hmem hxc hxcρ hca hcb hcna hcnb
  have hmd := hmem hxd hxdρ hda hdb hdna hdnb
  have h := List.all_eq_true.1 (List.all_eq_true.1 hok xc hmc) xd hmd
  have hne : (xc == xd) = false := by
    rw [beq_eq_false_iff_ne]
    rintro rfl
    exact hcd (R.inj (hxcρ.trans hxdρ.symm))
  rw [hne, Bool.false_or] at h
  constructor
  · intro hcomm
    rw [if_pos (R.commb_of_commute'' hxcρ hxdρ hcomm), beq_iff_eq] at h
    rw [R.cls_eq hxc hxcρ, R.cls_eq hxd hxdρ, h]
  · intro hcomm
    have hb : commb (Rm xc) (Rm xd) = false := by
      by_contra hb
      exact hcomm (R.commute_of_commb'' hxcρ hxdρ (Bool.not_eq_false _ ▸ hb))
    rw [if_neg (by simp [hb])] at h
    exact R.orderOf_eq_four_of_ord4b hxcρ hxdρ h

theorem cls_eq_or_orderOf_eq_four_of_pairFrame {a b c d : W} (ha : R.IsRefl a)
    (hb : R.IsRefl b) (hab : Commute a b) (hne : a ≠ b) (hcls : R.cls a = R.cls b)
    (hc : R.IsRefl c) (hd : R.IsRefl d) (hca : Commute c a) (hcb : Commute c b)
    (hda : Commute d a) (hdb : Commute d b) (hcna : c ≠ a) (hcnb : c ≠ b) (hdna : d ≠ a)
    (hdnb : d ≠ b) (hcd : c ≠ d) :
    (Commute c d → R.cls c = R.cls d) ∧ (¬ Commute c d → orderOf (c * d) = 4) := by
  obtain ⟨g, hg⟩ := R.exists_conj_pair_same ha hb hab hne hcls
  let κ : W ≃* W := MulAut.conj g
  have hκ : ∀ u, κ u = g * u * g⁻¹ := fun _ => rfl
  have hrefl : ∀ {u : W}, R.IsRefl u → R.IsRefl (κ u) := fun hu => by
    rw [hκ]
    exact hu.conj g
  have hcomm : ∀ {u v : W}, Commute u v → Commute (κ u) (κ v) := fun h => h.map κ
  have hne' : ∀ {u v : W}, u ≠ v → κ u ≠ κ v := fun h e => h (κ.injective e)
  have hclsκ : ∀ {u : W}, R.IsRefl u → R.cls (κ u) = R.cls u := fun hu => by
    rw [hκ]
    exact R.cls_conj hu g
  have hback : (Commute (κ c) (κ d) → R.cls (κ c) = R.cls (κ d)) ∧
      (¬ Commute (κ c) (κ d) → orderOf (κ c * κ d) = 4) →
      (Commute c d → R.cls c = R.cls d) ∧ (¬ Commute c d → orderOf (c * d) = 4) := by
    rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hclsκ hc, ← hclsκ hd]
      exact h1 (hcomm h)
    · have h' : ¬ Commute (κ c) (κ d) := fun h' => h (by
        simpa only [MulEquiv.symm_apply_apply] using h'.map κ.symm)
      rw [← map_mul, MulEquiv.orderOf_eq] at h2
      exact h2 h'
  apply hback
  rcases hg with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
  · have haρ : R.ρ (κ a) = (Sm 1).toMat := by rw [hκ, hga, R.hs]
    have hbρ : R.ρ (κ b) = ((Sm 2).mul ((Sm 1).mul (Sm 2))).toMat := by
      rw [hκ, hgb]
      exact R.rho_mul3 (R.hs 2) (R.hs 1) (R.hs 2)
    exact R.pairFrameOrd_std pairFrameOrd_long haρ hbρ (hrefl hc) (hrefl hd) (hcomm hca)
      (hcomm hcb) (hcomm hda) (hcomm hdb) (hne' hcna) (hne' hcnb) (hne' hdna) (hne' hdnb)
      (hne' hcd)
  · have haρ : R.ρ (κ a) = (Sm 2).toMat := by rw [hκ, hga, R.hs]
    have hbρ : R.ρ (κ b) = ((Sm 1).mul ((Sm 2).mul (Sm 1))).toMat := by
      rw [hκ, hgb]
      exact R.rho_mul3 (R.hs 1) (R.hs 2) (R.hs 1)
    exact R.pairFrameOrd_std pairFrameOrd_short haρ hbρ (hrefl hc) (hrefl hd) (hcomm hca)
      (hcomm hcb) (hcomm hda) (hcomm hdb) (hne' hcna) (hne' hcnb) (hne' hdna) (hne' hdnb)
      (hne' hcd)

end F4Rep

end CFSG.StandardType.F4Model
