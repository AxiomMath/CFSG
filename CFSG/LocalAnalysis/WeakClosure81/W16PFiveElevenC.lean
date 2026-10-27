module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenA
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenB
public import CFSG.LocalAnalysis.WeakClosure81.W19ModE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.commutator_kerMOf_le_centralizer_eSub (h1 : W16One G) (hS : Std15 G)
    (h152 : Thm152 G) (hV₀ : V₀ ≤ pCoreOf 2 H) (hX : Hyp167 M V₀ V U S H g X T)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥) :
    ⁅conjSubgroup V g, kerMOf M X⁆ ≤ centralizer (eSub V₀ X T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : Subgroup G := eSub V₀ X T
  let A : Subgroup G := conjSubgroup V g
  let K : Subgroup G := kerMOf M X
  have hE : IsElemAbelian 2 E := Hyp167.isElemAbelian_eSub h1 hS hV₀ hX
  have hXn : X ≤ normalizer (E : Set G) := le_normalizer_conjClosure _ _
  have hAX : A ≤ X := hX.A_le_T.trans (hX.sylow.le.trans inf_le_left)
  have hKX : K ≤ X := kerMOf_le_group M X
  have hKn : (K.subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hAKnorm : A ≤ normalizer (K : Set G) :=
    hAX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn)
  have hAelem : IsElemAbelian 2 A :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  obtain ⟨Mρ⟩ := exists_modDataE (J := X) (E := E) hE hXn
  have hAe : IsElemAbelian 2 (Mρ.img A) := by
    have hA' : IsElemAbelian 2 (A.subgroupOf X) := hAelem.subgroupOf X
    simpa only [ModDataE.img] using hA'.map Mρ.ρ
  have hA_ne_bot : Mρ.img A ≠ ⊥ := by
    intro hbot
    apply hX.mem.2.2.not_le_ker
    intro a ha
    have haX : a ∈ X := hAX ha
    have hρ1 : Mρ.ρ ⟨a, haX⟩ = 1 := by
      have hmem : Mρ.ρ ⟨a, haX⟩ ∈ (⊥ : Subgroup (LGL 2 Mρ.W)) := by
        rw [← hbot]
        exact Mρ.mem_img.2 ⟨⟨a, haX⟩, ha, rfl⟩
      simpa using hmem
    exact Hyp167.inf_centralizer_eSub_le_kerMOf hX
      (Subgroup.mem_inf.2 ⟨haX, (Mρ.ρ_eq_one_iff ⟨a, haX⟩).1 hρ1⟩)
  have hAY : Mρ.img A ≤ Subgroup.normalizer
      ((Mρ.img K : Subgroup (LGL 2 Mρ.W)) : Set (LGL 2 Mρ.W)) :=
    Mρ.img_le_normalizer hAX hKX hAKnorm
  have hYodd : Odd (Nat.card (Mρ.img K)) := by
    have hsub : (X ⊓ centralizer (E : Set G)).subgroupOf K =
        (centralizer (E : Set G)).subgroupOf K := by
      ext k
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hKX k.2, h⟩⟩
    have hCX : (X ⊓ centralizer (E : Set G)).relIndex K =
        (centralizer (E : Set G)).relIndex K := by
      rw [Subgroup.relIndex, Subgroup.relIndex, hsub]
    rw [Mρ.card_img hKX, ← hCX]
    exact Hyp167.odd_relIndex_inf_centralizer_eSub hX
  have hfix : ∀ D : Subgroup (LGL 2 Mρ.W), D ≤ Mρ.img A →
      D.relIndex (Mρ.img A) < 2 ^ 2 → fixSub D = fixSub (Mρ.img A) := by
    intro D hD hrel
    let A' : Subgroup ↥X := A.subgroupOf X
    let f : ↥A' →* LGL 2 Mρ.W := Mρ.ρ.comp A'.subtype
    let D₀' : Subgroup ↥X := (D.comap f).map A'.subtype
    let D₀ : Subgroup G := D₀'.map X.subtype
    have hA'map : A'.map X.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAX
    have hfr : f.range = Mρ.img A := by
      rw [show f = Mρ.ρ.comp A'.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype]
      rfl
    have hDle : D ≤ f.range := by rw [hfr]; exact hD
    have hD₀'a : D₀' ≤ A' := Subgroup.map_subtype_le _
    have hD₀A : D₀ ≤ A := by
      show D₀'.map X.subtype ≤ A
      rw [← hA'map]
      exact Subgroup.map_mono hD₀'a
    have hD₀X : D₀ ≤ X := hD₀A.trans hAX
    have hD₀rel : D₀.relIndex A = D.relIndex (Mρ.img A) := by
      have h1 : D₀.relIndex A = D₀'.relIndex A' := by
        rw [show D₀ = D₀'.map X.subtype from rfl,
          show A = A'.map X.subtype from hA'map.symm]
        exact Subgroup.relIndex_map_map_of_injective D₀' A' X.subtype_injective
      have h2 : D₀'.relIndex A' = (D.comap f).relIndex ⊤ := by
        have htop : (⊤ : Subgroup ↥A').map A'.subtype = A' :=
          (MonoidHom.range_eq_map A'.subtype).symm.trans (Subgroup.range_subtype A')
        have h := Subgroup.relIndex_map_map_of_injective (D.comap f)
          (⊤ : Subgroup ↥A') A'.subtype_injective
        rw [htop] at h
        exact h
      have h3 : (D.comap f).relIndex ⊤ = D.relIndex (Mρ.img A) := by
        rw [Subgroup.relIndex_comap, ← MonoidHom.range_eq_map, hfr]
      exact h1.trans (h2.trans h3)
    have hrelD₀ : D₀.relIndex A < 2 ^ 2 := by rw [hD₀rel]; exact hrel
    have hmq : E3.mQuot A D₀ ≤ 1 := by
      have hA2 : IsPGroup 2 A := E3.isPGroup_conjSubgroup hX.cex.hyp.isPGroup g
      have hpow : D₀.relIndex A = 2 ^ E3.mQuot A D₀ := E3.relIndex_eq_two_pow hA2 D₀
      rw [hpow] at hrelD₀
      have h2 : E3.mQuot A D₀ < 2 :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by simpa using hrelD₀)
      omega
    have hmSub : 1 ≤ mSub V₀ := by
      have hP : IsPGroup 2 V₀ := hX.cex.hyp.elemAbelian₀.isPGroup
      haveI : Nontrivial ↥V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).2 hX.cex.hyp.ne_bot
      have h2 : 1 < Nat.card ↥V₀ := Finite.one_lt_card_iff_nontrivial.2 inferInstance
      rw [card_eq_two_pow_mSub hP] at h2
      by_contra hlt
      have h0 : mSub V₀ = 0 := by omega
      rw [h0, pow_zero] at h2
      exact absurd h2 (by norm_num)
    have hmlt : 1 < Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := by
      refine lt_min ?_ hX.cex.mbar
      have hn := hX.cex.one_le_n h152
      omega
    have hm : E3.mQuot A D₀ < Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := lt_of_le_of_lt hmq hmlt
    have hinf := Hyp167.inf_centralizer_le_of_inf_eq_bot h1 hS hV₀ hX hBE hD₀A hm
    have himg : Mρ.img D₀ = D := by
      have h1 : Mρ.img D₀ = D₀'.map Mρ.ρ := by
        show (D₀.subgroupOf X).map Mρ.ρ = D₀'.map Mρ.ρ
        have hsub : D₀.subgroupOf X = D₀' := by
          show (D₀'.map X.subtype).comap X.subtype = D₀'
          exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective D₀'
        rw [hsub]
      have h2 : D₀'.map Mρ.ρ = D := by
        rw [show D₀' = (D.comap f).map A'.subtype from rfl, Subgroup.map_map]
        exact Subgroup.map_comap_eq_self hDle
      rw [h1, h2]
    have hle : fixSub D ≤ fixSub (Mρ.img A) := by
      intro w hw
      obtain ⟨e, he, rfl⟩ := Mρ.ι_surj w
      have hcen : e ∈ centralizer (D₀ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        have hdX : d ∈ X := hD₀X hd
        have hρd : Mρ.ρ ⟨d, hdX⟩ ∈ D := by
          rw [← himg]
          exact Mρ.mem_img.2 ⟨⟨d, hdX⟩, hd, rfl⟩
        have hfixd : Mρ.ρ ⟨d, hdX⟩ (Mρ.ι e) = Mρ.ι e := hw _ hρd
        have hde : d * e * d⁻¹ = e := by
          apply Mρ.ι_injOn
          · exact (Subgroup.mem_normalizer_iff.1 (hXn hdX) e).1 he
          · exact he
          · rw [← Mρ.ρ_ι ⟨d, hdX⟩ e he]
            exact hfixd
        calc d * e = (d * e * d⁻¹) * d := by group
          _ = e * d := by rw [hde]
      have heA : e ∈ centralizer (A : Set G) :=
        hinf (Subgroup.mem_inf.2 ⟨he, hcen⟩)
      intro r hr
      obtain ⟨j, hjA, rfl⟩ := Mρ.mem_img.1 hr
      have hje : (j : G) * e = e * (j : G) :=
        Subgroup.mem_centralizer_iff.1 heA (j : G) hjA
      have hconj : (j : G) * e * (j : G)⁻¹ = e := by
        calc (j : G) * e * (j : G)⁻¹ = e * (j : G) * (j : G)⁻¹ := by rw [hje]
          _ = e := by group
      rw [Mρ.ρ_ι ⟨j, j.2⟩ e he, hconj]
    exact le_antisymm hle (fixSub_anti D (Mρ.img A) hD)
  have hcomm_img : ⁅Mρ.img A, Mρ.img K⁆ = ⊥ :=
    commutator_eq_bot_of_odd_of_fixSub_eq hA_ne_bot hAe hAY hYodd hfix
  let A' : Subgroup ↥X := A.subgroupOf X
  let K' : Subgroup ↥X := K.subgroupOf X
  have hA'img : A'.map Mρ.ρ = Mρ.img A := rfl
  have hK'img : K'.map Mρ.ρ = Mρ.img K := rfl
  have hKer : ⁅A', K'⁆ ≤ (centralizer (E : Set G)).subgroupOf X := by
    intro y hy
    have hy1 : Mρ.ρ y = 1 := by
      have h1 : Mρ.ρ y ∈ (⁅A', K'⁆).map Mρ.ρ := ⟨y, hy, rfl⟩
      rw [Subgroup.map_commutator, hA'img, hK'img, hcomm_img, Subgroup.mem_bot] at h1
      exact h1
    exact (Mρ.ρ_eq_one_iff y).1 hy1
  have hA'map : A'.map X.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAX
  have hK'map : K'.map X.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKX
  calc ⁅A, K⁆ = ⁅A'.map X.subtype, K'.map X.subtype⁆ := by rw [hA'map, hK'map]
    _ = (⁅A', K'⁆).map X.subtype := (Subgroup.map_commutator A' K' X.subtype).symm
    _ ≤ ((centralizer (E : Set G)).subgroupOf X).map X.subtype := Subgroup.map_mono hKer
    _ = centralizer (E : Set G) ⊓ X := Subgroup.subgroupOf_map_subtype _ _
    _ ≤ centralizer (E : Set G) := inf_le_left

end CFSG.LocalAnalysis.WeakClosure81

end
