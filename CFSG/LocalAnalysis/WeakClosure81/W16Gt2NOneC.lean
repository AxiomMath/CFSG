module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2WeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneImg
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ModDataE.isSylowIn_img_of_isSylowIn {J E : Subgroup G} (M : ModDataE J E)
    {T : Subgroup G} (hT : IsSylowIn 2 T J) : IsSylowIn 2 (M.img T) (M.img J) := by
  have hrelidx : (M.img T).relIndex (M.img J) = ((T.subgroupOf J) ⊔ M.ρ.ker).index := by
    unfold ModDataE.img
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_map_map]
    simp
  have hdvd : ((T.subgroupOf J) ⊔ M.ρ.ker).index ∣ T.relIndex J :=
    Subgroup.index_dvd_of_le (H := T.subgroupOf J)
      (K := (T.subgroupOf J) ⊔ M.ρ.ker) le_sup_left
  refine ⟨M.img_mono hT.le, M.isPGroup_img hT.isPGroup, ?_⟩
  rw [hrelidx]
  exact fun h => hT.not_dvd_relIndex (h.trans hdvd)

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem isConjClosure_img (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hn : E3.mQuot V (U ⊔ V₀) = 1) {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) :
    NOne.IsConjClosure (Mo.img H) (Mo.img (conjClosure V H)) t := by
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have hcard : Nat.card ↥(Mo.img V) = 2 := card_img_eq_two h1 h5 h15 hS c Mo hn
  have hzV : Mo.img V = Subgroup.zpowers t := img_eq_zpowers h1 h5 h15 hS c Mo hn ht ht1
  refine ⟨Mo.img_mono hKH, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, -, rfl⟩ := Mo.mem_img.1 hx
    have hsub : conjSubgroup V (h : G) ≤ conjClosure V H :=
      conjSubgroup_le_conjClosure_of_mem h.2 le_rfl
    refine Mo.img_mono hsub ?_
    have hconj : Mo.img (conjSubgroup V (h : G)) = cj (Mo.ρ (h⁻¹ : ↥H)) (Mo.img V) := by
      simpa using (Mo.img_conj (A := V) hVH (h⁻¹ : ↥H)).symm
    rw [hconj]
    refine mem_cj.2 ?_
    have hinv : Mo.ρ (h⁻¹ : ↥H) = (Mo.ρ h)⁻¹ := map_inv Mo.ρ h
    rw [hinv]
    convert ht using 1
    group
  · intro x hx k hk
    obtain ⟨h, -, rfl⟩ := Mo.mem_img.1 hx
    obtain ⟨k', hk', rfl⟩ := Mo.mem_img.1 hk
    refine Mo.mem_img.2 ⟨h * k' * h⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H h.2) (k' : G)).1 hk'
    · rw [map_mul, map_mul, map_inv]
  · intro J hJ
    unfold ModDataE.img
    rw [Subgroup.map_le_iff_le_comap]
    have hL : conjClosure V H ≤ (J.comap Mo.ρ).map H.subtype := by
      refine conjClosure_le ?_
      intro h hh z hz
      refine Subgroup.mem_map.2 ⟨(⟨h, hh⟩ : ↥H) * ⟨z, hVH hz⟩ * (⟨h, hh⟩ : ↥H)⁻¹, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hzimg : Mo.ρ (⟨z, hVH hz⟩ : ↥H) ∈ Mo.img V :=
        Mo.mem_img.2 ⟨⟨z, hVH hz⟩, hz, rfl⟩
      by_cases hz1 : Mo.ρ (⟨z, hVH hz⟩ : ↥H) = 1
      · rw [map_mul, map_mul, map_inv, hz1, mul_one, mul_inv_cancel]
        exact J.one_mem
      · have hzt : Mo.ρ (⟨z, hVH hz⟩ : ↥H) = t :=
          CFSG.ShultStronglyClosedTI.eq_of_ne_one_of_card_two (Mo.img V) hcard ht ht1 hzimg hz1
        rw [map_mul, map_mul, map_inv, hzt]
        have hx : (Mo.ρ (⟨h, hh⟩ : ↥H))⁻¹ ∈ Mo.img H :=
          (Mo.img H).inv_mem (Mo.mem_img.2 ⟨⟨h, hh⟩, hh, rfl⟩)
        simpa using hJ (Mo.ρ (⟨h, hh⟩ : ↥H))⁻¹ hx
    have hLJ : ((J.comap Mo.ρ).map H.subtype).subgroupOf H ≤ J.comap Mo.ρ := by
      intro j hj
      rw [Subgroup.mem_subgroupOf] at hj
      rw [Subgroup.mem_comap]
      obtain ⟨j', hj'J, hj'eq⟩ := Subgroup.mem_map.1 hj
      have : j' = j := Subtype.ext hj'eq
      rwa [this] at hj'J
    exact (Subgroup.subgroupOf_mono H hL).trans hLJ

theorem exists_mem_img_conjClosure_conj_ne (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) :
    ∃ k ∈ Mo.img (conjClosure V H), k⁻¹ * t * k ≠ t ∧
      Mo.img (conjSubgroup V g) = Subgroup.zpowers (k⁻¹ * t * k) := by
  obtain ⟨κ, hκK, hκV, -⟩ := exists_mem_conjClosure_conjSubgroup_eq h15 hS c c.g_mem.1
  have hκH : κ ∈ H := conjClosure_le_H c hκK
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hzV : Mo.img V = Subgroup.zpowers t := img_eq_zpowers h1 h5 h15 hS c Mo hn ht ht1
  have hinv : Mo.ρ ((⟨κ, hκH⟩ : ↥H)⁻¹) = (Mo.ρ ⟨κ, hκH⟩)⁻¹ := map_inv Mo.ρ ⟨κ, hκH⟩
  have hcj : cj (Mo.ρ ((⟨κ, hκH⟩ : ↥H)⁻¹)) (Subgroup.zpowers t) =
      Subgroup.zpowers ((Mo.ρ ⟨κ, hκH⟩)⁻¹ * t * Mo.ρ ⟨κ, hκH⟩) := by
    rw [cj, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hinv, inv_inv]
  have himgκ : Mo.img (conjSubgroup V κ) = cj (Mo.ρ ((⟨κ, hκH⟩ : ↥H)⁻¹)) (Mo.img V) := by
    simpa using (Mo.img_conj (A := V) hVH ((⟨κ, hκH⟩ : ↥H)⁻¹)).symm
  have hconj : Mo.img (conjSubgroup V g) = Mo.img (conjSubgroup V κ) := congrArg Mo.img hκV
  refine ⟨Mo.ρ ⟨κ, hκH⟩, Mo.mem_img.2 ⟨⟨κ, hκH⟩, hκK, rfl⟩, ?_, ?_⟩
  · intro hkt
    apply c.g_not
    have hEq : Mo.img (conjSubgroup V g) = Mo.img V := by
      rw [hconj, himgκ, hzV, hcj, hkt]
    have hmem : g * (1 : G)⁻¹ ∈ M :=
      (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo c.g_mem.1 H.one_mem).1 (by
        rw [conjSubgroup_one]
        exact hEq)
    simpa using hmem
  · rw [hconj, himgκ, hzV, hcj]

section Certified


theorem inv_conj_mem_img_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hμ : 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian) {P : Subgroup G} (hP : IsSylowIn 2 P H)
    (hRP : R ≤ P) {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V) (ht1 : t ≠ 1) {x : LGL 2 Mo.W}
    (hx : x ∈ Mo.img H) (hxP : x⁻¹ * t * x ∈ Mo.img P) : x⁻¹ * t * x = t := by
  obtain ⟨h, -, rfl⟩ := Mo.mem_img.1 hx
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hcard : Nat.card ↥(Mo.img V) = 2 := card_img_eq_two h1 h5 h15 hS c Mo hn
  have hzV : Mo.img V = Subgroup.zpowers t := img_eq_zpowers h1 h5 h15 hS c Mo hn ht ht1
  have hinv : Mo.ρ (h⁻¹ : ↥H) = (Mo.ρ h)⁻¹ := map_inv Mo.ρ h
  have himg : Mo.img (conjSubgroup V (h : G)) =
      Subgroup.zpowers ((Mo.ρ h)⁻¹ * t * Mo.ρ h) := by
    have hconj : Mo.img (conjSubgroup V (h : G)) = cj (Mo.ρ (h⁻¹ : ↥H)) (Mo.img V) := by
      simpa using (Mo.img_conj (A := V) hVH (h⁻¹ : ↥H)).symm
    rw [hconj, hzV, cj, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hinv, inv_inv]
  have hVxH : conjSubgroup V (h : G) ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) * (h : G) := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem h.2) (hVH hz)) h.2
  have hle_img : Mo.img (conjSubgroup V (h : G)) ≤ Mo.img P := by
    rw [himg]
    exact Subgroup.zpowers_le.2 hxP
  have hle : conjSubgroup V (h : G) ≤
      P ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :=
    (Mo.img_le_img_iff hVxH hP.le).1 hle_img
  have hμ' : 2 * E3.mQuot V (U ⊔ V₀) < mBar M V₀ V c.cex.hyp.h6.elemAbelian := by
    rw [hn, mul_one]
    exact hμ
  have hM : (h : G) ∈ M :=
    mem_of_conjSubgroup_le_sup h1 h5 h15 hS c hP hRP hμ' h.2 hle
  have hVeq : conjSubgroup V (h : G) = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (by rw [c.cex.hyp.h6.normalizer_eq]; exact hM)
  have hzpeq : Subgroup.zpowers ((Mo.ρ h)⁻¹ * t * Mo.ρ h) = Mo.img V := by
    rw [← himg, hVeq]
  have hmem : (Mo.ρ h)⁻¹ * t * Mo.ρ h ∈ Mo.img V := by
    rw [← hzpeq]
    exact Subgroup.mem_zpowers _
  have hne : (Mo.ρ h)⁻¹ * t * Mo.ρ h ≠ 1 := by
    intro h1'
    apply ht1
    have h3 : Mo.ρ h * ((Mo.ρ h)⁻¹ * t * Mo.ρ h) * (Mo.ρ h)⁻¹ = t := by group
    rw [h1', mul_one, mul_inv_cancel] at h3
    exact h3.symm
  exact CFSG.ShultStronglyClosedTI.eq_of_ne_one_of_card_two (Mo.img V) hcard ht ht1 hmem hne

theorem exists_odd_normal_img (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hμ : 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian) {t : LGL 2 Mo.W} (ht : t ∈ Mo.img V)
    (ht1 : t ≠ 1) :
    ∃ O : Subgroup (LGL 2 Mo.W), O ≤ Mo.img (conjClosure V H) ∧ Odd (Nat.card O) ∧
      (∀ x ∈ Mo.img H, ∀ o ∈ O, x * o * x⁻¹ ∈ O) ∧
      Mo.img (conjClosure V H) = Subgroup.zpowers t ⊔ O := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hRP⟩ := exists_isSylowIn_ge 2 c.mem.1 c.sylow.isPGroup
  have hPM : P ≤ M := le_M_of_isSylowIn h1 h15 hS c hP hRP
  have hP' : IsSylowIn 2 (Mo.img P) (Mo.img H) := Mo.isSylowIn_img_of_isSylowIn hP
  have hVP : V ≤ P := c.V_le_R.trans hRP
  have htP : t ∈ Mo.img P := Mo.img_mono hVP ht
  have hPinf : P ≤ H ⊓ M := le_inf hP.le hPM
  have hPt : ∀ x ∈ Mo.img P, x * t = t * x := fun x hx =>
    img_commute_of_mem_inf h1 h5 h15 hS c Mo hn (Mo.img_mono hPinf hx) ht
  have ht2 : t * t = 1 := by
    have h := (Mo.isElemAbelian_img c.cex.hyp.h6.elemAbelian).2 t ht
    simpa [pow_two] using h
  have hwc : ∀ x ∈ Mo.img H, x⁻¹ * t * x ∈ Mo.img P → x⁻¹ * t * x = t :=
    fun x hx hxP => inv_conj_mem_img_eq h1 h5 h15 hS c Mo hn hμ hP hRP ht ht1 hx hxP
  have hK : NOne.IsConjClosure (Mo.img H) (Mo.img (conjClosure V H)) t :=
    isConjClosure_img h1 h5 h15 hS c Mo hn ht ht1
  exact NOne.exists_odd_normal_eq_zpowers_sup hK hP' htP ht2 ht1 hPt hwc

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
