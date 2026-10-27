module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenF
public import CFSG.LocalAnalysis.WeakClosure81.TwelveNine
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenG
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.min_le_mQuot_A (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G)
    (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥) :
    Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀) (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) ≤
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) := by
  by_contra hcon
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) <
      Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := not_le.1 hcon
  have hD : conjSubgroup V g ⊓ kerMOf M X ≤ conjSubgroup V g := inf_le_left
  have hle := Hyp167.inf_centralizer_le_of_inf_eq_bot h1 hS hV₀ hX hBE hD hm
  have hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) :=
    Hyp167.kerMOf_le_centralizer_of_inf_eq_bot hI hS h152 h1 hV₀ hX hBE
  have hE : eSub V₀ X T ≤ centralizer (conjSubgroup V g ⊓ kerMOf M X : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact ((Subgroup.mem_centralizer_iff.1 (hK hd.2)) e he).symm
  have hE' : eSub V₀ X T ≤ centralizer (conjSubgroup V g : Set G) :=
    (le_inf le_rfl hE).trans hle
  have hAC : conjSubgroup V g ≤ centralizer (eSub V₀ X T : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (hE' he)) a ha).symm
  have hAX : conjSubgroup V g ≤ X := hX.A_le_T.trans (hX.sylow.le.trans inf_le_left)
  exact hX.mem.2.2.not_le_ker
    ((le_inf hAX hAC).trans (Hyp167.inf_centralizer_eSub_le_kerMOf hX))

section Certified


theorem Hyp167.closure_le_centralizer_of_ne_bot (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hc : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) ≠ ⊥) :
    conjClosure V₀ X ≤ centralizer (conjSubgroup V₀ g : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  have hcB : (c : G) ∈ conjSubgroup V₀ g := c.2.1
  have hcC : (c : G) ∈ centralizer (eSub V₀ X T : Set G) := c.2.2
  have hc1 : (c : G) ≠ 1 := fun hh => hc1' (Subtype.ext hh)
  have hTV₀ : T ≤ normalizer (V₀ : Set G) := by
    rw [hX.cex.hyp.normalizer₀]
    exact hX.sylow.le.trans inf_le_right
  have hCV : V₀ ⊓ centralizer (T : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      hX.sylow.isPGroup hX.cex.hyp.elemAbelian₀.isPGroup hX.cex.hyp.ne_bot hTV₀
  refine conjClosure_le fun x hx z hz => ?_
  have hmem : x * z * x⁻¹ ∈ conjSubgroup V₀ x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have hce : x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z := by group
    rw [hce]
    exact hz
  have hN : conjSubgroup V₀ g ⊓ normalizer (conjSubgroup V₀ x⁻¹ : Set G) ≠ ⊥ := by
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCV
    have hwV₀ : (w : G) ∈ V₀ := w.2.1
    have hzmem : x * (w : G) * x⁻¹ ∈ conjSubgroup (V₀ ⊓ centralizer (T : Set G)) x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hce : x⁻¹ * (x * (w : G) * x⁻¹) * (x⁻¹)⁻¹ = (w : G) := by group
      rw [hce]
      exact w.2
    have hzE : x * (w : G) * x⁻¹ ∈ eSub V₀ X T := by
      rw [eSub]
      exact mem_conjClosure hx w.2
    have hzV : x * (w : G) * x⁻¹ ∈ conjSubgroup V₀ x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hce : x⁻¹ * (x * (w : G) * x⁻¹) * (x⁻¹)⁻¹ = (w : G) := by group
      rw [hce]
      exact hwV₀
    have hz1 : x * (w : G) * x⁻¹ ≠ 1 := by
      intro hzero
      apply hw1
      apply Subtype.ext
      have := congrArg (fun t => x⁻¹ * t * x) hzero
      simpa [mul_assoc] using this
    have hcz : x * (w : G) * x⁻¹ * (c : G) = (c : G) * (x * (w : G) * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hcC _ hzE
    have hcN : (c : G) ∈ normalizer (conjSubgroup V₀ x⁻¹ : Set G) :=
      centralizer_le_normalizer_conj hX.cex.hyp.isTI x⁻¹ hzV hz1
        (Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcz)
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(c : G), hcB, hcN⟩, fun hh => hc1 (congrArg Subtype.val hh)⟩
  have hBS : conjSubgroup V₀ g ≤ S :=
    (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le).trans hX.le_S
  have hxH : x ∈ H := hX.mem.1 hx
  have hpCH : conjSubgroup (pCoreOf 2 H) x⁻¹ = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hxH))
  have hVx : conjSubgroup V x⁻¹ ≤ pCoreOf 2 H := by
    calc conjSubgroup V x⁻¹ ≤ conjSubgroup (pCoreOf 2 H) x⁻¹ :=
          E3.conjSubgroup_mono_left x⁻¹ hVO
      _ = pCoreOf 2 H := hpCH
  have hV₀x : conjSubgroup V₀ x⁻¹ ≤ pCoreOf 2 H :=
    (E3.conjSubgroup_mono_left x⁻¹ hX.cex.hyp.h6.le).trans hVx
  have hO2S : pCoreOf 2 H ≤ S := Cex16.pCoreOf_le_S h1 hS hX.cex hX.min.1
  have hP : IsPGroup 2 ↥(conjSubgroup V₀ g ⊔ conjSubgroup V₀ x⁻¹) :=
    hX.cex.sylow.isPGroup.to_le (sup_le hBS (hV₀x.trans hO2S))
  have hcomm := commute_of_isPGroup_sup (W := conjSubgroup V₀ g)
    (W' := conjSubgroup V₀ x⁻¹) hX.cex.hyp.elemAbelian₀ hX.cex.hyp.isTI
    ⟨g, rfl⟩ ⟨x⁻¹, rfl⟩ hN hP
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hcomm b hb (x * z * x⁻¹) hmem

end Certified

private theorem w16pThirteenC_conjSubgroup_le_centralizer_V (h1 : W16One G) (hS : Std15 G)
    (hX : Hyp167 M V₀ V U S H g X T) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
  (E3.le_wClos (E3.mem_gammaSet_iff.mpr ⟨hX.le_S, g, le_rfl, E3.mQuot_self _⟩)).trans
    (hX.cex.wClos_le_centralizer h1 hS)

theorem Hyp167.V₀_le_A (hMult : SchurMultiplierInput)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) {Y : Subgroup G} {k : ℕ} (hAY : conjSubgroup V g ≤ Y)
    (hYX : Y ≤ X) (hYM : ¬ Y ≤ M)
    (h12 : Setting12Two ((conjSubgroup V g).subgroupOf Y) (M.subgroupOf Y) k)
    (hFA : conjClosure V₀ X ≤ conjSubgroup M g) : V₀ ≤ conjSubgroup V g := by
  have hFabelian : IsElemAbelian 2 (conjClosure V₀ X) :=
    CFSG.Open.IsElemAbelian.mono (Hyp167.isElemAbelian_I h1 hS hX hVO)
      (conjClosure_mono hX.cex.hyp.h6.le le_rfl)
  have hYN : Y ≤ normalizer (conjClosure V₀ X : Set G) :=
    hYX.trans (le_normalizer_conjClosure V₀ X)
  obtain ⟨MD⟩ := exists_modDataE hFabelian hYN
  have hAc : conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
    w16pThirteenC_conjSubgroup_le_centralizer_V h1 hS hX
  have hAc₀ : conjSubgroup V g ≤ Subgroup.centralizer (V₀ : Set G) :=
    hAc.trans (Subgroup.centralizer_le hX.cex.hyp.h6.le)
  have hAab : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hAA : ⁅conjSubgroup V g, conjSubgroup V g⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact B2F.isElemAbelian_comm hAab hb ha
  have hFAcomm : ⁅conjClosure V₀ X, conjSubgroup V g⁆ ≤ conjSubgroup V g := by
    rw [Subgroup.commutator_le]
    intro f hf a ha
    have hnorm : conjSubgroup M g = normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, hX.cex.hyp.h6.normalizer_eq]
    have hfN : f ∈ normalizer (conjSubgroup V g : Set G) := hnorm ▸ hFA hf
    have h1 : f * a * f⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hfN a).1 ha
    have h2 : (f * a * f⁻¹) * a⁻¹ ∈ conjSubgroup V g :=
      (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem ha)
    simpa [commutatorElement_def] using h2
  have hdouble : ⁅⁅conjClosure V₀ X, conjSubgroup V g⁆, conjSubgroup V g⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono hFAcomm le_rfl).trans (le_of_eq hAA)
  have hquad : RepQuad MD.ρ ((conjSubgroup V g).subgroupOf Y) :=
    MD.commSpace_commSub_img_eq_bot hAY hdouble
  have hV₀C : V₀ ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.1 (hAc₀ ha)) v hv).symm
  have hUA : MD.sp V₀ ≤ fixSub (((conjSubgroup V g).subgroupOf Y).map MD.ρ) := by
    show MD.sp V₀ ≤ fixSub (MD.img (conjSubgroup V g))
    rw [MD.fixSub_img hAY]
    exact MD.sp_mono hV₀C
  have hMU : ∀ m ∈ M.subgroupOf Y, ∀ u ∈ MD.sp V₀, MD.ρ m u ∈ MD.sp V₀ := by
    intro m hm u hu
    obtain ⟨v, hv, rfl⟩ := MD.mem_sp.1 hu
    have hmN : (m : G) ∈ normalizer (V₀ : Set G) := by
      rw [hX.cex.hyp.normalizer₀]
      exact hm
    have hv' : (m : G) * v * (m : G)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 hmN v).1 hv.1
    rw [MD.ρ_ι m v hv.2]
    exact MD.mem_sp.2 ⟨_, ⟨hv', le_conjClosure V₀ X hv'⟩, rfl⟩
  have hdec := Setting12Two.eq_inf_fixSub_sup_inf_commSub h12 (hAab.subgroupOf Y) MD.ρ hquad
    hUA hMU
  have hV₀Y : V₀ ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    by_contra hv1
    have hYle : Y ≤ Subgroup.centralizer ({v} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ((Subgroup.mem_centralizer_iff.1 hv.2) y hy).symm
    exact hYM (hYle.trans (hX.cex.hyp.centralizer_le hv.1 hv1))
  have hYrange : MD.img Y = MD.ρ.range := by
    simp only [ModDataE.img, Subgroup.subgroupOf_self]
    exact Subgroup.map_top MD.ρ
  have hfixbot : MD.sp V₀ ⊓ fixSub MD.ρ.range = ⊥ := by
    rw [← hYrange, MD.fixSub_img le_rfl, ← MD.sp_inf, hV₀Y]
    exact MD.sp_eq_bot_iff.mpr (by simp)
  have hfixle : MD.sp V₀ ⊓ fixSub MD.ρ.range ≤ MD.sp (conjSubgroup V g) := by
    rw [hfixbot]
    exact bot_le
  have hcommSub_eq : commSub (MD.img (conjSubgroup V g)) =
      MD.sp ⁅conjClosure V₀ X, conjSubgroup V g⁆ := by
    refine le_antisymm ?_ ?_
    · intro w hw
      obtain ⟨e, he, rfl⟩ := MD.ι_surj w
      exact MD.mem_sp.2 ⟨e, ⟨(MD.mem_commSub_img_iff hAY he).1 hw, he⟩, rfl⟩
    · intro w hw
      obtain ⟨e, he, rfl⟩ := MD.mem_sp.1 hw
      exact (MD.mem_commSub_img_iff hAY he.2).2 he.1
  have hcommle : MD.sp V₀ ⊓ commSub (((conjSubgroup V g).subgroupOf Y).map MD.ρ) ≤
      MD.sp (conjSubgroup V g) := by
    show MD.sp V₀ ⊓ commSub (MD.img (conjSubgroup V g)) ≤ MD.sp (conjSubgroup V g)
    rw [hcommSub_eq]
    exact inf_le_right.trans (MD.sp_mono hFAcomm)
  have hsp_le : MD.sp V₀ ≤ MD.sp (conjSubgroup V g) := by
    rw [hdec]
    exact sup_le hfixle hcommle
  intro v hv
  have hvF : v ∈ conjClosure V₀ X := le_conjClosure V₀ X hv
  have hmem : MD.ι v ∈ MD.sp (conjSubgroup V g) :=
    hsp_le (MD.mem_sp.2 ⟨v, ⟨hv, hvF⟩, rfl⟩)
  obtain ⟨a, ha, hae⟩ := MD.mem_sp.1 hmem
  have hav : a = v := MD.ι_injOn ha.2 hvF hae
  exact hav ▸ ha.1

theorem Hyp167.conj_V_le_centralizer_B (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hn : E3.mQuot V (U ⊔ V₀) < mSub V₀) (hV₀A : V₀ ≤ conjSubgroup V g)
    (hF : conjClosure V₀ X ≤ centralizer (conjSubgroup V₀ g : Set G)) :
    ∀ x ∈ X, conjSubgroup V x ≤ centralizer (conjSubgroup V₀ g : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgM : g ∉ M := Hyp167.not_mem_M h1 hS hX hVO
  have hAc : conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
    w16pThirteenC_conjSubgroup_le_centralizer_V h1 hS hX
  have hBle : conjSubgroup V₀ g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le
  intro x hx
  by_cases hxM : x ∈ M
  · have hVx : conjSubgroup V x = V := by
      rw [conjSubgroup_eq_iff_mem_normalizer, hX.cex.hyp.h6.normalizer_eq]
      exact hxM
    rw [hVx]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (hAc (hBle hb))) v hv).symm
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    by_contra hbv
    set t : G := x * b * x⁻¹ with ht
    set w : G := x * v * x⁻¹ with hw
    have hwV : w ∈ V := by
      rw [hw]
      exact mem_conjSubgroup_iff.1 hv
    have htV₀ : t ∈ Subgroup.centralizer (V₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hfF : x⁻¹ * z * x ∈ conjClosure V₀ X := by
        simpa using mem_conjClosure (X.inv_mem hx) hz
      have hbf : b * (x⁻¹ * z * x) = (x⁻¹ * z * x) * b :=
        (Subgroup.mem_centralizer_iff.1 (hF hfF)) b hb
      have h1 : t * z * t⁻¹ * z⁻¹ = 1 := by
        rw [ht]
        calc x * b * x⁻¹ * z * (x * b * x⁻¹)⁻¹ * z⁻¹
            = x * (b * (x⁻¹ * z * x) * b⁻¹ * (x⁻¹ * z * x)⁻¹) * x⁻¹ := by group
          _ = x * 1 * x⁻¹ := by rw [hbf]; group
          _ = 1 := by group
      have h2 : t * z * t⁻¹ = z := mul_inv_eq_one.1 h1
      calc z * t = (t * z * t⁻¹) * t := by rw [h2]
        _ = t * z := by group
    have htM : t ∈ M := by
      have h := Subgroup.centralizer_le_normalizer (V₀ : Set G) htV₀
      rwa [hX.cex.hyp.normalizer₀] at h
    have hUt : U ≤ Subgroup.centralizer ({t} : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hxu : u * x = x * u :=
        (Subgroup.mem_centralizer_iff.1 ((hX.mem.1.trans hX.min.1.2.1) hx)) u hu
      have hbu : b * u = u * b :=
        ((Subgroup.mem_centralizer_iff.1 (hX.cex.S_le_centralizer (hX.le_S (hBle hb)))) u hu).symm
      have hxux : x⁻¹ * u * x = u := by
        calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
          _ = x⁻¹ * (x * u) := by rw [hxu]
          _ = u := by group
      have h1 : t * u * t⁻¹ * u⁻¹ = 1 := by
        rw [ht]
        calc x * b * x⁻¹ * u * (x * b * x⁻¹)⁻¹ * u⁻¹
            = x * (b * (x⁻¹ * u * x) * b⁻¹ * (x⁻¹ * u * x)⁻¹) * x⁻¹ := by group
          _ = x * (b * u * b⁻¹ * u⁻¹) * x⁻¹ := by rw [hxux]
          _ = x * 1 * x⁻¹ := by rw [hbu]; group
          _ = 1 := by group
      have h2 : t * u * t⁻¹ = u := mul_inv_eq_one.1 h1
      calc t * u = (t * u * t⁻¹) * t := by group
        _ = u * t := by rw [h2]
    have hV₀t : V₀ ≤ Subgroup.centralizer ({t} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Subgroup.mem_centralizer_iff.1 htV₀) z hz).symm
    have hCt : U ⊔ V₀ ≤ Subgroup.centralizer ({t} : Set G) := sup_le hUt hV₀t
    have htw : t * w * t⁻¹ * w⁻¹ = x * (b * v * b⁻¹ * v⁻¹) * x⁻¹ := by
      rw [ht, hw]
      group
    have htwnc : t * w ≠ w * t := by
      intro heq
      have h1 : t * w * t⁻¹ * w⁻¹ = 1 := by rw [heq]; group
      rw [htw] at h1
      have h2 : b * v * b⁻¹ * v⁻¹ = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      have h3 : b * v * b⁻¹ = v := mul_inv_eq_one.1 h2
      exact hbv (by
        calc b * v = (b * v * b⁻¹) * b := by group
          _ = v * b := by rw [h3])
    have ht_not_cent : ¬ V ≤ Subgroup.centralizer ({t} : Set G) := by
      intro hle
      have hwt : w ∈ Subgroup.centralizer ({t} : Set G) := hle hwV
      exact htwnc ((Subgroup.mem_centralizer_iff.1 hwt) t (Set.mem_singleton t))
    have htA : t ∈ conjSubgroup (conjSubgroup V₀ g) x⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hxt : x⁻¹ * t * (x⁻¹)⁻¹ = b := by rw [ht]; group
      rw [hxt]
      exact hb
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1
      (E3.isPGroup_conjSubgroup (E3.isPGroup_conjSubgroup
        hX.cex.hyp.elemAbelian₀.isPGroup g) x⁻¹)) ⟨t, htA⟩
    have ht2 : ∃ k : ℕ, orderOf t = 2 ^ k :=
      ⟨k, (Subgroup.orderOf_coe (⟨t, htA⟩ : conjSubgroup (conjSubgroup V₀ g) x⁻¹)).trans hk⟩
    have ht_ct : t ∈ F11.CTilde M V₀ V :=
      mem_cTilde_of_mQuot_lt (hV := hX.cex.hyp.h6.elemAbelian) (hV₀ := hX.cex.hyp.h6.le)
        (hM := hX.cex.hyp.h6.normalizer_eq.symm.le) (hM₀ := hX.cex.hyp.h6.le_normalizer₀)
        (ht := htM) (ht2 := ht2) (C := U ⊔ V₀)
        (hCV := sup_le hX.cex.le hX.cex.hyp.h6.le) (hCt := hCt)
        (hlt := by exact_mod_cast hX.cex.n_lt_mBar)
    have h146 := mQuot_centralizer_ge_rk_conjSubgroup_inf (M := M) (V₀ := V₀) (V := V)
      hX.cex.hyp.h6.elemAbelian hX.cex.hyp.h6.le
      hX.cex.hyp.h6.normalizer_eq.symm.le hX.cex.hyp.normalizer₀ hX.cex.hyp.isTI
      (hX.cex.hyp.h6.conjGenerated hX.cex.hyp.ne_bot)
      (g := g⁻¹) (fun hg => hgM (by simpa using M.inv_mem hg)) ht_ct ht_not_cent
    have hV₀g' : conjSubgroup V₀ g⁻¹ ≤ V :=
      (E3.conjSubgroup_mono_left g⁻¹ hV₀A).trans (le_of_eq (E3.conjSubgroup_conj_inv V g))
    have hrk : rk ↥(conjSubgroup V₀ g⁻¹ ⊓ V) = mSub V₀ := by
      rw [inf_eq_left.mpr hV₀g']
      simp only [mSub, rk, E3.card_conjSubgroup]
    have hquot : E3.mQuot V (V ⊓ Subgroup.centralizer ({t} : Set G)) ≤
        E3.mQuot V (U ⊔ V₀) :=
      E3.mQuot_mono (le_inf (sup_le hX.cex.le hX.cex.hyp.h6.le) hCt)
    exact absurd (hrk ▸ h146.trans hquot) (not_le.2 hn)

end CFSG.LocalAnalysis.WeakClosure81

end
