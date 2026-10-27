module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.W16Four
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem conj_comm_inf_pCoreOf {M V₀ V U S H : Subgroup G}
    (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) :
    ∀ z ∈ V ⊓ pCoreOf 2 H, ∀ k ∈ H, ∀ z' ∈ V ⊓ pCoreOf 2 H,
      z * (k * z' * k⁻¹) = (k * z' * k⁻¹) * z := by
  intro z hz k hk z' hz'
  have hZV : V ⊓ pCoreOf 2 H ≤ V := inf_le_left
  have hZP : V ⊓ pCoreOf 2 H ≤ pCoreOf 2 H := inf_le_right
  by_cases hkM : k ∈ M
  · have hkV : k ∈ normalizer (V : Set G) := by
      rw [h.hyp.h6.normalizer_eq]
      exact hkM
    have hwV : k * z' * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hkV z').1 (hZV hz')
    exact B2F.isElemAbelian_comm h.hyp.h6.elemAbelian (hZV hz) hwV
  · have hwP : k * z' * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hk) z').1 (hZP hz')
    have hwS : k * z' * k⁻¹ ∈ S := h.pCoreOf_le_S h1 hS hF hwP
    have hV0₁ : z * (k * z' * k⁻¹) * z⁻¹ * (k * z' * k⁻¹)⁻¹ ∈ V₀ := by
      have hcomm := h.comm_mem_V₀ hwS (hZV hz)
      have e : z * (k * z' * k⁻¹) * z⁻¹ * (k * z' * k⁻¹)⁻¹ =
          ((k * z' * k⁻¹) * z * (k * z' * k⁻¹)⁻¹ * z⁻¹)⁻¹ := by group
      rw [e]
      exact V₀.inv_mem hcomm
    have hV0₂ : z * (k * z' * k⁻¹) * z⁻¹ * (k * z' * k⁻¹)⁻¹ ∈ conjSubgroup V₀ k⁻¹ := by
      rw [mem_conjSubgroup_iff]
      simp only [inv_inv]
      have hzP : k⁻¹ * z * k ∈ pCoreOf 2 H := by
        have h := (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hk)) z).1 (hZP hz)
        simpa only [inv_inv] using h
      have hzS : k⁻¹ * z * k ∈ S := h.pCoreOf_le_S h1 hS hF hzP
      have e : k⁻¹ * (z * (k * z' * k⁻¹) * z⁻¹ * (k * z' * k⁻¹)⁻¹) * k =
          (k⁻¹ * z * k) * z' * (k⁻¹ * z * k)⁻¹ * z'⁻¹ := by group
      rw [e]
      exact h.comm_mem_V₀ hzS (hZV hz')
    have hkinv : k⁻¹ ∉ M := fun hkm => hkM (by simpa using M.inv_mem hkm)
    have hbot : conjSubgroup V₀ k⁻¹ ⊓ V₀ = ⊥ := h.hyp.conj_inf_eq_bot hkinv
    have hx1 : z * (k * z' * k⁻¹) * z⁻¹ * (k * z' * k⁻¹)⁻¹ = 1 :=
      Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨hV0₂, hV0₁⟩)
    have hzw : z * (k * z' * k⁻¹) * z⁻¹ = k * z' * k⁻¹ := mul_inv_eq_one.mp hx1
    calc z * (k * z' * k⁻¹) = z * (k * z' * k⁻¹) * z⁻¹ * z := by group
      _ = (k * z' * k⁻¹) * z := by rw [hzw]

theorem Cex16.isElemAbelian_iSub16 (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hF : Fam16 M U S H) : IsElemAbelian 2 (iSub16 V H) := by
  rw [iSub16, conjClosure]
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro a ⟨h₁, hh₁, z₁, hz₁, rfl⟩ b ⟨h₂, hh₂, z₂, hz₂, rfl⟩
    have hk : h₁⁻¹ * h₂ ∈ H := H.mul_mem (H.inv_mem hh₁) hh₂
    have hcomm := conj_comm_inf_pCoreOf h1 hS h hF z₁ hz₁ (h₁⁻¹ * h₂) hk z₂ hz₂
    have e1 : (h₁ * z₁ * h₁⁻¹) * (h₂ * z₂ * h₂⁻¹) =
        h₁ * (z₁ * ((h₁⁻¹ * h₂) * z₂ * (h₁⁻¹ * h₂)⁻¹)) * h₁⁻¹ := by group
    have e2 : (h₂ * z₂ * h₂⁻¹) * (h₁ * z₁ * h₁⁻¹) =
        h₁ * (((h₁⁻¹ * h₂) * z₂ * (h₁⁻¹ * h₂)⁻¹) * z₁) * h₁⁻¹ := by group
    rw [e1, e2, hcomm]
  · rintro a ⟨h₁, hh₁, z₁, hz₁, rfl⟩
    have hz1 : z₁ ^ 2 = 1 := h.hyp.h6.elemAbelian.2 z₁ hz₁.1
    rw [conj_pow, hz1]
    group

theorem Cex16.iSub16_le_pCoreOf (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) :
    iSub16 V H ≤ pCoreOf 2 H := by
  rw [iSub16]
  refine conjClosure_le fun k hk z hz => ?_
  exact (Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hk) z).1 hz.2

theorem Cex16.V₀_le_pCoreOf (h5 : W16Five G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) : V₀ ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV0H : V₀ ≤ H := h.hyp.h6.le.trans (h.V_le_S.trans hF.1)
  have hX2 : IsPGroup 2 ↥(V₀.subgroupOf H) :=
    (CFSG.Open.IsElemAbelian.isPGroup h.hyp.elemAbelian₀).of_equiv
      (Subgroup.subgroupOfEquivOfLe hV0H).symm
  rcases baer_suzuki_subgroup (G := ↥H) (p := 2) (X := V₀.subgroupOf H) hX2 with hle | ⟨g', hg'⟩
  · intro v hv
    exact ⟨⟨v, hV0H hv⟩, hle (show (⟨v, hV0H hv⟩ : ↥H) ∈ V₀.subgroupOf H from hv), rfl⟩
  · exfalso
    have hgH : (g' : G) ∈ H := g'.2
    have hV0p : IsPGroup 2 ↥V₀ := CFSG.Open.IsElemAbelian.isPGroup h.hyp.elemAbelian₀
    have hV0g : IsPGroup 2 ↥(conjSubgroup V₀ (g' : G)) :=
      CFSG.Open.IsElemAbelian.isPGroup (by
        simpa [conjSubgroup] using
          h.hyp.elemAbelian₀.map (MulAut.conj (g' : G)⁻¹).toMonoidHom)
    have h2G : IsPGroup 2 ↥(V₀ ⊔ conjSubgroup V₀ (g' : G)) := by
      by_cases hcomm : ∀ x ∈ V, ∀ y ∈ conjSubgroup V (g' : G), x * y = y * x
      · have hsup : IsElemAbelian 2 (V₀ ⊔ conjSubgroup V₀ (g' : G)) :=
          B2F.isElemAbelian_sup_of_commute h.hyp.elemAbelian₀ (by
            simpa [conjSubgroup] using
              h.hyp.elemAbelian₀.map (MulAut.conj (g' : G)⁻¹).toMonoidHom)
            (fun a ha b hb =>
              hcomm a (h.hyp.h6.le ha) b (Subgroup.map_mono h.hyp.h6.le hb))
        exact CFSG.Open.IsElemAbelian.isPGroup hsup
      · have hfive := h5 hS h hF hV (g' : G) hgH hcomm
        have hV0le : V₀ ≤ conjSubgroup M (g' : G) := by
          calc V₀ ≤ U ⊔ V₀ := le_sup_right
            _ = V ⊓ conjSubgroup M (g' : G) := hfive.symm
            _ ≤ conjSubgroup M (g' : G) := inf_le_right
        have hnorm : V₀ ≤ Subgroup.normalizer (conjSubgroup V₀ (g' : G) : Set G) := by
          rw [← E3.conjSubgroup_normalizer, h.hyp.normalizer₀]
          exact hV0le
        exact IsPGroup.to_sup_of_normal_right' hV0p hV0g hnorm
    have hV0gH : conjSubgroup V₀ (g' : G) ≤ H := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have e : y = (g' : G)⁻¹ * ((g' : G) * y * (g' : G)⁻¹) * (g' : G) := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hgH) (hV0H hy)) hgH
    set Y : Subgroup ↥H := V₀.subgroupOf H ⊔ conjSubgroup (V₀.subgroupOf H) g' with hY
    have hmap : Y.map H.subtype = V₀ ⊔ conjSubgroup V₀ (g' : G) := by
      rw [hY, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hV0H]
      congr 1
      ext y
      constructor
      · intro hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        rw [mem_conjSubgroup_iff] at hy' ⊢
        simpa using Subgroup.mem_subgroupOf.mp hy'
      · intro hy
        rw [mem_conjSubgroup_iff] at hy
        refine Subgroup.mem_map.2 ⟨⟨y, ?_⟩, ?_, rfl⟩
        · have : y = (g' : G)⁻¹ * ((g' : G) * y * (g' : G)⁻¹) * (g' : G) := by group
          rw [this]
          exact H.mul_mem (H.mul_mem (H.inv_mem hgH) (hV0H hy)) hgH
        · rw [mem_conjSubgroup_iff]
          exact Subgroup.mem_subgroupOf.mpr hy
    have h2Y : IsPGroup 2 ↥(Y.map H.subtype) := hmap ▸ h2G
    exact hg' (h2Y.of_equiv (Y.equivMapOfInjective H.subtype H.subtype_injective).symm)

private theorem exists_conj_not_comm_of_not_le_pCoreOf {V H : Subgroup G}
    (hVH : V ≤ H) (hVab : IsElemAbelian 2 V) (hV : ¬ V ≤ pCoreOf 2 H) :
    ∃ g ∈ H, ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
  by_contra hcon
  push Not at hcon
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk)
  have hKp : conjClosure V H ≤ pCoreOf 2 H := by
    refine le_pCoreOf_of_isPGroup_of_normal hKH ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
      exact le_normalizer_conjClosure V H
    · exact CFSG.Open.IsElemAbelian.isPGroup (by
        rw [conjClosure]
        refine B2F.isElemAbelian_closure ?_ ?_
        · rintro a ⟨g, hg, x, hx, rfl⟩ b ⟨h, hh, y, hy, rfl⟩
          have hk : g⁻¹ * h ∈ H := H.mul_mem (H.inv_mem hg) hh
          have hz : (g⁻¹ * h) * y * (g⁻¹ * h)⁻¹ ∈ conjSubgroup V (g⁻¹ * h)⁻¹ := by
            rw [mem_conjSubgroup_iff]
            simp only [inv_inv]
            have e : (g⁻¹ * h)⁻¹ * ((g⁻¹ * h) * y * (g⁻¹ * h)⁻¹) * (g⁻¹ * h) = y := by
              group
            rw [e]
            exact hy
          have hcomm := hcon (g⁻¹ * h)⁻¹ (H.inv_mem hk) x hx
            ((g⁻¹ * h) * y * (g⁻¹ * h)⁻¹) hz
          have e1 : (g * x * g⁻¹) * (h * y * h⁻¹) =
              g * (x * ((g⁻¹ * h) * y * (g⁻¹ * h)⁻¹)) * g⁻¹ := by
            rw [show h = g * (g⁻¹ * h) by group]
            group
          have e2 : (h * y * h⁻¹) * (g * x * g⁻¹) =
              g * (((g⁻¹ * h) * y * (g⁻¹ * h)⁻¹) * x) * g⁻¹ := by
            rw [show h = g * (g⁻¹ * h) by group]
            group
          rw [e1, e2, hcomm]
        · rintro a ⟨g, hg, x, hx, rfl⟩
          rw [conj_pow, hVab.2 x hx]
          group)
  exact hV ((le_conjClosure V H).trans hKp)

theorem Cex16.inf_pCoreOf_eq (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    V ⊓ pCoreOf 2 H = U ⊔ V₀ := by
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hUH : U ≤ H := h.le.trans hVH
  have hU2 : IsPGroup 2 U := h.hyp.isPGroup.to_le h.le
  have hUnorm : (U.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUH]
    exact hF.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hUO : U ≤ pCoreOf 2 H := le_pCoreOf_of_isPGroup_of_normal hUH hUnorm hU2
  have hV0O : V₀ ≤ pCoreOf 2 H := h.V₀_le_pCoreOf h5 hS hF hV
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg, hgnot⟩ :=
      exists_conj_not_comm_of_not_le_pCoreOf hVH h.hyp.h6.elemAbelian hV
    have hfive := h5 hS h hF hV g hg hgnot
    have hpCore_le_conjM : pCoreOf 2 H ≤ conjSubgroup M g := by
      intro y hy
      rw [mem_conjSubgroup_iff]
      have hgy : g * y * g⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) y).1 hy
      exact h.S_le_M (h.pCoreOf_le_S h1 hS hF hgy)
    calc V ⊓ pCoreOf 2 H ≤ V ⊓ conjSubgroup M g := inf_le_inf_left V hpCore_le_conjM
      _ = U ⊔ V₀ := hfive
  · exact le_inf (sup_le h.le h.hyp.h6.le) (sup_le hUO hV0O)

theorem Cex16.inf_centralizer_iSub16_eq (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    V ⊓ centralizer (iSub16 V H : Set G) = U ⊔ V₀ := by
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hIab : IsElemAbelian 2 (iSub16 V H) := h.isElemAbelian_iSub16 h1 hS hF
  have hUH : U ≤ H := h.le.trans hVH
  have hU2 : IsPGroup 2 U := h.hyp.isPGroup.to_le h.le
  have hUnorm : (U.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUH]
    exact hF.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hUO : U ≤ pCoreOf 2 H := le_pCoreOf_of_isPGroup_of_normal hUH hUnorm hU2
  have hV0O : V₀ ≤ pCoreOf 2 H := h.V₀_le_pCoreOf h5 hS hF hV
  have hUI : U ≤ iSub16 V H := (le_inf h.le hUO).trans (le_conjClosure _ _)
  have hV0I : V₀ ≤ iSub16 V H := (le_inf h.hyp.h6.le hV0O).trans (le_conjClosure _ _)
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg, hgnot⟩ :=
      exists_conj_not_comm_of_not_le_pCoreOf hVH h.hyp.h6.elemAbelian hV
    have hfive := h5 hS h hF hV g hg hgnot
    have hV0gI : conjSubgroup V₀ g ≤ iSub16 V H := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hmem : g * y * g⁻¹ ∈ iSub16 V H := hV0I hy
      have hnorm : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
        le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
      have h := (Subgroup.mem_normalizer_iff.1 (hnorm (H.inv_mem hg)) (g * y * g⁻¹)).1 hmem
      simpa [mul_assoc] using h
    intro x hx
    have hxCV0g : x ∈ centralizer (conjSubgroup V₀ g : Set G) :=
      Subgroup.centralizer_le hV0gI hx.2
    have hxN : x ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) :=
      Subgroup.centralizer_le_normalizer _ hxCV0g
    have hxM : x ∈ conjSubgroup M g := by
      rw [← E3.conjSubgroup_normalizer, h.hyp.normalizer₀] at hxN
      exact hxN
    have hxVM : x ∈ V ⊓ conjSubgroup M g := ⟨hx.1, hxM⟩
    rwa [hfive] at hxVM
  · have hIleC : iSub16 V H ≤ centralizer (iSub16 V H : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hIab.1
    exact le_inf (sup_le h.le h.hyp.h6.le) ((sup_le hUI hV0I).trans hIleC)

theorem Cex16.inf_iSub16_eq (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    V ⊓ iSub16 V H = U ⊔ V₀ := by
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hUH : U ≤ H := h.le.trans hVH
  have hU2 : IsPGroup 2 U := h.hyp.isPGroup.to_le h.le
  have hUnorm : (U.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUH]
    exact hF.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hUO : U ≤ pCoreOf 2 H := le_pCoreOf_of_isPGroup_of_normal hUH hUnorm hU2
  have hV0O : V₀ ≤ pCoreOf 2 H := h.V₀_le_pCoreOf h5 hS hF hV
  have hUI : U ≤ iSub16 V H := (le_inf h.le hUO).trans (le_conjClosure _ _)
  have hV0I : V₀ ≤ iSub16 V H := (le_inf h.hyp.h6.le hV0O).trans (le_conjClosure _ _)
  have hIleC : iSub16 V H ≤ centralizer (iSub16 V H : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (h.isElemAbelian_iSub16 h1 hS hF).1
  refine le_antisymm ?_ ?_
  · calc V ⊓ iSub16 V H ≤ V ⊓ centralizer (iSub16 V H : Set G) :=
        le_inf inf_le_left (inf_le_right.trans hIleC)
      _ = U ⊔ V₀ := h.inf_centralizer_iSub16_eq h1 h5 hS hF hV
  · exact sup_le (le_inf h.le hUI) (le_inf h.hyp.h6.le hV0I)


end CFSG.LocalAnalysis.WeakClosure81

end
