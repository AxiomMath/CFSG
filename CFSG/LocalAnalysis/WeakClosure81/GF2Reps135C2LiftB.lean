module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LiftA
import CFSG.ClassicalInvolution.Generic.Generation.Layer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}

theorem w135c2_lift_gen (hctx : Is135Context Y L) {t : MulAut W} (htY : t ∈ Y)
    [hN : ((Zc L).subgroupOf Y).Normal] (Tb : Finset (↥Y ⧸ (Zc L).subgroupOf Y))
    (hconj : ∀ y ∈ Tb,
      ∃ s ∈ ((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))),
        y = s * QuotientGroup.mk' ((Zc L).subgroupOf Y) ⟨t, htY⟩ * s⁻¹)
    (hgen : ((L.subgroupOf Y).map (QuotientGroup.mk' ((Zc L).subgroupOf Y))) ≤
      Subgroup.closure (Tb : Set (↥Y ⧸ (Zc L).subgroupOf Y))) :
    ∃ T : Finset (MulAut W), T.card ≤ Tb.card ∧ (∀ x ∈ T, ∃ g ∈ L, x = g * t * g⁻¹) ∧
      L ≤ Subgroup.closure (T : Set (MulAut W)) := by
  classical
  have hLY : L ≤ Y := hctx.2.2.1
  let N : Subgroup ↥Y := (Zc L).subgroupOf Y
  haveI hN' : N.Normal := hN
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  let S : Subgroup (↥Y ⧸ N) := (L.subgroupOf Y).map π
  let tb : ↥Y ⧸ N := π ⟨t, htY⟩
  let sf : {y : ↥Y ⧸ N // y ∈ Tb} → (↥Y ⧸ N) :=
    fun y => Classical.choose (hconj y.1 y.2)
  have hsf_mem : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, sf y ∈ S :=
    fun y => (Classical.choose_spec (hconj y.1 y.2)).1
  have hsf_eq : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, y.1 = sf y * tb * (sf y)⁻¹ :=
    fun y => (Classical.choose_spec (hconj y.1 y.2)).2
  let lY : {y : ↥Y ⧸ N // y ∈ Tb} → ↥Y :=
    fun y => Classical.choose (Subgroup.mem_map.mp (hsf_mem y))
  have hlY_mem : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, lY y ∈ L.subgroupOf Y :=
    fun y => (Classical.choose_spec (Subgroup.mem_map.mp (hsf_mem y))).1
  have hlY_pi : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, π (lY y) = sf y :=
    fun y => (Classical.choose_spec (Subgroup.mem_map.mp (hsf_mem y))).2
  let x : {y : ↥Y ⧸ N // y ∈ Tb} → MulAut W :=
    fun y => (lY y : MulAut W) * t * (lY y : MulAut W)⁻¹
  have hxY : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, x y ∈ Y := by
    intro y
    have h1 : (lY y : MulAut W) ∈ Y := hLY (Subgroup.mem_subgroupOf.mp (hlY_mem y))
    exact Y.mul_mem (Y.mul_mem h1 htY) (Y.inv_mem h1)
  have hxconj : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, ∃ g ∈ L, x y = g * t * g⁻¹ :=
    fun y => ⟨(lY y : MulAut W), Subgroup.mem_subgroupOf.mp (hlY_mem y), rfl⟩
  have hxpi : ∀ y : {y : ↥Y ⧸ N // y ∈ Tb}, π ⟨x y, hxY y⟩ = y.1 := by
    intro y
    have hcoe : (⟨x y, hxY y⟩ : ↥Y) = lY y * ⟨t, htY⟩ * (lY y)⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hcoe, map_mul, map_mul, map_inv, hlY_pi y]
    exact (hsf_eq y).symm
  let T : Finset (MulAut W) := Tb.attach.image x
  have hTcard : T.card ≤ Tb.card := by
    calc T.card = (Tb.attach.image x).card := rfl
      _ ≤ Tb.attach.card := Finset.card_image_le
      _ = Tb.card := Finset.card_attach
  have hTconj : ∀ z ∈ T, ∃ g ∈ L, z = g * t * g⁻¹ := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
    exact hxconj y
  have hTY : ∀ z ∈ T, z ∈ Y := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hz
    exact hxY y
  set H : Subgroup (MulAut W) := Subgroup.closure (T : Set (MulAut W)) with hH
  have hHY : H ≤ Y := by
    rw [hH]
    exact (Subgroup.closure_le Y).mpr (fun z hz => hTY z hz)
  set T' : Set ↥Y := {g | (g : MulAut W) ∈ T} with hT'
  set H' : Subgroup ↥Y := H.subgroupOf Y with hH'
  have hH'eq : H' = Subgroup.closure T' := by
    apply le_antisymm
    · have hmap : (Subgroup.closure T').map Y.subtype = H := by
        rw [MonoidHom.map_closure]
        have himg : Y.subtype '' T' = (T : Set (MulAut W)) := by
          ext z
          constructor
          · rintro ⟨g, hg, rfl⟩
            rwa [hT'] at hg
          · intro hz
            exact ⟨⟨z, hTY z hz⟩, by rw [hT']; exact hz, rfl⟩
        rw [himg, hH]
      intro g hg
      have hgH : (g : MulAut W) ∈ H := Subgroup.mem_subgroupOf.mp hg
      have hmem : (g : MulAut W) ∈ (Subgroup.closure T').map Y.subtype := by
        rw [hmap]; exact hgH
      obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp hmem
      have hgg : g' = g := Subtype.ext hgg'
      rwa [hgg] at hg'
    · exact (Subgroup.closure_le H').mpr (fun g hg => by
        refine Subgroup.mem_subgroupOf.mpr ?_
        rw [hH]
        exact Subgroup.subset_closure (by rwa [hT'] at hg))
  have hmap : H'.map π = Subgroup.closure (Tb : Set (↥Y ⧸ N)) := by
    rw [hH'eq, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgT : (g : MulAut W) ∈ T := by rwa [hT'] at hg
      obtain ⟨y₀, -, hxy₀⟩ := Finset.mem_image.mp hgT
      have hg_eq : g = ⟨x y₀, hxY y₀⟩ := Subtype.ext hxy₀.symm
      rw [hg_eq, hxpi y₀]
      exact y₀.2
    · intro hy
      refine ⟨⟨x ⟨y, hy⟩, hxY ⟨y, hy⟩⟩, ?_, hxpi ⟨y, hy⟩⟩
      rw [hT']
      exact Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
  have hgen' : S ≤ H'.map π := by
    rw [hmap]
    exact hgen
  have hzcent : ∀ z ∈ Zc L, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have h := Subgroup.mem_center_iff.mp hz' (⟨l, hl⟩ : ↥L)
    exact (congrArg Subtype.val h).symm
  have hdecomp : ∀ l ∈ L, ∃ k ∈ H ⊓ L, ∃ z ∈ Zc L, l = k * z := by
    intro l hl
    have hmemS : π ⟨l, hLY hl⟩ ∈ S :=
      Subgroup.mem_map.mpr ⟨⟨l, hLY hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hmemH' : π ⟨l, hLY hl⟩ ∈ H'.map π := hgen' hmemS
    obtain ⟨h, hhH', hhh⟩ := Subgroup.mem_map.mp hmemH'
    let n : ↥Y := h⁻¹ * ⟨l, hLY hl⟩
    have hnN : n ∈ N := by
      have h1 : π n = 1 := by
        dsimp [n]
        rw [map_mul, map_inv, hhh, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff n).mp h1
    have hln : (⟨l, hLY hl⟩ : ↥Y) = h * n := by
      dsimp [n]; group
    have hl_coe : l = (h : MulAut W) * (n : MulAut W) := by
      have hcoe := congrArg (fun g : ↥Y => (g : MulAut W)) hln
      simpa using hcoe
    have hnnL : (n : MulAut W) ∈ L := w135c2_Zc_le L (Subgroup.mem_subgroupOf.mp hnN)
    have hhL : (h : MulAut W) ∈ L := by
      have heq : (h : MulAut W) = l * (n : MulAut W)⁻¹ := by
        rw [hl_coe]; group
      rw [heq]
      exact L.mul_mem hl (L.inv_mem hnnL)
    exact ⟨(h : MulAut W), ⟨Subgroup.mem_subgroupOf.mp hhH', hhL⟩,
      (n : MulAut W), Subgroup.mem_subgroupOf.mp hnN, hl_coe⟩
  refine ⟨T, hTcard, hTconj, ?_⟩
  haveI : Group.IsPerfect ↥L := hctx.2.2.2.2.1.1
  have hLleH : L ≤ H :=
    (CFSG.ClassicalInvolution.Generic.le_of_perfect_of_le_sup_central
      (H := L) (A := H ⊓ L) (Z := Zc L) inf_le_right (w135c2_Zc_le L)
      (fun z hz h hh => hzcent z hz h hh)
      (by rw [Subgroup.commutator_eq_self])
      (fun l hl => by
        obtain ⟨k, hk, z, hz, rfl⟩ := hdecomp l hl
        exact Subgroup.mul_mem (H := (H ⊓ L) ⊔ Zc L)
          (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hz))).trans
      inf_le_left
  rw [← hH]
  exact hLleH

theorem w135c2_gen_of_alpha (hGS : ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → ∀ A : ℕ, AlphaCase ↥S A → ∀ x : G, orderOf x = 2 → ∃ T :
    Finset G, T.card ≤ A ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧ S ≤ Subgroup.closure (T : Set
    G)) (hctx : Is135Context Y L) {t : MulAut W}
    (htY : t ∈ Y) (ht2 : orderOf t = 2) {A : ℕ}
    (hA : AlphaCase (↥L ⧸ Subgroup.center ↥L) A) :
    ∃ T : Finset (MulAut W), T.card ≤ A ∧ (∀ x ∈ T, ∃ g ∈ L, x = g * t * g⁻¹) ∧
      L ≤ Subgroup.closure (T : Set (MulAut W)) := by
  classical
  haveI hZNorm : ((Zc L).subgroupOf Y).Normal := w135c2_Zc_normal_in hctx
  let N : Subgroup ↥Y := (Zc L).subgroupOf Y
  haveI hN' : N.Normal := hZNorm
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  let S : Subgroup (↥Y ⧸ N) := (L.subgroupOf Y).map π
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Finite ↥Y :=
    Finite.of_injective (fun y : ↥Y => (y : MulAut W)) Subtype.coe_injective
  haveI : Finite (↥Y ⧸ N) := inferInstance
  let tb : ↥Y ⧸ N := π ⟨t, htY⟩
  have ht_sq : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2] at h
  have htb2 : tb ^ 2 = 1 := by
    dsimp [tb]
    rw [← map_pow, show (⟨t, htY⟩ : ↥Y) ^ 2 = 1 by
      apply Subtype.ext
      simpa using ht_sq, map_one]
  have htb1 : tb ≠ 1 := by
    intro h1
    have hmem : (⟨t, htY⟩ : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact w135c2_not_mem_Zc_of_order_two hctx ht2 (Subgroup.mem_subgroupOf.mp hmem)
  have hord : orderOf tb = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime htb2 htb1
  have hSnormal : S.Normal := w135c2_S_normal hctx
  have hScent : Subgroup.centralizer (S : Set (↥Y ⧸ N)) = ⊥ :=
    w135c2_S_centralizer hctx
  have hSA : AlphaCase ↥S A := w135c2_alphaCase_S hctx hA
  obtain ⟨Tb, hTbcard, hTbconj, hTbgen⟩ :=
    hGS (↥Y ⧸ N) S hSnormal hScent A hSA tb hord
  obtain ⟨T, hTcard, hTconj, hLgen⟩ := w135c2_lift_gen hctx htY Tb hTbconj hTbgen
  exact ⟨T, hTcard.trans hTbcard, hTconj, hLgen⟩

theorem w135c2_gen_of_alpha_outer (hGS : GS03AlphaOuterGeneral) (hctx : Is135Context Y L)
    {t : MulAut W} (htY : t ∈ Y) (ht2 : orderOf t = 2) (htL : t ∉ L) {tag : StatedLieTag}
    {n f : ℕ} (hR : tag = .PSL ∧ n = 4 ∧ f = 1)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) tag n 2 f) :
    ∃ T : Finset (MulAut W), T.card ≤ gs03Bound tag n f ∧
      (∀ x ∈ T, ∃ g ∈ L, x = g * t * g⁻¹) ∧ L ≤ Subgroup.closure (T : Set (MulAut W)) := by
  classical
  haveI hZNorm : ((Zc L).subgroupOf Y).Normal := w135c2_Zc_normal_in hctx
  let N : Subgroup ↥Y := (Zc L).subgroupOf Y
  haveI hN' : N.Normal := hZNorm
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  let S : Subgroup (↥Y ⧸ N) := (L.subgroupOf Y).map π
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Finite ↥Y :=
    Finite.of_injective (fun y : ↥Y => (y : MulAut W)) Subtype.coe_injective
  haveI : Finite (↥Y ⧸ N) := inferInstance
  let tb : ↥Y ⧸ N := π ⟨t, htY⟩
  have ht_sq : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2] at h
  have htb2 : tb ^ 2 = 1 := by
    dsimp [tb]
    rw [← map_pow, show (⟨t, htY⟩ : ↥Y) ^ 2 = 1 by
      apply Subtype.ext
      simpa using ht_sq, map_one]
  have htb1 : tb ≠ 1 := by
    intro h1
    have hmem : (⟨t, htY⟩ : ↥Y) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact w135c2_not_mem_Zc_of_order_two hctx ht2 (Subgroup.mem_subgroupOf.mp hmem)
  have hord : orderOf tb = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime htb2 htb1
  have hSnormal : S.Normal := w135c2_S_normal hctx
  have hScent : Subgroup.centralizer (S : Set (↥Y ⧸ N)) = ⊥ :=
    w135c2_S_centralizer hctx
  have hlieS : LieModel ↥S tag n 2 f := w135c2_lieModel_S hctx hlie
  have htbS : tb ∉ S := by
    intro hmem
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp hmem
    have hyN : y⁻¹ * ⟨t, htY⟩ ∈ N := QuotientGroup.eq.mp hyt
    have hz : (↑(y⁻¹ * ⟨t, htY⟩ : ↥Y) : MulAut W) ∈ Zc L := Subgroup.mem_subgroupOf.mp hyN
    have hzL : (↑(y⁻¹ * ⟨t, htY⟩ : ↥Y) : MulAut W) ∈ L := w135c2_Zc_le L hz
    have hyL : (y : MulAut W) ∈ L := Subgroup.mem_subgroupOf.mp hy
    apply htL
    have := L.mul_mem hyL hzL
    simpa using this
  obtain ⟨Tb, hTbcard, hTbconj, hTbgen⟩ :=
    hGS (↥Y ⧸ N) S hSnormal hScent tag n f hR hlieS tb hord htbS
  obtain ⟨T, hTcard, hTconj, hLgen⟩ := w135c2_lift_gen hctx htY Tb hTbconj hTbgen
  exact ⟨T, hTcard.trans hTbcard, hTconj, hLgen⟩

end CFSG.LocalAnalysis.WeakClosure81
