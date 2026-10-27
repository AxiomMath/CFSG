module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open Subgroup CFSG.Quasithin

open scoped Pointwise

private theorem w183K3Dyn_le_normalizer_of_comm {A : Type} [Group A] {N M : Subgroup A}
    (hcent : ∀ z ∈ N, ∀ l ∈ M, z * l = l * z) : M ≤ Subgroup.normalizer (N : Set A) :=
  Subgroup.le_normalizer_iff.mpr fun l hl n hn => by
    rw [show l * n = n * l from (hcent n hn l hl).symm]
    simpa using hn

private theorem w183K3Dyn_eq_sup_inf_of_le_sup {A : Type} [Group A] {N L₀ X : Subgroup A}
    (hcomm : L₀ ≤ Subgroup.normalizer (N : Set A)) (hN : N ≤ X) (hXL : X ≤ L₀ ⊔ N) :
    (X ⊓ L₀) ⊔ N = X := by
  refine le_antisymm (sup_le inf_le_left hN) ?_
  intro x hx
  have hx' : x ∈ (L₀ : Set A) * (N : Set A) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L₀ N hcomm]
    exact hXL hx
  obtain ⟨a, ha, z, hz, haz⟩ := Set.mem_mul.mp hx'
  have haX : a ∈ X := by
    have h : a = x * z⁻¹ := by rw [← haz]; group
    rw [h]
    exact X.mul_mem hx (hN (N.inv_mem hz))
  rw [← haz]
  exact ((X ⊓ L₀) ⊔ N).mul_mem
    ((le_sup_left : X ⊓ L₀ ≤ (X ⊓ L₀) ⊔ N) ⟨haX, ha⟩)
    ((le_sup_right : N ≤ (X ⊓ L₀) ⊔ N) hz)

private theorem w183K3Dyn_mem_of_map_mem {A B : Type} [Group A] [Group B] (f : A →* B)
    {L X : Subgroup A} (hker : f.ker ⊓ L ≤ X) (hXL : X ≤ L) {a : A} (ha : a ∈ L)
    (hfa : f a ∈ X.map f) : a ∈ X := by
  obtain ⟨x, hxX, hxfa⟩ := Subgroup.mem_map.mp hfa
  have hxa_ker : x⁻¹ * a ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxfa]
    group
  have hxa_L : x⁻¹ * a ∈ L := L.mul_mem (L.inv_mem (hXL hxX)) ha
  have hxa_X : x⁻¹ * a ∈ X := hker (Subgroup.mem_inf.mpr ⟨hxa_ker, hxa_L⟩)
  have hxa' : a = x * (x⁻¹ * a) := by group
  rw [hxa']
  exact X.mul_mem hxX hxa_X

private theorem w183K3Dyn_map_comap_inf_eq {A B : Type} [Group A] [Group B] (f : A →* B)
    {Y' : Subgroup B} {L : Subgroup A} (hY' : Y' ≤ L.map f) :
    (Y'.comap f ⊓ L).map f = Y' := by
  refine le_antisymm ?_ ?_
  · calc (Y'.comap f ⊓ L).map f ≤ (Y'.comap f).map f := Subgroup.map_mono inf_le_left
      _ ≤ Y' := Subgroup.map_comap_le f Y'
  · intro y hy
    obtain ⟨l, hlL, hl⟩ := Subgroup.mem_map.mp (hY' hy)
    have hfl : f l ∈ Y' := by rw [hl]; exact hy
    exact Subgroup.mem_map.mpr ⟨l, ⟨Subgroup.mem_comap.mpr hfl, hlL⟩, hl⟩

private theorem w183K3Dyn_relIndex_map {A B : Type} [Group A] [Group B] (f : A →* B)
    {S L : Subgroup A} (hker : f.ker ⊓ L ≤ S) (hSL : S ≤ L) :
    (S.map f).relIndex (L.map f) = S.relIndex L := by
  have hkey : ∀ x : ↥L, f (x : A) ∈ S.map f ↔ (x : A) ∈ S := by
    intro x
    exact ⟨fun hx => w183K3Dyn_mem_of_map_mem f hker hSL x.2 hx,
      fun hx => Subgroup.mem_map.mpr ⟨(x : A), hx, rfl⟩⟩
  let g : ↥L →* ↥(L.map f) := f.subgroupMap L
  have hcomap : ((S.map f).subgroupOf (L.map f)).comap g = S.subgroupOf L := by
    ext x
    exact hkey x
  calc (S.map f).relIndex (L.map f)
      = ((S.map f).subgroupOf (L.map f)).index := rfl
    _ = (((S.map f).subgroupOf (L.map f)).comap g).index := by
          rw [Subgroup.index_comap (H := (S.map f).subgroupOf (L.map f)) g,
            MonoidHom.range_eq_top.mpr (f.subgroupMap_surjective L),
            Subgroup.relIndex_top_right]
    _ = (S.subgroupOf L).index := by rw [hcomap]
    _ = S.relIndex L := rfl

private theorem w183K3Dyn_relIndex_sup_of_central {A : Type} [Group A]
    {N L₀ S : Subgroup A} (hNL₀ : N ⊓ L₀ ≤ S) (hSL₀ : S ≤ L₀)
    (hcent : ∀ z ∈ N, ∀ l ∈ L₀, z * l = l * z) :
    (S ⊔ N).relIndex (L₀ ⊔ N) = S.relIndex L₀ := by
  have hnorm : L₀ ⊔ N ≤ Subgroup.normalizer (N : Set A) :=
    sup_le (w183K3Dyn_le_normalizer_of_comm hcent) Subgroup.le_normalizer
  haveI : (N.subgroupOf (L₀ ⊔ N)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hker : (QuotientGroup.mk' (N.subgroupOf (L₀ ⊔ N))).ker ⊓
      (L₀.subgroupOf (L₀ ⊔ N)) ≤ S.subgroupOf (L₀ ⊔ N) := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨hxN, hxL₀⟩ := Subgroup.mem_inf.mp hx
    exact hNL₀ (Subgroup.mem_inf.mpr ⟨hxN, hxL₀⟩)
  have hgen := w183K3Dyn_relIndex_map (f := QuotientGroup.mk' (N.subgroupOf (L₀ ⊔ N)))
    (S := S.subgroupOf (L₀ ⊔ N)) (L := L₀.subgroupOf (L₀ ⊔ N)) hker
    (Subgroup.subgroupOf_mono (L₀ ⊔ N) hSL₀)
  have h1 : (S.subgroupOf (L₀ ⊔ N)).relIndex (L₀.subgroupOf (L₀ ⊔ N)) = S.relIndex L₀ :=
    Subgroup.relIndex_subgroupOf (H := S) (K := L₀) (L := L₀ ⊔ N) le_sup_left
  rw [← h1, ← hgen]
  rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk',
    (Subgroup.subgroupOf_sup (A := S) (A' := N) (B := L₀ ⊔ N)
      (hSL₀.trans le_sup_left) le_sup_right).symm,
    (Subgroup.subgroupOf_sup (A := L₀) (A' := N) (B := L₀ ⊔ N)
      le_sup_left le_sup_right).symm,
    Subgroup.subgroupOf_self]
  have hsub := Subgroup.relIndex_subgroupOf (H := S ⊔ N) (K := L₀ ⊔ N) (L := L₀ ⊔ N) le_rfl
  rw [Subgroup.subgroupOf_self] at hsub
  exact hsub.symm

theorem actsOnDynkinMod_map {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    {N L : Subgroup A} {t : A} (hker : f.ker ⊓ L ≤ N) (h : ActsOnDynkinMod N L t) :
    ActsOnDynkinMod (N.map f) (L.map f) (f t) := by
  obtain ⟨htN, P, hP, hmove⟩ := h
  obtain ⟨hNP, hPLt, hmax, S, hNS, hSL, hS2, hSodd, hSnorm⟩ := hP
  have hPL : P ≤ L := hPLt.le
  have htLmap : f t ∈ Subgroup.normalizer ((L.map f : Subgroup B) : Set B) :=
    Subgroup.le_normalizer_map f (Subgroup.mem_map.mpr ⟨t, htN, rfl⟩)
  refine ⟨htLmap, P.map f, ⟨Subgroup.map_mono hNP, ?_, ?_,
    S.map f, Subgroup.map_mono hNS, Subgroup.map_mono hSL, ?_, ?_, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono hPL) ?_
    intro heq
    exact hPLt.not_ge fun l hl => w183K3Dyn_mem_of_map_mem f (hker.trans hNP) hPL hl
      (by rw [heq]; exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)
  · intro Y' hPY' hY'L
    have hP_le_Y : P ≤ Y'.comap f ⊓ L := by
      refine le_inf (fun p hp => Subgroup.mem_comap.mpr ?_) hPL
      exact hPY'.le (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
    have hY_ne : P ≠ Y'.comap f ⊓ L := by
      intro heq
      have hmap : (Y'.comap f ⊓ L).map f = P.map f := by rw [heq]
      rw [w183K3Dyn_map_comap_inf_eq f hY'L] at hmap
      exact hPY'.ne hmap.symm
    have hPY : P < Y'.comap f ⊓ L := lt_of_le_of_ne hP_le_Y hY_ne
    have hYL : Y'.comap f ⊓ L = L := hmax _ hPY inf_le_right
    exact (w183K3Dyn_map_comap_inf_eq f hY'L).symm.trans (by rw [hYL])
  · intro s' hs'
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨k, hk⟩ := hS2 s hsS
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map.mpr ⟨s ^ 2 ^ k, hk, rfl⟩⟩
  · rw [w183K3Dyn_relIndex_map f (hker.trans hNS) hSL]
    exact hSodd
  · intro y hy
    obtain ⟨hyL, hynorm⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hxL, rfl⟩ := Subgroup.mem_map.mp hyL
    have hxnorm : x ∈ Subgroup.normalizer (S : Set A) := by
      rw [Subgroup.mem_normalizer_iff] at hynorm ⊢
      intro s
      constructor
      · intro hs
        have hxsL : x * s * x⁻¹ ∈ L := L.mul_mem (L.mul_mem hxL (hSL hs)) (L.inv_mem hxL)
        have : f (x * s * x⁻¹) ∈ S.map f := by
          have h := (hynorm (f s)).mp (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
          simpa only [map_mul, map_inv] using h
        exact w183K3Dyn_mem_of_map_mem f (hker.trans hNS) hSL hxsL this
      · intro hs
        have hsL : s ∈ L := by
          have : s = x⁻¹ * (x * s * x⁻¹) * x := by group
          rw [this]
          exact L.mul_mem (L.mul_mem (L.inv_mem hxL) (hSL hs)) hxL
        have hfs : f s ∈ S.map f := by
          have hconj : f (x * s * x⁻¹) ∈ S.map f :=
            Subgroup.mem_map.mpr ⟨x * s * x⁻¹, hs, rfl⟩
          exact (hynorm (f s)).mpr (by simpa only [map_mul, map_inv] using hconj)
        exact w183K3Dyn_mem_of_map_mem f (hker.trans hNS) hSL hsL hfs
    exact Subgroup.mem_map.mpr ⟨x, hSnorm (Subgroup.mem_inf.mpr ⟨hxL, hxnorm⟩), rfl⟩
  · intro l' hl'
    obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hl'
    intro heq
    rw [← map_inv, ← map_mul] at heq
    have hg_norm : t⁻¹ * l ∈ Subgroup.normalizer (L : Set A) :=
      (Subgroup.normalizer (L : Set A)).mul_mem
        ((Subgroup.normalizer (L : Set A)).inv_mem htN) (Subgroup.le_normalizer hlL)
    have hconj_le_L : conjSubgroup P (t⁻¹ * l) ≤ L :=
      (Subgroup.map_mono hPL).trans (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr hg_norm))
    have hle : conjSubgroup P (t⁻¹ * l) ≤ P := by
      intro q hq
      have hfq : f q ∈ P.map f := by
        have hmem : f q ∈ conjSubgroup (P.map f) (f (t⁻¹ * l)) := by
          rw [mem_conjSubgroup_iff]
          refine Subgroup.mem_map.mpr
            ⟨t⁻¹ * l * q * (t⁻¹ * l)⁻¹, mem_conjSubgroup_iff.mp hq, ?_⟩
          simp only [map_mul, map_inv]
        rwa [heq] at hmem
      exact w183K3Dyn_mem_of_map_mem f (hker.trans hNP) hPL (hconj_le_L hq) hfq
    exact hmove l hlL (Subgroup.eq_of_le_of_card_ge hle (by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj (t⁻¹ * l)⁻¹).injective]))

private theorem w183K3Dyn_subgroupOf_map_subtype {A : Type} [Group A] {H : Subgroup A}
    (Y' : Subgroup ↥H) : (Y'.map H.subtype).subgroupOf H = Y' := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem actsOnDynkinMod_subgroupOf {A : Type} [Group A] [Finite A] {N L : Subgroup A}
    (H : Subgroup A) (hLH : L ≤ H) {t : A} (ht : t ∈ H) (h : ActsOnDynkinMod N L t) :
    ActsOnDynkinMod (N.subgroupOf H) (L.subgroupOf H) ⟨t, ht⟩ := by
  obtain ⟨htN, P, hP, hmove⟩ := h
  obtain ⟨hNP, hPLt, hmax, S, hNS, hSL, hS2, hSodd, hSnorm⟩ := hP
  have hPL : P ≤ L := hPLt.le
  have htN' : (⟨t, ht⟩ : ↥H) ∈
      Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hLH]
    exact Subgroup.mem_subgroupOf.mpr htN
  refine ⟨htN', P.subgroupOf H, ⟨Subgroup.subgroupOf_mono H hNP, ?_, ?_,
    S.subgroupOf H, Subgroup.subgroupOf_mono H hNS, Subgroup.subgroupOf_mono H hSL, ?_, ?_, ?_⟩,
    ?_⟩
  · refine lt_of_le_of_ne (Subgroup.subgroupOf_mono H hPL) ?_
    intro heq
    have hmap := congrArg (Subgroup.map H.subtype) heq
    rw [Subgroup.map_subgroupOf_eq_of_le (hPL.trans hLH),
      Subgroup.map_subgroupOf_eq_of_le hLH] at hmap
    exact hPLt.ne hmap
  · intro Y' hPY' hY'L
    have hP_le : P ≤ Y'.map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (hPL.trans hLH)]
      exact Subgroup.map_mono hPY'.le
    have hY_le : Y'.map H.subtype ≤ L := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
      exact Subgroup.map_mono hY'L
    have hne : P ≠ Y'.map H.subtype := by
      intro heq
      have : P.subgroupOf H = Y' := by rw [heq, w183K3Dyn_subgroupOf_map_subtype Y']
      exact hPY'.ne this
    have hPY : P < Y'.map H.subtype := lt_of_le_of_ne hP_le hne
    have hEq : Y'.map H.subtype = L := hmax _ hPY hY_le
    rw [← w183K3Dyn_subgroupOf_map_subtype Y', hEq]
  · intro s hs
    obtain ⟨k, hk⟩ := hS2 (s : A) hs
    exact ⟨k, by rw [Subgroup.mem_subgroupOf]; simpa using hk⟩
  · rw [Subgroup.relIndex_subgroupOf (H := S) (K := L) (L := H) hLH]
    exact hSodd
  · intro x hx
    obtain ⟨hxL, hxnorm⟩ := Subgroup.mem_inf.mp hx
    have hxnormA : (x : A) ∈ Subgroup.normalizer (S : Set A) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (hSL.trans hLH)] at hxnorm
      exact Subgroup.mem_subgroupOf.mp hxnorm
    exact Subgroup.mem_subgroupOf.mpr
      (hSnorm (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxL, hxnormA⟩))
  · intro l' hl'
    let l : A := (l' : A)
    let g : A := t⁻¹ * l
    have hlL : l ∈ L := hl'
    have hlH : l ∈ H := hLH hlL
    have hgH : g ∈ H := H.mul_mem (H.inv_mem ht) hlH
    have hgN : g ∈ Subgroup.normalizer (L : Set A) :=
      (Subgroup.normalizer (L : Set A)).mul_mem
        ((Subgroup.normalizer (L : Set A)).inv_mem htN) (Subgroup.le_normalizer hlL)
    have hsub : (⟨t, ht⟩ : ↥H)⁻¹ * l' = ⟨g, hgH⟩ := Subtype.ext rfl
    rw [hsub]
    intro heq
    have hconj : conjSubgroup (P.subgroupOf H) ⟨g, hgH⟩ = (conjSubgroup P g).subgroupOf H := by
      ext x
      simp only [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
      rfl
    have hconj_le_H : conjSubgroup P g ≤ H :=
      (Subgroup.map_mono hPL).trans
        ((le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr hgN)).trans hLH)
    have hmap := congrArg (Subgroup.map H.subtype) heq
    rw [hconj, Subgroup.map_subgroupOf_eq_of_le hconj_le_H,
      Subgroup.map_subgroupOf_eq_of_le (hPL.trans hLH)] at hmap
    exact hmove l hlL hmap

theorem actsOnDynkinMod_of_central {A : Type} [Group A] [Finite A] {N L₀ : Subgroup A} {t : A}
    (hcent : ∀ z ∈ N, ∀ l ∈ L₀ ⊔ N, z * l = l * z) (htL₀ : t ∈ Subgroup.normalizer (L₀ : Set A))
    (htN : t ∈ Subgroup.normalizer (N : Set A)) (h : ActsOnDynkinMod N (L₀ ⊔ N) t) :
    ActsOnDynkinMod (N ⊓ L₀) L₀ t := by
  obtain ⟨_htn, P, hP, hmove⟩ := h
  obtain ⟨hNP, hPLt, hmax, S, hNS, hSL, hS2, hSodd, hSnorm⟩ := hP
  have hPL : P ≤ L₀ ⊔ N := hPLt.le
  have hcent₀ : ∀ z ∈ N, ∀ l ∈ L₀, z * l = l * z :=
    fun z hz l hl => hcent z hz l ((le_sup_left : L₀ ≤ L₀ ⊔ N) hl)
  have hcomm : L₀ ≤ Subgroup.normalizer (N : Set A) :=
    w183K3Dyn_le_normalizer_of_comm hcent₀
  have hP_eq : (P ⊓ L₀) ⊔ N = P :=
    w183K3Dyn_eq_sup_inf_of_le_sup hcomm hNP hPL
  have hS_eq : (S ⊓ L₀) ⊔ N = S :=
    w183K3Dyn_eq_sup_inf_of_le_sup hcomm hNS hSL
  refine ⟨htL₀, P ⊓ L₀, ⟨le_inf (le_trans inf_le_left hNP) inf_le_right, ?_, ?_,
    S ⊓ L₀, le_inf (le_trans inf_le_left hNS) inf_le_right, inf_le_right, ?_, ?_, ?_⟩, ?_⟩
  · refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hL₀P : L₀ ≤ P := by rw [← heq]; exact inf_le_left
    exact hPLt.ne (le_antisymm hPL (sup_le hL₀P hNP))
  · intro Y hPY hYL₀
    have hYle : Y ⊔ N ≤ L₀ ⊔ N :=
      sup_le (hYL₀.trans (le_sup_left : L₀ ≤ L₀ ⊔ N)) le_sup_right
    have hP_le : P ≤ Y ⊔ N := by
      rw [← hP_eq]
      exact sup_le (hPY.le.trans (le_sup_left : Y ≤ Y ⊔ N)) le_sup_right
    have hne : P ≠ Y ⊔ N := by
      intro heq
      have hYP : Y ≤ P := by rw [heq]; exact le_sup_left
      have : Y = P ⊓ L₀ := le_antisymm (le_inf hYP hYL₀) hPY.le
      exact hPY.ne this.symm
    have hmaxY : Y ⊔ N = L₀ ⊔ N := hmax _ (lt_of_le_of_ne hP_le hne) hYle
    refine le_antisymm hYL₀ ?_
    intro a ha
    have ha_sup : a ∈ Y ⊔ N := by
      rw [hmaxY]; exact (le_sup_left : L₀ ≤ L₀ ⊔ N) ha
    have hYcomm : Y ≤ Subgroup.normalizer (N : Set A) := hYL₀.trans hcomm
    have ha_mul : a ∈ (Y : Set A) * (N : Set A) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y N hYcomm]
      exact ha_sup
    obtain ⟨y, hy, n, hn, hyn⟩ := Set.mem_mul.mp ha_mul
    have hnNL₀ : n ∈ N ⊓ L₀ := by
      refine ⟨hn, ?_⟩
      have : n = y⁻¹ * a := by rw [← hyn]; group
      rw [this]
      exact L₀.mul_mem (L₀.inv_mem (hYL₀ hy)) ha
    have hnY : n ∈ Y := (le_trans (le_inf (le_trans inf_le_left hNP) inf_le_right) hPY.le) hnNL₀
    have : a = y * n := hyn.symm
    rw [this]
    exact Y.mul_mem hy hnY
  · intro s hs
    obtain ⟨k, hk⟩ := hS2 s hs.1
    exact ⟨k, ⟨hk, L₀.pow_mem hs.2 (2 ^ k)⟩⟩
  · have h := w183K3Dyn_relIndex_sup_of_central (N := N) (L₀ := L₀) (S := S ⊓ L₀)
      (le_inf (le_trans inf_le_left hNS) inf_le_right) inf_le_right hcent₀
    rw [← h, hS_eq]
    exact hSodd
  · intro x hx
    obtain ⟨hxL₀, hxnorm₀⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ Subgroup.normalizer (N : Set A) := hcomm hxL₀
    have hxnormS : x ∈ Subgroup.normalizer (S : Set A) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hxnorm₀ ⊢
      rw [← hS_eq, Subgroup.map_sup, hxnorm₀, Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN]
    exact Subgroup.mem_inf.mpr
      ⟨hSnorm (Subgroup.mem_inf.mpr ⟨(le_sup_left : L₀ ≤ L₀ ⊔ N) hxL₀, hxnormS⟩), hxL₀⟩
  · intro l hl
    let g : A := t⁻¹ * l
    have hgN : g ∈ Subgroup.normalizer (N : Set A) :=
      (Subgroup.normalizer (N : Set A)).mul_mem
        ((Subgroup.normalizer (N : Set A)).inv_mem htN) (hcomm hl)
    intro heq
    have hconj_sup : conjSubgroup (P ⊓ L₀ ⊔ N) g =
        conjSubgroup (P ⊓ L₀) g ⊔ conjSubgroup N g := by
      simp only [conjSubgroup, Subgroup.map_sup]
    have hconjP : conjSubgroup P g = P := by
      rw [← hP_eq, hconj_sup, heq, conjSubgroup_eq_iff_mem_normalizer.mpr hgN]
    exact hmove l ((le_sup_left : L₀ ≤ L₀ ⊔ N) hl) hconjP

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
