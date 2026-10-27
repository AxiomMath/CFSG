module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.Timmesfeld.ARS.Sec8Restrict

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

private abbrev pullback {X X' : Type*} [Group X] [Group X'] {L : Subgroup X} {L' : Subgroup X'}
    (e : ↥L ≃* ↥L') (A' : Subgroup X') : Subgroup X :=
  ((A'.subgroupOf L').comap e.toMonoidHom).map L.subtype

private lemma pullback_le {X X' : Type*} [Group X] [Group X'] {L : Subgroup X}
    {L' : Subgroup X'} (e : ↥L ≃* ↥L') (A' : Subgroup X') : pullback e A' ≤ L :=
  (Subgroup.map_le_range L.subtype _).trans (le_of_eq (Subgroup.range_subtype L))

private lemma conjSubgroup_le_of_le_of_mem {X : Type*} [Group X] {A H : Subgroup X}
    {g : X} (hA : A ≤ H) (hg : g ∈ H) : conjSubgroup A g ≤ H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group]
  exact H.mul_mem (H.mul_mem (H.inv_mem hg) (hA hx)) hg

private lemma mem_pullback_subgroupOf_comap_map {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L') (A' : Subgroup X')
    {x : X} (hx : x ∈ L) :
    x ∈ pullback e A' ↔ (e ⟨x, hx⟩ : X') ∈ A' := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hy
    have hxy : y = ⟨x, hx⟩ := Subtype.ext hyx
    simpa [hxy] using hy
  · intro hx'
    exact ⟨⟨x, hx⟩, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hx', rfl⟩

private lemma card_pullback_subgroupOf_comap_map {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L') (A' : Subgroup X')
    (hA' : A' ≤ L') :
    Nat.card (pullback e A') = Nat.card A' := by
  rw [Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.comap_equiv_eq_map_symm' e (A'.subgroupOf L'),
    Subgroup.card_map_of_injective e.symm.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA').toEquiv

private lemma map_conjSubgroup_subgroupOf_map {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {S : Subgroup X} {S' : Subgroup X'}
    (hS : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') (g : ↥L) :
    ((conjSubgroup S (g : X)).subgroupOf L).map e.toMonoidHom =
      (conjSubgroup S' (e g : X')).subgroupOf L' := by
  have hleft : (conjSubgroup S (g : X)).subgroupOf L = conjSubgroup (S.subgroupOf L) g := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
      (conjSubgroup_le_of_le_of_mem hSL g.2),
      map_conjSubgroup_subgroupOf' hSL g.2]
  have hright : (conjSubgroup S' (e g : X')).subgroupOf L' =
      conjSubgroup (S'.subgroupOf L') (e g) := by
    apply Subgroup.map_injective L'.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
      (conjSubgroup_le_of_le_of_mem hS'L (e g).2),
      map_conjSubgroup_subgroupOf' hS'L (e g).2]
  rw [hleft, hright, ← map_conjSubgroup_hom e.toMonoidHom (S.subgroupOf L) g, hS]
  rfl

private lemma mem_centralizer_map_iff {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {S : Subgroup X} {S' : Subgroup X'} (hSL : S ≤ L) (hS'L : S' ≤ L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S') (x : ↥L) :
    (e x : X') ∈ Subgroup.centralizer (S' : Set X') ↔
      (x : X) ∈ Subgroup.centralizer (S : Set X) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have hsL : s ∈ L := hSL hs
    have hs' : (e ⟨s, hsL⟩ : X') ∈ S' := (hS ⟨s, hsL⟩).mp hs
    have hc := h (e ⟨s, hsL⟩) hs'
    have hc' : (⟨s, hsL⟩ : ↥L) * x = x * ⟨s, hsL⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact Subtype.ext hc
    exact congrArg Subtype.val hc'
  · intro h s' hs'
    let s : ↥L := e.symm ⟨s', hS'L hs'⟩
    have hes : (e s : X') = s' := congrArg Subtype.val (e.apply_symm_apply _)
    have hsS : (s : X) ∈ S := (hS s).mpr (by rw [hes]; exact hs')
    have hc : (s : X) * (x : X) = (x : X) * (s : X) := h s hsS
    have hc' : s * x = x * s := Subtype.ext hc
    have hmap := congrArg (fun z : ↥L' => (z : X')) (congrArg e hc')
    rw [map_mul, map_mul] at hmap
    simp only [Subgroup.coe_mul] at hmap
    rw [hes] at hmap
    exact hmap

private lemma isPGroup_sup_conjSubgroup_map_iff {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {S : Subgroup X} {S' : Subgroup X'}
    (hS : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') (g : ↥L) :
    IsPGroup 2 ↥(S ⊔ conjSubgroup S (g : X)) ↔
      IsPGroup 2 ↥(S' ⊔ conjSubgroup S' (e g : X')) := by
  have hgL : conjSubgroup S (g : X) ≤ L :=
    conjSubgroup_le_of_le_of_mem hSL g.2
  have hg'L : conjSubgroup S' (e g : X') ≤ L' :=
    conjSubgroup_le_of_le_of_mem hS'L (e g).2
  have hAL : S ⊔ conjSubgroup S (g : X) ≤ L := sup_le hSL hgL
  have hA'L : S' ⊔ conjSubgroup S' (e g : X') ≤ L' := sup_le hS'L hg'L
  have hmap : ((S ⊔ conjSubgroup S (g : X)).subgroupOf L).map e.toMonoidHom =
      (S' ⊔ conjSubgroup S' (e g : X')).subgroupOf L' := by
    rw [Subgroup.subgroupOf_sup hSL hgL, Subgroup.map_sup, hS,
      map_conjSubgroup_subgroupOf_map e hS hSL hS'L g, Subgroup.subgroupOf_sup hS'L hg'L]
  have hEquiv : ↥((S ⊔ conjSubgroup S (g : X)).subgroupOf L) ≃*
      ↥((S' ⊔ conjSubgroup S' (e g : X')).subgroupOf L') :=
    (MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr hmap)
  constructor
  · intro h
    exact ((h.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm).of_equiv hEquiv).of_equiv
      (Subgroup.subgroupOfEquivOfLe hA'L)
  · intro h
    exact ((h.of_equiv (Subgroup.subgroupOfEquivOfLe hA'L).symm).of_equiv hEquiv.symm).of_equiv
      (Subgroup.subgroupOfEquivOfLe hAL)

private lemma subgroupOf_conjSubgroup_eq {X : Type*} [Group X] {L A : Subgroup X} (hA : A ≤ L)
    (g : ↥L) : (conjSubgroup A (g : X)).subgroupOf L = conjSubgroup (A.subgroupOf L) g := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    (conjSubgroup_le_of_le_of_mem hA g.2),
    map_conjSubgroup_subgroupOf' hA g.2]

private lemma mem_normalizer_of_map_mem_normalizer {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {Y : Subgroup X} {Y' : Subgroup X'} (hYle : Y ≤ L)
    (hYmem : ∀ {y : X} (hy : y ∈ L), y ∈ Y ↔ (e ⟨y, hy⟩ : X') ∈ Y') {x : ↥L}
    (h : (e x : X') ∈ Subgroup.normalizer (Y' : Set X')) :
    (x : X) ∈ Subgroup.normalizer (Y : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyL : y ∈ L := hYle hy
    have hy' : (e ⟨y, hyL⟩ : X') ∈ Y' := (hYmem hyL).mp hy
    have hconj' : (e x : X') * (e ⟨y, hyL⟩ : X') * (e x : X')⁻¹ ∈ Y' :=
      (Subgroup.mem_normalizer_iff.mp h _).mp hy'
    have hmem : (x : X) * y * (x : X)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem x.2 hyL) (L.inv_mem x.2)
    have he : (e ⟨(x : X) * y * (x : X)⁻¹, hmem⟩ : X') =
        (e x : X') * (e ⟨y, hyL⟩ : X') * (e x : X')⁻¹ := by
      have hsub : (⟨(x : X) * y * (x : X)⁻¹, hmem⟩ : ↥L) = x * ⟨y, hyL⟩ * x⁻¹ := by
        ext
        rfl
      rw [hsub]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [hYmem hmem, he]
    exact hconj'
  · intro hy
    have hmem : (x : X) * y * (x : X)⁻¹ ∈ L := hYle hy
    have hyL : y ∈ L := by
      rw [show y = (x : X)⁻¹ * ((x : X) * y * (x : X)⁻¹) * (x : X) by group]
      exact L.mul_mem (L.mul_mem (L.inv_mem x.2) hmem) x.2
    have he : (e ⟨(x : X) * y * (x : X)⁻¹, hmem⟩ : X') =
        (e x : X') * (e ⟨y, hyL⟩ : X') * (e x : X')⁻¹ := by
      have hsub : (⟨(x : X) * y * (x : X)⁻¹, hmem⟩ : ↥L) = x * ⟨y, hyL⟩ * x⁻¹ := by
        ext
        rfl
      rw [hsub]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    have hconj' : (e x : X') * (e ⟨y, hyL⟩ : X') * (e x : X')⁻¹ ∈ Y' := by
      rw [← he]
      exact (hYmem hmem).mp hy
    exact (hYmem hyL).mpr ((Subgroup.mem_normalizer_iff.mp h _).mpr hconj')

private lemma map_mem_normalizer_of_mem_normalizer {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {Y : Subgroup X} {Y' : Subgroup X'} (hYle : Y ≤ L) (hY'le : Y' ≤ L')
    (hYmem : ∀ {y : X} (hy : y ∈ L), y ∈ Y ↔ (e ⟨y, hy⟩ : X') ∈ Y') {x : ↥L}
    (h : (x : X) ∈ Subgroup.normalizer (Y : Set X)) :
    (e x : X') ∈ Subgroup.normalizer (Y' : Set X') := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y'
  constructor
  · intro hy'
    have hy'L : y' ∈ L' := hY'le hy'
    let y : ↥L := e.symm ⟨y', hy'L⟩
    have hey : (e y : X') = y' := congrArg Subtype.val (e.apply_symm_apply _)
    have hy : (y : X) ∈ Y := (hYmem y.2).mpr (by rw [hey]; exact hy')
    have hconj : (x : X) * (y : X) * (x : X)⁻¹ ∈ Y := (h _).mp hy
    have he : (e ⟨(x : X) * (y : X) * (x : X)⁻¹, hYle hconj⟩ : X') =
        (e x : X') * y' * (e x : X')⁻¹ := by
      have hsub : (⟨(x : X) * (y : X) * (x : X)⁻¹, hYle hconj⟩ : ↥L) = x * y * x⁻¹ := by
        ext
        rfl
      rw [hsub]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, hey]
    rw [← he]
    exact (hYmem (hYle hconj)).mp hconj
  · intro hy'
    have hconjL : (e x : X') * y' * (e x : X')⁻¹ ∈ L' := hY'le hy'
    have hy'L : y' ∈ L' := by
      rw [show y' = (e x : X')⁻¹ * ((e x : X') * y' * (e x : X')⁻¹) * (e x : X') by group]
      exact L'.mul_mem (L'.mul_mem (L'.inv_mem (e x).2) hconjL) (e x).2
    let y : ↥L := e.symm ⟨y', hy'L⟩
    have hey : (e y : X') = y' := congrArg Subtype.val (e.apply_symm_apply _)
    have hmem : (x : X) * (y : X) * (x : X)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem x.2 y.2) (L.inv_mem x.2)
    have he : (e ⟨(x : X) * (y : X) * (x : X)⁻¹, hmem⟩ : X') =
        (e x : X') * y' * (e x : X')⁻¹ := by
      have hsub : (⟨(x : X) * (y : X) * (x : X)⁻¹, hmem⟩ : ↥L) = x * y * x⁻¹ := by
        ext
        rfl
      rw [hsub]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, hey]
    have hxyY : (x : X) * (y : X) * (x : X)⁻¹ ∈ Y := by
      rw [hYmem hmem, he]
      exact hy'
    have hyY : (y : X) ∈ Y := (h _).mpr hxyY
    rw [← hey]
    exact (hYmem y.2).mp hyY

private lemma mem_normalizer_map_iff {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L')
    {Y : Subgroup X} {Y' : Subgroup X'} (hYle : Y ≤ L) (hY'le : Y' ≤ L')
    (hYmem : ∀ {y : X} (hy : y ∈ L), y ∈ Y ↔ (e ⟨y, hy⟩ : X') ∈ Y') {x : ↥L} :
    (e x : X') ∈ Subgroup.normalizer (Y' : Set X') ↔
      (x : X) ∈ Subgroup.normalizer (Y : Set X) :=
  ⟨mem_normalizer_of_map_mem_normalizer e hYle hYmem,
    map_mem_normalizer_of_mem_normalizer e hYle hY'le hYmem⟩

private lemma map_subgroupOf_of_mem_iff {X X' : Type*} [Group X] [Group X']
    {L S : Subgroup X} {L' S' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S') :
    (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L' := by
  ext x
  rw [show x = e (e.symm x) from (e.apply_symm_apply x).symm]
  change e.toMonoidHom (e.symm x) ∈ Subgroup.map e.toMonoidHom (S.subgroupOf L) ↔
    e (e.symm x) ∈ S'.subgroupOf L'
  rw [Subgroup.mem_map_iff_mem e.injective, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hS (e.symm x)

private lemma card_s_of_mulEquiv {X X' : Type*} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') (hcard : Nat.card S' = 2) : Nat.card S = 2 := by
  calc Nat.card S = Nat.card (S.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).symm
    _ = Nat.card ((S.subgroupOf L).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (S'.subgroupOf L') := by rw [hSmap]
    _ = Nat.card S' := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'L).toEquiv
    _ = 2 := hcard

private lemma isElemAbelian_pullback {X X' : Type*} [Group X] [Group X'] {L : Subgroup X}
    {L' : Subgroup X'} (e : ↥L ≃* ↥L') {p : ℕ} {Y' : Subgroup X'}
    (h : IsElemAbelian p Y') : IsElemAbelian p (pullback e Y') :=
  ((h.subgroupOf L').comap (f := e.toMonoidHom) e.injective).map L.subtype

private lemma s_le_pullback {X X' : Type*} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' Y' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S') (hSL : S ≤ L) (hS'L : S' ≤ L')
    (hYmem : ∀ {y : X} (hy : y ∈ L), y ∈ pullback e Y' ↔ (e ⟨y, hy⟩ : X') ∈ Y')
    (hnorm : S' ≤ Subgroup.normalizer (Y' : Set X')) :
    S ≤ Subgroup.normalizer (pullback e Y' : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro s hs y hy
  have hsL : s ∈ L := hSL hs
  have hyL : y ∈ L := pullback_le e Y' hy
  have hs' : (e ⟨s, hsL⟩ : X') ∈ S' := (hS ⟨s, hsL⟩).mp hs
  have hy' : (e ⟨y, hyL⟩ : X') ∈ Y' := (hYmem hyL).mp hy
  have hconj' : (e ⟨s, hsL⟩ : X') * (e ⟨y, hyL⟩ : X') * (e ⟨s, hsL⟩ : X')⁻¹ ∈ Y' :=
    (Subgroup.le_normalizer_iff.mp hnorm) _ hs' _ hy'
  have hmemL : (⟨s * y * s⁻¹, L.mul_mem (L.mul_mem hsL hyL) (L.inv_mem hsL)⟩ : ↥L) =
      ⟨s, hsL⟩ * ⟨y, hyL⟩ * (⟨s, hsL⟩ : ↥L)⁻¹ := by
    ext
    rfl
  refine (hYmem (L.mul_mem (L.mul_mem hsL hyL) (L.inv_mem hsL))).mpr ?_
  rw [show (e ⟨s * y * s⁻¹, L.mul_mem (L.mul_mem hsL hyL) (L.inv_mem hsL)⟩ : X') =
      (e ⟨s, hsL⟩ : X') * (e ⟨y, hyL⟩ : X') * (e ⟨s, hsL⟩ : X')⁻¹ from by
    rw [hmemL]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]]
  exact hconj'

private lemma z_eq_pullback {X X' : Type*} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' Y' Z' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S') (hSL : S ≤ L) (hS'L : S' ≤ L')
    (hYmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e Y' ↔ (e ⟨x, hx⟩ : X') ∈ Y')
    (hZmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e Z' ↔ (e ⟨x, hx⟩ : X') ∈ Z')
    (hZ'eq : Z' = Y' ⊓ Subgroup.centralizer (S' : Set X')) :
    pullback e Z' = pullback e Y' ⊓ Subgroup.centralizer (S : Set X) := by
  have hZ'Y' : Z' ≤ Y' := by
    rw [hZ'eq]
    exact inf_le_left
  have hYle : pullback e Y' ≤ L := pullback_le e Y'
  have hZle : pullback e Z' ≤ L := pullback_le e Z'
  ext x
  constructor
  · intro hxZ
    have hxL : x ∈ L := hZle hxZ
    have hx' : (e ⟨x, hxL⟩ : X') ∈ Z' := (hZmem hxL).mp hxZ
    have hx'C : (e ⟨x, hxL⟩ : X') ∈ Subgroup.centralizer (S' : Set X') := by
      rw [hZ'eq] at hx'
      exact hx'.2
    exact ⟨(hYmem hxL).mpr (hZ'Y' hx'),
      (mem_centralizer_map_iff e hSL hS'L hS ⟨x, hxL⟩).mp hx'C⟩
  · rintro ⟨hxY, hxC⟩
    have hxL : x ∈ L := hYle hxY
    have hx'Y : (e ⟨x, hxL⟩ : X') ∈ Y' := (hYmem hxL).mp hxY
    have hx'C : (e ⟨x, hxL⟩ : X') ∈ Subgroup.centralizer (S' : Set X') :=
      (mem_centralizer_map_iff e hSL hS'L hS ⟨x, hxL⟩).mpr hxC
    exact (hZmem hxL).mpr (by rw [hZ'eq]; exact ⟨hx'Y, hx'C⟩)

private lemma card_z_pullback {X X' : Type*} [Group X] [Group X'] {L : Subgroup X}
    {L' Y' Z' : Subgroup X'} {p : ℕ} (e : ↥L ≃* ↥L') (hY'L : Y' ≤ L') (hZ'L : Z' ≤ L')
    (hcard : Nat.card Z' * p = Nat.card Y') :
    Nat.card (pullback e Z') * p = Nat.card (pullback e Y') := by
  rw [card_pullback_subgroupOf_comap_map e Z' hZ'L,
    card_pullback_subgroupOf_comap_map e Y' hY'L]
  exact hcard

private lemma exists_preimage_mem_conjSubgroup {X X' : Type*} [Group X] [Group X']
    {L S : Subgroup X} {L' S' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') {g' : X'} (hg' : g' ∈ L')
    (hP : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')) {y : X'}
    (hy : y ∈ conjSubgroup S' g') :
    ∃ hyL : y ∈ L', ((e.symm ⟨y, hyL⟩ : ↥L) : X) ∈
      (⨆ (g : X) (_ : g ∈ L) (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g) := by
  have hyL' : y ∈ L' := conjSubgroup_le_of_le_of_mem hS'L hg' hy
  have hyS' : g' * y * g'⁻¹ ∈ S' := mem_conjSubgroup_iff.mp hy
  let g : ↥L := e.symm ⟨g', hg'⟩
  have hegb : (e g : X') = g' := congrArg Subtype.val (e.apply_symm_apply _)
  let y' : ↥L := e.symm ⟨y, hyL'⟩
  have hey : (e y' : X') = y := congrArg Subtype.val (e.apply_symm_apply _)
  have hyS : ((g * y' * g⁻¹ : ↥L) : X) ∈ S := by
    rw [hS]
    have hcoe : ((e (g * y' * g⁻¹) : ↥L') : X') = g' * y * g'⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hegb, hey]
    rw [hcoe]
    exact hyS'
  have hyConj : (y' : X) ∈ conjSubgroup S (g : X) := mem_conjSubgroup_iff.mpr hyS
  have hP' : IsPGroup 2 ↥(S ⊔ conjSubgroup S (g : X)) :=
    (isPGroup_sup_conjSubgroup_map_iff e hSmap hSL hS'L g).mpr (by rw [hegb]; exact hP)
  exact ⟨hyL', Subgroup.mem_iSup_of_mem (g : X)
    (Subgroup.mem_iSup_of_mem g.2 (Subgroup.mem_iSup_of_mem hP' hyConj))⟩

private lemma exists_preimage_of_mem_iSup {X X' : Type*} [Group X] [Group X']
    {L S : Subgroup X} {L' S' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') :
    ∀ x : X', x ∈ (⨆ (g' : X') (_ : g' ∈ L')
        (_ : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')), conjSubgroup S' g') →
      ∃ hx : x ∈ L', ((e.symm ⟨x, hx⟩ : ↥L) : X) ∈
        (⨆ (g : X) (_ : g ∈ L) (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g) := by
  intro x hx
  let C : X' → Prop := fun y => ∃ hy : y ∈ L', ((e.symm ⟨y, hy⟩ : ↥L) : X) ∈
    (⨆ (g : X) (_ : g ∈ L) (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g)
  have hone : C 1 := by
    refine ⟨L'.one_mem, ?_⟩
    have h1 : (e.symm (⟨1, L'.one_mem⟩ : ↥L') : ↥L) = 1 := by
      apply e.injective
      simp
    simpa [h1] using Subgroup.one_mem _
  have hmul : ∀ y z : X', C y → C z → C (y * z) := by
    rintro y z ⟨hyL', hySup⟩ ⟨hzL', hzSup⟩
    refine ⟨L'.mul_mem hyL' hzL', ?_⟩
    have hsub : (⟨y * z, L'.mul_mem hyL' hzL'⟩ : ↥L') = ⟨y, hyL'⟩ * ⟨z, hzL'⟩ :=
      Subtype.ext rfl
    have hpre : ((e.symm ⟨y * z, L'.mul_mem hyL' hzL'⟩ : ↥L) : X) =
        ((e.symm ⟨y, hyL'⟩ : ↥L) : X) * ((e.symm ⟨z, hzL'⟩ : ↥L) : X) := by
      rw [hsub, map_mul]
      rfl
    rw [hpre]
    exact Subgroup.mul_mem _ hySup hzSup
  refine Subgroup.iSup_induction (C := C)
    (fun g' : X' => ⨆ (_ : g' ∈ L'), ⨆ (_ : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')),
      conjSubgroup S' g') hx ?_ hone hmul
  intro g' y hy
  refine Subgroup.iSup_induction (C := C)
    (fun (_ : g' ∈ L') => ⨆ (_ : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')), conjSubgroup S' g')
    hy ?_ hone hmul
  intro hg' y hy
  refine Subgroup.iSup_induction (C := C)
    (fun (_ : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')) => conjSubgroup S' g') hy ?_ hone hmul
  intro hP y hy
  exact exists_preimage_mem_conjSubgroup e hS hSmap hSL hS'L hg' hP hy

private lemma z_le_pullback {X X' : Type*} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' Z' : Subgroup X'} (e : ↥L ≃* ↥L')
    (hS : ∀ x : ↥L, (x : X) ∈ S ↔ (e x : X') ∈ S')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L')
    (hZmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e Z' ↔ (e ⟨x, hx⟩ : X') ∈ Z')
    (hZ'le : Z' ≤ ⨆ (g' : X') (_ : g' ∈ L')
        (_ : IsPGroup 2 ↥(S' ⊔ conjSubgroup S' g')), conjSubgroup S' g') :
    pullback e Z' ≤ ⨆ (g : X) (_ : g ∈ L)
      (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g := by
  intro z hz
  have hzL : z ∈ L := pullback_le e Z' hz
  have hz' : (e ⟨z, hzL⟩ : X') ∈ Z' := (hZmem hzL).mp hz
  obtain ⟨hz'L', hzSup⟩ := exists_preimage_of_mem_iSup e hS hSmap hSL hS'L _ (hZ'le hz')
  have hzeq : ((e.symm ⟨e ⟨z, hzL⟩, hz'L'⟩ : ↥L) : X) = z := by
    have h1 : e.symm (⟨e ⟨z, hzL⟩, hz'L'⟩ : ↥L') = ⟨z, hzL⟩ := by
      apply e.injective
      simp
    rw [h1]
  rwa [hzeq] at hzSup

private lemma subgroupOf_pullback_map {X X' : Type*} [Group X] [Group X']
    {L : Subgroup X} {L' : Subgroup X'} (e : ↥L ≃* ↥L') (A' : Subgroup X')
    (hmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e A' ↔ (e ⟨x, hx⟩ : X') ∈ A') :
    ((pullback e A').subgroupOf L).map e.toMonoidHom = A'.subgroupOf L' := by
  ext x
  rw [show x = e (e.symm x) from (e.apply_symm_apply x).symm]
  change e.toMonoidHom (e.symm x) ∈ Subgroup.map e.toMonoidHom ((pullback e A').subgroupOf L) ↔
    e (e.symm x) ∈ A'.subgroupOf L'
  rw [Subgroup.mem_map_iff_mem e.injective, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hmem (e.symm x).2

private lemma map_conjSubgroup_pullback {X X' : Type*} [Group X] [Group X']
    {L B : Subgroup X} {L' : Subgroup X'} {B' : Subgroup ↥L'} (e : ↥L ≃* ↥L')
    (hBL : B ≤ L) (hB' : B' = (B.subgroupOf L).map e.toMonoidHom)
    {hL : ↥L} {h'L : ↥L'} (hehL : e hL = h'L) :
    ((conjSubgroup B (hL : X)).subgroupOf L).map e.toMonoidHom = conjSubgroup B' h'L := by
  rw [subgroupOf_conjSubgroup_eq hBL hL, ← map_conjSubgroup_hom e.toMonoidHom (B.subgroupOf L) hL,
    ← hB', show e.toMonoidHom hL = h'L from hehL]

private lemma map_conjSubgroup_map_subtype {X' : Type*} [Group X'] {L' : Subgroup X'}
    {B' : Subgroup ↥L'} {B'' : Subgroup X'}
    (hB'' : B'' = B'.map L'.subtype) (h'L : ↥L') :
    (conjSubgroup B' h'L).map L'.subtype = conjSubgroup B'' (h'L : X') := by
  rw [← map_conjSubgroup_hom L'.subtype B' h'L, ← hB'']
  rfl

private lemma conjSubgroup_pullback_ne {X X' : Type*} [Group X] [Group X']
    {L B : Subgroup X} {L' : Subgroup X'} {B' : Subgroup ↥L'} {B'' Z' : Subgroup X'}
    (e : ↥L ≃* ↥L')
    (hBL : B ≤ L) (hB' : B' = (B.subgroupOf L).map e.toMonoidHom)
    (hB'' : B'' = B'.map L'.subtype)
    (hZsub : ((pullback e Z').subgroupOf L).map e.toMonoidHom = Z'.subgroupOf L')
    (hZ'L : Z' ≤ L') {hL : ↥L} {h'L : ↥L'} (hehL : e hL = h'L)
    (hne : conjSubgroup B'' (h'L : X') ≠ Z') :
    conjSubgroup B (hL : X) ≠ pullback e Z' := by
  intro heq
  apply hne
  have hmapB := map_conjSubgroup_pullback e hBL hB' hehL
  have h1 : ((conjSubgroup B (hL : X)).subgroupOf L).map e.toMonoidHom =
      ((pullback e Z').subgroupOf L).map e.toMonoidHom := by
    rw [heq]
  rw [hmapB, hZsub] at h1
  have h2 : (conjSubgroup B' h'L).map L'.subtype = (Z'.subgroupOf L').map L'.subtype := by
    rw [h1]
  rw [map_conjSubgroup_map_subtype hB'' h'L, Subgroup.map_subgroupOf_eq_of_le hZ'L] at h2
  exact h2

private lemma commutator_not_le_conjSubgroup_pullback {X X' : Type*} [Group X] [Group X']
    {L S B : Subgroup X} {L' S' Y' : Subgroup X'} {B' : Subgroup ↥L'} {B'' : Subgroup X'}
    (e : ↥L ≃* ↥L')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L')
    (hYsub : ((pullback e Y').subgroupOf L).map e.toMonoidHom = Y'.subgroupOf L')
    (hY'L : Y' ≤ L')
    (hB' : B' = (B.subgroupOf L).map e.toMonoidHom) (hB'' : B'' = B'.map L'.subtype)
    (hBL : B ≤ L) {hL : ↥L} {h'L : ↥L'} (hehL : e hL = h'L)
    (hcomm : ¬ ⁅Y', S'⁆ ≤ conjSubgroup B'' (h'L : X')) :
    ¬ ⁅pullback e Y', S⁆ ≤ conjSubgroup B (hL : X) := by
  intro hle
  apply hcomm
  have hmapB := map_conjSubgroup_pullback e hBL hB' hehL
  have h1 : ((⁅pullback e Y', S⁆).subgroupOf L).map e.toMonoidHom ≤
      ((conjSubgroup B (hL : X)).subgroupOf L).map e.toMonoidHom :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono L hle)
  have hLHS : ((⁅pullback e Y', S⁆).subgroupOf L).map e.toMonoidHom =
      ⁅Y'.subgroupOf L', S'.subgroupOf L'⁆ := by
    rw [← CFSG.Timmesfeld.ARS.Restrict.commutator_subgroupOf (pullback_le e Y') hSL,
      Subgroup.map_commutator, hYsub, hSmap]
  rw [hLHS, hmapB] at h1
  have h2 : (⁅Y'.subgroupOf L', S'.subgroupOf L'⁆).map L'.subtype ≤
      (conjSubgroup B' h'L).map L'.subtype := Subgroup.map_mono h1
  have h2L : (⁅Y'.subgroupOf L', S'.subgroupOf L'⁆).map L'.subtype = ⁅Y', S'⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hY'L,
      Subgroup.map_subgroupOf_eq_of_le hS'L]
  rw [h2L, map_conjSubgroup_map_subtype hB'' h'L] at h2
  exact h2

private lemma exists_conj_pullback {X X' : Type*} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' Y' Z' : Subgroup X'} {p : ℕ} (e : ↥L ≃* ↥L')
    (hSmap : (S.subgroupOf L).map e.toMonoidHom = S'.subgroupOf L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') (hY'L : Y' ≤ L') (hZ'L : Z' ≤ L')
    (hYmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e Y' ↔ (e ⟨x, hx⟩ : X') ∈ Y')
    (hZmem : ∀ {x : X} (hx : x ∈ L), x ∈ pullback e Z' ↔ (e ⟨x, hx⟩ : X') ∈ Z')
    (hYcard : Nat.card (pullback e Y') = Nat.card Y')
    (hex : ∀ B' : Subgroup X', B' ≤ Y' → Nat.card B' * p = Nat.card Y' →
      ∃ h' ∈ L', h' ∈ Subgroup.normalizer (Y' : Set X') ∧ conjSubgroup B' h' ≠ Z' ∧
        ¬ ⁅Y', S'⁆ ≤ conjSubgroup B' h') :
    ∀ B : Subgroup X, B ≤ pullback e Y' → Nat.card B * p = Nat.card (pullback e Y') →
      ∃ h ∈ L, h ∈ Subgroup.normalizer (pullback e Y' : Set X) ∧
        conjSubgroup B h ≠ pullback e Z' ∧
        ¬ ⁅pullback e Y', S⁆ ≤ conjSubgroup B h := by
  intro B hBY hBcard
  have hBL : B ≤ L := hBY.trans (pullback_le e Y')
  have hYsub : ((pullback e Y').subgroupOf L).map e.toMonoidHom = Y'.subgroupOf L' :=
    subgroupOf_pullback_map e Y' fun hy => hYmem hy
  have hZsub : ((pullback e Z').subgroupOf L).map e.toMonoidHom = Z'.subgroupOf L' :=
    subgroupOf_pullback_map e Z' fun hx => hZmem hx
  set B' : Subgroup ↥L' := (B.subgroupOf L).map e.toMonoidHom with hB'
  set B'' : Subgroup X' := B'.map L'.subtype with hB''
  have hB''Y' : B'' ≤ Y' := by
    rintro b ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact (hYmem z.2).mp (hBY (Subgroup.mem_subgroupOf.mp hz))
  have hB''card : Nat.card B'' = Nat.card B := by
    rw [hB'', hB', Subgroup.card_map_of_injective L'.subtype_injective,
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hB''p : Nat.card B'' * p = Nat.card Y' := by
    rw [hB''card, ← hYcard]
    exact hBcard
  obtain ⟨h', hh'L', hh'norm', hne', hcomm'⟩ := hex B'' hB''Y' hB''p
  let h'L : ↥L' := ⟨h', hh'L'⟩
  let hL : ↥L := e.symm h'L
  have hehL : e hL = h'L := e.apply_symm_apply h'L
  have hnorm : (hL : X) ∈ Subgroup.normalizer (pullback e Y' : Set X) := by
    have hnorm' : (e hL : X') ∈ Subgroup.normalizer (Y' : Set X') := by
      rw [show (e hL : X') = h' from congrArg Subtype.val hehL]
      exact hh'norm'
    exact (mem_normalizer_map_iff e (pullback_le e Y') hY'L hYmem).mp hnorm'
  exact ⟨(hL : X), hL.2, hnorm,
    conjSubgroup_pullback_ne e hBL hB' hB'' hZsub hZ'L hehL hne',
    commutator_not_le_conjSubgroup_pullback e hSmap hSL hS'L hYsub hY'L hB' hB'' hBL hehL hcomm'⟩

theorem SevenNineConfig.of_mulEquiv {X X' : Type} [Group X] [Group X'] {L S : Subgroup X}
    {L' S' Y' Z' : Subgroup X'} {p : ℕ} (h : SevenNineConfig L' S' p Y' Z') (e : ↥L ≃* ↥L')
    (hSL : S ≤ L) (hS'L : S' ≤ L') (hS : ∀ x : ↥L, (x : X) ∈ S ↔ ((e x : ↥L') : X') ∈ S') :
    SevenNineConfig L S p (((Y'.subgroupOf L').comap e.toMonoidHom).map L.subtype)
      (((Z'.subgroupOf L').comap e.toMonoidHom).map L.subtype) := by
  have hSmap := map_subgroupOf_of_mem_iff e hS
  have hY'L : Y' ≤ L' := h.le
  have hZ'L : Z' ≤ L' := by
    rw [h.z_eq]
    exact inf_le_left.trans h.le
  have hcard_s : Nat.card S = 2 := card_s_of_mulEquiv e hSmap hSL hS'L h.card_s
  have helemAbelian : IsElemAbelian p (pullback e Y') := isElemAbelian_pullback e h.elemAbelian
  have hs_le : S ≤ Subgroup.normalizer (pullback e Y' : Set X) :=
    s_le_pullback e hS hSL hS'L (fun hy => mem_pullback_subgroupOf_comap_map e Y' hy) h.s_le
  have hz_eq : pullback e Z' = pullback e Y' ⊓ Subgroup.centralizer (S : Set X) :=
    z_eq_pullback e hS hSL hS'L (fun hx => mem_pullback_subgroupOf_comap_map e Y' hx)
      (fun hx => mem_pullback_subgroupOf_comap_map e Z' hx) h.z_eq
  have hcard_z : Nat.card (pullback e Z') * p = Nat.card (pullback e Y') :=
    card_z_pullback e hY'L hZ'L h.card_z
  have hz_le : pullback e Z' ≤ ⨆ (g : X) (_ : g ∈ L)
      (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g :=
    z_le_pullback e hS hSmap hSL hS'L
      (fun hx => mem_pullback_subgroupOf_comap_map e Z' hx) h.z_le
  have hexists : ∀ B : Subgroup X, B ≤ pullback e Y' →
      Nat.card B * p = Nat.card (pullback e Y') →
      ∃ h ∈ L, h ∈ Subgroup.normalizer (pullback e Y' : Set X) ∧
        conjSubgroup B h ≠ pullback e Z' ∧ ¬ ⁅pullback e Y', S⁆ ≤ conjSubgroup B h :=
    exists_conj_pullback e hSmap hSL hS'L hY'L hZ'L
      (fun hx => mem_pullback_subgroupOf_comap_map e Y' hx)
      (fun hx => mem_pullback_subgroupOf_comap_map e Z' hx)
      (card_pullback_subgroupOf_comap_map e Y' hY'L)
      (fun B' hB'Y' hB'p => h.exists_conj B' hB'Y' hB'p)
  exact
    { prime := h.prime
      ne_two := h.ne_two
      card_s := hcard_s
      le := pullback_le e Y'
      elemAbelian := helemAbelian
      s_le := hs_le
      z_eq := hz_eq
      card_z := hcard_z
      z_le := hz_le
      exists_conj := hexists }

end CFSG.LocalAnalysis.WeakClosure81
