module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Y : Subgroup (LGL 2 V)}
  {G' : Type} [Group G']

@[expose] def imgOf (ψ : ↥Y →* G') (A : Subgroup (LGL 2 V)) : Subgroup G' :=
  (A.subgroupOf Y).map ψ

private theorem w183b2img_mem_imgOf {ψ : ↥Y →* G'} {C : Subgroup (LGL 2 V)} {t : LGL 2 V}
    (ht : t ∈ C) (hY : t ∈ Y) : ψ ⟨t, hY⟩ ∈ imgOf ψ C :=
  Subgroup.mem_map.mpr ⟨⟨t, hY⟩, show (⟨t, hY⟩ : ↥Y) ∈ C.subgroupOf Y from ht, rfl⟩

private theorem w183b2img_subgroupOf_le_subgroupOf_iff {A B : Subgroup (LGL 2 V)}
    (hA : A ≤ Y) : A.subgroupOf Y ≤ B.subgroupOf Y ↔ A ≤ B := by
  constructor
  · intro h a ha
    exact Subgroup.mem_subgroupOf.mp
      (h (show (⟨a, hA ha⟩ : ↥Y) ∈ A.subgroupOf Y from ha))
  · intro h
    exact Subgroup.subgroupOf_mono Y h

private theorem w183b2img_cj_le {A : Subgroup (LGL 2 V)} (hA : A ≤ Y) {y : LGL 2 V}
    (hy : y ∈ Y) : cj y A ≤ Y := by
  intro x hx
  rw [cj, Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact Y.mul_mem (Y.mul_mem hy (hA ha)) (Y.inv_mem hy)

private theorem w183b2img_subgroupOf_cj {A : Subgroup (LGL 2 V)} (hA : A ≤ Y) {y : LGL 2 V}
    (hy : y ∈ Y) :
    (cj y A).subgroupOf Y =
      (A.subgroupOf Y).map (MulAut.conj (⟨y, hy⟩ : ↥Y)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf, cj, Subgroup.mem_map] at hx
    obtain ⟨a, ha, hay⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨a, hA ha⟩,
      show (⟨a, hA ha⟩ : ↥Y) ∈ (A.subgroupOf Y) from ha, ?_⟩
    apply Subtype.ext
    show y * a * y⁻¹ = (x : LGL 2 V)
    simpa [MulAut.conj_apply] using hay
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, hay⟩ := hx
    rw [Subgroup.mem_subgroupOf, cj, Subgroup.mem_map]
    exact ⟨(a : LGL 2 V), Subgroup.mem_subgroupOf.mp ha,
      by simpa [MulAut.conj_apply] using congrArg Subtype.val hay⟩

private theorem w183b2img_isElemAbelian_subtype_iff {G : Type*} [Group G] (E : Subgroup G) :
    IsElemAbelian 2 E ↔ IsMulCommutative ↥E ∧ ∀ x : ↥E, x ^ 2 = 1 := by
  constructor
  · intro h
    exact ⟨h.1, fun x => Subtype.ext (by simpa using h.2 x.1 x.2)⟩
  · intro h
    exact ⟨h.1, fun x hx => congrArg Subtype.val (h.2 ⟨x, hx⟩)⟩

private theorem w183b2img_isElemAbelian_mulEquiv_iff {G H : Type*} [Group G] [Group H]
    {E : Subgroup G} {E' : Subgroup H} (e : E ≃* E') :
    IsElemAbelian 2 E' ↔ IsElemAbelian 2 E := by
  rw [w183b2img_isElemAbelian_subtype_iff E', w183b2img_isElemAbelian_subtype_iff E]
  constructor
  · intro h
    obtain ⟨hcomm, hpow⟩ := h
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff] at hcomm ⊢
      intro a b
      exact e.injective (by rw [map_mul, map_mul]; exact hcomm (e a) (e b))
    · intro a
      exact e.injective (by rw [map_pow, map_one]; exact hpow (e a))
  · intro h
    obtain ⟨hcomm, hpow⟩ := h
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff] at hcomm ⊢
      intro a b
      have hc : e.symm a * e.symm b = e.symm b * e.symm a := hcomm _ _
      calc a * b = e (e.symm a * e.symm b) := by
              rw [map_mul, e.apply_symm_apply a, e.apply_symm_apply b]
        _ = e (e.symm b * e.symm a) := by rw [hc]
        _ = b * a := by rw [map_mul, e.apply_symm_apply b, e.apply_symm_apply a]
    · intro a
      have h1 : (e.symm a : ↥E) ^ 2 = 1 := hpow (e.symm a)
      have h2 : e ((e.symm a : ↥E) ^ 2) = e 1 := congrArg e h1
      rwa [map_pow, map_one, e.apply_symm_apply] at h2

theorem imgOf_le_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {A B : Subgroup (LGL 2 V)}
    (hA : A ≤ Y) (hB : B ≤ Y) : imgOf ψ A ≤ imgOf ψ B ↔ A ≤ B := by
  rw [imgOf, imgOf]
  exact (Subgroup.map_le_map_iff_of_injective hψ).trans
    (w183b2img_subgroupOf_le_subgroupOf_iff hA)

theorem imgOf_card {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {A : Subgroup (LGL 2 V)}
    (hA : A ≤ Y) : Nat.card (imgOf ψ A) = Nat.card A := by
  rw [imgOf]
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (A.subgroupOf Y) ψ hψ).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem imgOf_cj (ψ : ↥Y →* G') {A : Subgroup (LGL 2 V)} (hA : A ≤ Y) {y : LGL 2 V}
    (hy : y ∈ Y) :
    imgOf ψ (cj y A) = (imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom := by
  have hcomp : (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom.comp ψ =
      ψ.comp (MulAut.conj (⟨y, hy⟩ : ↥Y)).toMonoidHom := by
    ext a
    simp [MulAut.conj_apply, map_mul]
  change ((cj y A).subgroupOf Y).map ψ =
    ((A.subgroupOf Y).map ψ).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom
  rw [w183b2img_subgroupOf_cj hA hy]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem w183b2img_mem_normalizer_imgOf_iff {ψ : ↥Y →* G'}
    (hψ : Function.Injective ψ) {B : Subgroup (LGL 2 V)} (hB : B ≤ Y) {x : LGL 2 V}
    (hx : x ∈ Y) :
    ψ ⟨x, hx⟩ ∈ Subgroup.normalizer ((imgOf ψ B : Subgroup G') : Set G') ↔
      x ∈ Subgroup.normalizer (B : Set (LGL 2 V)) := by
  have hcjB : cj x B ≤ Y := w183b2img_cj_le hB hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro hm
    have himg : imgOf ψ (cj x B) = imgOf ψ B := by
      rw [imgOf_cj ψ hB hx]
      exact hm
    have h1 : cj x B ≤ B := (imgOf_le_iff hψ hcjB hB).mp (le_of_eq himg)
    have h2 : B ≤ cj x B := (imgOf_le_iff hψ hB hcjB).mp (le_of_eq himg.symm)
    exact le_antisymm h1 h2
  · intro hm
    exact (imgOf_cj ψ hB hx).symm.trans (congrArg (imgOf ψ) hm)

theorem imgOf_normalizer_le_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A B : Subgroup (LGL 2 V)} (hA : A ≤ Y) (hB : B ≤ Y) :
    imgOf ψ A ≤ Subgroup.normalizer (imgOf ψ B : Set G') ↔
      A ≤ Subgroup.normalizer (B : Set (LGL 2 V)) := by
  rw [imgOf, imgOf, Subgroup.map_le_iff_le_comap,
    Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range ψ (B.subgroupOf Y)),
    Subgroup.comap_map_eq_self_of_injective hψ (B.subgroupOf Y),
    ← Subgroup.subgroupOf_normalizer_eq hB]
  exact w183b2img_subgroupOf_le_subgroupOf_iff hA

theorem imgOf_isElemAbelian_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A : Subgroup (LGL 2 V)} (hA : A ≤ Y) :
    IsElemAbelian 2 (imgOf ψ A) ↔ IsElemAbelian 2 A := by
  rw [imgOf, w183b2img_isElemAbelian_mulEquiv_iff
      (Subgroup.equivMapOfInjective (A.subgroupOf Y) ψ hψ),
    w183b2img_isElemAbelian_mulEquiv_iff (Subgroup.subgroupOfEquivOfLe hA)]

theorem imgOf_sup_inf {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {A B : Subgroup (LGL 2 V)}
    (hA : A ≤ Y) (hB : B ≤ Y) :
    imgOf ψ (A ⊔ B) = imgOf ψ A ⊔ imgOf ψ B ∧ imgOf ψ (A ⊓ B) = imgOf ψ A ⊓ imgOf ψ B := by
  refine ⟨?_, ?_⟩
  · rw [imgOf, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup, ← imgOf, ← imgOf]
  · rw [imgOf,
      show (A ⊓ B).subgroupOf Y = A.subgroupOf Y ⊓ B.subgroupOf Y from
        Subgroup.comap_inf A B Y.subtype,
      Subgroup.map_inf _ _ _ hψ, ← imgOf, ← imgOf]

private theorem w183b2img_relIndex_imgOf {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {S L : Subgroup (LGL 2 V)} (hSL : S ≤ L) (hL : L ≤ Y) :
    (imgOf ψ S).relIndex (imgOf ψ L) = S.relIndex L := by
  rw [imgOf, imgOf,
    Subgroup.relIndex_map_map_of_injective (S.subgroupOf Y) (L.subgroupOf Y) hψ,
    Subgroup.relIndex_subgroupOf (H := S) (K := L) (L := Y) hL]

theorem imgOf_mOfG {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {A B : Subgroup (LGL 2 V)}
    (hA : A ≤ Y) (hBA : B ≤ A) : mOfG (imgOf ψ A) (imgOf ψ B) = mOfG A B := by
  change Nat.log 2 ((imgOf ψ B).relIndex (imgOf ψ A)) = Nat.log 2 (B.relIndex A)
  rw [w183b2img_relIndex_imgOf hψ hBA hA]

private theorem w183b2img_imgOf_inf_normalizer {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A B : Subgroup (LGL 2 V)} (hA : A ≤ Y) (hB : B ≤ Y) :
    imgOf ψ A ⊓ Subgroup.normalizer ((imgOf ψ B : Subgroup G') : Set G') =
      imgOf ψ (A ⊓ Subgroup.normalizer (B : Set (LGL 2 V))) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxN⟩ := hx
    rw [imgOf, Subgroup.mem_map] at hxA
    obtain ⟨a, ha, rfl⟩ := hxA
    have haN : (a : LGL 2 V) ∈ Subgroup.normalizer (B : Set (LGL 2 V)) :=
      (w183b2img_mem_normalizer_imgOf_iff (ψ := ψ) hψ hB a.2).mp hxN
    exact w183b2img_mem_imgOf
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ha, haN⟩) a.2
  · intro x hx
    rw [imgOf, Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haInf := Subgroup.mem_subgroupOf.mp ha
    exact Subgroup.mem_inf.mpr
      ⟨w183b2img_mem_imgOf (Subgroup.mem_inf.mp haInf).1 a.2,
        (w183b2img_mem_normalizer_imgOf_iff (ψ := ψ) hψ hB a.2).mpr
          (Subgroup.mem_inf.mp haInf).2⟩

private noncomputable def w183b2img_barEquiv (ψ : ↥Y →* G') (hψ : Function.Injective ψ)
    {X : Subgroup (LGL 2 V)} (hX : X ≤ Y) : Bar2 X ≃* Bar2 (imgOf ψ X) :=
  let e : X ≃* imgOf ψ X :=
    (Subgroup.subgroupOfEquivOfLe hX).symm.trans
      (Subgroup.equivMapOfInjective (X.subgroupOf Y) ψ hψ)
  QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(imgOf ψ X)) e
    (CFSG.pCore_map_iso 2 e)

theorem w183b2img_pairQuotOK_iff {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {X : Subgroup (LGL 2 V)} (hX : X ≤ Y) (k₁ k₂ : ℕ) :
    PairQuotOK k₁ k₂ (imgOf ψ X) ↔ PairQuotOK k₁ k₂ X := by
  have hp : IsPGroup 2 (imgOf ψ X) ↔ IsPGroup 2 X := by
    let e : X ≃* imgOf ψ X :=
      (Subgroup.subgroupOfEquivOfLe hX).symm.trans
        (Subgroup.equivMapOfInjective (X.subgroupOf Y) ψ hψ)
    exact ⟨fun h => h.of_equiv e.symm, fun h => h.of_equiv e⟩
  have hcard : Nat.card (Bar2 (imgOf ψ X)) = Nat.card (Bar2 X) :=
    (Nat.card_congr (w183b2img_barEquiv ψ hψ hX).toEquiv).symm
  have hdih : (∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 (imgOf ψ X) ≃* DihedralGroup r)) ↔
      (∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 X ≃* DihedralGroup r)) :=
    exists_congr fun r => and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun ⟨f⟩ => ⟨(w183b2img_barEquiv ψ hψ hX).trans f⟩,
        fun ⟨f⟩ => ⟨(w183b2img_barEquiv ψ hψ hX).symm.trans f⟩⟩
  unfold PairQuotOK
  rw [hp, hcard, hdih]

theorem pairViolation_of_imgOf {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A : Subgroup (LGL 2 V)} (hA : A ≤ Y) {y : LGL 2 V} (hy : y ∈ Y) :
    PairViolation (imgOf ψ A) (ψ ⟨y, hy⟩) → PairViolation A y := by
  intro h
  have hcj : cj y A ≤ Y := w183b2img_cj_le hA hy
  have hinf1 : imgOf ψ A ⊓
      Subgroup.normalizer (((imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom :
        Subgroup G') : Set G') =
      imgOf ψ (A ⊓ Subgroup.normalizer (cj y A : Set (LGL 2 V))) := by
    rw [← imgOf_cj ψ hA hy]
    exact w183b2img_imgOf_inf_normalizer hψ hA hcj
  have hinf2 : ((imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom) ⊓
      Subgroup.normalizer (imgOf ψ A : Set G') =
      imgOf ψ (cj y A ⊓ Subgroup.normalizer (A : Set (LGL 2 V))) := by
    rw [← imgOf_cj ψ hA hy]
    exact w183b2img_imgOf_inf_normalizer hψ hcj hA
  unfold PairViolation at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    exact h.1 (by
      rw [← imgOf_cj ψ hA hy]
      exact (imgOf_normalizer_le_iff hψ hcj hA).mpr hc)
  · intro hc
    exact h.2.1 (by
      rw [← imgOf_cj ψ hA hy]
      exact (imgOf_normalizer_le_iff hψ hA hcj).mpr hc)
  · have h3 := h.2.2.1
    rw [hinf1] at h3
    exact (imgOf_mOfG hψ hA inf_le_left) ▸ h3
  · have h4 := h.2.2.2.1
    rw [hinf2, ← imgOf_cj ψ hA hy] at h4
    exact (imgOf_mOfG hψ hcj inf_le_left) ▸ h4
  · have hk1 : mOfG (imgOf ψ A)
        (imgOf ψ (A ⊓ Subgroup.normalizer (cj y A : Set (LGL 2 V)))) =
        mOfG A (A ⊓ Subgroup.normalizer (cj y A : Set (LGL 2 V))) :=
      imgOf_mOfG hψ hA inf_le_left
    have hk2 : mOfG (imgOf ψ (cj y A))
        (imgOf ψ (cj y A ⊓ Subgroup.normalizer (A : Set (LGL 2 V)))) =
        mOfG (cj y A) (cj y A ⊓ Subgroup.normalizer (A : Set (LGL 2 V))) :=
      imgOf_mOfG hψ hcj inf_le_left
    have hsup : imgOf ψ A ⊔ (imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom =
        imgOf ψ (A ⊔ cj y A) := by
      rw [← imgOf_cj ψ hA hy]
      exact (imgOf_sup_inf hψ hA hcj).1.symm
    have e1 : mOfG (imgOf ψ A) (imgOf ψ A ⊓
        Subgroup.normalizer (((imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom :
          Subgroup G') : Set G')) = mOfG A (A ⊓ Subgroup.normalizer (cj y A : Set (LGL 2 V))) := by
      rw [hinf1, hk1]
    have e2 : mOfG ((imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom)
        (((imgOf ψ A).map (MulAut.conj (ψ ⟨y, hy⟩)).toMonoidHom) ⊓
          Subgroup.normalizer (imgOf ψ A : Set G')) =
        mOfG (cj y A) (cj y A ⊓ Subgroup.normalizer (A : Set (LGL 2 V))) := by
      rw [hinf2, ← imgOf_cj ψ hA hy, hk2]
    intro hpv
    exact h.2.2.2.2 (by
      rw [e1, e2, hsup]
      exact (w183b2img_pairQuotOK_iff hψ (sup_le hA hcj) _ _).mpr hpv)

theorem isSylowIn_imgOf {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {T : Subgroup (LGL 2 V)}
    (hT : IsSylowIn 2 T Y) : IsSylowIn 2 (imgOf ψ T) ψ.range := by
  refine ⟨?_, ?_, ?_⟩
  · rw [imgOf, ← Subgroup.map_top ψ]
    exact Subgroup.map_mono le_top
  · have hpT : IsPGroup 2 (T.subgroupOf Y) :=
      hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm
    rw [imgOf]
    exact hpT.map ψ
  · rw [imgOf, ← Subgroup.map_top ψ,
      Subgroup.relIndex_map_map_of_injective (T.subgroupOf Y) (⊤ : Subgroup ↥Y) hψ,
      Subgroup.relIndex_top_right]
    exact hT.not_dvd_relIndex

theorem exists_eq_imgOf (ψ : ↥Y →* G') {B : Subgroup G'} (hB : B ≤ ψ.range) :
    ∃ A : Subgroup (LGL 2 V), A ≤ Y ∧ imgOf ψ A = B := by
  refine ⟨(B.comap ψ).map Y.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [imgOf,
    show ((B.comap ψ).map Y.subtype).subgroupOf Y =
      ((B.comap ψ).map Y.subtype).comap Y.subtype from rfl,
    Subgroup.comap_map_eq_self_of_injective (f := Y.subtype) Y.subtype_injective (B.comap ψ)]
  exact Subgroup.map_comap_eq_self hB

theorem imgOf_mono (ψ : ↥Y →* G') {A B : Subgroup (LGL 2 V)} (h : A ≤ B) :
    imgOf ψ A ≤ imgOf ψ B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono Y h)

theorem imgOf_le_range (ψ : ↥Y →* G') (A : Subgroup (LGL 2 V)) : imgOf ψ A ≤ ψ.range := by
  rw [imgOf, ← Subgroup.map_top ψ]
  exact Subgroup.map_mono le_top

theorem apply_mem_imgOf (ψ : ↥Y →* G') {A : Subgroup (LGL 2 V)} {t : LGL 2 V} (ht : t ∈ A)
    (hY : t ∈ Y) : ψ ⟨t, hY⟩ ∈ imgOf ψ A :=
  w183b2img_mem_imgOf ht hY

private theorem w183b2img_imgOf_inj_of_le {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {A B : Subgroup (LGL 2 V)} (hA : A ≤ Y) (hB : B ≤ Y) (h : imgOf ψ A = imgOf ψ B) :
    A = B :=
  le_antisymm ((imgOf_le_iff hψ hA hB).mp (le_of_eq h))
    ((imgOf_le_iff hψ hB hA).mp (le_of_eq h.symm))

private theorem w183b2img_imgOf_conjSubgroup {ψ : ↥Y →* G'} {P : Subgroup (LGL 2 V)}
    (hP : P ≤ Y) {g : LGL 2 V} (hg : g ∈ Y) :
    imgOf ψ (conjSubgroup P g) = conjSubgroup (imgOf ψ P) (ψ ⟨g, hg⟩) := by
  have hg' : g⁻¹ ∈ Y := Y.inv_mem hg
  have h1 : conjSubgroup P g = cj g⁻¹ P := rfl
  have h2 : conjSubgroup (imgOf ψ P) (ψ ⟨g, hg⟩) =
      (imgOf ψ P).map (MulAut.conj ((ψ ⟨g, hg⟩))⁻¹).toMonoidHom := rfl
  rw [h1, h2, imgOf_cj ψ hP hg']
  have hsub : (⟨g⁻¹, hg'⟩ : ↥Y) = (⟨g, hg⟩ : ↥Y)⁻¹ := Subtype.ext rfl
  rw [hsub, map_inv]

private theorem w183b2img_conjSubgroup_le {P : Subgroup (LGL 2 V)} (hP : P ≤ Y)
    {g : LGL 2 V} (hg : g ∈ Y) : conjSubgroup P g ≤ Y := by
  rw [show conjSubgroup P g = cj g⁻¹ P from rfl]
  exact w183b2img_cj_le hP (Y.inv_mem hg)

private theorem w183b2img_isMaxParabolicMod_imgOf {ψ : ↥Y →* G'} (hψ : Function.Injective ψ)
    {N L P : Subgroup (LGL 2 V)} (hL : L ≤ Y) (h : IsMaxParabolicMod N L P) :
    IsMaxParabolicMod (imgOf ψ N) (imgOf ψ L) (imgOf ψ P) := by
  obtain ⟨hNP, hPL, hmax, S, hNS, hSL, hSpow, hSodd, hSnorm⟩ := h
  have hS : S ≤ Y := hSL.trans hL
  refine ⟨Subgroup.map_mono (Subgroup.subgroupOf_mono Y hNP), ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.subgroupOf_mono Y hPL.1)) ?_
    intro heq
    have hLP : L ≤ P := (imgOf_le_iff hψ hL (hPL.1.trans hL)).mp (le_of_eq heq.symm)
    exact hPL.2 hLP
  · intro Y'' hPY'' hY''L
    have hLrange : imgOf ψ L ≤ ψ.range := by
      rw [imgOf, ← Subgroup.map_top ψ]
      exact Subgroup.map_mono le_top
    have hY''range : Y'' ≤ ψ.range := hY''L.trans hLrange
    obtain ⟨Y₀, hY₀, hY₀eq⟩ := exists_eq_imgOf ψ hY''range
    have hle : imgOf ψ P ≤ imgOf ψ Y₀ := by rw [hY₀eq]; exact hPY''.1
    have hPY0 : P < Y₀ := by
      refine lt_of_le_of_ne ((imgOf_le_iff hψ (hPL.1.trans hL) hY₀).mp hle) ?_
      intro heq
      have hEq : Y'' = imgOf ψ P := by rw [← hY₀eq, ← heq]
      exact hPY''.2 (le_of_eq hEq)
    have hY0L : Y₀ ≤ L := (imgOf_le_iff hψ hY₀ hL).mp (by rw [hY₀eq]; exact hY''L)
    rw [← hY₀eq, hmax Y₀ hPY0 hY0L]
  · refine ⟨imgOf ψ S, Subgroup.map_mono (Subgroup.subgroupOf_mono Y hNS),
      Subgroup.map_mono (Subgroup.subgroupOf_mono Y hSL), ?_, ?_, ?_⟩
    · intro s hs
      rw [imgOf, Subgroup.mem_map] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      obtain ⟨k, hk⟩ := hSpow (s₀ : LGL 2 V) (Subgroup.mem_subgroupOf.mp hs₀)
      exact ⟨k, by
        rw [← map_pow]
        exact Subgroup.mem_map.mpr ⟨s₀ ^ 2 ^ k,
          show s₀ ^ 2 ^ k ∈ N.subgroupOf Y from hk, rfl⟩⟩
    · rw [w183b2img_relIndex_imgOf hψ hSL hL]
      exact hSodd
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL, hxN⟩ := hx
      rw [imgOf, Subgroup.mem_map] at hxL
      obtain ⟨l, hl, rfl⟩ := hxL
      have hlL : (l : LGL 2 V) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have hlnorm : (l : LGL 2 V) ∈ Subgroup.normalizer (S : Set (LGL 2 V)) :=
        (w183b2img_mem_normalizer_imgOf_iff (ψ := ψ) hψ hS l.2).mp hxN
      exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr
        (hSnorm (Subgroup.mem_inf.mpr ⟨hlL, hlnorm⟩)), rfl⟩

theorem imgOf_actsOnDynkin {ψ : ↥Y →* G'} (hψ : Function.Injective ψ) {L : Subgroup (LGL 2 V)}
    (hL : L ≤ Y) {t : LGL 2 V} (ht : t ∈ Y) (h : ActsOnDynkinMod ⊥ L t) :
    ActsOnDynkinMod ⊥ (imgOf ψ L) (ψ ⟨t, ht⟩) := by
  obtain ⟨htN, P, hPmax, hPmove⟩ := h
  have hP : P ≤ Y := hPmax.2.1.1.trans hL
  refine ⟨?_, imgOf ψ P, ?_, ?_⟩
  · exact (w183b2img_mem_normalizer_imgOf_iff (ψ := ψ) hψ hL ht).mpr htN
  · have h' := w183b2img_isMaxParabolicMod_imgOf (ψ := ψ) hψ hL hPmax
    have hbot : imgOf ψ (⊥ : Subgroup (LGL 2 V)) = ⊥ := by
      rw [imgOf, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    rwa [hbot] at h'
  · intro l' hl'
    rw [imgOf, Subgroup.mem_map] at hl'
    obtain ⟨l, hlsub, rfl⟩ := hl'
    have hlL : (l : LGL 2 V) ∈ L := Subgroup.mem_subgroupOf.mp hlsub
    have hlY : (l : LGL 2 V) ∈ Y := hL hlL
    have hgY : (t⁻¹ * (l : LGL 2 V)) ∈ Y := Y.mul_mem (Y.inv_mem ht) hlY
    have hconj := w183b2img_imgOf_conjSubgroup (ψ := ψ) hP hgY (g := t⁻¹ * (l : LGL 2 V))
    have heqψ : (ψ ⟨t, ht⟩)⁻¹ * ψ l = ψ ⟨t⁻¹ * (l : LGL 2 V), hgY⟩ := by
      rw [← map_inv, ← map_mul]
      exact congrArg ψ (Subtype.ext rfl)
    rw [heqψ]
    intro heq
    rw [← hconj] at heq
    exact hPmove (l : LGL 2 V) hlL
      (w183b2img_imgOf_inj_of_le hψ (w183b2img_conjSubgroup_le hP hgY) hP heq)

end CFSG.LocalAnalysis.WeakClosure81

end
