module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneSix
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

namespace LemmaOneSixSetting

variable {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}

private theorem commutatorSpace_mono_aux {A B : Subgroup (U ≃ₗ[ZMod p] U)} (h : A ≤ B) :
    HardMathSupport.Kantor79.commutatorSpace A ≤ HardMathSupport.Kantor79.commutatorSpace B := by
  rw [HardMathSupport.Kantor79.commutatorSpace, HardMathSupport.Kantor79.commutatorSpace,
    Submodule.span_le]
  rintro w ⟨g, hg, v, rfl⟩
  exact Submodule.subset_span ⟨g, h hg, v, rfl⟩

private theorem commutatorSpace_eq_iSup_movedSpace_aux [Module.Finite (ZMod p) U]
    (G : Subgroup (U ≃ₗ[ZMod p] U)) :
    HardMathSupport.Kantor79.commutatorSpace G =
      ⨆ g : ↥G, HardMathSupport.Kantor79.movedSpace (g : U ≃ₗ[ZMod p] U) := by
  have hcl : Subgroup.closure (Set.range (Subtype.val : ↥G → U ≃ₗ[ZMod p] U)) = G := by
    rw [Subtype.range_coe_subtype]
    show Subgroup.closure (G : Set (U ≃ₗ[ZMod p] U)) = G
    exact le_antisymm ((Subgroup.closure_le G).mpr (fun x hx => hx))
      (fun x hx => Subgroup.subset_closure hx)
  have h := HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (K := ZMod p) (E := U) (Subtype.val : ↥G → U ≃ₗ[ZMod p] U)
  rw [hcl] at h
  exact h

private theorem commutatorSpace_closure_insert_aux [Module.Finite (ZMod p) U]
    (x : U ≃ₗ[ZMod p] U) (G : Subgroup (U ≃ₗ[ZMod p] U)) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert x (G : Set (U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.movedSpace x ⊔
        HardMathSupport.Kantor79.commutatorSpace G := by
  have hrange : Set.range
      (fun o : Option ↥G => o.elim x (fun g => (g : U ≃ₗ[ZMod p] U))) =
      insert x (G : Set (U ≃ₗ[ZMod p] U)) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inl rfl
      | some g => exact Or.inr g.2
    · rintro (rfl | hy)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨y, hy⟩, rfl⟩
  have hsome : (⨆ b : ↥G, HardMathSupport.Kantor79.movedSpace
      ((some b).elim x (fun g => (g : U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.commutatorSpace G := by
    change (⨆ b : ↥G, HardMathSupport.Kantor79.movedSpace (b : U ≃ₗ[ZMod p] U)) =
      HardMathSupport.Kantor79.commutatorSpace G
    rw [← commutatorSpace_eq_iSup_movedSpace_aux G]
  have h := HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (K := ZMod p) (E := U)
      (fun o : Option ↥G => o.elim x (fun g => (g : U ≃ₗ[ZMod p] U)))
  rw [hrange] at h
  rw [iSup_option] at h
  rw [hsome] at h
  simpa using h

private theorem finrank_movedSpace_eq_one_of_isRefl {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := by
  rw [HardMathSupport.Kantor79.movedSpace]
  exact ht.2

private theorem exists_isRefl_of_reflGen_ne_bot {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : ReflGen p G) (hne : G ≠ ⊥) : ∃ t ∈ G, IsRefl p t := by
  by_contra h
  push Not at h
  apply hne
  rw [hG]
  rw [show {t : U ≃ₗ[ZMod p] U | t ∈ G ∧ IsRefl p t} = ∅ from ?_]
  · exact Subgroup.closure_empty
  · rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    exact h t ht.1 ht.2

private def kerSectionSubgroup (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {t | t ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
    t v - v ∈ centralizerSpace F}
  one_mem' := by
    refine ⟨F.one_mem, ?_⟩
    intro v _
    simp
  mul_mem' := by
    rintro t s ⟨htF, ht⟩ ⟨hsF, hs⟩
    refine ⟨F.mul_mem htF hsF, ?_⟩
    intro v hv
    have hsv : s v ∈ HardMathSupport.Kantor79.commutatorSpace F := by
      have hmap := map_commutatorSpace_of_mem_normalizer (H := F) (Subgroup.le_normalizer hsF)
      have := Submodule.mem_map_of_mem (f := (s : U →ₗ[ZMod p] U)) hv
      rwa [hmap] at this
    have h1 : t (s v) - s v ∈ centralizerSpace F := ht (s v) hsv
    have h2 : s v - v ∈ centralizerSpace F := hs v hv
    have hsum : (t * s) v - v = (t (s v) - s v) + (s v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [hsum]
    exact (centralizerSpace F).add_mem h1 h2
  inv_mem' := by
    rintro t ⟨htF, ht⟩
    refine ⟨F.inv_mem htF, ?_⟩
    intro v hv
    have htv : t v - v ∈ centralizerSpace F := ht v hv
    have h1 : t⁻¹ (t v - v) ∈ centralizerSpace F := by
      have hmap := map_centralizerSpace_of_mem_normalizer (H := F)
        (Subgroup.le_normalizer (F.inv_mem htF))
      have := Submodule.mem_map_of_mem (f := ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) htv
      rwa [hmap] at this
    have heq : t⁻¹ v - v = -(t⁻¹ (t v - v)) := by
      rw [map_sub]
      rw [show t⁻¹ (t v) = v from LinearEquiv.symm_apply_apply t v]
      abel
    rw [heq]
    exact (centralizerSpace F).neg_mem h1

private theorem kerSection_eq_kerSectionSubgroup (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    kerSection F = kerSectionSubgroup F := by
  refine le_antisymm ?_ ?_
  · rw [kerSection]
    exact (Subgroup.closure_le (kerSectionSubgroup F)).mpr (fun x hx => hx)
  · intro x hx
    exact Subgroup.subset_closure hx

private theorem commutator_le_kerSection {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁F : H₁ ≤ F) :
    ⁅H₁, kerSection F⁆ ≤ kerSection F := by
  rw [kerSection_eq_kerSectionSubgroup F]
  refine Subgroup.commutator_le.mpr ?_
  intro g hg t ht
  have hgt : g * t * g⁻¹ ∈ kerSectionSubgroup F := by
    refine ⟨F.mul_mem (F.mul_mem (hH₁F hg) ht.1) (F.inv_mem (hH₁F hg)), ?_⟩
    intro v hv
    have hgv : g⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F := by
      have hmap := map_commutatorSpace_of_mem_normalizer (H := F)
        (Subgroup.le_normalizer (F.inv_mem (hH₁F hg)))
      have := Submodule.mem_map_of_mem (f := ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) hv
      rwa [hmap] at this
    have ht' : t (g⁻¹ v) - g⁻¹ v ∈ centralizerSpace F := ht.2 (g⁻¹ v) hgv
    have hgw : g (t (g⁻¹ v) - g⁻¹ v) ∈ centralizerSpace F := by
      have hmap := map_centralizerSpace_of_mem_normalizer (H := F)
        (Subgroup.le_normalizer (hH₁F hg))
      have := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) ht'
      rwa [hmap] at this
    have heq : (g * t * g⁻¹) v - v = g (t (g⁻¹ v) - g⁻¹ v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub,
        show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v]
    rw [heq]
    exact hgw
  have hprod : (g * t * g⁻¹) * t⁻¹ ∈ kerSectionSubgroup F :=
    (kerSectionSubgroup F).mul_mem hgt ((kerSectionSubgroup F).inv_mem ht)
  rw [commutatorElement_def]
  simpa only [mul_assoc] using hprod

private theorem movedSpace_le_sup_span_of_codim_one {s : U ≃ₗ[ZMod p] U}
    {V₀ : Submodule (ZMod p) U} {W : Submodule (ZMod p) U} {u : U}
    (htop : V₀ ⊔ Submodule.span (ZMod p) {u} = ⊤)
    (hV0 : ∀ v ∈ V₀, s v - v ∈ W) :
    HardMathSupport.Kantor79.movedSpace s ≤
      W ⊔ Submodule.span (ZMod p) {s u - u} := by
  rw [HardMathSupport.Kantor79.movedSpace, LinearMap.range_eq_map, ← htop, Submodule.map_sup,
    Submodule.map_span]
  refine sup_le ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact Submodule.mem_sup_left (hV0 v hv)
  · rw [Set.image_singleton]
    refine Submodule.span_le.mpr ?_
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_sup_right (by
      have hval : ((s : U →ₗ[ZMod p] U) - 1) u = s u - u := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        rfl
      rw [hval]
      exact Submodule.subset_span (Set.mem_singleton _))

open scoped commutatorElement in
private theorem closure_insert_reflGen_conj_mem {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : U ≃ₗ[ZMod p] U} {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) (hH₁B : H₁ ≤ B) {x t : U ≃ₗ[ZMod p] U}
    (hx : x ∈ H₁) (ht : t ∈ kerSection F) : t * x * t⁻¹ ∈ B := by
  have heq : t * x * t⁻¹ = ⁅x, t⁆⁻¹ * x := by
    rw [commutatorElement_def]
    group
  have hcomm'B : ⁅x, t⁆⁻¹ ∈ B := by
    rw [hB]
    exact Subgroup.subset_closure
      (Set.mem_insert_iff.mpr (Or.inr (Subgroup.mem_sup_left
        ((⁅H₁, kerSection F⁆ : Subgroup _).inv_mem
          (Subgroup.commutator_mem_commutator hx ht)))))
  rw [heq]
  exact B.mul_mem hcomm'B (hH₁B hx)

open scoped commutatorElement in
private theorem closure_insert_reflGen_key {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH₁' : ReflGen p H₁) {b : U ≃ₗ[ZMod p] U} {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) (hH₁B : H₁ ≤ B)
    (hH₁R : H₁ ≤ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t})
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) :
    ∀ g ∈ H₁, ⁅g, t⁆ ∈ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t} := by
  set R : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t} with hR
  intro g hg
  rw [hH₁'] at hg
  refine Subgroup.closure_induction (p := fun x _ => ⁅x, t⁆ ∈ R) ?_ ?_ ?_ ?_ hg
  · intro x hx
    have hconjR : t * x * t⁻¹ ∈ R :=
      Subgroup.subset_closure ⟨closure_insert_reflGen_conj_mem hB hH₁B hx.1 ht,
        IsRefl.conj hx.2 t⟩
    have heq2 : ⁅x, t⁆ = x * (t * x * t⁻¹) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hx.2.1]
      group
    rw [heq2]
    exact R.mul_mem (hH₁R hx.1) hconjR
  · rw [commutatorElement_def]
    simp
  · intro x y hx hy ihx ihy
    have hxH₁ : x ∈ H₁ := by rw [← hH₁'] at hx; exact hx
    have hxy : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
      rw [commutatorElement_def]
      group
    rw [hxy]
    exact R.mul_mem (R.mul_mem (R.mul_mem (hH₁R hxH₁) ihy) (R.inv_mem (hH₁R hxH₁))) ihx
  · intro x hx ih
    have hxH₁ : x ∈ H₁ := by rw [← hH₁'] at hx; exact hx
    have hx1 : ⁅x⁻¹, t⁆ = x⁻¹ * ⁅x, t⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [hx1]
    exact R.mul_mem (R.mul_mem (R.inv_mem (hH₁R hxH₁)) (R.inv_mem ih)) (hH₁R hxH₁)

open scoped commutatorElement in
private theorem closure_insert_reflGen [Module.Finite (ZMod p) U]
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁' : ReflGen p H₁)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b) {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) : ReflGen p B := by
  let R : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ B ∧ IsRefl p t}
  change B = R
  have hRB : R ≤ B := (Subgroup.closure_le B).mpr (fun t ht => ht.1)
  have hH₁B : H₁ ≤ B := by
    intro h hh
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (Subgroup.mem_sup_right hh)))
  have hH₁R : H₁ ≤ R := by
    rw [hH₁']
    refine (Subgroup.closure_le R).mpr ?_
    intro t ht
    exact Subgroup.subset_closure ⟨hH₁B ht.1, ht.2⟩
  have hSR : ⁅H₁, kerSection F⁆ ≤ R := by
    refine Subgroup.commutator_le.mpr ?_
    intro g hg t ht
    exact closure_insert_reflGen_key hH₁' hB hH₁B hH₁R ht g hg
  have hbB : b ∈ B := by
    rw [hB]; exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  have hbR : b ∈ R := Subgroup.subset_closure ⟨hbB, hb⟩
  have hsupR : (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) ≤ R := sup_le hSR hH₁R
  refine le_antisymm ?_ hRB
  rw [hB]
  refine (Subgroup.closure_le R).mpr ?_
  rintro x (rfl | hx)
  · exact hbR
  · exact hsupR hx

private theorem closure_insert_dim_moved_disjoint {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :
    HardMathSupport.Kantor79.movedSpace b ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) = ⊥ := by
  have hLfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 :=
    finrank_movedSpace_eq_one_of_isRefl hb
  have hVbnotle : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    intro hle
    obtain ⟨v, hv, hbv⟩ := hbV
    have hmem : b v - v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F :=
      hle ⟨v, by simp⟩
    refine hbv ?_
    have := (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F).add_mem hv hmem
    simpa using this
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro w hw
  by_contra hw0
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hLfin hw.1 hw0
  exact hVbnotle (by
    rw [hspan]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hw.2))

private theorem closure_insert_dim_moved_disjoint_commutator {b : U ≃ₗ[ZMod p] U}
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hVbinf : HardMathSupport.Kantor79.movedSpace b ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) = ⊥)
    (hVGle : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :
    HardMathSupport.Kantor79.movedSpace b ⊓
      HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc HardMathSupport.Kantor79.movedSpace b ⊓
        HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁)
      ≤ HardMathSupport.Kantor79.movedSpace b ⊓
          (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :=
        inf_le_inf_left _ hVGle
    _ = ⊥ := hVbinf

private theorem closure_insert_dim_finrank_commutator (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    (hWleH₁ : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      centralizerSpace H₁)
    (hVG : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) :
    Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁)) =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) + 1 := by
  have hVinjW : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc HardMathSupport.Kantor79.commutatorSpace H₁ ⊓
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
        ≤ HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ :=
          inf_le_inf_left _ hWleH₁
      _ = ⊥ := hc
  rw [hVG]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H₁)
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
  rw [hVinjW, finrank_bot, add_zero, hS.degenerate.1] at h
  omega

private theorem closure_insert_dim (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) + 2 := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun h hh => Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hh))
  have hH₁F : H₁ ≤ F := le_trans hH₁ hHF
  have hVH₁F : HardMathSupport.Kantor79.commutatorSpace H₁ ≤
      HardMathSupport.Kantor79.commutatorSpace F := commutatorSpace_mono_aux hH₁F
  have hLfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 :=
    finrank_movedSpace_eq_one_of_isRefl hb
  have hVbinf := closure_insert_dim_moved_disjoint (F := F) hb hbV
  have hVG : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
    (le_of_invariant_of_ne_bot hS hp hH₁ hH₁' hH₁1 hc).1
  have hVGle : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    rw [hVG]
    exact sup_le (le_trans hVH₁F le_sup_left) (le_trans inf_le_left le_sup_left)
  have hVbinfG := closure_insert_dim_moved_disjoint_commutator hVbinf hVGle
  have hVB : HardMathSupport.Kantor79.commutatorSpace B =
      HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) := by
    rw [hB, commutatorSpace_closure_insert_aux]
  have hWleH₁ : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      centralizerSpace H₁ := by
    intro w hw
    exact (mem_centralizerSpace).mpr fun h hh =>
      (mem_centralizerSpace.mp hw.2) h (hH₁F hh)
  have hVGfin := closure_insert_dim_finrank_commutator hS hc hWleH₁ hVG
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.movedSpace b)
    (HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁))
  rw [hVbinfG, finrank_bot, add_zero] at hfin
  rw [hVB, hfin, hLfin, hVGfin]
  omega

private theorem movedSpace_not_le_of_not_mapsTo {b : U ≃ₗ[ZMod p] U}
    {V₀ : Submodule (ZMod p) U} (hbV : ∃ v ∈ V₀, b v ∉ V₀) :
    ¬ HardMathSupport.Kantor79.movedSpace b ≤ V₀ := by
  rintro h
  obtain ⟨v, hv, hbv⟩ := hbV
  have hmem : b v - v ∈ V₀ := h ⟨v, by simp⟩
  refine hbv ?_
  have := V₀.add_mem hv hmem
  simpa using this

private theorem movedSpace_le_of_mem_of_isRefl_moves_W {b : U ≃ₗ[ZMod p] U}
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {X W : Submodule (ZMod p) U}
    (hLfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1)
    (hbW : ∃ w ∈ W, b w ∉ W) (hbB : b ∈ B)
    (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X) (hWX : W ≤ X) :
    HardMathSupport.Kantor79.movedSpace b ≤ X := by
  obtain ⟨w, hwW, hbw⟩ := hbW
  have hbwX : b w - w ∈ X := X.sub_mem (hXinv b hbB w (hWX hwW)) (hWX hwW)
  have hbwmem : b w - w ∈ HardMathSupport.Kantor79.movedSpace b := ⟨w, by simp⟩
  have hbwne : b w ≠ w := fun h => hbw (h.symm ▸ hwW)
  have hbw0 : b w - w ≠ 0 := sub_ne_zero.mpr hbwne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hLfin hbwmem hbw0
  rw [hspan]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hbwX)

private theorem inf_ne_bot_of_mem_notMem {X VG W : Submodule (ZMod p) U} {w : U}
    (hwW : w ∉ W) (hwX : w ∈ X) (hwVG : w ∈ VG) : X ⊓ VG ≠ ⊥ := by
  intro hbot
  have hz : w ∈ (⊥ : Submodule (ZMod p) U) := by rw [← hbot]; exact ⟨hwX, hwVG⟩
  have hz0 : w = 0 := by simpa using hz
  exact hwW (hz0.symm ▸ Submodule.zero_mem _)

private theorem closure_insert_moved_sub_mem_sup {G G' : Subgroup (U ≃ₗ[ZMod p] U)}
    (hle : G ≤ G') {s : U ≃ₗ[ZMod p] U} (hsG : s ∈ G) (u : U) :
    u - s u ∈ HardMathSupport.Kantor79.commutatorSpace G' := by
  have h1 : (s : U ≃ₗ[ZMod p] U) u - u ∈ HardMathSupport.Kantor79.commutatorSpace G' :=
    commutatorSpace_mono_aux hle (by
      simpa using (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hsG ⟨u, by simp⟩))
  have := (HardMathSupport.Kantor79.commutatorSpace G').neg_mem h1
  simpa only [neg_sub] using this

private theorem closure_insert_VB_inf_V0 {b : U ≃ₗ[ZMod p] U}
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {VG : Submodule (ZMod p) U}
    (hVB : HardMathSupport.Kantor79.commutatorSpace B =
      HardMathSupport.Kantor79.movedSpace b ⊔ VG)
    (hVGle : VG ≤ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (hVbinf : HardMathSupport.Kantor79.movedSpace b ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) = ⊥) :
    HardMathSupport.Kantor79.commutatorSpace B ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) = VG := by
  rw [hVB, sup_comm, sup_inf_assoc_of_le (HardMathSupport.Kantor79.movedSpace b) hVGle,
    hVbinf, sup_bot_eq]

private theorem closure_insert_sup_span_eq_top (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u : U}
    (huV0 : u ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :
    (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u} = ⊤ := by
  have hV0fin := finrank_sup_eq hS hp
  have hleU : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) ≤
      Module.finrank (ZMod p) U :=
    Submodule.finrank_le (HardMathSupport.Kantor79.commutatorSpace F)
  have hposU : 1 ≤ Module.finrank (ZMod p) U := by
    rw [hS.finrank_eq] at hleU
    omega
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton huV0, hV0fin]
  omega

private theorem closure_insert_exists_reflection_not_commute (hS : LemmaOneSixSetting F H a l)
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) :
    ∃ h ∈ H₁, IsRefl p h ∧ ∃ t ∈ kerSection F, ¬ Commute h t := by
  obtain ⟨h, hhH₁, hhref⟩ := exists_isRefl_of_reflGen_ne_bot hH₁' hH₁1
  obtain ⟨t, htT, htnotcomm⟩ :=
    exists_not_commute_kerSection hS hp (hH₁ hhH₁) (IsRefl.ne_one hhref)
  exact ⟨h, hhH₁, hhref, t, htT, htnotcomm⟩

private theorem closure_insert_u_sub_notMem (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u : U}
    (htop : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u} = ⊤)
    {s : U ≃ₗ[ZMod p] U} (hsT : s ∈ kerSection F) (hs1 : s ≠ 1) :
    u - s u ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  intro hmem
  have hle := movedSpace_le_sup_span_of_codim_one
    (V₀ := HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (W := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) htop
    (fun v hv => (finrank_movedSpace_of_mem_kerSection hS hp hsT hs1).1 v hv)
  have hdim2 := (finrank_movedSpace_of_mem_kerSection hS hp hsT hs1).2.1
  have hspanW : Submodule.span (ZMod p) {(s : U ≃ₗ[ZMod p] U) u - u} ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (by
      have hneg := (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F).neg_mem hmem
      rw [neg_sub] at hneg
      exact hneg))
  have hleW : HardMathSupport.Kantor79.movedSpace s ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    le_trans hle (sup_le le_rfl hspanW)
  have hfin := Submodule.finrank_mono hleW
  rw [hdim2, hS.degenerate.1] at hfin
  omega

private theorem closure_insert_VG_le_X (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) {VG : Submodule (ZMod p) U}
    (hVG : VG = HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F))
    {B : Subgroup (U ≃ₗ[ZMod p] U)} (hGleB : ⁅H₁, kerSection F⁆ ≤ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X) {u : U} (huX : u ∈ X)
    (htop : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u} = ⊤)
    (hWX : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X)
    (hSleT : ⁅H₁, kerSection F⁆ ≤ kerSection F) :
    VG ≤ X := by
  have hVG' : VG = HardMathSupport.Kantor79.commutatorSpace ⁅H₁, kerSection F⁆ := by
    rw [hVG, commutatorSpace_commutator hS hp hH₁ hH₁' hH₁1]
  rw [hVG', commutatorSpace_le_iff]
  intro s hs v
  by_cases hs1 : s = 1
  · rw [hs1]; simp
  · have hsT : s ∈ kerSection F := hSleT hs
    have hle := movedSpace_le_sup_span_of_codim_one
      (V₀ := HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
      (W := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) htop
      (fun w hw => (finrank_movedSpace_of_mem_kerSection hS hp hsT hs1).1 w hw)
    have hsB : s ∈ B := hGleB hs
    have hsuX : (s : U ≃ₗ[ZMod p] U) u - u ∈ X := X.sub_mem (hXinv s hsB u huX) huX
    have hspanX : Submodule.span (ZMod p) {(s : U ≃ₗ[ZMod p] U) u - u} ≤ X :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hsuX)
    have : ((s : U →ₗ[ZMod p] U) - 1) v ∈ X :=
      le_trans hle (sup_le hWX hspanX) ⟨v, rfl⟩
    simpa using this

private theorem closure_insert_W_le_of_invariant (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hGleB : (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) ≤ B)
    {X : Submodule (ZMod p) U} (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X)
    (hYne : X ⊓ HardMathSupport.Kantor79.commutatorSpace
      (⁅H₁, kerSection F⁆ ⊔ H₁) ≠ ⊥) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X := by
  have hVGinv : ∀ g ∈ (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)),
      ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁),
      g x ∈ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) := by
    intro g hg x hx
    have hmap := map_commutatorSpace_of_mem_normalizer
      (H := (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _)) (Subgroup.le_normalizer hg)
    have := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hx
    rwa [hmap] at this
  have hInv : ∀ g ∈ (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)),
      ∀ x ∈ X ⊓ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁),
      g x ∈ X ⊓ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) :=
    fun g hg x hx => ⟨hXinv g (hGleB hg) x hx.1, hVGinv g hg x hx.2⟩
  exact le_trans ((le_of_invariant_of_ne_bot hS hp hH₁ hH₁' hH₁1 hc).2 _ inf_le_right hYne hInv)
    inf_le_left

private theorem closure_insert_irred_sup_basic (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b) :
    H₁ ≤ F ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 ∧
      HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
        HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ≤
        HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun h hh => Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hh))
  have hH₁F : H₁ ≤ F := le_trans hH₁ hHF
  have hLfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 :=
    finrank_movedSpace_eq_one_of_isRefl hb
  have hVG : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
    (le_of_invariant_of_ne_bot hS hp hH₁ hH₁' hH₁1 hc).1
  have hVGle : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    rw [hVG]
    exact sup_le (le_trans (commutatorSpace_mono_aux hH₁F) le_sup_left)
      (le_trans inf_le_left le_sup_left)
  exact ⟨hH₁F, hLfin, hVG, hVGle⟩

private theorem closure_insert_irred_B_basic [Module.Finite (ZMod p) U]
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁F : H₁ ≤ F)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (hVGle : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) :
    ⁅H₁, kerSection F⁆ ≤ kerSection F ∧
      HardMathSupport.Kantor79.commutatorSpace B =
        HardMathSupport.Kantor79.movedSpace b ⊔
          HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) ∧
      ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) ≤ B) ∧
      HardMathSupport.Kantor79.commutatorSpace B ⊓
        (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
        HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) := by
  have hSleT : ⁅H₁, kerSection F⁆ ≤ kerSection F := commutator_le_kerSection hH₁F
  have hVB : HardMathSupport.Kantor79.commutatorSpace B =
      HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) := by
    rw [hB, commutatorSpace_closure_insert_aux]
  have hGleB : (⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) ≤ B := by
    intro g hg
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hg))
  have hVbinf := closure_insert_dim_moved_disjoint (F := F) hb hbV
  have hVBV0 := closure_insert_VB_inf_V0 hVB hVGle hVbinf
  exact ⟨hSleT, hVB, hGleB, hVBV0⟩

private theorem closure_insert_irred_not_le_V0 (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) {X : Submodule (ZMod p) U}
    (hXV : X ≤ HardMathSupport.Kantor79.commutatorSpace B) (hXne : X ≠ ⊥)
    (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X) :
    ¬ X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
  intro hle
  obtain ⟨hH₁F, hLfin, _hVG, hVGle⟩ :=
    closure_insert_irred_sup_basic hS hp hH₁ hH₁' hH₁1 hc hb
  obtain ⟨_hSleT, _hVB, hGleB, hVBV0⟩ :=
    closure_insert_irred_B_basic hb hH₁F hbV hVGle hB
  have hVbnotle := movedSpace_not_le_of_not_mapsTo (V₀ :=
    HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) hbV
  have hXVG : X ≤ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) := by
    have : X ≤ HardMathSupport.Kantor79.commutatorSpace B ⊓
        (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) := le_inf hXV hle
    rwa [hVBV0] at this
  have hWX : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X :=
    (le_of_invariant_of_ne_bot hS hp hH₁ hH₁' hH₁1 hc).2 X hXVG hXne
      (fun g hg x hx => hXinv g (hGleB hg) x hx)
  have hbB : b ∈ B := by
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  have hLleX := movedSpace_le_of_mem_of_isRefl_moves_W hLfin hbW hbB hXinv hWX
  exact hVbnotle (le_trans hLleX hle)

open scoped commutatorElement in
private theorem closure_insert_irred_eq_top (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) {X : Submodule (ZMod p) U}
    (hXV : X ≤ HardMathSupport.Kantor79.commutatorSpace B)
    (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X)
    (hnotle : ¬ X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :
    X = HardMathSupport.Kantor79.commutatorSpace B := by
  obtain ⟨hH₁F, hLfin, hVG, hVGle⟩ :=
    closure_insert_irred_sup_basic hS hp hH₁ hH₁' hH₁1 hc hb
  obtain ⟨hSleT, hVB, hGleB, _hVBV0⟩ := closure_insert_irred_B_basic hb hH₁F hbV hVGle hB
  obtain ⟨u, huX, huV0⟩ := Set.not_subset.mp hnotle
  have htop := closure_insert_sup_span_eq_top hS hp huV0
  obtain ⟨h, hhH₁, _hhref, t, htT, htnotcomm⟩ :=
    closure_insert_exists_reflection_not_commute hS hp hH₁ hH₁' hH₁1
  have hcommS : ⁅h, t⁆ ∈ (⁅H₁, kerSection F⁆ : Subgroup _) :=
    Subgroup.commutator_mem_commutator hhH₁ htT
  have hcommT : ⁅h, t⁆ ∈ kerSection F := hSleT hcommS
  have hcomm1 : ⁅h, t⁆ ≠ 1 := fun hcon =>
    htnotcomm (commutatorElement_eq_one_iff_mul_comm.mp hcon)
  have hsu := closure_insert_u_sub_notMem hS hp htop hcommT hcomm1
  have hsm : u - ⁅h, t⁆ u ∈ HardMathSupport.Kantor79.commutatorSpace
      (⁅H₁, kerSection F⁆ ⊔ H₁) :=
    closure_insert_moved_sub_mem_sup le_sup_left hcommS u
  have hs_mem_X : u - ⁅h, t⁆ u ∈ X := by
    have hsB : ⁅h, t⁆ ∈ B := hGleB (Subgroup.mem_sup_left hcommS)
    have := X.sub_mem (hXinv ⁅h, t⁆ hsB u huX) huX
    simpa only [neg_sub] using X.neg_mem this
  have hYne := inf_ne_bot_of_mem_notMem hsu hs_mem_X hsm
  have hWX := closure_insert_W_le_of_invariant hS hp hH₁ hH₁' hH₁1 hc hGleB hXinv hYne
  have hVGleX := closure_insert_VG_le_X hS hp hH₁ hH₁' hH₁1 hVG
    (fun g hg => hGleB (Subgroup.mem_sup_left hg)) hXinv huX htop hWX hSleT
  have hbB : b ∈ B := by
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
  have hLleX := movedSpace_le_of_mem_of_isRefl_moves_W hLfin hbW hbB hXinv hWX
  have hle : HardMathSupport.Kantor79.commutatorSpace B ≤ X := by
    rw [hVB]
    exact sup_le hLleX hVGleX
  exact le_antisymm hXV hle

private theorem closure_insert_irred (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) :
    IrredOnSection B ⊥ (HardMathSupport.Kantor79.commutatorSpace B) := by
  intro X _ hXV hXinv
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  right
  have hnotle :=
    closure_insert_irred_not_le_V0 hS hp hH₁ hH₁' hH₁1 hc hb hbW hbV hB hXV hX0 hXinv
  exact closure_insert_irred_eq_top hS hp hH₁ hH₁' hH₁1 hc hb hbW hbV hB hXV hXinv hnotle

open scoped commutatorElement in
private theorem closure_insert_pair (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) (hHF : H ≤ F)
    {b : U ≃ₗ[ZMod p] U} {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) :
    ∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
  have hH₁B : H₁ ≤ B := by
    intro g hg
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr (Subgroup.mem_sup_right hg)))
  have hH₁F : H₁ ≤ F := le_trans hH₁ hHF
  obtain ⟨h, hhH₁, hhref, t, htT, htnotcomm⟩ :=
    closure_insert_exists_reflection_not_commute hS hp hH₁ hH₁' hH₁1
  have hcommS : ⁅h, t⁆ ∈ (⁅H₁, kerSection F⁆ : Subgroup _) :=
    Subgroup.commutator_mem_commutator hhH₁ htT
  have hcommT : ⁅h, t⁆ ∈ kerSection F := commutator_le_kerSection hH₁F hcommS
  refine ⟨h, hH₁B hhH₁, t * h * t⁻¹, ?_, hhref, IsRefl.conj hhref t, ?_⟩
  · have heq : t * h * t⁻¹ = h * ⁅h, t⁆ := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hhref.1,
        show h * (h * t * h * t⁻¹) = (h * h) * (t * h * t⁻¹) by group, hhref.1, one_mul]
    rw [heq]
    have hcommB : ⁅h, t⁆ ∈ B := by
      rw [hB]
      exact Subgroup.subset_closure
        (Set.mem_insert_iff.mpr (Or.inr (Subgroup.mem_sup_left hcommS)))
    exact B.mul_mem (hH₁B hhH₁) hcommB
  · have hxy : h * (t * h * t⁻¹) = ⁅h, t⁆ := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hhref.1]
      group
    rw [hxy]
    refine orderOf_eq_prime ?_ ?_
    · exact pow_eq_one_of_mem_kerSection hS hp hcommT
    · intro h1
      exact htnotcomm (commutatorElement_eq_one_iff_mul_comm.mp h1)

theorem irredOnSection_closure_insert (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hB : B = Subgroup.closure (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup _) :
      Set (U ≃ₗ[ZMod p] U)))) :
    ReflGen p B ∧ IrredOnSection B ⊥ (HardMathSupport.Kantor79.commutatorSpace B) ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
        Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) + 2 ∧
      ∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun h hh => Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr hh))
  exact ⟨closure_insert_reflGen hH₁' hb hB,
    closure_insert_irred hS hp hH₁ hH₁' hH₁1 hc hb hbW hbV hB,
    closure_insert_dim hS hp hH₁ hH₁' hH₁1 hc hb hbV hB,
    closure_insert_pair hS hp hH₁ hH₁' hH₁1 hHF hB⟩

end LemmaOneSixSetting

end CFSG.StandardType.ZS
