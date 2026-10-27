
module

public import CFSG.Monster.B.TwoA.Base.IncidenceBase
public import CFSG.Monster.B.TwoA.Base.GeomLin

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open scoped IsMulCommutative

attribute [local instance] parAction

theorem subOf_conjSub
    {G : Type*} [Group G] {E F : Subgroup G} [CFSG.IsElementaryAbelian 2 E]
    (k : Subgroup.normalizer (E : Set G)) :
    subOf E (conjSub (k : G) F) =
      (subOf E F).map (linConj E k : Additive E →ₗ[ZMod 2] Additive E) := by
  ext x
  rw [mem_subOf, mem_conjSub]
  constructor
  · intro hx
    have hy : (k : G)⁻¹ * ((Additive.toMul x : E) : G) * (k : G)⁻¹⁻¹ ∈ E :=
      conj_mem_of_normalizer (Subgroup.inv_mem _ k.2) (Additive.toMul x).2
    rw [inv_inv] at hy
    refine ⟨Additive.ofMul ⟨_, hy⟩, hx, ?_⟩
    apply (Additive.toMul).injective
    apply Subtype.ext
    change (k : G) * ((k : G)⁻¹ * ((Additive.toMul x : E) : G) * k) * (k : G)⁻¹ = _
    group
  · rintro ⟨y, hy, rfl⟩
    change (k : G)⁻¹ * ((k : G) * ((Additive.toMul y : E) : G) * (k : G)⁻¹) * k ∈ F
    rw [show (k : G)⁻¹ * ((k : G) * ((Additive.toMul y : E) : G) * (k : G)⁻¹) * k =
      ((Additive.toMul y : E) : G) by group]
    exact hy

theorem conjSub_le_of_normalizer {G : Type*} [Group G] {E F : Subgroup G}
    {k : G} (hk : k ∈ Subgroup.normalizer (E : Set G)) (hFE : F ≤ E) : conjSub k F ≤ E := by
  have h := conjSub_mono (g := k) hFE
  rwa [conjSub_eq_self_iff.2 hk] at h

theorem exists_normalizer_map_chain
    {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    [CFSG.IsElementaryAbelian 2 E] (hsurj : Function.Surjective (conjE E)) (I : Finset ℕ)
    (F C : ℕ → Subgroup G) (hF : ∀ s ∈ I, F s ≤ E) (hC : ∀ s ∈ I, C s ≤ E)
    (hFm : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → F s ≤ F t) (hCm : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → C s ≤ C t)
    (hFc : ∀ s ∈ I, Nat.card (F s) = 2 ^ s) (hCc : ∀ s ∈ I, Nat.card (C s) = 2 ^ s) :
    ∃ k ∈ Subgroup.normalizer (E : Set G), ∀ s ∈ I, conjSub k (F s) = C s := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_flag I (fun s => subOf E (F s)) (fun s => subOf E (C s))
    (fun s hs t ht hst => (subOf_le_subOf_iff (hF s hs)).2 (hFm s hs t ht hst))
    (fun s hs t ht hst => (subOf_le_subOf_iff (hC s hs)).2 (hCm s hs t ht hst))
    (fun s hs => (finrank_subOf E (hF s hs) (hFc s hs)).trans
      (finrank_subOf E (hC s hs) (hCc s hs)).symm)
  obtain ⟨k, hk⟩ := linConj_surjective E hsurj e
  refine ⟨k, k.2, fun s hs => ?_⟩
  refine subOf_injective (conjSub_le_of_normalizer k.2 (hF s hs)) (hC s hs) ?_
  rw [subOf_conjSub, hk]
  exact he s hs

abbrev IsObj (i : ℕ) (A : Subgroup Dfull) : Prop := (i, A) ∈ ParObj

theorem parType_mem_Icc (x : ParGeom) : parType x ∈ Finset.Icc 1 5 :=
  Finset.mem_Icc.2 (parType_bounds x)

theorem smul_obj_eq (g : Shat) {x : ParGeom} {h : Dfull}
    (hx : x.1.2 = conjSub h (Echain (parType x))) :
    (g • x).1.2 = conjSub ((g : Dfull) * h) (Echain (parType x)) := by
  change conjSub (g : Dfull) x.1.2 = _
  rw [hx, conjSub_mul]

theorem obj_ext {x y : ParGeom} (ht : parType x = parType y) (hA : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext ht hA)

@[expose] def stdChamber (g : Shat) : Set ParGeom := (g • ·) '' stdParFlag

theorem isParFlag_smul {F : Set ParGeom} (hF : IsParFlag F) (g : Shat) :
    IsParFlag ((g • ·) '' F) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (parInc_smul_iff g x y).2 (hF x hx y hy)

theorem parType_image_smul (F : Set ParGeom) (g : Shat) :
    parType '' ((g • ·) '' F) = parType '' F := by
  rw [Set.image_image]
  rfl

end CFSG.Monster.B.TwoA
