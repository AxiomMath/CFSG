module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof153Block

open CFSG.QuasithinUnique
open Matrix

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_subgroupOf_of_coe_of_injective (f : G →* G') (hf : Function.Injective f)
    {X : Subgroup G} {X' : Subgroup G'} (e : X ≃* X') (he : ∀ x : X, (e x : G') = f x)
    (L : Subgroup G) : (L.subgroupOf X).map e.toMonoidHom = (L.map f).subgroupOf X' := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, (he x).symm⟩
  · rintro ⟨g, hg, hgy⟩
    refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr ?_, e.apply_symm_apply y⟩
    have h1 : f (e.symm y : G) = (y : G') := by rw [← he, e.apply_symm_apply]
    rw [hf (h1.trans hgy.symm)]
    exact hg

theorem blockQ_map_of_injective (f : G →* G') (hf : Function.Injective f) (L : Subgroup G) :
    (blockQ L).map f = blockQ (L.map f) := by
  have h := CFSG.pCore_map_iso 2 (L.equivMapOfInjective f hf)
  simp only [blockQ, CFSG.Open.pCoreOf]
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem blockU_map_of_injective (f : G →* G') (hf : Function.Injective f) (L : Subgroup G) :
    (blockU L).map f = blockU (L.map f) := by
  rw [blockU, blockU, Subgroup.map_commutator, blockQ_map_of_injective f hf]

theorem map_centralizer_le (f : G →* G') (K : Subgroup G) :
    (Subgroup.centralizer (K : Set G)).map f ≤
      Subgroup.centralizer ((K.map f : Subgroup G') : Set G') := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_mul, ← map_mul, hx k hk]

theorem blockZ_map_of_injective (f : G →* G') (hf : Function.Injective f) (L : Subgroup G) :
    (blockZ L).map f = blockZ (L.map f) := by
  apply le_antisymm
  · rw [blockZ, blockZ, ← blockU_map_of_injective f hf]
    exact (Subgroup.map_inf_le _ _ f).trans (inf_le_inf_left _ (map_centralizer_le f L))
  · intro y hy
    obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [← blockU_map_of_injective f hf] at hyU
    obtain ⟨u, hu, rfl⟩ := hyU
    refine ⟨u, Subgroup.mem_inf.mpr ⟨hu, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro l hl
    apply hf
    rw [map_mul, map_mul]
    exact hyC (f l) ⟨l, hl, rfl⟩

theorem exists_blockU_mulEquiv_of_injective (f : G →* G') (hf : Function.Injective f)
    (L : Subgroup G) :
    ∃ e : blockU L ≃* blockU (L.map f), ∀ u : blockU L, (e u : G') = f u :=
  ⟨((blockU L).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (blockU_map_of_injective f hf L)), fun _ => rfl⟩

theorem nonempty_tildeU_mulEquiv_of_injective (f : G →* G') (hf : Function.Injective f)
    (L : Subgroup G) : Nonempty (tildeU L ≃* tildeU (L.map f)) := by
  obtain ⟨e, he⟩ := exists_blockU_mulEquiv_of_injective f hf L
  exact ⟨QuotientGroup.congr ((blockZ L).subgroupOf (blockU L))
    ((blockZ (L.map f)).subgroupOf (blockU (L.map f))) e
    ((map_subgroupOf_of_coe_of_injective f hf e he (blockZ L)).trans
      (congrArg (fun K => K.subgroupOf (blockU (L.map f))) (blockZ_map_of_injective f hf L)))⟩

theorem isShort_map_of_injective [Finite G] [Finite G'] (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} (h : IsShort L) : IsShort (L.map f) := by
  have e : L ≃* L.map f := L.equivMapOfInjective f hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N _ hN
    have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
    have h2 : IsPGroup 2 (L ⧸ N.comap e.toMonoidHom) :=
      hN.of_equiv (QuotientGroup.congr _ _ e hmap).symm
    rw [← hmap, h.eq_twoResidual _ h2, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp
      (isCharacteristicP_congr_mulEquiv e
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mpr h.generalizedFitting_eq))
  · rw [← blockU_map_of_injective f hf, ← blockQ_map_of_injective f hf]
    exact (Subgroup.map_mono h.blockU_le_center).trans
      ((Subgroup.map_inf_le _ _ f).trans (inf_le_inf_left _ (map_centralizer_le f _)))
  · have e' := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
    rcases h.quasisimple_or_prime with hq | hp
    · exact Or.inl (LocalCores.isQuasisimple_of_mulEquiv e' hq)
    · exact Or.inr (by rwa [← Nat.card_congr e'.toEquiv])
  · rw [← blockZ_map_of_injective f hf, ← blockU_map_of_injective f hf]
    exact (Subgroup.map_lt_map_iff_of_injective (f := f) hf).mpr h.blockZ_lt_blockU
  · intro W hZW hWU hLW
    have hWr : W ≤ f.range :=
      hWU.trans ((blockU_map_of_injective f hf L) ▸ Subgroup.map_le_range f _)
    obtain ⟨W₀, rfl⟩ : ∃ W₀ : Subgroup G, W₀.map f = W :=
      ⟨W.comap f, by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hWr]⟩
    rw [← blockZ_map_of_injective f hf, Subgroup.map_le_map_iff_of_injective hf] at hZW
    rw [← blockU_map_of_injective f hf, Subgroup.map_le_map_iff_of_injective hf] at hWU
    have hLW₀ : L ≤ Subgroup.normalizer (W₀ : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hfl := hLW (Subgroup.mem_map_of_mem f hl)
      rw [Subgroup.mem_normalizer_iff] at hfl
      have hx := hfl (f x)
      rwa [Subgroup.mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hf] at hx
    rcases h.irreducible W₀ hZW hWU hLW₀ with rfl | rfl
    · exact Or.inl (blockZ_map_of_injective f hf L)
    · exact Or.inr (blockU_map_of_injective f hf L)

theorem exists_typeWitness_map_of_injective (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} {T M : Type*} [Group T] [Group M] (R : T → M → M → Prop)
    (h : ∃ α : L →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
      ∃ β : blockU L →* M, Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
        ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v)) :
    ∃ α : L.map f →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 (L.map f) ∧
      ∃ β : blockU (L.map f) →* M, Function.Surjective β ∧
        β.ker = (blockZ (L.map f)).subgroupOf (blockU (L.map f)) ∧
        ∀ (ℓ : L.map f) (u v : blockU (L.map f)),
          (v : G') = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v) := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  obtain ⟨e', he'⟩ := exists_blockU_mulEquiv_of_injective f hf L
  set e := L.equivMapOfInjective f hf
  refine ⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_,
    β.comp e'.symm.toMonoidHom, hβs.comp e'.symm.surjective, ?_, fun ℓ u v huv => ?_⟩
  · rw [ker_comp_symm, hαk, CFSG.pCore_map_iso]
  · rw [ker_comp_symm, hβk, map_subgroupOf_of_coe_of_injective f hf e' he',
      blockZ_map_of_injective f hf]
  · have hv : f (e'.symm v : G) = v := by rw [← he', e'.apply_symm_apply]
    have hu : f (e'.symm u : G) = u := by rw [← he', e'.apply_symm_apply]
    have hl : f (e.symm ℓ : G) = ℓ := by
      change ((e (e.symm ℓ) : L.map f) : G') = ℓ
      rw [e.apply_symm_apply]
    refine hR (e.symm ℓ) (e'.symm u) (e'.symm v) (hf ?_)
    rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, hv, hu, hl, huv, Subgroup.coe_inv]

theorem isLin2Type_map_of_injective (f : G →* G') (hf : Function.Injective f) {L : Subgroup G}
    {n : ℕ} (h : IsLin2Type L n) : IsLin2Type (L.map f) n := by
  obtain ⟨F, _, _, hF, hw⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF, exists_typeWitness_map_of_injective f hf
    (fun (t : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Multiplicative (Fin 2 → F)) =>
      Multiplicative.toAdd y = (t : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x))
    hw⟩

theorem isAltNaturalType_map_of_injective (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} {n : ℕ} (h : IsAltNaturalType L n) : IsAltNaturalType (L.map f) n :=
  exists_typeWitness_map_of_injective f hf
    (fun (t : alternatingGroup (Fin n)) (x y : Multiplicative (altHeart n)) =>
      ∀ z : evenWeight n, Multiplicative.toAdd x = (z : altHeart n) →
        Multiplicative.toAdd y = (evenWeightPerm (t : Equiv.Perm (Fin n)) z : altHeart n)) h

theorem isOmegaPlusType_map_of_injective (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} {m : ℕ} (h : IsOmegaPlusType L m) : IsOmegaPlusType (L.map f) m :=
  exists_typeWitness_map_of_injective f hf
    (fun (t : omegaPlusTwo m) (x y : Multiplicative (Fin m ⊕ Fin m → ZMod 2)) =>
      Multiplicative.toAdd y =
        ((t : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ Multiplicative.toAdd x) h

theorem isOmegaMinusType_map_of_injective (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} {m : ℕ} (h : IsOmegaMinusType L m) : IsOmegaMinusType (L.map f) m :=
  exists_typeWitness_map_of_injective f hf
    (fun (t : omegaMinusTwo m) (x y : Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)) =>
      Multiplicative.toAdd y =
        ((t : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Multiplicative.toAdd x) h

theorem isA6Z3Type_map_of_injective [Finite G] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) {L : Subgroup G} (h : IsA6Z3Type L) : IsA6Z3Type (L.map f) := by
  obtain ⟨⟨α, hαs, hle, hcard⟩, hr⟩ := h
  obtain ⟨u⟩ := nonempty_tildeU_mulEquiv_of_injective f hf L
  set e := L.equivMapOfInjective f hf
  refine ⟨⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_, ?_⟩, ?_⟩
  · rw [ker_comp_symm, ← CFSG.pCore_map_iso 2 e]
    exact Subgroup.map_mono hle
  · rw [ker_comp_symm, ← CFSG.pCore_map_iso 2 e,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  · rw [← pRank_congr_mulEquiv Nat.prime_two.one_lt u, hr]

theorem isA7FourType_map_of_injective [Finite G] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) {L : Subgroup G} (h : IsA7FourType L) :
    IsA7FourType (L.map f) := by
  obtain ⟨⟨α, hαs, hαk⟩, hr⟩ := h
  obtain ⟨u⟩ := nonempty_tildeU_mulEquiv_of_injective f hf L
  set e := L.equivMapOfInjective f hf
  refine ⟨⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_⟩, ?_⟩
  · rw [ker_comp_symm, hαk, CFSG.pCore_map_iso]
  · rw [← pRank_congr_mulEquiv Nat.prime_two.one_lt u, hr]

theorem isTypeScriptL_map_of_injective [Finite G] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) {L : Subgroup G} (h : IsTypeScriptL L) :
    IsTypeScriptL (L.map f) := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | h | h
  · exact Or.inl ⟨n, isLin2Type_map_of_injective f hf h⟩
  · exact Or.inr (Or.inl ⟨n, isAltNaturalType_map_of_injective f hf h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, isOmegaPlusType_map_of_injective f hf h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, isOmegaMinusType_map_of_injective f hf h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isA6Z3Type_map_of_injective f hf h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isA7FourType_map_of_injective f hf h)))))

end Transport

theorem isScriptLBlock_map_subtype {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    {L : Subgroup ↥H} (hL : IsScriptLBlock ⊤ L) (hHN : H ≤ N)
    (hsub : ((L.map H.subtype).subgroupOf N).IsSubnormal) :
    IsScriptLBlock N (L.map H.subtype) :=
  ⟨⟨isShort_map_of_injective H.subtype H.subtype_injective hL.1.1,
      (Subgroup.map_subtype_le L).trans hHN, hsub⟩,
    isTypeScriptL_map_of_injective H.subtype H.subtype_injective hL.2⟩

end Proof153Block

open Proof153Block

end CFSG.RankThree.PartTwo.Sec15
