module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoreTransport
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.QuasithinUnique
open CFSG.Assembly.RankThreeEven (orthogonalPlus orthogonalMinus)
open Matrix

variable {G : Type*} [Group G]

theorem blockU_le_self (L : Subgroup G) : blockU L ≤ L := by
  rw [blockU, Subgroup.commutator_le]
  intro q hq l hl
  have hqL : q ∈ L := by
    obtain ⟨q', -, rfl⟩ := Subgroup.mem_map.mp hq
    exact q'.2
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hqL hl) (L.inv_mem hqL)) (L.inv_mem hl)

theorem blockZ_le_blockU (L : Subgroup G) : blockZ L ≤ blockU L :=
  inf_le_left

theorem blockZ_subgroupOf_le_center (L : Subgroup G) :
    (blockZ L).subgroupOf (blockU L) ≤ Subgroup.center (blockU L) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hz).2 u
    (blockU_le_self L u.2)

instance blockZ_subgroupOf_normal (L : Subgroup G) :
    ((blockZ L).subgroupOf (blockU L)).Normal :=
  ⟨fun z hz u => by
    rw [Subgroup.mem_center_iff.mp (blockZ_subgroupOf_le_center L hz) u, mul_inv_cancel_right]
    exact hz⟩

abbrev tildeU (L : Subgroup G) : Type _ :=
  blockU L ⧸ (blockZ L).subgroupOf (blockU L)

structure IsShort (L : Subgroup G) : Prop where
  eq_twoResidual : ∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤
  generalizedFitting_eq : generalizedFitting L = CFSG.pCore 2 L
  blockU_le_center : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G)
  quasisimple_or_prime :
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) ∨ (Nat.card (L ⧸ CFSG.pCore 2 L)).Prime
  blockZ_lt_blockU : blockZ L < blockU L
  irreducible : ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
    L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L

@[expose] def IsBlock (X L : Subgroup G) : Prop :=
  IsShort L ∧ L ≤ X ∧ (L.subgroupOf X).IsSubnormal

theorem IsShort2.isShort [Finite G] {L : Subgroup G} (h : IsShort2 L) : IsShort L := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, ?_, h3.1, h4.imp_right fun h => by rw [h]; exact Nat.prime_three, h5, h6⟩
  have hchar : IsCharacteristicP 2 L := by
    intro x hx
    have hxG : (x : G) ∈ L ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 L : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx y' hy')
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (h2 hxG)
    rw [← Subtype.ext hzx]
    exact hz
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mp hchar

theorem IsBlock2.isBlock [Finite G] {X L : Subgroup G} (h : IsBlock2 X L) : IsBlock X L :=
  ⟨IsShort2.isShort h.1, h.2⟩

@[expose] def allOnes (n : ℕ) : Fin n → ZMod 2 :=
  fun _ => 1

@[expose] def evenWeightOnes (n : ℕ) : AddSubgroup (evenWeight n) :=
  (AddSubgroup.zmultiples (allOnes n)).addSubgroupOf (evenWeight n)

abbrev altHeart (n : ℕ) : Type :=
  evenWeight n ⧸ evenWeightOnes n

@[expose] def evenWeightPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : evenWeight n) :
    evenWeight n :=
  ⟨fun i => (x : Fin n → ZMod 2) (σ⁻¹ i), by
    have hx := x.2
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hx ⊢
    rw [Equiv.sum_comp σ⁻¹ (x : Fin n → ZMod 2)]
    exact hx⟩

@[expose] def IsAltNaturalType (L : Subgroup G) (n : ℕ) : Prop :=
  ∃ α : L →* alternatingGroup (Fin n), Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
  ∃ β : blockU L →* Multiplicative (altHeart n), Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (β u) = (x : altHeart n) →
      Multiplicative.toAdd (β v) = (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x : altHeart n)

noncomputable abbrev omegaPlusTwo (m : ℕ) : Subgroup (GL (Fin m ⊕ Fin m) (ZMod 2)) :=
  ⁅orthogonalPlus m (ZMod 2), orthogonalPlus m (ZMod 2)⁆

noncomputable abbrev omegaMinusTwo (m : ℕ) : Subgroup (GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :=
  ⁅orthogonalMinus m (ZMod 2) 1 1, orthogonalMinus m (ZMod 2) 1 1⁆

@[expose] def IsOmegaPlusType (L : Subgroup G) (m : ℕ) : Prop :=
  ∃ α : L →* omegaPlusTwo m, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
  ∃ β : blockU L →* Multiplicative (Fin m ⊕ Fin m → ZMod 2), Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ Multiplicative.toAdd (β u)

@[expose] def IsOmegaMinusType (L : Subgroup G) (m : ℕ) : Prop :=
  ∃ α : L →* omegaMinusTwo m, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
  ∃ β : blockU L →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2), Function.Surjective β ∧
    β.ker = (blockZ L).subgroupOf (blockU L) ∧
    ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Multiplicative.toAdd (β u)

@[expose] def IsA6Z3Type (L : Subgroup G) : Prop :=
  (∃ α : L →* alternatingGroup (Fin 6), Function.Surjective α ∧ CFSG.pCore 2 L ≤ α.ker ∧
    Nat.card α.ker = 3 * Nat.card (CFSG.pCore 2 L)) ∧
  CFSG.pRank 2 (tildeU L) = 6

@[expose] def IsA7FourType (L : Subgroup G) : Prop :=
  (∃ α : L →* alternatingGroup (Fin 7), Function.Surjective α ∧ α.ker = CFSG.pCore 2 L) ∧
  CFSG.pRank 2 (tildeU L) = 4

@[expose] def IsTypeScriptL (L : Subgroup G) : Prop :=
  (∃ n, IsLin2Type L n) ∨ (∃ n, IsAltNaturalType L n) ∨ (∃ m, IsOmegaPlusType L m) ∨
    (∃ m, IsOmegaMinusType L m) ∨ IsA6Z3Type L ∨ IsA7FourType L

@[expose] def IsScriptLBlock (X L : Subgroup G) : Prop :=
  IsBlock X L ∧ IsTypeScriptL L

theorem IsScriptLBlock.isBlock {X L : Subgroup G} (h : IsScriptLBlock X L) : IsBlock X L :=
  h.1

theorem IsBlock.isShort {X L : Subgroup G} (h : IsBlock X L) : IsShort L :=
  h.1

theorem IsBlock.le {X L : Subgroup G} (h : IsBlock X L) : L ≤ X :=
  h.2.1

section Transport

variable {G' : Type*} [Group G'] (φ : G ≃* G')

omit [Group G] in
theorem ker_comp_symm {A B T : Type*} [Group A] [Group B] [Group T] (ε : A ≃* B) (g : A →* T) :
    (g.comp ε.symm.toMonoidHom).ker = g.ker.map ε.toMonoidHom := by
  ext y
  constructor
  · intro hy
    exact ⟨ε.symm y, hy, ε.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    change g (ε.symm (ε x)) = 1
    rw [ε.symm_apply_apply]
    exact hx

omit [Group G] in
theorem isCharacteristicP_congr_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (ε : A ≃* B) (h : IsCharacteristicP p A) : IsCharacteristicP p B := by
  change Subgroup.centralizer (CFSG.pCore p B : Set B) ≤ CFSG.pCore p B
  rw [← CFSG.pCore_map_iso p ε, ← CFSG.RankThreeEvenClassification.Helpers.centralizer_map_equiv]
  exact Subgroup.map_mono h

omit [Group G] in
theorem pRank_congr_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    (_hp : 1 < p) (ε : A ≃* B) : CFSG.pRank p A = CFSG.pRank p B := CFSG.pRank_congr_of_mulEquiv ε p

theorem map_subgroupOf_of_coe {X : Subgroup G} {X' : Subgroup G'} (f : X ≃* X')
    (hf : ∀ x : X, (f x : G') = φ x) (L : Subgroup G) :
    (L.subgroupOf X).map f.toMonoidHom = (L.map φ.toMonoidHom).subgroupOf X' := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, (hf x).symm⟩
  · rintro ⟨g, hg, hgy⟩
    refine ⟨f.symm y, Subgroup.mem_subgroupOf.mpr ?_, f.apply_symm_apply y⟩
    have h1 : φ (f.symm y : G) = (y : G') := by rw [← hf, f.apply_symm_apply]
    rw [φ.injective (h1.trans hgy.symm)]
    exact hg

theorem blockQ_map (L : Subgroup G) :
    (blockQ L).map φ.toMonoidHom = blockQ (L.map φ.toMonoidHom) := by
  have h := CFSG.pCore_map_iso 2 (L.equivMapOfInjective φ.toMonoidHom φ.injective)
  simp only [blockQ, CFSG.Open.pCoreOf]
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem blockU_map (L : Subgroup G) :
    (blockU L).map φ.toMonoidHom = blockU (L.map φ.toMonoidHom) := by
  rw [blockU, blockU, Subgroup.map_commutator, blockQ_map]

theorem blockZ_map (L : Subgroup G) :
    (blockZ L).map φ.toMonoidHom = blockZ (L.map φ.toMonoidHom) := by
  rw [blockZ, blockZ, Subgroup.map_inf _ _ φ.toMonoidHom φ.injective, blockU_map,
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_equiv]

theorem exists_blockU_mulEquiv (L : Subgroup G) :
    ∃ f : blockU L ≃* blockU (L.map φ.toMonoidHom), ∀ u : blockU L, (f u : G') = φ u :=
  ⟨((blockU L).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (blockU_map φ L)), fun _ => rfl⟩

theorem nonempty_tildeU_mulEquiv (L : Subgroup G) :
    Nonempty (tildeU L ≃* tildeU (L.map φ.toMonoidHom)) := by
  obtain ⟨f, hf⟩ := exists_blockU_mulEquiv φ L
  exact ⟨QuotientGroup.congr ((blockZ L).subgroupOf (blockU L))
    ((blockZ (L.map φ.toMonoidHom)).subgroupOf (blockU (L.map φ.toMonoidHom))) f
    ((map_subgroupOf_of_coe φ f hf (blockZ L)).trans
      (congrArg (fun K => K.subgroupOf (blockU (L.map φ.toMonoidHom))) (blockZ_map φ L)))⟩

theorem IsShort.map [Finite G] [Finite G'] {L : Subgroup G} (h : IsShort L) :
    IsShort (L.map φ.toMonoidHom) := by
  have e : L ≃* L.map φ.toMonoidHom := L.equivMapOfInjective φ.toMonoidHom φ.injective
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
  · rw [← blockU_map, ← blockQ_map,
      ← CFSG.RankThreeEvenClassification.Helpers.centralizer_map_equiv,
      ← Subgroup.map_inf _ _ φ.toMonoidHom φ.injective]
    exact Subgroup.map_mono h.blockU_le_center
  · have e' := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
    rcases h.quasisimple_or_prime with hq | hp
    · exact Or.inl (LocalCores.isQuasisimple_of_mulEquiv e' hq)
    · exact Or.inr (by rwa [← Nat.card_congr e'.toEquiv])
  · rw [← blockZ_map, ← blockU_map]
    exact (Subgroup.map_lt_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mpr
      h.blockZ_lt_blockU
  · intro W hZW hWU hLW
    obtain ⟨W₀, rfl⟩ : ∃ W₀ : Subgroup G, W₀.map φ.toMonoidHom = W :=
      ⟨W.map φ.symm.toMonoidHom, by
        rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' from
          MonoidHom.ext φ.apply_symm_apply, Subgroup.map_id]⟩
    rw [← blockZ_map, Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
      at hZW
    rw [← blockU_map, Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
      at hWU
    rw [← Subgroup.map_equiv_normalizer_eq,
      Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective] at hLW
    rcases h.irreducible W₀ hZW hWU hLW with rfl | rfl
    · exact Or.inl (blockZ_map φ L)
    · exact Or.inr (blockU_map φ L)

theorem isShort_map_iff [Finite G] [Finite G'] {L : Subgroup G} :
    IsShort (L.map φ.toMonoidHom) ↔ IsShort L := by
  refine ⟨fun h => ?_, fun h => h.map φ⟩
  have h' := h.map φ.symm
  rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G from
    MonoidHom.ext φ.symm_apply_apply, Subgroup.map_id] at h'

theorem IsBlock.map [Finite G] [Finite G'] {X L : Subgroup G} (h : IsBlock X L) :
    IsBlock (X.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  refine ⟨h.1.map φ, Subgroup.map_mono h.2.1, ?_⟩
  rw [← map_subgroupOf_of_coe φ (X.equivMapOfInjective φ.toMonoidHom φ.injective) (fun _ => rfl)]
  exact h.2.2.map (X.equivMapOfInjective φ.toMonoidHom φ.injective).surjective

theorem exists_typeWitness_map {L : Subgroup G} {T M : Type*} [Group T] [Group M]
    (R : T → M → M → Prop)
    (h : ∃ α : L →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
      ∃ β : blockU L →* M, Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
        ∀ (ℓ : L) (u v : blockU L), (v : G) = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v)) :
    ∃ α : L.map φ.toMonoidHom →* T, Function.Surjective α ∧
      α.ker = CFSG.pCore 2 (L.map φ.toMonoidHom) ∧
      ∃ β : blockU (L.map φ.toMonoidHom) →* M, Function.Surjective β ∧
        β.ker = (blockZ (L.map φ.toMonoidHom)).subgroupOf (blockU (L.map φ.toMonoidHom)) ∧
        ∀ (ℓ : L.map φ.toMonoidHom) (u v : blockU (L.map φ.toMonoidHom)),
          (v : G') = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v) := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  obtain ⟨f, hf⟩ := exists_blockU_mulEquiv φ L
  set e := L.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_,
    β.comp f.symm.toMonoidHom, hβs.comp f.symm.surjective, ?_, fun ℓ u v huv => ?_⟩
  · rw [ker_comp_symm, hαk, CFSG.pCore_map_iso]
  · rw [ker_comp_symm, hβk, map_subgroupOf_of_coe φ f hf, blockZ_map]
  · have hv : φ (f.symm v : G) = v := by rw [← hf, f.apply_symm_apply]
    have hu : φ (f.symm u : G) = u := by rw [← hf, f.apply_symm_apply]
    have hl : φ (e.symm ℓ : G) = ℓ := by
      change ((e (e.symm ℓ) : L.map φ.toMonoidHom) : G') = ℓ
      rw [e.apply_symm_apply]
    refine hR (e.symm ℓ) (f.symm u) (f.symm v) (φ.injective ?_)
    rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, hv, hu, hl, huv, Subgroup.coe_inv]

theorem isLin2Type_map {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    IsLin2Type (L.map φ.toMonoidHom) n := by
  obtain ⟨F, _, _, hF, hw⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF, exists_typeWitness_map φ
    (fun (t : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Multiplicative (Fin 2 → F)) =>
      Multiplicative.toAdd y = (t : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x))
    hw⟩

theorem IsAltNaturalType.map {L : Subgroup G} {n : ℕ} (h : IsAltNaturalType L n) :
    IsAltNaturalType (L.map φ.toMonoidHom) n :=
  exists_typeWitness_map φ
    (fun (t : alternatingGroup (Fin n)) (x y : Multiplicative (altHeart n)) =>
      ∀ z : evenWeight n, Multiplicative.toAdd x = (z : altHeart n) →
        Multiplicative.toAdd y = (evenWeightPerm (t : Equiv.Perm (Fin n)) z : altHeart n)) h

theorem IsOmegaPlusType.map {L : Subgroup G} {m : ℕ} (h : IsOmegaPlusType L m) :
    IsOmegaPlusType (L.map φ.toMonoidHom) m :=
  exists_typeWitness_map φ
    (fun (t : omegaPlusTwo m) (x y : Multiplicative (Fin m ⊕ Fin m → ZMod 2)) =>
      Multiplicative.toAdd y =
        ((t : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ Multiplicative.toAdd x) h

theorem IsOmegaMinusType.map {L : Subgroup G} {m : ℕ} (h : IsOmegaMinusType L m) :
    IsOmegaMinusType (L.map φ.toMonoidHom) m :=
  exists_typeWitness_map φ
    (fun (t : omegaMinusTwo m) (x y : Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)) =>
      Multiplicative.toAdd y =
        ((t : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Multiplicative.toAdd x) h

theorem IsA6Z3Type.map [Finite G] [Finite G'] {L : Subgroup G} (h : IsA6Z3Type L) :
    IsA6Z3Type (L.map φ.toMonoidHom) := by
  obtain ⟨⟨α, hαs, hle, hcard⟩, hr⟩ := h
  obtain ⟨u⟩ := nonempty_tildeU_mulEquiv φ L
  set e := L.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_, ?_⟩, ?_⟩
  · rw [ker_comp_symm, ← CFSG.pCore_map_iso 2 e]
    exact Subgroup.map_mono hle
  · rw [ker_comp_symm, ← CFSG.pCore_map_iso 2 e,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  · rw [← pRank_congr_mulEquiv Nat.prime_two.one_lt u, hr]

theorem IsA7FourType.map [Finite G] [Finite G'] {L : Subgroup G} (h : IsA7FourType L) :
    IsA7FourType (L.map φ.toMonoidHom) := by
  obtain ⟨⟨α, hαs, hαk⟩, hr⟩ := h
  obtain ⟨u⟩ := nonempty_tildeU_mulEquiv φ L
  set e := L.equivMapOfInjective φ.toMonoidHom φ.injective
  refine ⟨⟨α.comp e.symm.toMonoidHom, hαs.comp e.symm.surjective, ?_⟩, ?_⟩
  · rw [ker_comp_symm, hαk, CFSG.pCore_map_iso]
  · rw [← pRank_congr_mulEquiv Nat.prime_two.one_lt u, hr]

theorem IsTypeScriptL.map [Finite G] [Finite G'] {L : Subgroup G} (h : IsTypeScriptL L) :
    IsTypeScriptL (L.map φ.toMonoidHom) := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | h | h
  · exact Or.inl ⟨n, isLin2Type_map φ h⟩
  · exact Or.inr (Or.inl ⟨n, h.map φ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, h.map φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, h.map φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.map φ)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.map φ)))))

theorem IsScriptLBlock.map [Finite G] [Finite G'] {X L : Subgroup G} (h : IsScriptLBlock X L) :
    IsScriptLBlock (X.map φ.toMonoidHom) (L.map φ.toMonoidHom) :=
  ⟨h.1.map φ, h.2.map φ⟩

end Transport

end CFSG.RankThree.PartTwo
