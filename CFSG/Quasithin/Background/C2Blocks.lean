
module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Small

variable {G : Type} [Group G]

@[expose] def IsBorelIn (X B : Subgroup G) : Prop :=
  ∃ S : Subgroup G, IsSylowTwoOf S X ∧ B = X ⊓ Subgroup.normalizer (S : Set G)

@[expose] def IsPartitionOfType {n : ℕ} (P : Finset (Finset (Fin n))) (sizes : Multiset ℕ) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧ (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧
    P.biUnion id = Finset.univ ∧ P.val.map Finset.card = sizes

@[expose] def IsG2Two (X : Type) [Group X] : Prop :=
  Nat.card X = 12096 ∧ Subgroup.center X = ⊥ ∧
    ∃ D : Subgroup X, D.Normal ∧ D.index = 2 ∧ IsPSU 3 3 1 ↥D

@[expose] def IsRankTwoLie2Derived (X : Type) [Group X] : Prop :=
  (∃ e : ℕ, IsPSL 3 2 e X) ∨ (∃ e : ℕ, IsPSU 4 2 e X) ∨ (∃ e : ℕ, IsPSU 5 2 e X) ∨
    (∃ e : ℕ, IsPSp4 2 e X) ∨ IsAlt 6 X ∨ (∃ e : ℕ, IsG2 2 e X) ∨ IsPSU 3 3 1 X ∨
    (∃ e : ℕ, Is3D4 2 e X) ∨ (∃ e : ℕ, Is2F4 e X) ∨ IsTits X

end Small

section BlockTypes

variable {G : Type} [Group G]

@[expose] def constWeight (m : ℕ) : AddSubgroup ↥(evenWeight m) where
  carrier := {x | ∀ i j, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j}
  zero_mem' := fun i j => rfl
  add_mem' := fun {a b} ha hb i j => by
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    rw [ha i j, hb i j]
  neg_mem' := fun {a} ha i j => by
    simp only [AddSubgroup.coe_neg, Pi.neg_apply]
    rw [ha i j]

abbrev AltHeart (m : ℕ) : Type := ↥(evenWeight m) ⧸ constWeight m

@[expose] def permWeight (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : ↥(evenWeight m)) :
    ↥(evenWeight m) :=
  ⟨fun i => (x : Fin m → ZMod 2) (σ⁻¹ i), by
    have hx : ∑ i, (x : Fin m → ZMod 2) i = 0 := by
      have := x.2
      simpa [evenWeight] using this
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    rw [Equiv.sum_comp σ⁻¹ (fun i => (x : Fin m → ZMod 2) i)]
    exact hx⟩

@[expose] def IsAltBlockTypeWith (L : Subgroup G) (m : ℕ)
    (α : ↥L →* alternatingGroup (Fin m)) : Prop :=
  Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
    ∃ β : ↥(blockU L) →* Multiplicative (AltHeart m),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
        ∀ x : ↥(evenWeight m), (QuotientAddGroup.mk x : AltHeart m) = Multiplicative.toAdd (β u) →
          (QuotientAddGroup.mk (permWeight m (α ℓ : Equiv.Perm (Fin m)) x) : AltHeart m) =
            Multiplicative.toAdd (β v)

@[expose] def IsAltBlockType (L : Subgroup G) (m : ℕ) : Prop :=
  IsShort2 L ∧ ∃ α : ↥L →* alternatingGroup (Fin m), IsAltBlockTypeWith L m α

@[expose] def IsMatrixBlockType (L : Subgroup G) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (H : Subgroup (Matrix.GeneralLinearGroup ι F)) : Prop :=
  ∃ α : ↥L →* ↥H, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
    ∃ β : ↥(blockU L) →* Multiplicative (ι → F),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α ℓ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u))

@[expose] def IsSL3Block (L : Subgroup G) : Prop :=
  IsShort2 L ∧ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    IsMatrixBlockType L (StatedSL 3 F)

@[expose] def IsSp4Block (L : Subgroup G) : Prop :=
  IsShort2 L ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
    IsMatrixBlockType L (StatedSp 2 F)

@[expose] def IsLnBlock (L : Subgroup G) (n : ℕ) : Prop :=
  IsShort2 L ∧ IsMatrixBlockType L (StatedSL n (ZMod 2))

@[expose] def IsG2BlockNatural (L : Subgroup G) : Prop :=
  let actor := ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
  let model := FFModel.zornQ actor
  ∃ α : ↥L →* ↥actor, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
    ∃ β : ↥(blockU L) →* ↥model.sec ⧸ model.ker.subgroupOf model.sec,
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ (ℓ : ↥L) (u v : ↥(blockU L)) (representative : ↥model.sec),
        (v : G) = ℓ * u * ℓ⁻¹ → β u = QuotientGroup.mk representative →
        ∃ image : ↥model.sec, (image : model.Amb) = model.act (α ℓ) representative ∧
          β v = QuotientGroup.mk image

@[expose] def IsG2BlockPartial (L : Subgroup G) : Prop :=
  IsShort2 L ∧ IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    ((blockZ L).subgroupOf (blockU L)).index = 2 ^ 6

@[expose] def IsG2Block (L : Subgroup G) : Prop :=
  IsShort2 L ∧ IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    ((blockZ L).subgroupOf (blockU L)).index = 2 ^ 6 ∧ IsG2BlockNatural L

@[expose] def IsHatA6Block (L : Subgroup G) : Prop :=
  IsShort2 L ∧ IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (alternatingGroup (Fin 6)) ∧
    Nat.card ↥(blockU L) = 2 ^ 6 ∧ L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L

@[expose] def IsExcA7Block (L : Subgroup G) : Prop :=
  IsShort2 L ∧ (∃ α : ↥L →* alternatingGroup (Fin 7),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) ∧
    ((blockZ L).subgroupOf (blockU L)).index = 2 ^ 4

@[expose] def IsChiBlock2 (X L : Subgroup G) : Prop :=
  IsBlock2 X L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ ∃ m : ℕ, Odd m ∧ IsAltType L m)

end BlockTypes

section MSPairs

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMSPair (G₀ R : Subgroup G) : Prop :=
  (IsSQTKIn G₀ ∧ CharTwo G₀ ∧
    ∃ L : Subgroup G, L ∈ cComp G₀ ∧ (G₀ : Set G) = (L : Set G) * (R : Set G) ∧
      IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) ∧
  ((∃ H' : Subgroup G, H' < G₀ ∧ ¬ 2 ∣ H'.relIndex G₀ ∧ R = pCoreOf 2 H') ∨
    (R ≤ G₀ ∧ pCoreOf 2 G₀ ≤ R ∧ IsG2Two (↥G₀ ⧸ CFSG.pCore 2 ↥G₀) ∧
      ∃ P : Subgroup (↥G₀ ⧸ CFSG.pCore 2 ↥G₀),
        IsMaxParabolic2 (⊤ : Subgroup (↥G₀ ⧸ CFSG.pCore 2 ↥G₀)) P ∧
        (R.subgroupOf G₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀)) ≤ P ∧
        ((((R.subgroupOf G₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀))).subgroupOf P).Normal) ∧
        IsE2 3 ↥((R.subgroupOf G₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀))))) ∧
  (∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
    ¬ G₀ ≤ Subgroup.normalizer (C : Set G))

end MSPairs

section Consistency

theorem constWeight_eq_bot_of_odd {m : ℕ} (hm : Odd m) : constWeight m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [AddSubgroup.mem_bot]
  have hsum : ∑ i, (x : Fin m → ZMod 2) i = 0 := by
    have := x.2
    simpa [evenWeight] using this
  have hne : Nonempty (Fin m) := ⟨⟨0, hm.pos⟩⟩
  obtain ⟨i₀⟩ := hne
  have hc : ∀ i, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) i₀ := fun i => hx i i₀
  have : ∑ i, (x : Fin m → ZMod 2) i = (m : ZMod 2) * (x : Fin m → ZMod 2) i₀ := by
    rw [Finset.sum_congr rfl (fun i _ => hc i)]
    simp
  rw [this] at hsum
  have hm2 : (m : ZMod 2) = 1 := by
    obtain ⟨k, rfl⟩ := hm
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this]
    simp
  rw [hm2, one_mul] at hsum
  ext i
  rw [hc i, hsum]
  rfl

theorem altHeart_mk_bijective {m : ℕ} (hm : Odd m) :
    Function.Bijective (QuotientAddGroup.mk' (constWeight m) : ↥(evenWeight m) → AltHeart m) := by
  refine ⟨?_, QuotientAddGroup.mk'_surjective _⟩
  rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_mk', constWeight_eq_bot_of_odd hm]

theorem isAltType_iff_exists_isAltBlockTypeWith {G : Type} [Group G] {L : Subgroup G} {m : ℕ}
    (hm : Odd m) :
    IsAltType L m ↔ ∃ α : ↥L →* alternatingGroup (Fin m), IsAltBlockTypeWith L m α := by
  have hq := altHeart_mk_bijective hm
  let q : ↥(evenWeight m) →+ AltHeart m := QuotientAddGroup.mk' (constWeight m)
  let e : ↥(evenWeight m) ≃+ AltHeart m := AddEquiv.ofBijective q hq
  constructor
  · rintro ⟨α, hα, hker, β, hβ, hβker, hβeq⟩
    refine ⟨α, hα, hker, (AddMonoidHom.toMultiplicative q).comp β, ?_, ?_, ?_⟩
    · exact (Function.Surjective.comp hq.2 hβ : _)
    · have hinj : Function.Injective (AddMonoidHom.toMultiplicative q) := fun a b hab => by
        have := hq.1 (congrArg Multiplicative.toAdd hab)
        exact this
      rw [MonoidHom.ker_comp_of_injective β _ hinj, hβker]
    · intro ℓ u v huv x hx
      have hxu : x = Multiplicative.toAdd (β u) := hq.1 hx
      subst hxu
      have : permWeight m (α ℓ : Equiv.Perm (Fin m)) (Multiplicative.toAdd (β u)) =
          Multiplicative.toAdd (β v) := by
        apply Subtype.ext
        funext i
        exact (hβeq ℓ u v huv i).symm
      rw [this]
      rfl
  · rintro ⟨α, hα, hker, β', hβ', hβ'ker, hβ'eq⟩
    refine ⟨α, hα, hker, (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom).comp β', ?_, ?_, ?_⟩
    · exact (Function.Surjective.comp e.symm.surjective hβ' : _)
    · have hinj : Function.Injective (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom) :=
        fun a b hab => by
          have := e.symm.injective (congrArg Multiplicative.toAdd hab)
          exact this
      rw [MonoidHom.ker_comp_of_injective β' _ hinj, hβ'ker]
    · intro ℓ u v huv i
      set y : ↥(evenWeight m) := e.symm (Multiplicative.toAdd (β' u)) with hy
      have hyq : (QuotientAddGroup.mk y : AltHeart m) = Multiplicative.toAdd (β' u) := by
        have := e.apply_symm_apply (Multiplicative.toAdd (β' u))
        exact this
      have h1 := hβ'eq ℓ u v huv y hyq
      have h2 : e.symm (Multiplicative.toAdd (β' v)) =
          permWeight m (α ℓ : Equiv.Perm (Fin m)) y := by
        rw [← h1]
        exact e.symm_apply_apply _
      show ((e.symm (Multiplicative.toAdd (β' v)) : ↥(evenWeight m)) : Fin m → ZMod 2) i = _
      rw [h2]
      rfl

end Consistency

end CFSG.Quasithin
