module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable (G : Type) [Group G] [Finite G]

@[expose] def ASC22One : Prop :=
  ∀ H R L : Subgroup G, IsSQTKIn H → IsTwoRadicalIn H R → L ∈ cComp H →
    ((R : Set G) ∩ ((L : Set G) * (centralizerSection H L (pCoreOf 2 L) : Set G))) =
      ((R ⊓ L : Subgroup G) : Set G) * (centralizerSection R L (pCoreOf 2 L) : Set G)

@[expose] def ASC22Two : Prop :=
  ∀ H R L : Subgroup G, IsSQTKIn H → IsTwoRadicalIn H R → L ∈ cComp H →
    (R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ∧
      R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) ∧
      (R ⊓ L ≠ ⊥ → IsTwoRadicalIn L (R ⊓ L)))

@[expose] def ASC22Three : Prop :=
  ∀ H R L : Subgroup G, IsSQTKIn H → IsTwoRadicalIn H R → L ∈ cComp H →
    (R ⊓ Subgroup.normalizer (L : Set G) =
        pCoreOf 2 ((L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) ⊓
          Subgroup.normalizer ((R ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G)) ∧
      (R ⊓ Subgroup.normalizer (L : Set G) ≠ ⊥ →
        IsTwoRadicalIn (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G)))
          (R ⊓ Subgroup.normalizer (L : Set G))))

@[expose] def ASC22Four : Prop :=
  ∀ H R L : Subgroup G, IsSQTKIn H → IsTwoRadicalIn H R → L ∈ cComp H →
    ((CFSG.Blueprint.EvenLieType
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsAlt 6 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsPSU 3 3 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) →
      IsParabolic2 (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
        (((L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))

@[expose] def ASC22Statement : Prop := ASC22One G ∧ ASC22Two G ∧ ASC22Three G ∧ ASC22Four G

@[expose] def ASC24One : Prop :=
  ∀ H R M L : Subgroup G, HypC23 H R M → L ∈ cComp H → CharTwo L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    IsSylowTwoOf (R ⊓ L) L →
      (L ≤ M ∨ (IsChi0Block H L ∧
        (∃ V : Subgroup G, IsTwoReducedIn (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V ∧
          ∃ A : Subgroup G, A ≤ R ⊓ Subgroup.normalizer (L : Set G) ∧
            IsFFOffender (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))) V A) ∧
        IsBorelOfBlock L (L ⊓ M)))

@[expose] def ASC24Two : Prop :=
  ∀ H R M L : Subgroup G, HypC23 H R M → L ∈ cComp H → CharTwo L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    (IsSylowTwoOf (R ⊓ L) L ∨ R ≤ Subgroup.normalizer (L : Set G))

@[expose] def ASC27Statement : Prop :=
  ∀ H R M K V : Subgroup G, HypC23 H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    (pCoreOf 2 (K ⊔ R) ≤ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ∧
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
      IsTwoReducedIn (K ⊔ R) V) ∧
    (¬ thompsonJ R ≤ thompsonJ (pCoreOf 2 (K ⊔ R)) ∧
      ∃ hV : IsElemAbelian 2 V,
        @IsFFModule V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) ∧
        ∃ A : Subgroup (MulAut ↥V), A ≤ autOn R V ∧
          @IsFFStarOffender V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) A) ∧
    (
      (IsChiBlock2 H K ∧
        (
          ((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∧
            IsSylowTwoOf (autOn (thompsonJ R) V) (autOn K V) ∧
            IsBorelIn (autOn K V) (autOn (M ⊓ K) V)) ∨
          (IsAltType K 5 ∧ IsSylowTwoOf R (K ⊔ R) ∧
            Nonempty (↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 5)) ∧
            IsBorelIn (autOn K V) (autOn (M ⊓ K) V)) ∨
          (IsAltType K 7 ∧ Nonempty (↥(autOn R V) ≃* DihedralGroup 4) ∧
            ∃ (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7))
              (P : Finset (Finset (Fin 7))), IsPartitionOfType P {4, 3} ∧
              ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
                MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) ∨
          (IsAltType K 7 ∧ IsE2 3 ↥(autOn R V) ∧
            ∃ (e : ↥(autOn (K ⊔ R) V) ≃* Equiv.Perm (Fin 7))
              (P : Finset (Finset (Fin 7))), IsPartitionOfType P {2, 2, 2, 1} ∧
              ((autOn (M ⊓ K) V).subgroupOf (autOn (K ⊔ R) V)).map e.toMonoidHom =
                MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)))) ∨
      ((∃ (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)), 5 ≤ n ∧ n ≤ 8 ∧ IsShort2 K ∧
          IsAltBlockTypeWith K n α ∧
          ∃ t : G, t ∈ R ∧ ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
            autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧
            orderOf (conjAct V ⟨t, htV⟩) = 2 ∧
            ∃ σ : Equiv.Perm (Fin n), σ.IsSwap ∧
              ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
                ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
                  σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹) ∧
        autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) ∨
      (IsHatA6Block K ∧ M.relIndex K = 15 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
          ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
            (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
            (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
              Multiplicative.toAdd (e v) =
                ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
                  (Multiplicative.toAdd (e u))) ∧
            ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
              ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
                ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w
                  ∈ W) ∨
      (IsExcA7Block K ∧ M.relIndex K = 35) ∨
      ((IsAltBlockType K 6 ∨ IsSp4Block K) ∧
        IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)) ∨
      (IsG2Block K ∧ IsG2Two ↥(autOn (K ⊔ R) V) ∧
        IsMaxParabolic2 (autOn (K ⊔ R) V) (autOn (M ⊓ K) V ⊔ autOn R V)) ∨
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
          Nonempty (↥(autOn K V) ≃* ↥(StatedSL 3 F))) ∧
        IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ IsMSPair (K ⊔ R) R) ∨
      ((Nonempty (↥(autOn K V) ≃* ↥(StatedSL 4 (ZMod 2))) ∨
          Nonempty (↥(autOn K V) ≃* ↥(StatedSL 5 (ZMod 2)))) ∧
        IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ ¬ IsBorelIn (autOn K V) (autOn (M ⊓ K) V)))

end CFSG.Quasithin
