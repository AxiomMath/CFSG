module

public import CFSG.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def C27Concl {G : Type} [Group G] [Finite G] (H R M K V : Subgroup G) : Prop :=
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

theorem c27Concl_of_statement {G : Type} [Group G] [Finite G] (h : ASC27Statement G)
    {H R M K V : Subgroup G} (hyp : HypC23 H R M) (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hc : CharTwo K) (hn : ¬ K ≤ M)
    (hR : R ≤ Subgroup.normalizer (K : Set G))
    (hV : V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) : C27Concl H R M K V :=
  h H R M K V hyp hK hq hc hn hR hV

end CFSG.Quasithin
