module

public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.Background.C41PfA
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure HypC41 (H R M L V K : Subgroup G) : Prop where
  hyp : HypC28 H R M L V
  comp : K ∈ cComp H
  charTwo : CharTwo K
  quasi : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  not_le : ¬ K ≤ M

structure SetC41 (H R M L V T K : Subgroup G) : Prop where
  hyp : HypC41 H R M L V K
  sylow : IsSylowTwoOf T M
  le_T : R ≤ T
  red : H = conjClosure K H ⊔ conjClosure L M ⊔ T

@[expose] def C41Case1 (R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 5 ∨ n = 6) ∧ IsAltBlockType (conjClosure L M) n ∧
    V = blockU (conjClosure L M) ∧ IsAltBlockType K (n + 2) ∧ InducesTransposition R K (n + 2) ∧
    M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G)

@[expose] def C41Case2 (M L V K : Subgroup G) : Prop :=
  IsSp4Block K ∧
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSp 2 F))
      (β : ↥(blockU K) →* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
      Fintype.card F = 4 ∧ IsMatrixBlockTypeWith K (StatedSp 2 F) α β ∧
        IsFLineVia (blockU K) (V ⊔ blockZ K) β ∧ IsMaxParabolic2 K (M ⊓ K) ∧
        M ⊓ K = K ⊓ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) ∧
        IsPSL 2 2 2 (ModO2 (conjClosure L M))

@[expose] def C41Case3 (R M L V K : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 < n ∧ Fintype.card F = 2 ^ n ∧
    Nonempty (ModO2 K ≃* ↥(StatedSL 3 F)) ∧ IsMSPair (K ⊔ R) R ∧
    (IsC134Case 1 (K ⊔ R) R K ∨ IsC134Case 2 (K ⊔ R) R K ∨ IsC134Case 3 (K ⊔ R) R K ∨
      IsC134Case 4 (K ⊔ R) R K) ∧
    IsMaxParabolic2 K (M ⊓ K) ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) ∧
    (IsStabilizedLineOfNatural F R M K V ∨
      (IsC134Case 2 (K ⊔ R) R K ∧ ∃ V₁ V₂ : Subgroup G,
        IsStabilizedLineOfNatural F R M K V₁ ∧ IsStabilizedLineOfNatural F R M K V₂ ∧
        V = V₁ ⊔ V₂))

@[expose] def C41Case4 (M L K : Subgroup G) : Prop :=
  (IsPSL 4 2 1 (ModO2 K) ∨ IsPSL 5 2 1 (ModO2 K)) ∧ IsParabolic2 K (M ⊓ K) ∧
    (IsPSL 3 2 1 (ModO2 (conjClosure L M)) ∨ IsPSL 4 2 1 (ModO2 (conjClosure L M)))

@[expose] def C41Concl (H R M L V K : Subgroup G) : Prop :=
  L = conjClosure L M ∧ conjClosure L M ≤ conjClosure K H ∧ conjClosure K H = K ∧
    (C41Case1 R M L V K ∨ C41Case2 M L V K ∨ C41Case3 R M L V K ∨ C41Case4 M L K)

theorem c42_local_intersection_eq (H M L T K : Subgroup G) :
    (M ⊓ (conjClosure K H ⊔ conjClosure L M ⊔ T)) ⊓ K = M ⊓ K := by
  have le_reduction : K ≤ conjClosure K H ⊔ conjClosure L M ⊔ T :=
    le_trans (le_conjClosure K H) (le_trans le_sup_left le_sup_left)
  rw [inf_assoc, inf_eq_right.mpr le_reduction]

theorem c41Concl_of_reduction_identifications {H X R M L V K : Subgroup G}
    (closure_eq : conjClosure K X = conjClosure K H)
    (local_closure_eq : conjClosure L (M ⊓ X) = conjClosure L M)
    (local_intersection_eq : (M ⊓ X) ⊓ K = M ⊓ K)
    (reduced_conclusion : C41Concl X R (M ⊓ X) L V K) : C41Concl H R M L V K := by
  have model_eq (d p f : ℕ) :
      IsPSL d p f (ModO2 (conjClosure L (M ⊓ X))) =
        IsPSL d p f (ModO2 (conjClosure L M)) :=
    congrArg (fun N : Subgroup G => IsPSL d p f (ModO2 N)) local_closure_eq
  simpa only [C41Concl, C41Case1, C41Case2, C41Case3, C41Case4,
    IsStabilizedLineOfNatural, model_eq, closure_eq, local_closure_eq, local_intersection_eq]
    using reduced_conclusion

@[expose] def C48Case1 (R L V : Subgroup G) : Prop :=
  ∃ n : ℕ, IsPSL 2 2 n (ModO2 L) ∧
    ((∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
          (R.subgroupOf (L ⊔ R)) (StatedSL 2 F)) ∨
      (n = 2 ∧ IsAltNaturalSection (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
        (R.subgroupOf (L ⊔ R)) 5) ∨
      (1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsSumOfNaturalModules (L ⊔ R) V (V ⊓ Subgroup.centralizer (L : Set G))
          (R.subgroupOf (L ⊔ R)) (StatedSL 2 F) false 2))

@[expose] def KDescribedC31C41 (H R M L V K : Subgroup G) : Prop :=
  (CFSG.Open.IsComponentOf K H ∧ C31Conclusion H R M L V K) ∨
    (K ∈ cComp H ∧ CharTwo K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ M ∧
      C41Concl H R M L V K)

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC41 H R M L V K →
    C41Concl H R M L V K

@[expose] def C42HypothesisPreservation : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), HypC41 H R M L V K →
    IsSylowTwoOf T M → R ≤ T →
    conjClosure K H ⊔ conjClosure L M ⊔ T ≤ H ∧
    HypC41 (conjClosure K H ⊔ conjClosure L M ⊔ T) R (M ⊓ (conjClosure K H ⊔ conjClosure L M ⊔ T))
      L V K

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_4_2_hypothesis_preservation
    : C42HypothesisPreservation := by
  intro G _ _ H R M L V T K h hT hRT
  obtain ⟨hA37, hA38, -⟩ := CFSG.Quasithin.H13.a3ForSQTK_holds
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp h.comp
  have hMH : M ≤ H := h.hyp.le_H
  have hM0H : CFSG.Quasithin.conjClosure L M ≤ H :=
    (CFSG.Quasithin.C2Nine.conjClosure_le_M h.hyp).trans hMH
  have hK0H : CFSG.Quasithin.conjClosure K H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun x hx z hz => H.mul_mem (H.mul_mem hx (hKH hz)) (H.inv_mem hx)
  have hTH : T ≤ H := hT.1.trans hMH
  have hXH : CFSG.Quasithin.conjClosure K H ⊔ CFSG.Quasithin.conjClosure L M ⊔ T ≤ H :=
    sup_le (sup_le hK0H hM0H) hTH
  have hX : CFSG.Quasithin.conjClosure L M ⊔ T ≤
      CFSG.Quasithin.conjClosure K H ⊔ CFSG.Quasithin.conjClosure L M ⊔ T :=
    sup_le_sup_right le_sup_right T
  have hKX : K ≤ CFSG.Quasithin.conjClosure K H ⊔ CFSG.Quasithin.conjClosure L M ⊔ T :=
    le_trans (CFSG.Quasithin.le_conjClosure K H) (le_trans le_sup_left le_sup_left)
  refine ⟨hXH, ?_⟩
  exact
    { hyp := CFSG.Quasithin.c2_9_three hA3 h.hyp hT hRT hX hXH
      comp := CFSG.Quasithin.cComp_mem_of_le h.comp hKX hXH
      charTwo := h.charTwo
      quasi := h.quasi
      not_le := fun hKM => h.not_le (hKM.trans inf_le_left) }

end

@[expose] def C_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), HypC41 H R M L V K →
    IsSylowTwoOf T M → R ≤ T →
    let X := conjClosure K H ⊔ conjClosure L M ⊔ T
    (conjClosure L M ⊔ T ≤ X ∧ X ≤ H) ∧
    HypC41 X R (M ⊓ X) L V K ∧
    SetC41 X R (M ⊓ X) L V T K ∧
    conjClosure L (M ⊓ X) = conjClosure L M ∧
    (C41Concl X R (M ⊓ X) L V K →
      conjClosure K H = conjClosure K X ∧ C41Concl H R M L V K)

@[expose] def C_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    ¬ conjClosure L M ≤ centralizerSection H (conjClosure K H) (pCoreOf 2 (conjClosure K H))

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_4_3
    : C_4_3 := by
  intro G _ _ H R M L V T K hSet hC
  obtain ⟨hA37, hA38, -⟩ := CFSG.Quasithin.H13.a3ForSQTK_holds
  have hA3 : CFSG.Quasithin.A3Orbits G := CFSG.Quasithin.a3Orbits_of_a37_a38 hA37 hA38
  have hK : K ∈ cComp H := hSet.hyp.comp
  have hNK : CFSG.Quasithin.conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.C41Pf.conjClosure_le_normalizer hA3 hSet.hyp.hyp hK
  have hnc := CFSG.Quasithin.C41Pf.not_commutator_le_pCoreOf
    (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc111Statement_holds G)
    (CFSG.Quasithin.asc19Statement_holds G) hA3 hSet.hyp.hyp hK hSet.hyp.not_le
  apply hnc
  have hKK₀ : K ≤ CFSG.Quasithin.conjClosure K H := CFSG.Quasithin.le_conjClosure K H
  have hKO : K ≤ Subgroup.normalizer
      ((pCoreOf 2 (CFSG.Quasithin.conjClosure K H) : Subgroup G) : Set G) :=
    hKK₀.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CFSG.Quasithin.conjClosure K H))
  have hKinf : K ≤ Subgroup.normalizer
      ((K ⊓ pCoreOf 2 (CFSG.Quasithin.conjClosure K H) : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x)
      (Subgroup.mem_normalizer_iff.mp (hKO hk) x)
  have hKOinf : K ⊓ pCoreOf 2 (CFSG.Quasithin.conjClosure K H) ≤
      pCoreOf 2 K := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKinf
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (CFSG.Quasithin.conjClosure K H)).to_le
        inf_le_right)
  refine Subgroup.commutator_le.mpr ?_
  intro m hm k hk
  have hmK : m * k * m⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hNK hm) k).mp hk
  obtain ⟨-, -, -, hmO⟩ := hC hm
  have hmO' : k * m * k⁻¹ * m⁻¹ ∈ pCoreOf 2 (CFSG.Quasithin.conjClosure K H) :=
    hmO k (hKK₀ hk)
  have hinv : m * k * m⁻¹ * k⁻¹ = (k * m * k⁻¹ * m⁻¹)⁻¹ := by group
  refine hKOinf ?_
  rw [commutatorElement_def]
  refine Subgroup.mem_inf.mpr ⟨K.mul_mem hmK (K.inv_mem hk), ?_⟩
  rw [hinv]
  exact (pCoreOf 2 (CFSG.Quasithin.conjClosure K H)).inv_mem hmO'

end

@[expose] def C_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G)

@[expose] def C_4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) →
    (conjClosure L M ≤ M ⊓ K ∧ ((conjClosure L M).subgroupOf (M ⊓ K)).Normal) ∧
    (conjClosure L M ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) ≤
        (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ∧
      (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ≤
        (M ⊓ K) ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ∧
    K = conjClosure K H

@[expose] def C_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) → conjClosure L M ≤ M ⊓ K → K = conjClosure K H →
    IsChiBlock2 H K → IsAltType K 7 ∧ C41Case1 R M L V K

@[expose] def C_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V T K : Subgroup G), SetC41 H R M L V T K →
    R ≤ Subgroup.normalizer (K : Set G) → conjClosure L M ≤ M ⊓ K → K = conjClosure K H →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (ModO2 K ≃* ↥(StatedSL 3 F))) →
    C41Case3 R M L V K

@[expose] def C_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V : Subgroup G), HypC28 H R M L V → M < H →
    L = conjClosure L M ∧
    ∃ K : Subgroup G, K ∈ cComp H ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ L ≤ K ∧
      (C48Case10 H R M L V K ∨
        ((C48Case1 R L V ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
            C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
            C48Case7 H R M L V K ∨ C48Case8 H R M L V K ∨ C48Case9 H R M L V K) ∧
          ¬ K ≤ M ∧ M ≤ Subgroup.normalizer (K : Set G) ∧ KDescribedC31C41 H R M L V K))

end CFSG.ASVolI
