module

import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

section Vocabulary

@[expose] def FacA5 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 5))

@[expose] def FacA6 (X : Type*) [Group X] : Prop :=
  Group.IsPerfect X ∧ Sec4.IsTripleCover X (alternatingGroup (Fin 6))

@[expose] def FacHJ (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)

variable {Γ : Type*} [Group Γ]

@[expose] def IsInv3 (D E Q : Subgroup Γ) : Prop :=
  Q ≤ D ∧ E ≤ Subgroup.normalizer (Q : Set Γ) ∧ ¬ 3 ∣ Nat.card Q

@[expose] def IsInvQ (D E Q : Subgroup Γ) : Prop :=
  IsInv3 D E Q ∧ Q = ⁅Q, E⁆

structure ProdSetting (U V E : Subgroup Γ) : Prop where
  comm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u
  elem : CFSG.Assembly.IsElemAbelian 3 E
  card : Nat.card E = 27
  norm : E ≤ Subgroup.normalizer ((U ⊔ V : Subgroup Γ) : Set Γ)
  perfect : Group.IsPerfect ↥(U ⊔ V)
  rank : ∀ F : Subgroup Γ, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27
  gen : U ⊔ V ≤ sSup {Q : Subgroup Γ | IsInvQ (U ⊔ V) E Q}

@[expose] def ProdTypeA (U V : Subgroup Γ) : Prop :=
  (Nat.card ↥(U ⊓ V) = 3 ∧ FacA6 ↥U ∧ FacA6 ↥V) ∨
    (U ⊓ V = ⊥ ∧ ((FacA6 ↥U ∧ FacA5 ↥V) ∨ (FacA5 ↥U ∧ FacA6 ↥V) ∨ (FacA5 ↥U ∧ FacA5 ↥V) ∨
      (FacA5 ↥U ∧ FacHJ ↥V)))

@[expose] def ProdTypeHJ (U V : Subgroup Γ) : Prop :=
  U ⊓ V = ⊥ ∧ FacHJ ↥U ∧ FacA5 ↥V

theorem exists_noncomm_of_fac {X : Type*} [Group X] (h : FacA5 X ∨ FacA6 X) :
    ∃ a b : X, a * b ≠ b * a := by
  rcases h with h5 | ⟨hp, hcard, ⟨φ⟩⟩
  · obtain ⟨e⟩ := h5
    obtain ⟨a, b, hab⟩ := Sec15.Y4Core.alternatingGroup_five_nonabelian
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  · obtain ⟨a, b, hab⟩ := Sec15.Y4Core.alternatingGroup_six_nonabelian
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm a)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm b)
    refine ⟨x, y, fun hc => hab ?_⟩
    have h1 : φ ((x : X ⧸ Subgroup.center X) * y) = φ ((y : X ⧸ Subgroup.center X) * x) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    rw [map_mul, map_mul, hx, hy] at h1
    simpa using h1

theorem ProdTypeA.fac_left {U V : Subgroup Γ} (h : ProdTypeA U V) : FacA5 ↥U ∨ FacA6 ↥U := by
  rcases h with ⟨-, hU, -⟩ | ⟨-, ⟨hU, -⟩ | ⟨hU, -⟩ | ⟨hU, -⟩ | ⟨hU, -⟩⟩
  exacts [Or.inr hU, Or.inr hU, Or.inl hU, Or.inl hU, Or.inl hU]

end Vocabulary

@[expose] def FixA5 : Prop :=
  ∀ (X : Type) [Group X], FacA5 X → ∀ σ : MulAut X, σ ^ 3 = 1 → σ ≠ 1 →
    ∀ y : X, σ y = y → ∃ k : ℕ, y ^ 3 ^ k = 1

@[expose] def FixA6Cover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FacA6 X → ∀ σ : MulAut X, σ ^ 3 = 1 → σ ≠ 1 →
    ∀ y : X, y⁻¹ * σ y ∈ Subgroup.center X → ∃ k : ℕ, y ^ 3 ^ k ∈ Subgroup.center X

@[expose] def CentJ2E9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FacHJ X → ∀ F : Subgroup X,
    CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 →
      ∀ y : X, (∀ f ∈ F, y * f = f * y) → ∃ k : ℕ, y ^ 3 ^ k = 1

@[expose] def ProdCoreA : Prop :=
  FixA5 → FixA6Cover → CentJ2E9 →
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (U V E : Subgroup Γ), ProdSetting U V E → ProdTypeA U V →
    ∃ B : Subgroup Γ, IsHyperplane E B ∧
      (∀ Q : Subgroup Γ, IsInv3 (U ⊔ V) E Q → B ≤ Subgroup.centralizer (Q : Set Γ) → Q ≤ U) ∧
      (∀ B' : Subgroup Γ, IsHyperplane E B' → B' ≠ B → ∀ Q : Subgroup Γ,
        IsInv3 (U ⊔ V) E Q → B' ≤ Subgroup.centralizer (Q : Set Γ) → Q ≤ V) ∧
      pPrimeCoreOf 3 ((U ⊔ V) ⊓ Subgroup.centralizer (B : Set Γ)) = ⊥

@[expose] noncomputable def Step148ProdShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ (M : Subgroup G) (hM : M ∈ scriptY2 A),
      generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ¬ IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        letI := ker148_normal hM.1.2
        ∃ U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M),
          img148 A M (deltaZero A (lB A) M) = U ⊔ V ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧
          Group.IsPerfect ↥(U ⊔ V) ∧ img148 A M J = U ∧ (ProdTypeA U V ∨ ProdTypeHJ U V)

@[expose] noncomputable def Step148ProdBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (M : Subgroup G) (hM : M ∈ scriptY A) (B : Subgroup G),
      IsHyperplane A B →
      letI := ker148_normal hM.2
      YBOne A (lB A) M B →
        img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G))) ≤
          pPrimeCoreOf 3 (img148 A M (deltaZero A (lB A) M) ⊓
            Subgroup.centralizer (img148 A M B : Set (↥(M ⊔ A) ⧸ ker148 A M)))

section Glue

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} [(ker148 A M).Normal]

theorem exists_hyperplane_of_img (hA : Late.IsE27 A)
    {BE : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hBE : IsHyperplane (img148 A M A) BE) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ img148 A M B = BE := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set φ := QuotientGroup.mk' (ker148 A M) with hφ
  set B : Subgroup G := ((BE.comap φ).map (M ⊔ A).subtype) ⊓ A with hB
  have hBA : B ≤ A := inf_le_right
  have himg : img148 A M B = BE := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨g, hg, hgB, rfl⟩ := mem_img148_iff.mp hx
      obtain ⟨y, hy, hyg⟩ := hgB.1
      have : y = ⟨g, hg⟩ := Subtype.ext hyg
      rw [← this]
      exact hy
    · intro x hx
      obtain ⟨a, ha, haA, rfl⟩ := mem_img148_iff.mp (hBE.1 hx)
      exact mem_img148_iff.mpr ⟨a, ha, ⟨⟨⟨a, ha⟩, hx, rfl⟩, haA⟩, rfl⟩
  refine ⟨B, ⟨hBA, ?_⟩, himg⟩
  have h1 : Nat.card (img148 A M A) = Nat.card A := Ronan148J.card_img148_of_le hA3 le_rfl
  have h2 : Nat.card (img148 A M B) = Nat.card B := Ronan148J.card_img148_of_le hA3 hBA
  rw [← h1, hBE.2, ← himg, h2]

theorem isHyperplane_img148 (hA : Late.IsE27 A) {B : Subgroup G} (hB : IsHyperplane A B) :
    IsHyperplane (img148 A M A) (img148 A M B) := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  refine ⟨img148_mono hB.1, ?_⟩
  rw [Ronan148J.card_img148_of_le hA3 le_rfl, Ronan148J.card_img148_of_le hA3 hB.1]
  exact hB.2

theorem le_of_img148_le (hA : Late.IsE27 A) {B B' : Subgroup G} (hB : B ≤ A) (hB' : B' ≤ A)
    (h : img148 A M B ≤ img148 A M B') : B ≤ B' := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  intro g hg
  have hx : alpha148 A M g (hB hg) ∈ img148 A M B :=
    mem_img148_iff.mpr ⟨g, Subgroup.mem_sup_right (hB hg), hg, (alpha148_eq_mk' (hB hg)).symm⟩
  obtain ⟨g', hg', hg'B, he⟩ := mem_img148_iff.mp (h hx)
  have he' : alpha148 A M g' (hB' hg'B) = alpha148 A M g (hB hg) := by
    rw [alpha148_eq_mk']
    exact he
  have := alpha148_injective hA3 (hB' hg'B) (hB hg) he'
  rw [← this]
  exact hg'B

theorem isInvQ_img148 {Q : Subgroup G} (hQ : Q ∈ collectionIn (scriptQZero A (lB A)) M) :
    IsInvQ (img148 A M (deltaZero A (lB A) M)) (img148 A M A) (img148 A M Q) := by
  obtain ⟨hQ0, hQM⟩ := hQ
  obtain ⟨hpi, hAQ, -⟩ := mem_scriptQ_iff.mp hQ0.1
  have h3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hpi
  refine ⟨⟨img148_mono (le_deltaZero hQ0 hQM), img148_le_normalizer hAQ,
    Item148PtRes.not_three_dvd_card_img148 h3⟩, ?_⟩
  rw [← HJRes2.img148_commutator_eq (hQM.trans le_sup_left) le_sup_right, ← hQ0.2]

theorem gen_img148 :
    img148 A M (deltaZero A (lB A) M) ≤
      sSup {Q : Subgroup (↥(M ⊔ A) ⧸ ker148 A M) |
        IsInvQ (img148 A M (deltaZero A (lB A) M)) (img148 A M A) Q} :=
  (Read148Perf.img148_deltaZero_le (lB A)).trans
    (sSup_le_sSup (by rintro _ ⟨Q, hQ, rfl⟩; exact isInvQ_img148 hQ))

theorem img148_deltaZero_centralizer_le {B : Subgroup G}
    {T : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)}
    (hT : ∀ Q : Subgroup (↥(M ⊔ A) ⧸ ker148 A M),
      IsInv3 (img148 A M (deltaZero A (lB A) M)) (img148 A M A) Q →
        img148 A M B ≤ Subgroup.centralizer (Q : Set (↥(M ⊔ A) ⧸ ker148 A M)) → Q ≤ T) :
    img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G))) ≤ T := by
  show img148 A M (sSup (collectionIn (scriptQZero A (lB A))
    (M ⊓ Subgroup.centralizer (B : Set G)))) ≤ T
  refine (Read148Perf.img148_sSup_le (fun Q hQ => hQ.2.trans (inf_le_left.trans le_sup_left))).trans
    (sSup_le ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  have hQM : Q ≤ M := hQ.2.trans inf_le_left
  refine hT _ (isInvQ_img148 ⟨hQ.1, hQM⟩).1 ?_
  rw [← Subgroup.le_centralizer_iff]
  exact Ronan148J.img148_le_centralizer (hQ.2.trans inf_le_right)

omit [Finite G] in
theorem map_le_of_img148_le {X J : Subgroup G} (hX : X ≤ M) (hJ : J ≤ M)
    (h : img148 A M X ≤ img148 A M J) :
    (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤
      (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) := by
  rw [← Subgroup.map_le_map_iff_of_injective
    (Proof15Res8Prod.iota148_injective (A := A) (M := M)),
    Proof15Res8Prod.map_iota148 hX, Proof15Res8Prod.map_iota148 hJ]
  exact h

end Glue

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
