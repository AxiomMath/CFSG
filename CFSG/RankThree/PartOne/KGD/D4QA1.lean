module

public import CFSG.RankThree.PartOne.KGD.D4Twist
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.SigmaMain

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Generic

variable {τ : Tag} {L : Type} [Field L]

theorem a1_sigma_family (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (S : Subgroup (SL2 L)) [Finite S]
    (hS1 : ∀ B : SL2 L, n * Φ (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔ B ∈ S)
    (hS2 : CFSG.IsQuasisimple S)
    (hS3 : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Subgroup (ModGL τ L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan τ L {θ, -θ} ∧ P ≤ twistedFixedPoints n Φ ∧ P ≤ adjointGroup τ L ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L {θ, -θ}, y ∈ twistedFixedPoints n Φ →
        ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L {θ, -θ}, y ∈ twistedFixedPoints n Φ →
        (∀ u ∈ P, y * u = u * y) → y ∈ subtorusSigma n Φ {θ, -θ}) := by
  classical
  set ρ := rootSL2 τ L θ with hρdef
  have hρinj : Function.Injective ρ := rootSL2_injective_of_field θ
  have hρadj : ∀ A, ρ A ∈ adjointGroup τ L :=
    (exceptional_Lang_root_rank_one_data τ L θ).2.2.2.2.1
  have hQ : rootSpan τ L {θ, -θ} = rootRankOneGroup τ L θ := by
    rw [rootSpan, iSup_insert, iSup_singleton,
      (exceptional_Lang_root_rank_one_torus_transport τ L hθ).1]
  set Q := rootRankOneGroup τ L θ with hQdef
  set Rs := twistedFixedPoints n Φ with hRs
  have hQrange : ∀ u ∈ Q, ∃ B, ρ B = u := fun u hu => MonoidHom.mem_range.1 hu
  set P : Subgroup (ModGL τ L) := Q ⊓ Rs with hPdef
  have hPS : P = S.map ρ := by
    ext u
    constructor
    · rintro ⟨hu, hu2⟩
      obtain ⟨B, rfl⟩ := hQrange u hu
      exact ⟨B, (hS1 B).1 hu2, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨⟨B, rfl⟩, (hS1 B).2 hB⟩
  have hPe : S ≃* P :=
    (Subgroup.equivMapOfInjective S ρ hρinj).trans (MulEquiv.subgroupCongr hPS.symm)
  have hPq : CFSG.IsQuasisimple P := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hS2
  have hPfin : Finite P := Finite.of_equiv S hPe.toEquiv
  have hle : torusGroup τ L ⊔ Q ≤ Subgroup.normalizer (Q : Set (ModGL τ L)) :=
    sup_le (torusGroup_le_normalizer_rootRankOneGroup hθ) Subgroup.le_normalizer
  refine ⟨P, hPfin, hPq, ?_, inf_le_right, ?_, ?_, ?_⟩
  · rw [hQ]
    exact inf_le_left
  · intro u hu
    obtain ⟨B, hB, rfl⟩ := hPS ▸ hu
    exact hρadj B
  · intro y hy hyR u hu
    rw [hQ] at hy
    exact ⟨((Subgroup.mem_normalizer_iff.1 (hle hy)) u).1 hu.1,
      Rs.mul_mem (Rs.mul_mem hyR hu.2) (Rs.inv_mem hyR)⟩
  · intro y hy hyR hcomm
    rw [hQ] at hy
    have hHQ : y ∈ (torusGroup τ L : Set (ModGL τ L)) * (Q : Set (ModGL τ L)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (torusGroup_le_normalizer_rootRankOneGroup hθ)]
      exact hy
    have hQc : ∀ A : SL2 L, y * ρ A = ρ A * y :=
      commute_rootSL2_of_commute_fixed hθ hS3 hHQ
        (fun A hA => hcomm _ (by rw [hPS]; exact ⟨A, hA, rfl⟩))
    have hHd : y ∈ torusGroup τ L := mem_torusGroup_of_centralizes_rootSL2 hθ hHQ hQc
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hHd, hyR⟩, ?_⟩
    rw [hQ, Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (hQc A).symm

end Generic

section D4

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ] [IsAlgClosed L]

theorem d4Q_a1_data (hf : 1 ≤ f) (hq4 : 4 ≤ ℓ ^ f) {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x)
    {θ : Fin TwistTag.D4.tag.rank → ℤ} (hθ : IsRoot TwistTag.D4.tag θ)
    (hρθ : permLattice TwistTag.D4.perm θ = θ) :
    ∃ S : Subgroup (SL2 L), Finite S ∧ CFSG.IsQuasisimple S ∧
      Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range ∧
      ∀ B : SL2 L, n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)
          (rootSL2 TwistTag.D4.tag L θ B) * n⁻¹ = rootSL2 TwistTag.D4.tag L θ B ↔ B ∈ S := by
  classical
  obtain ⟨k, _, _, _, hk⟩ := exists_finite_field_into ℓ f hf L
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card k := fun c => by
    rw [hk]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq_twist hn hθ
  have hγ : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • permLattice TwistTag.D4.perm θ = -θ := by
    rw [hρθ, hnW]
  rw [hγ] at hs
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hθ
  have hMdef : swapGL * diagUnitOne a * diagUnitOne s =
      (swapGL * diagUnitOne (a * s) : GL (Fin 2) L) := by
    rw [mul_assoc, diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k) Fr hFr 1 (a * s)
    (swapGL * diagUnitOne a * diagUnitOne s) (by
      rw [hMdef, coe_swapGL_mul_diagUnitOne]
      simp)
  have hk4 : 4 ≤ Nat.card k := hk ▸ hq4
  obtain ⟨hfin, hqs⟩ := sl2_conj_range_quasisimple (K := k) (L := L) hk4 Pm
  refine ⟨_, hfin, hqs, sl2_conj_range_centralizer Pm, fun B => ?_⟩
  refine a1_hS1_of_action Fr hFr Pm (fun B' => ?_) B
  rw [hPm]
  change n * (diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr) (rootSL2 TwistTag.D4.tag L θ B') *
    (diagramMap TwistTag.D4 L)⁻¹) * n⁻¹ = _
  rw [entrywise_rootSL2_of_field Fr θ B']
  calc n * (diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L θ
        (Matrix.SpecialLinearGroup.map Fr B') * (diagramMap TwistTag.D4 L)⁻¹) * n⁻¹
      = n * diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L θ
          (Matrix.SpecialLinearGroup.map Fr B') * (n * diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = _ := by
      rw [hs, ha, ← conjSL_mul]

end D4

end CFSG.RankThree.PartOne.KGD
