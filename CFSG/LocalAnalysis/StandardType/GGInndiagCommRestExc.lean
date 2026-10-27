module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestCore
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagRee
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace InndiagCommRest

theorem ggOutComm_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGOutComm (LargeEvenCenterQuot (LargeEvenSzGroup a K)) := by
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      GGOutComm (LargeEvenCenterQuot H) from key _ (largeEvenSzGroup_eq a K)
  rintro H rfl
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  have := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1
  have hO : GGOutCyclic (suzukiGroup a K) :=
    ggOutCyclic_of_hom (QuotientGroup.mk' (inner _)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)
  exact (hO.of_mulEquiv (centerQuotEquivOfBot hZ)).ggOutComm

theorem ggOutComm_g2der {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x) :
    GGOutComm (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) := by
  have hC : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) .PSU 3 3 1 := by
    rcases lieModel_g2der K hK hR with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · cases ht
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hC
  have hu : UnitaryFieldData 3 1 K' := ⟨Nat.prime_three, le_rfl, hK'.trans (by norm_num)⟩
  obtain ⟨-, -, -, -, hO, -⟩ := unitary_full_diagonal_outer_order hu (n := 3) le_rfl (by norm_num)
  have h2 : Nat.card (Outer (unitaryPSU hu 3)) = 2 := by
    rw [hO]
    norm_num
  exact (ggOutComm_of_card_outer_prime Nat.prime_two h2).of_mulEquiv
    (e.trans (unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm)

theorem ggOutComm_twF4der
    {a : ℕ} (ha : a = 0) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGOutComm (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  subst ha
  exact ggOutComm_of_card_outer_prime Nat.prime_two
    (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound _ 2 1
      ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩).2.2.1

end InndiagCommRest

open InndiagCommRest

theorem largeEvenLabelAll_inndiagComm_twB2 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twB2) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  intro Q h
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    ggInndiagCommEq_of_subset_inn subset_rfl (ggOutComm_suzuki (by omega) hK)⟩

section Twisted


theorem largeEvenLabelAll_inndiagComm_triD4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn
    (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab ht) ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGOutComm R)
    (fun K _ _ hK _ _ => (ggOutCyclic_triD4 hn K hK).ggOutComm) hQ

theorem largeEvenLabelAll_inndiagComm_twF4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn (largeEvenLabelAll_subset_inn_twF4 hlab ht) ?_
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, h3⟩ := hl
  intro Q hQ
  exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGOutComm R)
    (fun K _ _ hK _ _ => (ggOutCyclic_twF4 (by omega) K hK).ggOutComm) hQ

end Twisted

theorem largeEvenLabelAll_inndiagComm_g2der
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2der) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn (largeEvenLabelAll_subset_inn hlab
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))))) ?_
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q h
  exact recipeChevalley_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGOutComm R)
    (fun K _ _ hK _ hR => ggOutComm_g2der hK hR) h

theorem largeEvenLabelAll_inndiagComm_twF4der
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4der) : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  refine largeEvenLabelAll_inndiagComm_of_inn (largeEvenLabelAll_subset_inn hlab
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))))) ?_
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, hn1⟩ := hlab
  subst hn1
  intro Q h
  exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGOutComm R)
    (fun K _ _ hK _ _ => ggOutComm_twF4der (by norm_num) hK) h

end CFSG.StandardType

end
