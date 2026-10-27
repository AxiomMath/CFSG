module

public import CFSG.RankThree.PartTwo.Sec21.Item211
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofFour
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def Table211 (A L : Subgroup G) : Prop :=
  (Nonempty (lBar L ≃* NativeSporadic.M12) ∧ Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.M22) ∧ Nonempty (starOf A L ≃* QuaternionGroup 2)) ∨
  (Nonempty (lBar L ≃* NativeSporadic.M23) ∧
    Nonempty (starOf A L ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  (Nonempty (lBar L ≃* NativeSporadic.M24) ∧
    (Nonempty (starOf A L ≃* DihedralGroup 6) ∨ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.J2) ∧ Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.J4) ∧ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.HS) ∧
    Nonempty (starOf A L ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  (Nonempty (lBar L ≃* NativeSporadic.He) ∧
    (Nonempty (starOf A L ≃* DihedralGroup 6) ∨ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))) ∨
  (Nonempty (lBar L ≃* NativeSporadic.Ru) ∧ Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))

section Certs

@[expose] def List211 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  (∃ x ∈ A, KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) ∨
  (Nat.card A = 3 ^ 3 ∧ Sec4.IsHeisCentral ↥(Sec13.lBarA c L A) (lBar L) ∧
    (Sec4.IsTripleCover (lBar L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (lBar L) NativeSporadic.M22)) ∨
  (Nat.card A = 3 ^ 3 ∧ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    (ChevalleyExceptionalModel (lBar L) .G2 p 1 ∨
      Nonempty (lBar L ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (lBar L ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (lBar L ≃* projSL 4 (GaloisField p 1))) ∨
      ∃ e : ℕ, 1 ≤ e ∧ (Sec4.IsSLThreePiAt (lBar L) (p ^ e) ∨ Sec4.IsoLThreePi (lBar L) p e))) ∨
  (Nat.card A = 3 ^ 3 ∧ Nonempty (lBar L ≃* alternatingGroup (Fin 7)) ∧
    Nonempty (starOf A L ≃* Multiplicative (ZMod 4))) ∨
  (Nat.card A = 3 ^ 4 ∧ Nonempty (lBar L ≃* alternatingGroup (Fin 9)) ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))) ∨
  (Nat.card A = 3 ^ 3 ∧ Table211 A L) ∨
  (Nat.card A = 3 ^ 4 ∧
    (Nonempty (lBar L ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar L) NativeSporadic.J3) ∧
    Sec4.IsExtOf ↥(starOf A L) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))) ∨
  (Nat.card A = 3 ^ 3 ∧ Sec4.IsTripleCover (lBar L) NativeSporadic.ON) ∨
  (Nat.card A = 3 ^ 3 ∧ (∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) ∧ Sec4.IsTypeCOn A L) ∨
        (Nonempty (lBar L ≃* SL3 n) ∧ IsTypeCOnBarSL A L))) ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
  (Nat.card A = 3 ^ 3 ∧ (∃ n : ℕ, 0 < n ∧ Even n ∧
      (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
        ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) ∧
    Nonempty (starOf A L ≃* DihedralGroup 6)) ∨
  (Nat.card A = 3 ^ 3 ∧ ((∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (lBar L ≃* projSU 4 2 n))) ∨
      Nonempty (lBar L ≃* projSU 5 2 2) ∨ StatedClassicalModel (lBar L) .PSL 4 2 1 ∨
      StatedClassicalModel (lBar L) .PSL 5 2 1) ∧
    Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
  (Nat.card A = 3 ^ 4 ∧ (∃ n : ℕ, Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))) ∨
  (Nat.card A = 3 ^ 4 ∧ StatedClassicalModel (lBar L) .PSp 3 2 1 ∧
    Nonempty (starOf A L ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Item211List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) ∧ List211 A c L

@[expose] def Item211NoField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) →
      ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

@[expose] def Item211NoFieldThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

@[expose] def Item211ResidualSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    ¬ ((Nat.card A = 3 ^ 3 ∧ Sec4.IsHeisCentral ↥(Sec13.lBarA c L A) (lBar L) ∧
          Sec4.IsTripleCover (lBar L) (alternatingGroup (Fin 7))) ∨
        (Nat.card A = 3 ^ 3 ∧ Nonempty (lBar L ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (starOf A L ≃* Multiplicative (ZMod 4))) ∨
        (Nat.card A = 3 ^ 3 ∧ Nonempty (lBar L ≃* NativeSporadic.M12) ∧
          Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
        (Nat.card A = 3 ^ 3 ∧ Sec4.IsTripleCover (lBar L) NativeSporadic.ON))

@[expose] def Item211ResidualLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    ¬ ((Nat.card A = 3 ^ 3 ∧ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
          (ChevalleyExceptionalModel (lBar L) .G2 p 1 ∨
            Nonempty (lBar L ≃* projSp 2 (GaloisField p 1)) ∨
            (p % 3 = 1 ∧ Nonempty (lBar L ≃* projSU 4 p 1)) ∨
            (p % 3 = 2 ∧ Nonempty (lBar L ≃* projSL 4 (GaloisField p 1))) ∨
            ∃ e : ℕ, 1 ≤ e ∧
              (Sec4.IsSLThreePiAt (lBar L) (p ^ e) ∨ Sec4.IsoLThreePi (lBar L) p e))) ∨
        (Nat.card A = 3 ^ 4 ∧ Nonempty (lBar L ≃* projSU 4 2 1) ∧
          Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))) ∨
        (Nat.card A = 3 ^ 4 ∧ Nonempty (lBar L ≃* alternatingGroup (Fin 9)) ∧
          Nonempty (starOf A L ≃* Equiv.Perm (Fin 4))))

end Certs

@[expose] def Item211HeisStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
    Sec4.IsHeisCentral ↥(Sec13.lBarA c L A) (lBar L) →
    Sec4.IsTripleCover (lBar L) NativeSporadic.M22 →
    CFSG.Assembly.IsElemAbelian 3 (starOf A L) ∧ Nat.card (starOf A L) = 9

namespace Item211Proof

theorem sectionCentralizer_eq (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) :
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, hc3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun x hx => hAe.2 x hx.1
  rw [Sec13.sectionCentralizer_eq_inf hAL, hCA]

theorem exists_invTwoBarNontrivial {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) :
    ∃ E' ∈ partTwoE G, E' ≤ A ∧ Sec8.InvTwoBarNontrivial E' L := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  obtain ⟨E', hE', hE'A, -, U', hU', hcomm⟩ :=
    mem_lZeroUnion_iff.mp (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A c
      hpairs.2.2.1))
  refine ⟨E', hE', hE'A, ?_⟩
  obtain ⟨hU'L, hU'2, hE'U'⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hU'
  set θL := aschbacherSolvableCore 3 L with hθL
  refine ⟨(U'.subgroupOf L).map (QuotientGroup.mk' θL), ?_, ?_, ?_⟩
  · intro hbot
    apply hcomm
    have hU'θ : U' ≤ inSubgroup (aschbacherSolvableCore 3) L := by
      intro u hu
      have hmem : QuotientGroup.mk' θL (⟨u, hU'L hu⟩ : L) ∈
          (U'.subgroupOf L).map (QuotientGroup.mk' θL) := ⟨⟨u, hU'L hu⟩, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact ⟨_, hmem, rfl⟩
    rw [Subgroup.commutator_le]
    intro u hu e he
    have h1 : e * u⁻¹ * e⁻¹ ∈ U' :=
      (Subgroup.mem_normalizer_iff.mp (hE'U' he) u⁻¹).mp (U'.inv_mem hu)
    rw [commutatorElement_def]
    have : u * e * u⁻¹ * e⁻¹ = u * (e * u⁻¹ * e⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hU'θ hu) (hU'θ h1)
  · exact (hU'2.comap_of_injective L.subtype L.subtype_injective).map _
  · intro τ hτ y hy
    obtain ⟨h, hN, hE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    obtain ⟨⟨q, hqL⟩, hq, rfl⟩ := hy
    have hqU : q ∈ U' := Subgroup.mem_subgroupOf.mp hq
    have hhq : h * q * h⁻¹ ∈ U' := (Subgroup.mem_normalizer_iff.mp (hE'U' hE) q).mp hqU
    exact ⟨⟨h * q * h⁻¹, hU'L hhq⟩, Subgroup.mem_subgroupOf.mpr hhq, rfl⟩

end Item211Proof

section Certs

theorem item211NoField_of (h3 : Item211NoFieldThree) (h4 : Item1134Four) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item211NoField := by
  intro G _ _ A E U c L hpair hm x hx
  rcases hm with hm | hm
  · exact h3 G A E U c L hpair hm x hx
  · have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
    have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
    have hL : L ∈ lStarAt A c :=
      ⟨lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1),
        (lZeroStarAt_subset A c) hpairs.2.2.1⟩
    exact h4 G A c L hpair.standing hpair.mem_S.1 hm hcA hpairs.2.1 hL
      (Item211Proof.sectionCentralizer_eq h45 h66 hpair)
      (Item211Proof.exists_invTwoBarNontrivial hpair) x hx

theorem item211_of_list (hList : Item211List) (hNF : Item211NoField)
    (hSmall : Item211ResidualSmall) (hLie : Item211ResidualLie) (hE9 : Item211HeisStar) :
    Item211 := by
  intro G _ _ A E U c L hpair
  obtain ⟨hm, hl⟩ := hList G A E U c L hpair
  have hnf := hNF G A E U c L hpair hm
  have hS := hSmall G A E U c L hpair hnf
  have hR := hLie G A E U c L hpair hnf
  rcases hl with ⟨x, hx, hk⟩ | ⟨h27, hH, hT | hT⟩ | h3 | h4 | h5 | ⟨h27, h6⟩ | ⟨h81, hJ, hX⟩ |
      h8 | ⟨h27, h9, hS3⟩ | ⟨h27, h10, hD12⟩ | ⟨h27, h11, hD8⟩ | ⟨h81, ⟨n, hn, hU⟩, hS4⟩ |
      ⟨h81, h13, hZS⟩
  · exact (hk.elim (hnf x hx).1 (hnf x hx).2).elim
  · exact (hS (Or.inl ⟨h27, hH, hT⟩)).elim
  · obtain ⟨hab, h9⟩ := hE9 G A E U c L hpair h27 hH hT
    exact Or.inl ⟨hH, hT, h27, hab, h9⟩
  · exact (hR (Or.inl h3)).elim
  · exact (hS (Or.inr (Or.inl h4))).elim
  · exact (hR (Or.inr (Or.inr h5))).elim
  · rcases h6 with hM12 | ⟨hM, hQ⟩ | ⟨hM, hSD⟩ | ⟨hM, hD⟩ | ⟨hJ2, hS3⟩ | ⟨hJ4, hGL⟩ |
      ⟨hHS, hSD⟩ | ⟨hHe, hD⟩ | ⟨hRu, hGL⟩
    · exact (hS (Or.inr (Or.inr (Or.inl ⟨h27, hM12⟩)))).elim
    · exact Or.inr (Or.inl ⟨hM, h27, hQ⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hM, h27, hSD⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hM, h27, hD⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hJ2, h27, hS3⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr hJ4, h27, hGL⟩)))))
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr hHS, h27, hSD⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr hHe, h27, hD⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hRu, h27, hGL⟩)))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hJ, h81, hX⟩))))))))))
  · exact (hS (Or.inr (Or.inr (Or.inr h8)))).elim
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h9, h27, hS3⟩))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, h27, hD12⟩)))))))
  ·
    rcases h11 with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨Or.inl h, h27, hD8⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨Or.inr h, h27, hD8⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨Or.inl h, h27, hD8⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨Or.inr h, h27, hD8⟩)))))))))))
  ·
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨⟨n, hn1, hn, hU⟩, h81, hS4⟩)))))))))
    · have hn1' : n = 1 := by
        obtain ⟨k, rfl⟩ := hn
        omega
      subst hn1'
      exact (hR (Or.inr (Or.inl ⟨h81, hU, hS4⟩))).elim
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨h13, h81, hZS⟩)))))))))))

end Certs

end CFSG.RankThree.PartTwo.Sec21
