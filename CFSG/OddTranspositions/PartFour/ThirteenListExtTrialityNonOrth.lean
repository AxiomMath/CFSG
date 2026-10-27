module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityNonOrthBasic
import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityNonOrthOrth63
import CFSG.Adapters.LieModelSimple
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

namespace ExtSetting

variable {G : Type} [Group G] [Finite G] {t : G} {M : Subgroup G} [M.Normal]

theorem false_of_isSpGp (h : ExtSetting G t M) {X : Type} [Group X]
    (φ : X ≃* ↥(M ⊔ Subgroup.zpowers t)) {m n : ℕ} (hX : IsSpGp X m n) : False := by
  obtain ⟨k, -, F, _, _, hcard, ⟨ι⟩⟩ := hX
  have hS := h.nonOrthSocle (ι.symm.trans φ)
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rcases Nat.lt_or_ge 1 n with hn2 | hn1
  · apply hS.not_isPerfect
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)
    exact (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k F
      (Or.inl ⟨s, hs⟩)).commutator_eq_top
  · have hF2 : Nat.card F = 2 := by
      interval_cases n
      · rw [hcard, pow_zero] at h1
        exact absurd h1 (lt_irrefl 1)
      · rw [hcard, pow_one]
    rcases Nat.lt_or_ge k 3 with hk | hk3
    · interval_cases k
      · have : Subsingleton (Matrix.GeneralLinearGroup (Fin 0 ⊕ Fin 0) F) :=
          ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
        apply hS.ne_top
        rw [eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 1]
        exact one_mem _
      · have h6 : Nat.card (StatedSp 1 F) = 6 := by
          have := CFSG.GroupTheory.WeirSylow.natCard_statedSp_cast F 1
          rw [hF2] at this
          norm_num [Finset.Icc_self] at this
          exact_mod_cast this
        have h3 : Nat.card (derivedSeries (StatedSp 1 F) 1) = 3 := by
          have := Subgroup.card_mul_index (derivedSeries (StatedSp 1 F) 1)
          rw [hS.index, h6] at this
          omega
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have := isCyclic_of_prime_card h3
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := derivedSeries (StatedSp 1 F) 1)
        apply hS.not_comm
        intro a b
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
        exact (Commute.zpow_zpow_self g i j).eq
      · have := Fintype.ofFinite F
        obtain ⟨σ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
          (k := F) (by rw [← Nat.card_eq_fintype_card, hF2])
        exact (h.nonOrthSocle (σ.symm.trans (ι.symm.trans φ))).false_of_perm
    · apply hS.not_isPerfect
      exact (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k F
        (Or.inr (Or.inr ⟨hF2, hk3⟩))).commutator_eq_top

end ExtSetting

theorem extTrialityNonOrth_holds : ExtTrialityNonOrth := by
  intro G _ _ t M _ h Y₀ _ _ s₀ hL hcase
  obtain ⟨e, -⟩ := hL.equiv
  have hS := h.nonOrthSocle e
  rcases hcase with ⟨m, n, ⟨hSp, -⟩ | ⟨hU, -⟩ | hW⟩ | ⟨n, hSym⟩ | h63 | ⟨n, -, hSz⟩
  · exact h.false_of_isSpGp e hSp
  · exact hS.not_isSimpleGroup
      (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU)
  · obtain ⟨-, F, _, _, -, e', i, j, hij, -⟩ := hW
    have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
      ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h1 => by
        have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
          (g : Matrix (Fin 2) (Fin 2) F) 0 1) h1
        simp at this⟩⟩
    exact (h.nonOrthSocle (e'.symm.trans e)).false_of_wreathSym hij
  · obtain ⟨e', -⟩ := hSym
    exact (h.nonOrthSocle
      (e'.symm.trans ((QuotientGroup.quotientMulEquivOfEq hL.oddCore).trans e))).false_of_perm
  · exact hS.false_of_isOrth63Reflection h63
  · have := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n hSz).2
    have hZ : fusionZStar Y₀ = Subgroup.center Y₀ := by
      have key : ∀ (H : Subgroup Y₀) [H.Normal], H = Subgroup.center Y₀ →
          (Subgroup.center (Y₀ ⧸ H)).comap (QuotientGroup.mk' H) = Subgroup.center Y₀ := by
        rintro H _ rfl
        rw [h.center_eq_bot e, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      unfold fusionZStar
      exact key _ hL.oddCore
    exact hS.not_isSimpleGroup (QuotientGroup.quotientMulEquivOfEq hZ).symm.isSimpleGroup

end CFSG.OddTranspositions.PartFour
