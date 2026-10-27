module

public import CFSG.RankThree.PartTwo.KFacts.KS18Mult
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

@[expose] def Step1913Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A → Chosen136 A →
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22)) →
    ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
      A ≤ P → omegaOneThree P = A

theorem theta_eq_pCore_two_of_mult (hmult : KFacts.KS18Mult) {I : Type} [Group I] [Finite I]
    (hq : CFSG.IsQuasisimple (I ⧸ CFSG.pCore 2 I))
    (hS : IsLThreePi (I ⧸ aschbacherSolvableCore 3 I) ∨
      Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (I ⧸ aschbacherSolvableCore 3 I ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ := solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  have hO2θ : CFSG.pCore 2 I ≤ aschbacherSolvableCore 3 I :=
    hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  refine le_antisymm ?_ hO2θ
  set Q := CFSG.pCore 2 I with hQ
  set f := QuotientGroup.mk' Q with hf
  set θI := aschbacherSolvableCore 3 I with hθI
  have hθn : θI.Normal := by
    have := hθ.2.1
    infer_instance
  have hθs : Group.IsSolvable θI := hθ.1
  set Z := θI.map f with hZ
  have hZn : Z.Normal := Subgroup.Normal.map hθn f (QuotientGroup.mk'_surjective _)
  have hZs : Group.IsSolvable Z := Group.isSolvable_of_surjective (f.subgroupMap_surjective θI)
  have hZc : Z ≤ Subgroup.center (I ⧸ Q) := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hZn with ht | hc
    · exfalso
      have hsolv : Group.IsSolvable (I ⧸ Q) := by
        rw [ht] at hZs
        exact Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup (I ⧸ Q)) ≃* (I ⧸ Q)) :
            (⊤ : Subgroup (I ⧸ Q)) →* (I ⧸ Q))) Subgroup.topEquiv.surjective
      have : Nontrivial (I ⧸ Q) := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect (I ⧸ Q) := hq.1
      exact Group.IsPerfect.not_isSolvable (I ⧸ Q) hsolv
    · exact hc
  have h3 : ¬ 3 ∣ Nat.card Z := fun h => hθ.2.2.1 (h.trans (Subgroup.card_map_dvd θI f))
  have h2 : ¬ 2 ∣ Nat.card Z := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h
    have hzc : (z : I ⧸ Q) ∈ Subgroup.center (I ⧸ Q) := hZc z.2
    have hzn : (Subgroup.zpowers (z : I ⧸ Q)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hz2 : IsPGroup 2 (Subgroup.zpowers (z : I ⧸ Q)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hle : Subgroup.zpowers (z : I ⧸ Q) ≤ CFSG.pCore 2 (I ⧸ Q) := le_sSup ⟨hzn, hz2⟩
    rw [pCore_quotient_pCore_eq_bot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    rw [show z = 1 from Subtype.ext hle, orderOf_one] at hz
    omega
  have hcop : Nat.Coprime 6 (Nat.card Z) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
  set e := QuotientGroup.quotientQuotientEquivQuotient Q θI hO2θ with he
  have hS' : IsLThreePi ((I ⧸ Q) ⧸ Z) ∨
      Nonempty ((I ⧸ Q) ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty ((I ⧸ Q) ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty ((I ⧸ Q) ⧸ Z ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((I ⧸ Q) ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    rcases hS with h | h | h | h | h
    · exact Or.inl (isLThreePi_of_mulEquiv e h)
    · exact Or.inr (Or.inl (h.map fun φ => e.trans φ))
    · exact Or.inr (Or.inr (Or.inl (h.map fun φ => e.trans φ)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.map fun φ => e.trans φ))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h.map fun φ => e.trans φ))))
  have hZ1 := hmult (I ⧸ Q) Z hq.1 hZc hcop hS'
  rw [hZ, Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at hZ1
  exact hZ1

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec19
