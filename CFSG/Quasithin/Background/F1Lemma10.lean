module

public import CFSG.Quasithin.Background.F1Weak

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

variable {G : Type u} [Group G]

@[expose] def HypothesisB (B P1star P2star : Subgroup G) : Prop :=
  B = (P1star ⊓ B) ⊔ (P2star ⊓ B) ⊔ pCoreOf 2 B

namespace F1

theorem borelOf_le_normalizer_of_eq {Li S : Subgroup G}
    (h : S = pCoreOf 2 (Li ⊔ S) ⊔ (S ⊓ Li)) :
    borelOf Li S ≤ Subgroup.normalizer (S : Set G) := by
  have h1 : borelOf Li S ≤ Subgroup.normalizer (pCoreOf 2 (Li ⊔ S) : Set G) :=
    ((borelOf_le Li S).trans le_sup_left).trans (le_normalizer_pCoreOf 2 _)
  have h2 := le_normalizer_sup h1 (borelOf_le_normalizer Li S)
  rwa [← h] at h2

end F1

theorem lemma_F110_1 {Li S : Subgroup G} (h : S = pCoreOf 2 (Li ⊔ S) ⊔ (S ⊓ Li)) :
    (S.subgroupOf (S ⊔ borelOf Li S)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer (F1.borelOf_le_normalizer_of_eq h))

namespace F1

variable [Finite G] {L1 L2 S : Subgroup G}

theorem isSylowTwoOf_bigB_of_normal (h : Hyp111R L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    IsSylowTwoOf S (bigB L1 L2 S) := by
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  refine isSylowTwoOf_of_relIndex hSB' h.hyp.h1.pgroup ?_
  have hS1 : S ≤ borelOf L1 S ⊔ S := le_sup_right
  have hle : borelOf L1 S ⊔ S ≤ bigB L1 L2 S := sup_le hB1B hSB'
  rw [← Subgroup.relIndex_mul_relIndex S (borelOf L1 S ⊔ S) (bigB L1 L2 S) hS1 hle]
  have hf1 : ¬ 2 ∣ S.relIndex (borelOf L1 S ⊔ S) := by
    rw [relIndex_sup_eq_of_le_normalizer (hB1B.trans hSB), ← Subgroup.inf_relIndex_right]
    have hinf : S ⊓ borelOf L1 S = S ⊓ L1 :=
      le_antisymm (inf_le_inf_left S (borelOf_le L1 S)) (le_inf inf_le_left (sylow_le_borelOf L1 S))
    rw [hinf]
    exact isSylowTwoOf_odd_relIndex
      (isSylowTwoOf_mono_right h.hyp.h1.sylow (sylow_le_borelOf L1 S) (borelOf_le L1 S))
  have hB2N : borelOf L2 S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ S : Subgroup G) : Set G) :=
    le_normalizer_sup (borelOf_le_normalizer_borelOf h) (hB2B.trans hSB)
  have hbig : bigB L1 L2 S = borelOf L2 S ⊔ (borelOf L1 S ⊔ S) := by
    simp only [bigB]
    rw [← sup_assoc, sup_comm (borelOf L2 S) (borelOf L1 S)]
  have hf2 : ¬ 2 ∣ (borelOf L1 S ⊔ S).relIndex (bigB L1 L2 S) := by
    rw [hbig, relIndex_sup_eq_of_le_normalizer hB2N]
    intro hd
    have hS2 : S ⊓ L2 ≤ borelOf L1 S ⊔ S := inf_le_left.trans le_sup_right
    have hdvd := Subgroup.relIndex_dvd_of_le_left (borelOf L2 S) hS2
    exact (isSylowTwoOf_odd_relIndex
      (isSylowTwoOf_mono_right h.hyp.h2.sylow (sylow_le_borelOf L2 S) (borelOf_le L2 S)))
      (hd.trans hdvd)
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
  · exact hf1 hd
  · exact hf2 hd

end F1

theorem lemma_F110_2 {L1 L2 S : Subgroup G} [Finite G] (h : Hyp111R L1 L2 S)
    (hcase : ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∧ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) ∨
      S ≤ L1 ∨ S ≤ L2) :
    pCoreOf 2 (bigB L1 L2 S) = S ∧
      bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S ⊔ pCoreOf 2 (bigB L1 L2 S) ∧
      HypothesisB (bigB L1 L2 S) (pStar L1 (bigB L1 L2 S)) (pStar L2 (bigB L1 L2 S)) := by
  have hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
    rcases hcase with ⟨h1, h2⟩ | hS | hS
    · have e1 : S ⊔ borelOf L1 S ≤ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h1
      have e2 : S ⊔ borelOf L2 S ≤ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp h2
      exact sup_le (sup_le (le_sup_right.trans e1) (le_sup_right.trans e2)) Subgroup.le_normalizer
    · have := (F1.bigB_le_normalizer_sylow h).1
      rwa [inf_eq_left.mpr hS] at this
    · have := (F1.bigB_le_normalizer_sylow h).2
      rwa [inf_eq_left.mpr hS] at this
  have hsyl := F1.isSylowTwoOf_bigB_of_normal h hSB
  have hO : pCoreOf 2 (bigB L1 L2 S) = S :=
    le_antisymm (isSylowTwoOf_pCoreOf_le hsyl)
      (le_pCoreOf_of_le_normalizer 2 hsyl.1 hSB h.hyp.h1.pgroup)
  have hbig : bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S ⊔ pCoreOf 2 (bigB L1 L2 S) := by
    rw [hO]
    rfl
  refine ⟨hO, hbig, ?_⟩
  unfold HypothesisB
  apply le_antisymm
  · conv_lhs => rw [hbig]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_inf ((F1.borelOf_le L1 S).trans le_sup_right) (le_sup_left.trans le_sup_left)).trans
        (le_sup_left.trans le_sup_left)
    · exact (le_inf ((F1.borelOf_le L2 S).trans le_sup_right) (le_sup_right.trans le_sup_left)).trans
        (le_sup_right.trans le_sup_left)
    · exact le_sup_right
  · exact sup_le (sup_le inf_le_right inf_le_right) (pCoreOf_le 2 _)

@[expose] def IsSpecialPGroup (p : ℕ) (P : Type*) [Group P] : Prop :=
  IsPGroup p P ∧ ((IsMulCommutative P ∧ ∀ x : P, x ^ p = 1) ∨
    (commutator P = Subgroup.center P ∧ frattini P = Subgroup.center P ∧
      ∀ z ∈ Subgroup.center P, z ^ p = 1))

@[expose] def IsSpecialPow (p q w : ℕ) (P : Type*) [Group P] : Prop :=
  IsSpecialPGroup p P ∧ Nat.card P = q ^ (1 + 2 * w) ∧ Nat.card (Subgroup.center P) = q

end CFSG.Quasithin
