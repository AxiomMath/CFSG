module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKBand
public import CFSG.LocalAnalysis.StandardType.GGSixRCKBandTransport
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE8Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7E8Five
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType.RCKBand

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.ExcMaxToral CFSG.LieType.Universal
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def StepZeroRankFloor (t : StatedLieTag) (f p : ℕ)
    (A : Subgroup (ModGL (langTag t) GGL)) : Prop :=
  BandRankFloor t f p A ∧
    (t = .E8 → p = 5 → orderOf ((2 ^ f : ℕ) : ZMod 5) ≠ 4 → 5 ^ 7 ≤ Nat.card A)

theorem rckSZ_le_adjoint {t : StatedLieTag} {f : ℕ}
    {A : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f) :
    A ≤ adjointGroup (langTag t) GGL :=
  fun x hx => (Subgroup.mem_inf.mp (by simpa only [ggFixGp] using hA hx)).1

private theorem rckSZ_finite {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] {A : Subgroup G}
    (h4 : p ^ 4 ≤ Nat.card A) : Finite ↥A :=
  Nat.finite_of_card_ne_zero (ne_of_gt ((pow_pos hp.pos 4).trans_le h4))

theorem rckSZ_card_le_pow_four {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    {A : Subgroup G} (hel : IsElemAbelian p A) (h4 : p ^ 4 ≤ Nat.card A)
    (h5 : ¬ p ^ 5 ≤ Nat.card A) : Nat.card A ≤ p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥A := rckSZ_finite hp h4
  have hpg : IsPGroup p ↥A := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hel.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := p) hpg
  have hle : 4 ≤ k := (pow_le_pow_iff_right₀ hp.one_lt).1 (hk ▸ h4)
  have hlt : k < 5 := (pow_lt_pow_iff_right₀ hp.one_lt).1 (Nat.lt_of_not_le (hk ▸ h5))
  have hk4 : k = 4 := by omega
  rw [hk, hk4]

theorem rckSZ_bigElem
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ExcFramesHalf.BigElemAbelianToralBar τ p) {A : Subgroup (ModGL τ GGL)}
    (hA : A ≤ adjointGroup τ GGL) (hel : IsElemAbelian p A)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card A) : IsToralSubgroup τ GGL A := by
  refine h (ZMod 2) ?_ A hA ?_ hel.2 hcard
  · rw [Nat.card_zmod]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  · intro x hx y hy
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem rckSZ_halg : letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL := by
  have h : ZMod.algebra GGL 2 = (inferInstance : Algebra (ZMod 2) GGL) := Subsingleton.elim _ _
  rw [h]
  exact AlgebraicClosure.isAlgebraic (ZMod 2)

theorem ggLieToralStepZeroRCK_of_M6c
    (h6c : GGLieNonToralRankFour) :
    ∀ (t : StatedLieTag), GGExcFive t → ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ A : Subgroup (ModGL (langTag t) GGL), A ≤ ggFixGp t f → IsElemAbelian p A →
        p ^ 4 ≤ Nat.card A → StepZeroRankFloor t f p A → ¬ CaseEightV t f p A →
        IsToralSubgroup (langTag t) GGL A := by
  intro t ht f hf p hp hp2 A hA hel h4card hfl hv
  rcases hfl with ⟨hband, hfloor⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    by_cases hp3 : p = 3
    · subst hp3
      have hdvd : orderOf ((2 ^ f : ℕ) : ZMod 3) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        have h2 : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide
        rw [Nat.cast_pow, ← pow_mul, mul_comm, pow_mul, h2, one_pow]
      have hd : orderOf ((2 ^ f : ℕ) : ZMod 3) = 1 ∨
          orderOf ((2 ^ f : ℕ) : ZMod 3) = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
      have hc : excDegCount (langTag .F4) (orderOf ((2 ^ f : ℕ) : ZMod 3)) = 4 := by
        rcases hd with h | h <;> rw [h] <;> decide
      exact isToral_ggFixGp_of_maxElem (Or.inl rfl) hf hp hp2 (by rw [hc]) hA hel
        (by rw [hc]; exact h4card)
    · exact isToralSubgroup_of_nonTorsion (L := GGL) (ℓ := 2) hp hp2 (fun _ => hp3)
        (fun h => absurd h (by decide)) (fun h => hp2 h.symm) rckSZ_halg
        (rckSZ_le_adjoint hA) (rckSZ_finite hp h4card) hel
  ·
    by_cases hp3 : p = 3
    · subst hp3
      by_cases h5le : 3 ^ 5 ≤ Nat.card A
      · exact rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E6_three
          (rckSZ_le_adjoint hA) hel h5le
      · have hmax : Nat.card A ≤ 3 ^ 4 := rckSZ_card_le_pow_four hp hel h4card h5le
        exact ggLieToralBandRCK_of_M6c h6c .E6 (Or.inr (Or.inl rfl)) f hf 3 Nat.prime_three A hA hel
          h4card hmax hband hv
    · exact isToralSubgroup_of_nonTorsion (L := GGL) (ℓ := 2) hp hp2 (fun _ => hp3)
        (fun h => absurd h (by decide)) (fun h => hp2 h.symm) rckSZ_halg
        (rckSZ_le_adjoint hA) (rckSZ_finite hp h4card) hel
  ·
    by_cases hp3 : p = 3
    · subst hp3
      have h6 : 3 ^ ((langTag .E7).rank - 1) ≤ Nat.card A := (hband rfl).1 (Or.inl rfl)
      exact rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E7_three
        (rckSZ_le_adjoint hA) hel h6
    · exact isToralSubgroup_of_nonTorsion (L := GGL) (ℓ := 2) hp hp2 (fun _ => hp3)
        (fun h => absurd h (by decide)) (fun h => hp2 h.symm) rckSZ_halg
        (rckSZ_le_adjoint hA) (rckSZ_finite hp h4card) hel
  ·
    by_cases hp3 : p = 3
    · subst hp3
      have h7 : 3 ^ ((langTag .E8).rank - 1) ≤ Nat.card A := (hband rfl).1 (Or.inr rfl)
      exact rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E8_three
        (rckSZ_le_adjoint hA) hel h7
    · by_cases hp5 : p = 5
      · subst hp5
        by_cases hd : orderOf ((2 ^ f : ℕ) : ZMod 5) = 4
        · exact isToral_ggFixGp_E8_five_four hf hd hA hel h4card
        · have h57 : 5 ^ ((langTag .E8).rank - 1) ≤ Nat.card A := hfloor rfl rfl hd
          exact rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E8_five
            (rckSZ_le_adjoint hA) hel h57
      · exact isToralSubgroup_of_nonTorsion (L := GGL) (ℓ := 2) hp hp2 (fun _ => hp3)
          (fun _ => hp5) (fun h => hp2 h.symm) rckSZ_halg
          (rckSZ_le_adjoint hA) (rckSZ_finite hp h4card) hel
  ·
    by_cases hp3 : p = 3
    · subst hp3
      by_cases h5le : 3 ^ 5 ≤ Nat.card A
      · exact rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E6_three
          (rckSZ_le_adjoint hA) hel h5le
      · have hmax : Nat.card A ≤ 3 ^ 4 := rckSZ_card_le_pow_four hp hel h4card h5le
        exact ggLieToralBandRCK_of_M6c h6c .twistedE6 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          f hf 3 Nat.prime_three A hA hel h4card hmax hband hv
    · exact isToralSubgroup_of_nonTorsion (L := GGL) (ℓ := 2) hp hp2 (fun _ => hp3)
        (fun h => absurd h (by decide)) (fun h => hp2 h.symm) rckSZ_halg
        (rckSZ_le_adjoint hA) (rckSZ_finite hp h4card) hel

end CFSG.StandardType.RCKBand
