module

public import CFSG.Permutation.FiveTransitive.Degree20NormalSubgroup
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers
public import CFSG.Permutation.FiveTransitive.Degree20LongPrimeNormalizers
public import CFSG.Permutation.FiveTransitive.Degree20StabilizerFactor

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_mod_nineteen_ne_one
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (13 * Nat.card (fixingSubgroup P s)) % 19 ≠ 1 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hdiv : h ∣ 186624000 :=
    five_point_stabilizer_card_dvd_one_hundred_eighty_six_million
      X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hHindex : H.index = 1860480 := by
    change (fixingSubgroup P s).index = 1860480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1860480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  let S : Sylow 19 P := Sylow.nonempty.some
  have hScard : Nat.card S = 19 :=
    sylow_long_prime_card_eq_prime
      P h hPcard hdiv (Or.inr rfl) S
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let r := C.relIndex N
  have hnormalizerData :
      r ∣ 18 ∧
        0 < r ∧
        N.index % 19 = 1 ∧
        r * N.index * 19 = Nat.card P := by
    simpa only [C, N, r] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 19) (f := 1)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hdivided :
      r * N.index = 97920 * h := by
    rw [hPcard] at hnormalizerData
    nlinarith [hnormalizerData.2.2.2]
  have hmod :
      (13 * h) % 19 = r % 19 := by
    calc
      (13 * h) % 19 = (97920 * h) % 19 := by
        simp [Nat.mul_mod]
      _ = (r * N.index) % 19 :=
        congrArg (fun n => n % 19) hdivided.symm
      _ = r % 19 := by
        rw [Nat.mul_mod, hnormalizerData.2.2.1]
        simp
  change (13 * h) % 19 ≠ 1
  intro hmodOne
  have hrmod : r % 19 = 1 := by
    rw [← hmod, hmodOne]
  have hrle : r ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hnormalizerData.1
  have hr : r = 1 := by omega
  have hnormalizer :
      Subgroup.normalizer (S : Set P) ≤
        Subgroup.centralizer (S : Set P) := by
    exact Subgroup.relIndex_eq_one.mp
      (show C.relIndex N = 1 by simpa only [r] using hr)
  let transfer : P →* S :=
    MonoidHom.transferSylow S hnormalizer
  let Q : Subgroup P := transfer.ker
  letI : Q.Normal := by
    dsimp only [Q, transfer]
    infer_instance
  have hcomplement : IsComplement' Q S := by
    simpa only [Q, transfer] using
      MonoidHom.ker_transferSylow_isComplement'
        S hnormalizer
  have hcardMul := hcomplement.card_mul
  have hQcard : Nat.card Q = 97920 * h := by
    rw [hScard, hPcard] at hcardMul
    nlinarith
  have hQlarge : 20 < Nat.card Q := by
    rw [hQcard]
    nlinarith [Nat.card_pos (α := H)]
  have hnineteenQ : 19 ∣ Nat.card Q :=
    nineteen_dvd_card_of_large_normal_subgroup
      X P hcard h5 Q hQlarge
  rw [hQcard] at hnineteenQ
  rcases (show Nat.Prime 19 by norm_num).dvd_mul.mp
      hnineteenQ with hnineteen | hnineteen
  · norm_num at hnineteen
  · have : 19 ∣ 186624000 :=
      hnineteen.trans hdiv
    norm_num at this

end FiveTransitive.Degree20

end CFSG
