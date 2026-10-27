module

public import CFSG.Permutation.FiveTransitive.Degree25ElementarySmall
import CFSG.Permutation.FiveTransitive.Degree24ElementarySmall
public import CFSG.Permutation.FiveTransitive.Degree20SylowFiveMax
public import CFSG.Permutation.FiveTransitive.Degree25SmallSupport

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem alternatingGroup_le_of_one_below_maximal_sylow
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {p k d : ℕ} (hp : p.Prime)
    (S : Sylow p P) (hScard : Nat.card S = p ^ k)
    (hmax :
      p ^ (Nat.card (Equiv.Perm X)).factorization p =
        p ^ (k + d))
    (A : Subgroup (Equiv.Perm X))
    (hAcard : Nat.card A = p ^ (d + 1))
    (hAsmall :
      ∀ w : Equiv.Perm X, w ∈ A → w.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp (S : Subgroup P).subtype
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) := inclusion.range
  have hRcard : Nat.card R = p ^ k := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr
          (MonoidHom.ofInjective hinclusion).toEquiv.symm
      _ = p ^ k := hScard
  have hRisP : IsPGroup p R :=
    IsPGroup.of_card hRcard
  obtain ⟨Q, hRQ⟩ :=
    hRisP.exists_le_sylow
  have hAisP : IsPGroup p A :=
    IsPGroup.of_card hAcard
  obtain ⟨Q₀, hAQ₀⟩ :=
    hAisP.exists_le_sylow
  obtain ⟨q, hq⟩ :=
    exists_smul_eq (Equiv.Perm X) Q Q₀
  have hqSub :
      MulAut.conj q • (Q : Subgroup (Equiv.Perm X)) =
        (Q₀ : Subgroup (Equiv.Perm X)) := by
    have h :=
      congrArg
        (fun T : Sylow p (Equiv.Perm X) =>
          (T : Subgroup (Equiv.Perm X))) hq
    exact h
  let R' : Subgroup (Equiv.Perm X) :=
    MulAut.conj q • R
  have hR'Q₀ : R' ≤ Q₀ := by
    rw [← hqSub]
    exact
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hRQ
  have hR'card : Nat.card R' = p ^ k := by
    calc
      Nat.card R' = Nat.card R := by
        exact Nat.card_congr
          (Subgroup.equivSMul (MulAut.conj q) R).toEquiv.symm
      _ = p ^ k := hRcard
  let RQ : Subgroup Q₀ := R'.subgroupOf Q₀
  let AQ : Subgroup Q₀ := A.subgroupOf Q₀
  have hRQcard : Nat.card RQ = p ^ k := by
    calc
      Nat.card RQ = Nat.card R' :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hR'Q₀).toEquiv
      _ = p ^ k := hR'card
  have hAQcard : Nat.card AQ = p ^ (d + 1) := by
    calc
      Nat.card AQ = Nat.card A :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hAQ₀).toEquiv
      _ = p ^ (d + 1) := hAcard
  have hQ₀card : Nat.card Q₀ = p ^ (k + d) := by
    rw [Q₀.card_eq_multiplicity, hmax]
  have hRQindexCard := RQ.index_mul_card
  have hRQindex : RQ.index = p ^ d := by
    rw [hRQcard, hQ₀card, pow_add] at hRQindexCard
    nlinarith [show 0 < p ^ k from Nat.pow_pos hp.pos]
  have hAQindexCard := AQ.index_mul_card
  rw [hAQcard, hQ₀card] at hAQindexCard
  let K : Subgroup Q₀ := RQ ⊓ AQ
  have hKindexLe :
      K.index ≤ p ^ d * AQ.index := by
    calc
      K.index = (RQ ⊓ AQ).index := rfl
      _ ≤ RQ.index * AQ.index :=
        Subgroup.index_inf_le
      _ = p ^ d * AQ.index := by rw [hRQindex]
  have hKindexCard := K.index_mul_card
  rw [hQ₀card] at hKindexCard
  have hKcardGe : p ≤ Nat.card K := by
    have hscaled :
        K.index * p ≤ AQ.index * p ^ (d + 1) := by
      calc
        K.index * p ≤
            (p ^ d * AQ.index) * p :=
          Nat.mul_le_mul_right p hKindexLe
        _ = AQ.index * p ^ (d + 1) := by
          rw [pow_succ]
          ring
    rw [hAQindexCard] at hscaled
    have hscaled' :
        K.index * p ≤ K.index * Nat.card K := by
      rwa [hKindexCard]
    exact Nat.le_of_mul_le_mul_left hscaled'
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have hKnontrivial : Nontrivial K :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      have := hp.two_le
      omega)
  letI : Nontrivial K := hKnontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : K)
  let w₀ : Equiv.Perm X := ((w : K) : Q₀)
  have hw₀R' : w₀ ∈ R' :=
    w.prop.1
  have hw₀A : w₀ ∈ A :=
    w.prop.2
  have hw₀support : w₀.support.card ≤ 7 :=
    hAsmall w₀ hw₀A
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hw₀R'
  obtain ⟨r, hrR, hrw⟩ := hw₀R'
  have hrSupport :
      r.support.card = w₀.support.card := by
    rw [← hrw]
    change
      r.support.card =
        (q * r * q⁻¹).support.card
    rw [Equiv.Perm.card_support_conj]
  have hrSupportLe : r.support.card ≤ 7 := by
    rwa [hrSupport]
  have hw₀Ne : w₀ ≠ 1 := by
    intro h
    apply hw
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hrNe : r ≠ 1 := by
    intro hr
    apply hw₀Ne
    rw [← hrw, hr]
    simp
  obtain ⟨v, hv⟩ := hrR
  have hrMem : r ∈ P := by
    rw [← hv]
    exact ((S : Subgroup P).subtype v).prop
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    X P hcard h5 hrMem hrNe hrSupportLe

theorem alternatingGroup_le_of_sylow_three_card_nineteen_thousand
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 3 P) (hScard : Nat.card S = 19683) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ TwoThreePoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_twoThreePoints.symm)
  let standardMap :
      TwoThreeBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom TwoThreeBase TwoThreePoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let A : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hAcard : Nat.card A = 3 ^ 2 := by
    calc
      Nat.card A = Nat.card TwoThreeBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 3 ^ 2 := by
        rw [FiveTransitive.Degree24.card_twoThreeBase]
        norm_num
  have hAsmall :
      ∀ w : Equiv.Perm X,
        w ∈ A → w.support.card ≤ 7 := by
    intro w hw
    obtain ⟨a, rfl⟩ := hw
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          TwoThreeBase TwoThreePoints) a)).support.card ≤ 7
    rw [Degree20.card_support_permCongr]
    exact (twoThreeBase_support_le_six a).trans (by omega)
  have hmax :
      3 ^ (Nat.card (Equiv.Perm X)).factorization 3 =
        3 ^ (9 + 1) := by
    have hfactorial :
        ((25 : ℕ).factorial).factorization 3 = 10 := by
      rw [show (25 : ℕ).factorial =
          3 ^ 10 * 262683704098816000000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact
    alternatingGroup_le_of_one_below_maximal_sylow
      X P hcard h5 (p := 3) (k := 9) (d := 1) (by norm_num)
        S (by simpa using hScard) hmax A hAcard hAsmall

theorem alternatingGroup_le_of_sylow_two_card_two_million
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 2 P) (hScard : Nat.card S = 2097152) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ TwoTwoPoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_twoTwoPoints.symm)
  let standardMap :
      TwoTwoBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom TwoTwoBase TwoTwoPoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let A : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hAcard : Nat.card A = 2 ^ 2 := by
    calc
      Nat.card A = Nat.card TwoTwoBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 2 ^ 2 := by
        rw [FiveTransitive.Degree24.card_twoTwoBase]
        norm_num
  have hAsmall :
      ∀ w : Equiv.Perm X,
        w ∈ A → w.support.card ≤ 7 := by
    intro w hw
    obtain ⟨a, rfl⟩ := hw
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          TwoTwoBase TwoTwoPoints) a)).support.card ≤ 7
    rw [Degree20.card_support_permCongr]
    exact (twoTwoBase_support_le_four a).trans (by omega)
  have hmax :
      2 ^ (Nat.card (Equiv.Perm X)).factorization 2 =
        2 ^ (21 + 1) := by
    have hfactorial :
        ((25 : ℕ).factorial).factorization 2 = 22 := by
      rw [show (25 : ℕ).factorial =
          2 ^ 22 * 3698160658676859375 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact
    alternatingGroup_le_of_one_below_maximal_sylow
      X P hcard h5 (p := 2) (k := 21) (d := 1) (by norm_num)
        S (by simpa using hScard) hmax A hAcard hAsmall

theorem alternatingGroup_le_of_sylow_two_card_one_million
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 2 P) (hScard : Nat.card S = 1048576) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ ThreeTwoPoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_threeTwoPoints.symm)
  let standardMap :
      ThreeTwoBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom ThreeTwoBase ThreeTwoPoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let A : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hAcard : Nat.card A = 2 ^ (2 + 1) := by
    calc
      Nat.card A = Nat.card ThreeTwoBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 2 ^ (2 + 1) := by
        rw [FiveTransitive.Degree24.card_threeTwoBase]
        norm_num
  have hAsmall :
      ∀ w : Equiv.Perm X,
        w ∈ A → w.support.card ≤ 7 := by
    intro w hw
    obtain ⟨a, rfl⟩ := hw
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          ThreeTwoBase ThreeTwoPoints) a)).support.card ≤ 7
    rw [Degree20.card_support_permCongr]
    exact (threeTwoBase_support_le_six a).trans (by omega)
  have hmax :
      2 ^ (Nat.card (Equiv.Perm X)).factorization 2 =
        2 ^ (20 + 2) := by
    have hfactorial :
        ((25 : ℕ).factorial).factorization 2 = 22 := by
      rw [show (25 : ℕ).factorial =
          2 ^ 22 * 3698160658676859375 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact
    alternatingGroup_le_of_one_below_maximal_sylow
      X P hcard h5 (p := 2) (k := 20) (d := 2) (by norm_num)
        S (by simpa using hScard) hmax A hAcard hAsmall

theorem alternatingGroup_le_of_sylow_two_card_half_million
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 2 P) (hScard : Nat.card S = 524288) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ FourTwoPoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_fourTwoPoints.symm)
  let standardMap :
      FourTwoBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom FourTwoBase FourTwoPoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let A : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hAcard : Nat.card A = 2 ^ (3 + 1) := by
    calc
      Nat.card A = Nat.card FourTwoBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 2 ^ (3 + 1) := by
        rw [FiveTransitive.Degree24.card_fourTwoBase]
        norm_num
  have hAsmall :
      ∀ w : Equiv.Perm X,
        w ∈ A → w.support.card ≤ 7 := by
    intro w hw
    obtain ⟨a, rfl⟩ := hw
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          FourTwoBase FourTwoPoints) a)).support.card ≤ 7
    rw [Degree20.card_support_permCongr]
    exact (fourTwoBase_support_le_six a).trans (by omega)
  have hmax :
      2 ^ (Nat.card (Equiv.Perm X)).factorization 2 =
        2 ^ (19 + 3) := by
    have hfactorial :
        ((25 : ℕ).factorial).factorization 2 = 22 := by
      rw [show (25 : ℕ).factorial =
          2 ^ 22 * 3698160658676859375 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact
    alternatingGroup_le_of_one_below_maximal_sylow
      X P hcard h5 (p := 2) (k := 19) (d := 3) (by norm_num)
        S (by simpa using hScard) hmax A hAcard hAsmall

end FiveTransitive.Degree25

end CFSG
