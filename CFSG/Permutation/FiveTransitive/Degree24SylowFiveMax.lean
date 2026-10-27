module

public import CFSG.Permutation.FiveTransitive.Degree20SylowFiveMax
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerSevenSquared

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

@[expose] abbrev FourFiveBase := Degree20.FourFiveBase

@[expose] abbrev TwentyFourFivePoints :=
  Degree20.TwentyFivePoints ⊕ Fin 4

instance : SMul FourFiveBase TwentyFourFivePoints where
  smul a
    | Sum.inl x => Sum.inl (a • x)
    | Sum.inr i => Sum.inr i

instance : MulAction FourFiveBase TwentyFourFivePoints where
  one_smul
    | Sum.inl x => congrArg Sum.inl (one_smul FourFiveBase x)
    | Sum.inr _ => rfl
  mul_smul a b
    | Sum.inl x => congrArg Sum.inl (mul_smul a b x)
    | Sum.inr _ => rfl

instance : FaithfulSMul FourFiveBase TwentyFourFivePoints where
  eq_of_smul_eq_smul {a b} h := by
    funext i
    have hi :=
      h (Sum.inl
        (i, (1 : Degree20.FiveCycle)))
    injection hi with hi
    have hi' := congrArg Prod.snd hi
    change a i * 1 = b i * 1 at hi'
    simpa using hi'

theorem card_twentyFourFivePoints :
    Fintype.card TwentyFourFivePoints = 24 := by
  rw [Fintype.card_sum,
    Degree20.card_twentyFivePoints,
    Fintype.card_fin]

private theorem coordinateFive_support_card :
    ((MulAction.toPermHom FourFiveBase TwentyFourFivePoints)
      Degree20.coordinateFive).support.card = 5 := by
  decide

private theorem alternatingGroup_le_of_sylow_five_card_eq_six_hundred_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 5 P) (hScard : Nat.card S = 625) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp (S : Subgroup P).subtype
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) := inclusion.range
  have hRcard : Nat.card R = 625 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr
          (MonoidHom.ofInjective hinclusion).toEquiv.symm
      _ = 625 := hScard
  have hRcardSylow :
      Nat.card R =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hRcard, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 24 < 3 by norm_num)]
    rw [Finset.sum_Ico_succ_top
      (by norm_num : 1 ≤ 2)]
    norm_num
  let Q : Sylow 5 (Equiv.Perm X) :=
    Sylow.ofCard R hRcardSylow
  let e : X ≃ TwentyFourFivePoints :=
    Fintype.equivOfCardEq
      (hcard.trans card_twentyFourFivePoints.symm)
  let standardMap :
      FourFiveBase →* Equiv.Perm X :=
    e.symm.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom
        FourFiveBase TwentyFourFivePoints)
  have hstandardMap :
      Function.Injective standardMap :=
    (e.symm.permCongrHom.toEquiv.comp_injective _).mpr
      MulAction.toPerm_injective
  let R₀ : Subgroup (Equiv.Perm X) :=
    standardMap.range
  have hR₀card : Nat.card R₀ = 625 := by
    calc
      Nat.card R₀ = Nat.card FourFiveBase :=
        Nat.card_congr
          (MonoidHom.ofInjective hstandardMap).toEquiv.symm
      _ = 625 := Degree20.card_fourFiveBase
  have hR₀cardSylow :
      Nat.card R₀ =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [hR₀card, Nat.card_perm,
      Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_factorial
      (by norm_num : Nat.Prime 5)
      (show Nat.log 5 24 < 3 by norm_num)]
    rw [Finset.sum_Ico_succ_top
      (by norm_num : 1 ≤ 2)]
    norm_num
  let Q₀ : Sylow 5 (Equiv.Perm X) :=
    Sylow.ofCard R₀ hR₀cardSylow
  let w₀ : Equiv.Perm X :=
    standardMap Degree20.coordinateFive
  have hw₀Q :
      w₀ ∈ (Q₀ : Subgroup (Equiv.Perm X)) := by
    change w₀ ∈ R₀
    exact ⟨Degree20.coordinateFive, rfl⟩
  have hw₀support : w₀.support.card = 5 := by
    change
      (e.symm.permCongr
        ((MulAction.toPermHom
          FourFiveBase TwentyFourFivePoints)
            Degree20.coordinateFive)).support.card = 5
    rw [Degree20.card_support_permCongr,
      coordinateFive_support_card]
  obtain ⟨q, hq⟩ :=
    exists_smul_eq (Equiv.Perm X) Q Q₀
  have hqInv : q⁻¹ • Q₀ = Q :=
    inv_smul_eq_iff.mpr hq.symm
  let w : Equiv.Perm X :=
    MulAut.conj q⁻¹ w₀
  have hwConjugate :
      w ∈ (q⁻¹ • Q₀ :
        Sylow 5 (Equiv.Perm X)) := by
    change ∃ x ∈
      (Q₀ : Subgroup (Equiv.Perm X)),
        MulAut.conj q⁻¹ x = w
    exact ⟨w₀, hw₀Q, rfl⟩
  have hwQ :
      w ∈ (Q : Subgroup (Equiv.Perm X)) := by
    rwa [hqInv] at hwConjugate
  have hwRange : w ∈ R := by
    exact hwQ
  obtain ⟨v, hv⟩ := hwRange
  have hwMem : w ∈ P := by
    rw [← hv]
    exact ((S : Subgroup P).subtype v).prop
  have hwSupport : w.support.card = 5 := by
    change
      (q⁻¹ * w₀ * (q⁻¹)⁻¹).support.card = 5
    rw [Equiv.Perm.card_support_conj,
      hw₀support]
  have hwNe : w ≠ 1 := by
    intro hw
    rw [hw, Equiv.Perm.support_one] at hwSupport
    norm_num at hwSupport
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    X P hcard h5 hwMem hwNe (by omega)

private theorem five_cubed_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬5 ^ 3 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro hfiveCube
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hfiveFourthP : 5 ^ 4 ∣ Nat.card P := by
    change 125 ∣ Nat.card H at hfiveCube
    obtain ⟨k, hk⟩ := hfiveCube
    rw [hPcard, hk]
    refine ⟨1020096 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (24 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorizationLe :
      (Nat.card P).factorization 5 ≤ 4 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (24 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    have hleFive := hle 5
    have hfactorial :
        ((24 : ℕ).factorial).factorization 5 = 4 := by
      rw [show (24 : ℕ).factorial =
          5 * (5 * (5 * (5 * 992717442773183102976))) by
            norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    rw [hfactorial] at hleFive
    exact hleFive
  have hfactorizationGe :
      4 ≤ (Nat.card P).factorization 5 :=
    (show Nat.Prime 5 by norm_num).pow_dvd_iff_le_factorization
      Nat.card_pos.ne' |>.mp hfiveFourthP
  have hfactorization :
      (Nat.card P).factorization 5 = 4 := by
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 P := Sylow.nonempty.some
  have hScard : Nat.card S = 625 := by
    rw [S.card_eq_multiplicity, hfactorization]
    norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_five_card_eq_six_hundred_twenty_five
      X P hcard h5 S hScard)

theorem five_point_stabilizer_card_dvd_without_five_cubed
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 75246796800 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 376233984000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_seven_squared
        X P hcard h5 hnotAlt s hs
  have hnotFiveCube : ¬5 ^ 3 ∣ Nat.card H := by
    simpa only [H] using
      five_cubed_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (75246796800 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (376233984000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 5
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 5 < 3 := by
      rw [← not_le]
      intro hthree
      exact hnotFiveCube
        ((show Nat.Prime 5 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hthree)
    have htarget :
        (75246796800 : ℕ).factorization 5 = 2 := by
      rw [show 75246796800 =
          5 * (5 * 3009871872) by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    rw [htarget]
    omega
  · have horiginal :
        (376233984000 : ℕ).factorization p =
          (75246796800 : ℕ).factorization p := by
      have hp' : 5 ≠ p := Ne.symm hp
      rw [show 376233984000 =
          5 * 75246796800 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree24

end CFSG
