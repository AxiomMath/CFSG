module

public import CFSG.Permutation.FiveTransitive.LongPrimeArithmetic
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers

public section

namespace CFSG

namespace FiveTransitive.Degree26

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentySix
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 26)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card,
          hcard]
        omega)
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 21 := by
    change Nat.card ↥(sᶜ : Set X) = 21
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfaithful :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hHdvdFactorial : h ∣ (21 : ℕ).factorial := by
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithful
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hnotTwentyThree : ¬23 ∣ h := by
    intro hdvd
    have : 23 ∣ (21 : ℕ).factorial :=
      hdvd.trans hHdvdFactorial
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ :=
      h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 7893600 := by
    change (fixingSubgroup P s).index = 7893600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 7893600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have heNonempty : Nonempty (Fin 3 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 3 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP3.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 15600 := by
    change
      (fixingSubgroup P (Set.range e)).index = 15600
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 506 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hJfactorization :
      (506 * h).factorization 23 = 1 := by
    have hf := LongPrimeArithmetic.factorization_prime_mul_once 23 22 h
      (by decide) (by norm_num) hnotTwentyThree
    simpa only [show 23 * 22 = 506 by norm_num] using hf
  let T : Sylow 23 J := Sylow.nonempty.some
  have hTcard : Nat.card T = 23 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 23 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 23 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 23 := huorderT
  have huorderP : orderOf ((u : J) : P) = 23 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 23 := huorderJ
  let CJ : Subgroup J :=
    Subgroup.centralizer (T : Set J)
  let NJ : Subgroup J :=
    Subgroup.normalizer (T : Set J)
  have hTleCJ : (T : Subgroup J) ≤ CJ := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  let globalCu : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hglobalCucard : Nat.card globalCu = 23 := by
    simpa only [globalCu] using
      FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
        X P (p := 23) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : CJ →* P :=
    J.subtype.comp CJ.subtype
  have hbaseMapMem :
      ∀ c : CJ, baseMap c ∈ globalCu := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : CJ →* globalCu :=
    baseMap.codRestrict globalCu hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact CJ.subtype_injective
      (J.subtype_injective hab')
  have hCJdiv : Nat.card CJ ∣ 23 := by
    rw [← hglobalCucard]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hTwentyThreeDvdCJ : 23 ∣ Nat.card CJ := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleCJ
  have hCJcard : Nat.card CJ = 23 :=
    Nat.dvd_antisymm hCJdiv hTwentyThreeDvdCJ
  have hAutTcard : Nat.card (MulAut T) = 22 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime (show Nat.Prime 23 by norm_num)]
  have hrangeTDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 22 := by
    rw [← hAutTcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrJEq :
      CJ.relIndex NJ =
        Nat.card T.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (T : Set J)).relIndex
          (Subgroup.normalizer (T : Set J)) =
        Nat.card T.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      T.normalizerMonoidHom_ker]
    simp only [T.coe_coe]
  have hrJDvd : CJ.relIndex NJ ∣ 22 := by
    rw [hrJEq]
    exact hrangeTDvd
  letI : CJ.IsFiniteRelIndex NJ :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hNJmod : NJ.index % 23 = 1 := by
    change
      (Subgroup.normalizer (T : Set J)).index % 23 = 1
    have hsylow :
        (Subgroup.normalizer (T : Set J)).index ≡
          1 [MOD 23] := by
      rw [← T.card_eq_index_normalizer]
      exact card_sylow_modEq_one 23 J
    change
      (Subgroup.normalizer (T : Set J)).index % 23 =
        1 % 23 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrelJ :
      CJ.relIndex NJ * NJ.index = CJ.index := by
    simpa only [CJ, NJ] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (T : Set J))
  have hCJindex := CJ.index_mul_card
  have hlocalProduct :
      CJ.relIndex NJ * NJ.index * 23 = Nat.card J := by
    rw [hCJcard, ← hrelJ] at hCJindex
    exact hCJindex
  have hlocalDivided :
      CJ.relIndex NJ * NJ.index = 22 * h := by
    rw [hJcard] at hlocalProduct
    nlinarith only [hlocalProduct]
  have hlocalMod :
      (22 * h) % 23 = (CJ.relIndex NJ) % 23 := by
    calc
      (22 * h) % 23 =
          (CJ.relIndex NJ * NJ.index) % 23 :=
        congrArg (fun n => n % 23)
          hlocalDivided.symm
      _ = (CJ.relIndex NJ) % 23 := by
        rw [Nat.mul_mod, hNJmod]
        simp
  have hPfactorization :
      (7893600 * h).factorization 23 = 1 := by
    have hf := LongPrimeArithmetic.factorization_prime_mul_once 23 343200 h
      (by decide) (by norm_num) hnotTwentyThree
    simpa only [show 23 * 343200 = 7893600 by norm_num] using hf
  let S : Sylow 23 P := Sylow.nonempty.some
  have hScard : Nat.card S = 23 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  let CG : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let NG : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let rG := CG.relIndex NG
  have hglobal :
      rG ∣ 22 ∧
        0 < rG ∧
        NG.index % 23 = 1 ∧
        rG * NG.index * 23 = Nat.card P := by
    simpa only [CG, NG, rG] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 23) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hglobalDivided :
      rG * NG.index = 343200 * h := by
    rw [hPcard] at hglobal
    nlinarith only [hglobal.2.2.2]
  have hglobalMod :
      (17 * h) % 23 = rG % 23 := by
    calc
      (17 * h) % 23 = (343200 * h) % 23 := by
        simp [Nat.mul_mod]
      _ = (rG * NG.index) % 23 :=
        congrArg (fun n => n % 23)
          hglobalDivided.symm
      _ = rG % 23 := by
        rw [Nat.mul_mod, hglobal.2.2.1]
        simp
  exact LongPrimeArithmetic.degree_twenty_six_residue_impossible
    h (CJ.relIndex NJ) rG hrJDvd hglobal.1 hlocalMod hglobalMod

theorem classification_of_five_transitive_of_card_eq_twentySix
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 26)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G =
          (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X :=
    MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    intro i
    exact hg i
  have hAlt :=
    alternatingGroup_le_of_five_transitive_of_card_eq_twentySix
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree26

end CFSG
