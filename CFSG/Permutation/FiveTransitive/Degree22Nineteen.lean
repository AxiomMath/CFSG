module

public import CFSG.Permutation.FiveTransitive.Degree22LongPrimes
public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers
public import CFSG.Permutation.FiveTransitive.Degree19FiveNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree22

open MulAction SubMulAction Subgroup

theorem factorization_nineteen_mul
    (a h : ℕ) (ha : a ≠ 0) (hh : h ≠ 0)
    (ha19 : ¬ 19 ∣ a) (hh19 : ¬ 19 ∣ h) :
    (19 * a * h).factorization 19 = 1 := by
  rw [Nat.mul_assoc,
    Nat.factorization_mul (by norm_num) (Nat.mul_ne_zero ha hh),
    Finsupp.add_apply,
    (show Nat.Prime 19 by norm_num).factorization,
    Finsupp.single_eq_same,
    Nat.factorization_mul ha hh, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ha19,
    Nat.factorization_eq_zero_of_not_dvd hh19]
  norm_num

private theorem normalizer_relindex_lower
    (r i c : ℕ) (hi : 0 < i)
    (hbound : i * 108 ≤ c) (hprod : r * i * 19 = c) :
    6 ≤ r := by
  nlinarith

private theorem eighteen_divisor_cases
    (r : ℕ) (hdvd : r ∣ 18) :
    r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 ∨ r = 9 ∨ r = 18 := by
  have hr : r ≤ 18 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases r <;> norm_num at *

private theorem normalizer_mod_cases
    (h r t : ℕ) (hr : r = 6 ∨ r = 9 ∨ r = 18)
    (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 6 ∨ t = 9 ∨ t = 18)
    (hglobal : (13 * h) % 19 = r % 19)
    (hlocal : (18 * h) % 19 = t % 19) :
    h % 19 = 16 ∨ h % 19 = 18 := by
  rcases hr with rfl | rfl | rfl
  all_goals rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hglobal hlocal
  all_goals omega

theorem five_point_stabilizer_card_mod_nineteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 22)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) % 19 = 16 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hdiv : h ∣ 1609445376000 :=
    five_point_stabilizer_card_dvd_reduced
      X P hcard h5 hnotAlt s hs
  have hnotNineteen : ¬19 ∣ h := by
    intro hnineteen
    have : 19 ∣ 1609445376000 :=
      hnineteen.trans hdiv
    norm_num at this
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
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
  have hHindex : H.index = 3160080 := by
    change (fixingSubgroup P s).index = 3160080
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 3160080 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  let S : Sylow 19 P := Sylow.nonempty.some
  have hPfactorization :
      (3160080 * h).factorization 19 = 1 := by
    exact factorization_nineteen_mul 166320 h
      (by norm_num) hh (by norm_num) hnotNineteen
  have hScard : Nat.card S = 19 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let r := C.relIndex N
  have hglobal :
      r ∣ 18 ∧
        0 < r ∧
        N.index % 19 = 1 ∧
        r * N.index * 19 = Nat.card P := by
    simpa only [C, N, r] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 19) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hfixed
      (a : Degree15.NonidentitySylowElements 19 P) :
      Fintype.card
          (MulAction.fixedBy X
            (Degree15.nonidentitySylowElementVal 19 P a)) = 3 := by
    rcases a with ⟨T, u⟩
    change
      Fintype.card
          (MulAction.fixedBy X ((u.1 : T) : P)) = 3
    have hTcard : Nat.card T = 19 :=
      Degree15.sylow_card_eq_of_card_eq
        S hScard T
    have huorderT : orderOf u.1 = 19 :=
      Degree15.orderOf_eq_prime_of_card_eq_prime
        hTcard u.2
    let g : Equiv.Perm X := ((u.1 : T) : P)
    have hgorder : orderOf g = 19 := by
      calc
        orderOf g = orderOf ((u.1 : T) : P) :=
          Subgroup.orderOf_coe _
        _ = orderOf u.1 :=
          Subgroup.orderOf_coe _
        _ = 19 := huorderT
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        norm_num) (by
          rw [hcard, hgorder]
          norm_num)
    have hgsupport : g.support.card = 19 := by
      rw [← hgcycle.orderOf, hgorder]
    rw [Degree15.card_fixedBy_subgroup_perm, hcard]
    change 22 - g.support.card = 3
    rw [hgsupport]
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hglobalBoundRaw :
      N.index * (19 - 1) *
          (3 : ℕ).descFactorial 3 ≤ Nat.card P := by
    simpa only [N] using
      Degree19.nonidentity_sylow_fixed_embedding_bound
        X P (p := 19) (m := 3) (f := 3)
          (by norm_num) S hScard (by omega)
          hfixed hP3
  have hglobalBound :
      N.index * 108 ≤ Nat.card P := by
    norm_num [Nat.descFactorial] at hglobalBoundRaw
    rw [Nat.card_eq_fintype_card]
    nlinarith
  have hrLower : 6 ≤ r := by
    have hindexPos : 0 < N.index :=
      Nat.pos_of_ne_zero
        Subgroup.index_ne_zero_of_finite
    exact normalizer_relindex_lower r N.index (Nat.card P)
      hindexPos hglobalBound hglobal.2.2.2
  have hrLe : r ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hglobal.1
  have hrCases : r = 6 ∨ r = 9 ∨ r = 18 := by
    rcases eighteen_divisor_cases r hglobal.1 with hr | hr | hr | hr | hr | hr
    all_goals omega
  have hglobalDivided :
      r * N.index = 166320 * h := by
    rw [hPcard] at hglobal
    omega
  have hglobalMod :
      (13 * h) % 19 = r % 19 := by
    calc
      (13 * h) % 19 = (166320 * h) % 19 := by
        simp [Nat.mul_mod]
      _ = (r * N.index) % 19 :=
        congrArg (fun n => n % 19)
          hglobalDivided.symm
      _ = r % 19 := by
        rw [Nat.mul_mod, hglobal.2.2.1]
        simp
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
  have hJindex : J.index = 9240 := by
    change
      (fixingSubgroup P (Set.range e)).index = 9240
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 342 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  let T : Sylow 19 J := Sylow.nonempty.some
  have hJfactorization :
      (342 * h).factorization 19 = 1 := by
    exact factorization_nineteen_mul 18 h
      (by norm_num) hh (by norm_num) hnotNineteen
  have hTcard : Nat.card T = 19 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 19 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 19 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 19 := huorderT
  have huorderP : orderOf ((u : J) : P) = 19 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 19 := huorderJ
  let CJ : Subgroup J :=
    Subgroup.centralizer (T : Set J)
  let NJ : Subgroup J :=
    Subgroup.normalizer (T : Set J)
  have hTleCJ : (T : Subgroup J) ≤ CJ := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  let globalC : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hglobalCcard : Nat.card globalC = 19 := by
    simpa only [globalC] using
      FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
        X P (p := 19) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : CJ →* P :=
    J.subtype.comp CJ.subtype
  have hbaseMapMem :
      ∀ c : CJ, baseMap c ∈ globalC := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : CJ →* globalC :=
    baseMap.codRestrict globalC hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact CJ.subtype_injective
      (J.subtype_injective hab')
  have hCJdiv : Nat.card CJ ∣ 19 := by
    rw [← hglobalCcard]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hNineteenDvdCJ : 19 ∣ Nat.card CJ := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleCJ
  have hCJcard : Nat.card CJ = 19 :=
    Nat.dvd_antisymm hCJdiv hNineteenDvdCJ
  have hAutCard : Nat.card (MulAut T) = 18 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime (show Nat.Prime 19 by norm_num)]
  have hrangeDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 18 := by
    rw [← hAutCard]
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
  have hrJDvd : CJ.relIndex NJ ∣ 18 := by
    rwa [hrJEq]
  letI : CJ.IsFiniteRelIndex NJ :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hNJmod : NJ.index % 19 = 1 := by
    change
      (Subgroup.normalizer (T : Set J)).index % 19 = 1
    have hsylow :
        (Subgroup.normalizer (T : Set J)).index ≡
          1 [MOD 19] := by
      rw [← T.card_eq_index_normalizer]
      exact card_sylow_modEq_one 19 J
    change
      (Subgroup.normalizer (T : Set J)).index % 19 =
        1 % 19 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      CJ.relIndex NJ * NJ.index = CJ.index := by
    simpa only [CJ, NJ] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (T : Set J))
  have hCJindex := CJ.index_mul_card
  have hlocalProduct :
      CJ.relIndex NJ * NJ.index * 19 = Nat.card J := by
    rw [hCJcard, ← hrel] at hCJindex
    exact hCJindex
  have hlocalDivided :
      CJ.relIndex NJ * NJ.index = 18 * h := by
    rw [hJcard] at hlocalProduct
    omega
  have hlocalMod :
      (18 * h) % 19 = (CJ.relIndex NJ) % 19 := by
    calc
      (18 * h) % 19 =
          (CJ.relIndex NJ * NJ.index) % 19 :=
        congrArg (fun n => n % 19)
          hlocalDivided.symm
      _ = (CJ.relIndex NJ) % 19 := by
        rw [Nat.mul_mod, hNJmod]
        simp
  have hrJpos : 0 < CJ.relIndex NJ :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrJle : CJ.relIndex NJ ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hrJDvd
  have hrJcases :
      CJ.relIndex NJ = 1 ∨ CJ.relIndex NJ = 2 ∨ CJ.relIndex NJ = 3 ∨
        CJ.relIndex NJ = 6 ∨ CJ.relIndex NJ = 9 ∨ CJ.relIndex NJ = 18 :=
    eighteen_divisor_cases (CJ.relIndex NJ) hrJDvd
  have hmodCases : h % 19 = 16 ∨ h % 19 = 18 :=
    normalizer_mod_cases h r (CJ.relIndex NJ) hrCases hrJcases hglobalMod hlocalMod
  rcases hmodCases with hmodSixteen | hmodEighteen
  · exact hmodSixteen
  · have hrJOne : CJ.relIndex NJ = 1 := by
      have hlocalMod' := hlocalMod
      rw [Nat.mul_mod] at hlocalMod'
      rw [hmodEighteen] at hlocalMod'
      norm_num at hlocalMod'
      have hrJLt : CJ.relIndex NJ < 19 := by
        omega
      rw [Nat.mod_eq_of_lt hrJLt] at hlocalMod'
      exact hlocalMod'.symm
    have hnormalizer :
        Subgroup.normalizer (T : Set J) ≤
          Subgroup.centralizer (T : Set J) := by
      exact Subgroup.relIndex_eq_one.mp
        (show CJ.relIndex NJ = 1 by
          simpa only [CJ, NJ] using hrJOne)
    let transfer : J →* T :=
      MonoidHom.transferSylow T hnormalizer
    let Q : Subgroup J := transfer.ker
    letI : Q.Normal := by
      dsimp only [Q, transfer]
      infer_instance
    have hcomplement : IsComplement' Q T := by
      simpa only [Q, transfer] using
        MonoidHom.ker_transferSylow_isComplement'
          T hnormalizer
    have hcardMul := hcomplement.card_mul
    have hQcard : Nat.card Q = 18 * h := by
      rw [hTcard, hJcard] at hcardMul
      omega
    let Y := SubMulAction.ofFixingSubgroup P (Set.range e)
    have hYcard : Nat.card Y = 19 := by
      change Nat.card ↥((Set.range e)ᶜ : Set X) = 19
      rw [Nat.card_coe_set_eq]
      have htotal :=
        Set.ncard_add_ncard_compl (Set.range e)
      rw [Nat.card_eq_fintype_card, hcard,
        hecard] at htotal
      omega
    have hJ2 :
        MulAction.IsMultiplyPretransitive J Y 2 := by
      letI : MulAction.IsMultiplyPretransitive P X 5 :=
        hP5
      change
        MulAction.IsMultiplyPretransitive
          (fixingSubgroup P (Set.range e))
          (SubMulAction.ofFixingSubgroup P (Set.range e)) 2
      apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
        (m := 2) (n := 5) P (Set.range e)
      omega
    letI : MulAction.IsPreprimitive J Y :=
      MulAction.isPreprimitive_of_is_two_pretransitive hJ2
    letI : Nonempty Y :=
      Fintype.card_pos_iff.mp (by
        rw [← Nat.card_eq_fintype_card, hYcard]
        norm_num)
    have hfaithful :
        ∀ j : J, (∀ y : Y, j • y = y) → j = 1 := by
      intro j hj
      apply Subtype.ext
      apply P.subtype_injective
      ext x
      by_cases hx : x ∈ Set.range e
      · have hfix :=
          (mem_fixingSubgroup_iff P).mp j.prop x hx
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
          using hfix
      · let y : Y := ⟨x, hx⟩
        have hy := hj y
        have hy' := congrArg Subtype.val hy
        simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def]
          using hy'
    have hnormalCases :=
      OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
        J Y hfaithful Q
    have hQneOne : Nat.card Q ≠ 1 := by
      rw [hQcard]
      omega
    have hnineteenQ : 19 ∣ Nat.card Q := by
      rcases hnormalCases with hQone | hYdvd
      · exact (hQneOne hQone).elim
      · rwa [hYcard] at hYdvd
    rw [hQcard] at hnineteenQ
    exfalso
    rcases (show Nat.Prime 19 by norm_num).dvd_mul.mp
        hnineteenQ with hnineteen | hnineteen
    · norm_num at hnineteen
    · exact hnotNineteen hnineteen

end FiveTransitive.Degree22

end CFSG
