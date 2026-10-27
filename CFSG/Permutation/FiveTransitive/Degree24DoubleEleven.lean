module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerOneBelow

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem dvd_fortyFour_of_dvd_fourHundredEightyFour
    {k : ℕ} (hkdvd : k ∣ 484) (hnot : ¬121 ∣ k) :
    k ∣ 44 := by
  have hkne : k ≠ 0 := by
    intro hk
    subst k
    norm_num at hkdvd
  apply
    (Nat.factorization_le_iff_dvd hkne
      (by norm_num : (44 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hkne
      (by norm_num : (484 : ℕ) ≠ 0)).mpr hkdvd) p
  by_cases hp : p = 11
  · subst p
    have hlt : k.factorization 11 < 2 := by
      rw [← not_le]
      intro htwo
      exact hnot
        ((show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
          hkne |>.mpr htwo)
    have htarget : (44 : ℕ).factorization 11 = 1 := by
      rw [show 44 = 11 * 4 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 11 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (484 : ℕ).factorization p =
          (44 : ℕ).factorization p := by
      have hp' : 11 ≠ p := Ne.symm hp
      rw [show 484 = 11 * 44 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 11 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

theorem order_eleven_cycleType_eq_double
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 11) :
    (u : Equiv.Perm X).cycleType = {11, 11} := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 24 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ _
      _ = 24 := hcard
  have hmLe : m + 1 ≤ 2 := by
    nlinarith
  have hmPos : 0 < m + 1 := Nat.zero_lt_succ m
  rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
  · have hgcycle : g.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hm,
        Multiset.card_replicate, hmOne]
    have hgsupport : g.support.card = 11 := by
      rw [← hgcycle.orderOf, hgorder]
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_elevenCycle
          X P hcard h5 u.prop hgcycle hgsupport))
  · rw [hm, hgorder, hmTwo]
    norm_num

theorem order_eleven_centralizer_card_dvd_fourHundredEightyFour
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 11) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) ∣ 484 := by
  classical
  let g : Equiv.Perm X := u
  have hcycleType : g.cycleType = {11, 11} := by
    simpa only [g] using
      order_eleven_cycleType_eq_double
        X P hcard h5 hnotAlt u huorder
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro q
    change ((q.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp q.2)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective
      (P.subtype_injective hab')
  have hfullCard :
      Nat.card
          (Subgroup.centralizer
            ({g} : Set (Equiv.Perm X))) = 484 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hcycleType, hcard]
    norm_num
  rw [← hfullCard]
  exact Subgroup.card_dvd_of_injective
    centMap hcentMapInjective

private theorem sylow_eleven_centralizer_card_dvd_fortyFour
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hnotElevenSq : ¬11 ^ 2 ∣ Nat.card P)
    (S : Sylow 11 P) (hScard : Nat.card S = 11) :
    Nat.card
        (Subgroup.centralizer ((S : Subgroup P) : Set P)) ∣ 44 := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorderS : orderOf u = 11 :=
    huorder.trans hScard
  have huorderP : orderOf (u : P) = 11 := by
    calc
      orderOf (u : P) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 11 := huorderS
  let CS : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let Cu : Subgroup P :=
    Subgroup.centralizer ({(u : P)} : Set P)
  have hCSleCu : CS ≤ Cu := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc u u.prop).symm
  have hCSdvdCu : Nat.card CS ∣ Nat.card Cu :=
    Subgroup.card_dvd_of_le hCSleCu
  have hCudvd : Nat.card Cu ∣ 484 := by
    simpa only [Cu] using
      order_eleven_centralizer_card_dvd_fourHundredEightyFour
        X P hcard h5 hnotAlt (u : P) huorderP
  have hCSdvd : Nat.card CS ∣ 484 :=
    hCSdvdCu.trans hCudvd
  have hCSP : Nat.card CS ∣ Nat.card P :=
    Subgroup.card_subgroup_dvd_card CS
  have hnotCS : ¬121 ∣ Nat.card CS := by
    intro h
    exact hnotElevenSq (h.trans hCSP)
  simpa only [CS] using
    dvd_fortyFour_of_dvd_fourHundredEightyFour
      hCSdvd hnotCS

private theorem sylow_eleven_normalizer_constraints_of_centralizer_card_dvd
    (K : Type) [Group K] [Fintype K]
    (S : Sylow 11 K) (hScard : Nat.card S = 11)
    (hcentralizer :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup K) : Set K)) ∣ 44) :
    let C : Subgroup K :=
      Subgroup.centralizer ((S : Subgroup K) : Set K)
    let N : Subgroup K :=
      Subgroup.normalizer ((S : Subgroup K) : Set K)
    let c := (S : Subgroup K).relIndex C
    let r := C.relIndex N
    c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card K := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup K :=
    Subgroup.centralizer ((S : Subgroup K) : Set K)
  let N : Subgroup K :=
    Subgroup.normalizer ((S : Subgroup K) : Set K)
  let c := (S : Subgroup K).relIndex C
  let r := C.relIndex N
  change
    c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card K
  have hSleC : (S : Subgroup K) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSsubCard :
      Nat.card ((S : Subgroup K).subgroupOf C) = 11 := by
    calc
      Nat.card ((S : Subgroup K).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 11 := hScard
  have hcCardRaw :=
    ((S : Subgroup K).subgroupOf C).index_mul_card
  have hcCard : c * 11 = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup K).subgroupOf C).index * 11 =
        Nat.card C
    calc
      ((S : Subgroup K).subgroupOf C).index * 11 =
          ((S : Subgroup K).subgroupOf C).index *
            Nat.card ((S : Subgroup K).subgroupOf C) :=
        congrArg
          (((S : Subgroup K).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ 4 := by
    obtain ⟨t, ht⟩ := hcentralizer
    refine ⟨t, ?_⟩
    have hcancel : 11 * 4 = 11 * (c * t) := by
      calc
        11 * 4 = 44 := by norm_num
        _ = Nat.card C * t := ht
        _ = (c * 11) * t := by rw [hcCard]
        _ = 11 * (c * t) := by ring
    omega
  have hAutCard : Nat.card (MulAut S) = 10 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (show Nat.Prime 11 by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 10 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer
          ((S : Subgroup K) : Set K)).relIndex
          (Subgroup.normalizer
            ((S : Subgroup K) : Set K)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
  have hrDvd : r ∣ 10 := by
    change C.relIndex N ∣ 10
    rwa [hrEq]
  letI : (S : Subgroup K).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 11 = 1 := by
    change
      (Subgroup.normalizer
        ((S : Subgroup K) : Set K)).index % 11 = 1
    have hsylow :
        (Subgroup.normalizer (S : Set K)).index ≡
          1 [MOD 11] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 11 K
    change
      (Subgroup.normalizer
          ((S : Subgroup K) : Set K)).index % 11 =
        1 % 11 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          ((S : Subgroup K) : Set K))
  have hCindexCard := C.index_mul_card
  have hproduct :
      c * r * N.index * 11 = Nat.card K := by
    calc
      c * r * N.index * 11 =
          (r * N.index) * (c * 11) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card K := hCindexCard
  exact
    ⟨hcDvd, hrDvd, hcPos, hrPos, hNmod, hproduct⟩

theorem sylow_eleven_normalizer_constraints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hnotElevenSq : ¬11 ^ 2 ∣ Nat.card P)
    (S : Sylow 11 P) (hScard : Nat.card S = 11) :
    let C : Subgroup P :=
      Subgroup.centralizer ((S : Subgroup P) : Set P)
    let N : Subgroup P :=
      Subgroup.normalizer ((S : Subgroup P) : Set P)
    let c := (S : Subgroup P).relIndex C
    let r := C.relIndex N
    c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card P := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer ((S : Subgroup P) : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change
    c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
      N.index % 11 = 1 ∧
      c * r * N.index * 11 = Nat.card P
  have hSleC : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hCcardDvd : Nat.card C ∣ 44 := by
    simpa only [C] using
      sylow_eleven_centralizer_card_dvd_fortyFour
        X P hcard h5 hnotAlt hnotElevenSq S hScard
  have hSsubCard :
      Nat.card ((S : Subgroup P).subgroupOf C) = 11 := by
    calc
      Nat.card ((S : Subgroup P).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 11 := hScard
  have hcCardRaw :=
    ((S : Subgroup P).subgroupOf C).index_mul_card
  have hcCard : c * 11 = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup P).subgroupOf C).index * 11 =
        Nat.card C
    calc
      ((S : Subgroup P).subgroupOf C).index * 11 =
          ((S : Subgroup P).subgroupOf C).index *
            Nat.card ((S : Subgroup P).subgroupOf C) :=
        congrArg
          (((S : Subgroup P).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ 4 := by
    obtain ⟨t, ht⟩ := hCcardDvd
    refine ⟨t, ?_⟩
    have hcancel : 11 * 4 = 11 * (c * t) := by
      calc
        11 * 4 = 44 := by norm_num
        _ = Nat.card C * t := ht
        _ = (c * 11) * t := by rw [hcCard]
        _ = 11 * (c * t) := by ring
    omega
  have hAutCard : Nat.card (MulAut S) = 10 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (show Nat.Prime 11 by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 10 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer
          ((S : Subgroup P) : Set P)).relIndex
          (Subgroup.normalizer
            ((S : Subgroup P) : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
  have hrDvd : r ∣ 10 := by
    change C.relIndex N ∣ 10
    rwa [hrEq]
  letI : (S : Subgroup P).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 11 = 1 := by
    change
      (Subgroup.normalizer
        ((S : Subgroup P) : Set P)).index % 11 = 1
    have hsylow :
        (Subgroup.normalizer (S : Set P)).index ≡
          1 [MOD 11] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 11 P
    change
      (Subgroup.normalizer
          ((S : Subgroup P) : Set P)).index % 11 =
        1 % 11 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          ((S : Subgroup P) : Set P))
  have hCindexCard := C.index_mul_card
  have hproduct :
      c * r * N.index * 11 = Nat.card P := by
    calc
      c * r * N.index * 11 =
          (r * N.index) * (c * 11) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card P := hCindexCard
  exact
    ⟨hcDvd, hrDvd, hcPos, hrPos, hNmod, hproduct⟩

theorem five_point_stabilizer_mod_eleven_global_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    1 ≤ h % 11 ∧ h % 11 ≤ 8 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change 1 ≤ h % 11 ∧ h % 11 ≤ 8
  have hh : h ≠ 0 := Nat.card_pos.ne'
  have hdiv : h ∣ 522547200 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_without_two_thirteenth
        X P hcard h5 hnotAlt s hs
  have hnotEleven : ¬11 ∣ h := by
    intro heleven
    have : 11 ∣ 522547200 := heleven.trans hdiv
    norm_num at this
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
  have hPcard : Nat.card P = 5100480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hPfactorization :
      (5100480 * h).factorization 11 = 1 := by
    rw [show 5100480 = 11 * 463680 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotEleven]
    norm_num
  let S : Sylow 11 P := Sylow.nonempty.some
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  have hnotElevenSqP : ¬11 ^ 2 ∣ Nat.card P := by
    intro hdvd
    have hge :
        2 ≤ (Nat.card P).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        (Nat.card_pos.ne') |>.mp hdvd
    rw [hPcard, hPfactorization] at hge
    omega
  let C : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer ((S : Subgroup P) : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  have hconstraints :
      c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
        N.index % 11 = 1 ∧
        c * r * N.index * 11 = Nat.card P := by
    simpa only [C, N, c, r] using
      sylow_eleven_normalizer_constraints
        X P hcard h5 hnotAlt hnotElevenSqP S hScard
  have hdivided :
      c * r * N.index = 463680 * h := by
    rw [hPcard] at hconstraints
    nlinarith [hconstraints.2.2.2.2.2]
  have hmod :
      (8 * h) % 11 = (c * r) % 11 := by
    calc
      (8 * h) % 11 = (463680 * h) % 11 := by
        simp [Nat.mul_mod]
      _ = (c * r * N.index) % 11 :=
        congrArg (fun n => n % 11) hdivided.symm
      _ = (c * r) % 11 := by
        rw [Nat.mul_mod, hconstraints.2.2.2.2.1]
        simp
  have hresidue :
      h % 11 = (7 * (c * r)) % 11 := by
    have hm : 8 * h ≡ c * r [MOD 11] := hmod
    have hm' := hm.mul_left 7
    calc
      h % 11 = (11 * (5 * h) + h) % 11 := by
        simp
      _ = (7 * (8 * h)) % 11 := by
        congr 1
        ring
      _ = (7 * (c * r)) % 11 := hm'
  have hcLe : c ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hconstraints.1
  have hrLe : r ≤ 10 :=
    Nat.le_of_dvd (by norm_num) hconstraints.2.1
  have hcCases : c = 1 ∨ c = 2 ∨ c = 4 := by
    interval_cases c
    all_goals try norm_num at hconstraints
    all_goals omega
  have hrCases :
      r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 10 := by
    interval_cases r
    all_goals try norm_num at hconstraints
    all_goals omega
  rcases hcCases with hc | hc | hc
  all_goals rcases hrCases with hr | hr | hr | hr
  all_goals rw [hc, hr] at hresidue
  all_goals norm_num at hresidue
  all_goals omega

private theorem divisor_four_cases (k : ℕ) (hk : k ∣ 4) :
    k = 1 ∨ k = 2 ∨ k = 4 := by
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hk
  interval_cases k <;> simp_all

private theorem divisor_ten_cases (k : ℕ) (hk : k ∣ 10) :
    k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 10 := by
  have hle := Nat.le_of_dvd (by decide : 0 < 10) hk
  interval_cases k <;> simp_all

private theorem small_product_residues (c r : ℕ) (hc : c ∣ 4) (hr : r ∣ 10) :
    ((c * r) % 11 = 8 → c * r = 8) ∧
    ((c * r) % 11 = 5 → c * r = 5) ∧ (c * r) % 11 ≠ 6 := by
  rcases divisor_four_cases c hc with rfl | rfl | rfl <;>
    rcases divisor_ten_cases r hr with rfl | rfl | rfl | rfl <;> norm_num

private theorem factorization_eleven_of_not_dvd (a h : ℕ)
    (ha : a.factorization 11 = 1) (ha0 : a ≠ 0)
    (hh : h ≠ 0) (hnot : ¬ 11 ∣ h) : (a * h).factorization 11 = 1 := by
  rw [Nat.factorization_mul ha0 hh, Finsupp.add_apply, ha,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]

private theorem factorization_eleven_9240 : (9240 : ℕ).factorization 11 = 1 := by
  change (11 * 840).factorization 11 = 1
  rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    (show Nat.Prime 11 by decide).factorization, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide), add_zero]

private theorem factorization_eleven_5100480 : (5100480 : ℕ).factorization 11 = 1 := by
  change (11 * 463680).factorization 11 = 1
  rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    (show Nat.Prime 11 by decide).factorization, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide), add_zero]

private theorem relIndex_mul_card_of_le {G : Type*} [Group G]
    (A B : Subgroup G) (hle : A ≤ B) :
    A.relIndex B * Nat.card A = Nat.card B := by
  have hcard : Nat.card (A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  change (A.subgroupOf B).index * Nat.card A = Nat.card B
  rw [← hcard]
  exact (A.subgroupOf B).index_mul_card

theorem five_point_stabilizer_mod_eleven_ne_two_and_ne_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) % 11 ≠ 2 ∧
      Nat.card (fixingSubgroup P s) % 11 ≠ 7 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change h % 11 ≠ 2 ∧ h % 11 ≠ 7
  have hh : h ≠ 0 := Nat.card_pos.ne'
  have hdiv : h ∣ 522547200 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_without_two_thirteenth
        X P hcard h5 hnotAlt s hs
  have hnotEleven : ¬11 ∣ h := by
    intro heleven
    have : 11 ∣ 522547200 := heleven.trans hdiv
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 5100480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have heNonempty : Nonempty (Fin 2 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 2 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 2 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP2.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 552 := by
    change
      (fixingSubgroup P (Set.range e)).index = 552
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 9240 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hJfactorization : (9240 * h).factorization 11 = 1 :=
    factorization_eleven_of_not_dvd 9240 h factorization_eleven_9240 (by decide) hh hnotEleven
  let T : Sylow 11 J := Sylow.nonempty.some
  have hTcard : Nat.card T = 11 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 11 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 11 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 11 := huorderT
  have huorderP : orderOf ((u : J) : P) = 11 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 11 := huorderJ
  let CJ : Subgroup J :=
    Subgroup.centralizer ((T : Subgroup J) : Set J)
  let Cu : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hCudvd : Nat.card Cu ∣ 484 := by
    simpa only [Cu] using
      order_eleven_centralizer_card_dvd_fourHundredEightyFour
        X P hcard h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : CJ →* P :=
    J.subtype.comp CJ.subtype
  have hbaseMapMem :
      ∀ c : CJ, baseMap c ∈ Cu := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : CJ →* Cu :=
    baseMap.codRestrict Cu hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact CJ.subtype_injective
      (J.subtype_injective hab')
  have hCJdvdCu : Nat.card CJ ∣ Nat.card Cu :=
    Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hCJdvd : Nat.card CJ ∣ 484 :=
    hCJdvdCu.trans hCudvd
  have hCJJ : Nat.card CJ ∣ Nat.card J :=
    Subgroup.card_subgroup_dvd_card CJ
  have hnotJ : ¬121 ∣ Nat.card J := by
    intro hdvd
    have hge :
        2 ≤ (Nat.card J).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        (Nat.card_pos.ne') |>.mp (by
          norm_num at hdvd ⊢
          exact hdvd)
    rw [hJcard, hJfactorization] at hge
    omega
  have hnotCJ : ¬121 ∣ Nat.card CJ := by
    intro hdvd
    exact hnotJ (hdvd.trans hCJJ)
  have hCJdvdFortyFour : Nat.card CJ ∣ 44 :=
    dvd_fortyFour_of_dvd_fourHundredEightyFour
      hCJdvd hnotCJ
  let NJ : Subgroup J :=
    Subgroup.normalizer ((T : Subgroup J) : Set J)
  let c := (T : Subgroup J).relIndex CJ
  let r := CJ.relIndex NJ
  have hconstraints :
      c ∣ 4 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
        NJ.index % 11 = 1 ∧
        c * r * NJ.index * 11 = Nat.card J := by
    simpa only [CJ, NJ, c, r] using
      sylow_eleven_normalizer_constraints_of_centralizer_card_dvd
        J T hTcard (by
          simpa only [CJ] using hCJdvdFortyFour)
  have hdivided :
      c * r * NJ.index = 840 * h := by
    rw [hJcard] at hconstraints
    nlinarith only [hconstraints.2.2.2.2.2]
  have hmod :
      (4 * h) % 11 = (c * r) % 11 := by
    calc
      (4 * h) % 11 = (840 * h) % 11 := by
        simp [Nat.mul_mod]
      _ = (c * r * NJ.index) % 11 :=
        congrArg (fun n => n % 11) hdivided.symm
      _ = (c * r) % 11 := by
        rw [Nat.mul_mod, hconstraints.2.2.2.2.1]
        simp
  have hproductFacts := small_product_residues c r hconstraints.1 hconstraints.2.1
  have hneSeven : h % 11 ≠ 7 := by
    intro hseven
    have hproductMod : (c * r) % 11 = 6 := by
      rw [← hmod, Nat.mul_mod, hseven]
    exact hproductFacts.2.2 hproductMod
  have hPfactorization : (5100480 * h).factorization 11 = 1 :=
    factorization_eleven_of_not_dvd 5100480 h factorization_eleven_5100480 (by decide) hh hnotEleven
  obtain ⟨S, hScomap⟩ :=
    T.exists_comap_subtype_eq
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  have hnotElevenSqP : ¬11 ^ 2 ∣ Nat.card P := by
    intro hdvd
    have hge :
        2 ≤ (Nat.card P).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        (Nat.card_pos.ne') |>.mp hdvd
    rw [hPcard, hPfactorization] at hge
    omega
  let R : Subgroup P :=
    (T : Subgroup J).map J.subtype
  have hRcard : Nat.card R = 11 := by
    change
      Nat.card ((T : Subgroup J).map J.subtype) = 11
    rw [Subgroup.card_map_of_injective J.subtype_injective,
      hTcard]
  have hRleS : R ≤ (S : Subgroup P) := by
    change
      (T : Subgroup J).map J.subtype ≤
        (S : Subgroup P)
    rw [Subgroup.map_le_iff_le_comap, hScomap]
  have hRS : R = (S : Subgroup P) := by
    apply Subgroup.eq_of_le_of_card_ge hRleS
    rw [hRcard, hScard]
  have hSleRange :
      (S : Subgroup P) ≤ J.subtype.range := by
    rw [← hRS]
    exact Subgroup.map_le_range J.subtype (T : Subgroup J)
  let CG : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let NG : Subgroup P :=
    Subgroup.normalizer ((S : Subgroup P) : Set P)
  let cG := (S : Subgroup P).relIndex CG
  let rG := CG.relIndex NG
  have hglobal :
      cG ∣ 4 ∧ rG ∣ 10 ∧ 0 < cG ∧ 0 < rG ∧
        NG.index % 11 = 1 ∧
        cG * rG * NG.index * 11 = Nat.card P := by
    simpa only [CG, NG, cG, rG] using
      sylow_eleven_normalizer_constraints
        X P hcard h5 hnotAlt hnotElevenSqP S hScard
  have hglobalDivided :
      cG * rG * NG.index = 463680 * h := by
    rw [hPcard] at hglobal
    nlinarith only [hglobal.2.2.2.2.2]
  have hglobalMod :
      (8 * h) % 11 = (cG * rG) % 11 := by
    calc
      (8 * h) % 11 = (463680 * h) % 11 := by
        simp [Nat.mul_mod]
      _ = (cG * rG * NG.index) % 11 :=
        congrArg (fun n => n % 11)
          hglobalDivided.symm
      _ = (cG * rG) % 11 := by
        rw [Nat.mul_mod, hglobal.2.2.2.2.1]
        simp
  have hglobalProductFacts := small_product_residues cG rG hglobal.1 hglobal.2.1
  have hTleCJ : (T : Subgroup J) ≤ CJ := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  have hcCard : c * 11 = Nat.card CJ := by
    have h := relIndex_mul_card_of_le (T : Subgroup J) CJ hTleCJ
    simpa only [c, hTcard] using h
  have hrCard : r * Nat.card CJ = Nat.card NJ :=
    relIndex_mul_card_of_le CJ NJ (Subgroup.centralizer_le_normalizer _)
  have hSleCG : (S : Subgroup P) ≤ CG := by
    letI : IsCyclic S :=
      isCyclic_of_prime_card hScard
    letI : IsMulCommutative S :=
      IsCyclic.isMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hcGCard : cG * 11 = Nat.card CG := by
    have h := relIndex_mul_card_of_le (S : Subgroup P) CG hSleCG
    simpa only [cG, hScard] using h
  have hrGCard : rG * Nat.card CG = Nat.card NG :=
    relIndex_mul_card_of_le CG NG (Subgroup.centralizer_le_normalizer _)
  have hNgComap :
      NG.comap J.subtype = NJ := by
    have hnormalizerComap :=
      Subgroup.comap_normalizer_eq_of_le_range
        (H := (S : Subgroup P)) hSleRange
    simpa only [NG, NJ, hScomap] using
      hnormalizerComap
  let swapComap :
      J.comap NG.subtype ≃*
        NG.comap J.subtype :=
    { toFun := fun a =>
        (⟨(⟨a.1.1, a.prop⟩ : J), a.1.prop⟩ :
          NG.comap J.subtype)
      invFun := fun b =>
        (⟨(⟨b.1.1, b.prop⟩ : NG), b.1.prop⟩ :
          J.comap NG.subtype)
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro b
        rfl
      map_mul' := by
        intro a b
        rfl }
  have hNJdvdNG : Nat.card NJ ∣ Nat.card NG := by
    have hcardEq :
        Nat.card NJ = Nat.card (J.comap NG.subtype) := by
      calc
        Nat.card NJ = Nat.card (NG.comap J.subtype) := by
          rw [hNgComap]
        _ = Nat.card (J.comap NG.subtype) :=
          Nat.card_congr swapComap.toEquiv.symm
    rw [hcardEq]
    exact Subgroup.card_subgroup_dvd_card _
  have hneTwo : h % 11 ≠ 2 := by
    intro htwo
    have hlocalProductMod : (c * r) % 11 = 8 := by
      rw [← hmod, Nat.mul_mod, htwo]
    have hglobalProductMod : (cG * rG) % 11 = 5 := by
      rw [← hglobalMod, Nat.mul_mod, htwo]
    have hlocalProduct : c * r = 8 := hproductFacts.1 hlocalProductMod
    have hglobalProduct : cG * rG = 5 := hglobalProductFacts.2.1 hglobalProductMod
    have hNJcard : Nat.card NJ = 88 := by
      calc
        Nat.card NJ = r * Nat.card CJ := hrCard.symm
        _ = r * (c * 11) := by rw [hcCard]
        _ = 11 * (c * r) := by ring
        _ = 88 := by rw [hlocalProduct]
    have hNGcard : Nat.card NG = 55 := by
      calc
        Nat.card NG = rG * Nat.card CG := hrGCard.symm
        _ = rG * (cG * 11) := by rw [hcGCard]
        _ = 11 * (cG * rG) := by ring
        _ = 55 := by rw [hglobalProduct]
    rw [hNJcard, hNGcard] at hNJdvdNG
    norm_num at hNJdvdNG
  exact ⟨hneTwo, hneSeven⟩

end FiveTransitive.Degree24

end CFSG
