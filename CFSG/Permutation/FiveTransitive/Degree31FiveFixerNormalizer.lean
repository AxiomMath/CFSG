module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveFixerNormalizer

open MulAction

theorem normalizer_constraints
    (K : Type) [Group K] [Fintype K]
    {p : ℕ} [Fact p.Prime] (m : ℕ)
    (S : Sylow p K) (hScard : Nat.card S = p)
    (hcentralizer :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup K) : Set K)) ∣ p * m) :
    let C : Subgroup K :=
      Subgroup.centralizer ((S : Subgroup K) : Set K)
    let N : Subgroup K :=
      Subgroup.normalizer ((S : Subgroup K) : Set K)
    let c := (S : Subgroup K).relIndex C
    let r := C.relIndex N
    c ∣ m ∧ r ∣ (p - 1) ∧ 0 < c ∧ 0 < r ∧
      N.index % p = 1 ∧
      c * r * N.index * p = Nat.card K := by
  classical
  have hp : p.Prime := Fact.out
  let _ : IsCyclic S :=
    isCyclic_of_prime_card hScard
  let _ : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup K :=
    Subgroup.centralizer ((S : Subgroup K) : Set K)
  let N : Subgroup K :=
    Subgroup.normalizer ((S : Subgroup K) : Set K)
  let c := (S : Subgroup K).relIndex C
  let r := C.relIndex N
  change
    c ∣ m ∧ r ∣ (p - 1) ∧ 0 < c ∧ 0 < r ∧
      N.index % p = 1 ∧
      c * r * N.index * p = Nat.card K
  have hSleC : (S : Subgroup K) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hSsubCard :
      Nat.card ((S : Subgroup K).subgroupOf C) = p := by
    calc
      Nat.card ((S : Subgroup K).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = p := hScard
  have hcCardRaw :=
    ((S : Subgroup K).subgroupOf C).index_mul_card
  have hcCard : c * p = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup K).subgroupOf C).index * p =
        Nat.card C
    calc
      ((S : Subgroup K).subgroupOf C).index * p =
          ((S : Subgroup K).subgroupOf C).index *
            Nat.card ((S : Subgroup K).subgroupOf C) :=
        congrArg
          (((S : Subgroup K).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ m := by
    obtain ⟨t, ht⟩ := hcentralizer
    refine ⟨t, ?_⟩
    have hcancel : p * m = p * (c * t) := by
      calc
        p * m = Nat.card C * t := ht
        _ = (c * p) * t := by rw [hcCard]
        _ = p * (c * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos hcancel
  have hAutCard : Nat.card (MulAut S) = (p - 1) := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime hp]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ (p - 1) := by
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
  have hrDvd : r ∣ (p - 1) := by
    change C.relIndex N ∣ (p - 1)
    rwa [hrEq]
  let _ : (S : Subgroup K).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  let _ : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % p = 1 := by
    change
      (Subgroup.normalizer
        ((S : Subgroup K) : Set K)).index % p = 1
    have hsylow :
        (Subgroup.normalizer (S : Set K)).index ≡
          1 [MOD p] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one p K
    change
      (Subgroup.normalizer
          ((S : Subgroup K) : Set K)).index % p =
        1 % p at hsylow
    simpa only [Nat.mod_eq_of_lt hp.one_lt] using hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          ((S : Subgroup K) : Set K))
  have hCindexCard := C.index_mul_card
  have hproduct :
      c * r * N.index * p = Nat.card K := by
    calc
      c * r * N.index * p =
          (r * N.index) * (c * p) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card K := hCindexCard
  exact
    ⟨hcDvd, hrDvd, hcPos, hrPos, hNmod, hproduct⟩

theorem sylow_card
    (K : Type) [Group K] [Finite K] {a b p : ℕ} (hp : p = 29 ∨ p = 31)
    (hK : Nat.card K = 20389320 * 2 ^ a * 3 ^ b) (S : Sylow p K) : Nat.card S = p := by
  rcases hp with rfl | rfl
  · have hp : (Nat.Prime 29) := by norm_num
    let _ : Fact (Nat.Prime 29) := ⟨hp⟩
    have hc : (20389320 : ℕ).factorization 29 = 1 := by
      rw [show 20389320 = 29 * 703080 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        hp.factorization, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [S.card_eq_multiplicity,hK,
      Nat.factorization_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      hc,Nat.factorization_pow,Nat.factorization_pow,Finsupp.smul_apply,Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 29 ∣ 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 29 ∣ 3)]
    norm_num
  · have hp : (Nat.Prime 31) := by norm_num
    let _ : Fact (Nat.Prime 31) := ⟨hp⟩
    have hc : (20389320 : ℕ).factorization 31 = 1 := by
      rw [show 20389320 = 31 * 657720 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        hp.factorization, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [S.card_eq_multiplicity,hK,
      Nat.factorization_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      hc,Nat.factorization_pow,Nat.factorization_pow,Finsupp.smul_apply,Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 31 ∣ 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 31 ∣ 3)]
    norm_num

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 29 ∨ p = 31)
    (S : Sylow p P) (hScard : Nat.card S = p) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ p := by
  classical
  have hpprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  let _ : Fact p.Prime := ⟨hpprime⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = p := huRaw.trans hScard
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = p := (Subgroup.orderOf_coe u).trans huorder
  have hgorder : orderOf g = p := (Subgroup.orderOf_coe uP).trans huPorder
  have hgcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rwa [hgorder]) (by rw [hcard,hgorder]; rcases hp with rfl | rfl <;> omega)
  have hcycleType : g.cycleType = {p} := by rw [hgcycle.cycleType, ← hgcycle.orderOf, hgorder]
  have hgsupport : g.support.card = p := by rw [← hgcycle.orderOf,hgorder]
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((q.prop (u : P) u.prop).symm)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree28ThirteenCentralizer.centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) =
      g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne :
        supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne :
        supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wP : P := w
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwSupportSubset :
        wPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      exact
        Equiv.Perm.mem_support.mp hx
          (hwFixSupport x hxg)
    have hwSupportCard :
        wPerm.support.card ≤ 2 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ ≤ 2 := by
          rw [Finset.card_compl, hcard, hgsupport]
          rcases hp with rfl | rfl <;> norm_num
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    have hm := HighDegreeManningSupport.degree_le_two_mul_support
      P (by omega) h5 hnotAlt wP.prop hwPermNe
    change Fintype.card X ≤ 2 * wPerm.support.card at hm
    rw [hcard] at hm
    omega
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportTypeCard :
      Fintype.card g.support = p := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = p := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    rcases hp with rfl | rfl <;> norm_num
  have hCdvdSupport : Nat.card C ∣ p := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

theorem sylow_twenty_nine_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (S : Sylow 29 P) (hS : Nat.card S = 29) : Nat.card (MulAction.fixedPoints S X) = 2 := by
  classical
  let _ : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hgorder : orderOf u.val.val = 29 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact hu.trans hS
  have hcycle : u.val.val.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hgorder]; norm_num) (by rw [hgorder,hcard]; omega)
  have hsupport : u.val.val.support.card = 29 := by rw [← hcycle.orderOf,hgorder]
  have hsub : MulAction.fixedPoints S X ⊆ Function.fixedPoints u.val.val := by
    intro x hx
    exact MulAction.mem_fixedPoints.mp hx u
  have hle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := Function.fixedPoints u.val.val),
    Equiv.Perm.card_fixedPoints,u.val.val.sum_cycleType,hcard,hsupport] at hle
  change Nat.card (MulAction.fixedPoints S X) ≤ 2 at hle
  have hm := S.isPGroup'.card_modEq_card_fixedPoints X
  change Nat.card X % 29 = Nat.card (MulAction.fixedPoints S X) % 29 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

end FiveTransitive.Degree31FiveFixerNormalizer

end CFSG
