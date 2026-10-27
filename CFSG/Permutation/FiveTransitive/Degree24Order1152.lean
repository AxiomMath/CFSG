module

public import CFSG.Permutation.FiveTransitive.Degree24ThreeCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem five_not_dvd_mulAut_card_of_card_nine
    (G : Type) [Group G] [Fintype G]
    (hGcard : Nat.card G = 9) :
    ¬5 ∣ Nat.card (MulAut G) := by
  classical
  intro hfive
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, haorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := MulAut G) 5 hfive
  let permMap : MulAut G →* Equiv.Perm G := {
    toFun := fun e => e.toEquiv
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hpermMapInjective :
      Function.Injective permMap := by
    intro e f hef
    ext x
    exact congrFun
      (congrArg DFunLike.coe hef) x
  let g : Equiv.Perm G := permMap a
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf a :=
        orderOf_injective permMap
          hpermMapInjective a
      _ = 5 := haorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 9 := by
    calc
      g.support.card ≤ Fintype.card G :=
        Finset.card_le_univ g.support
      _ = Nat.card G := by
        rw [Nat.card_eq_fintype_card]
      _ = 9 := hGcard
  have hkOne : k + 1 = 1 := by
    omega
  have hcycleType : g.cycleType = {5} := by
    rw [hk, hgorder, hkOne]
    norm_num
  have hfixedCard :
      Nat.card (Function.fixedPoints g) = 4 := by
    rw [Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      hcycleType, ← Nat.card_eq_fintype_card,
      hGcard]
    norm_num
  let Fix : Subgroup G :=
    MonoidHom.eqLocus a.toMonoidHom
      (MonoidHom.id G)
  let fixedEquiv :
      Fix ≃ Function.fixedPoints g := {
    toFun := fun x => ⟨x.1, by
      change a x.1 = x.1
      exact x.2⟩
    invFun := fun x => ⟨x.1, by
      change a x.1 = x.1
      exact x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hFixCard : Nat.card Fix = 4 := by
    calc
      Nat.card Fix =
          Nat.card (Function.fixedPoints g) :=
        Nat.card_congr fixedEquiv
      _ = 4 := hfixedCard
  have hFixDvd :
      Nat.card Fix ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card Fix
  rw [hFixCard, hGcard] at hFixDvd
  norm_num at hFixDvd

theorem five_point_stabilizer_card_ne_one_thousand_one_hundred_fifty_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 1152 := by
  classical
  intro hHcard
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let S : Sylow 3 H := Sylow.nonempty.some
  have hScard : Nat.card S = 9 := by
    rw [S.card_eq_multiplicity,
      show Nat.card H = 1152 by
        simpa only [H] using hHcard,
      show 1152 = 3 ^ 2 * 128 by norm_num,
      Nat.factorization_mul (by norm_num)
        (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 3 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd
        (by norm_num)]
    norm_num
  let R : Subgroup P :=
    (S : Subgroup H).map H.subtype
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  let eSR : S ≃* R :=
    (S : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  have hRcard : Nat.card R = 9 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr eSR.symm.toEquiv
      _ = 9 := hScard
  have hnotFiveH :
      ¬5 ∣ Nat.card (fixingSubgroup P s) := by
    rw [hHcard]
    norm_num
  have hnotFiveAutR :
      ¬5 ∣ Nat.card (MulAut R) :=
    five_not_dvd_mulAut_card_of_card_nine
      R hRcard
  have hN5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : N, ∀ i, q • a i = b i := by
    simpa only [H, R, N, SN, F] using
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S
  have hNfive :
      MulAction.IsMultiplyPretransitive N F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hN5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  let J : Subgroup (Equiv.Perm F) := ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := hN5 a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    exact ⟨qJ, hq⟩
  have hJfive :
      MulAction.IsMultiplyPretransitive J F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hJ5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  let eX : Fin 5 ↪ X :=
    fiveEmbeddingOfSet X s hs
  have heXrange : Set.range eX = s :=
    range_fiveEmbeddingOfSet X s hs
  have heFixed (i : Fin 5) : eX i ∈ F := by
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨zH, hzS, hzEq⟩ :=
      Subgroup.mem_map.mp z.prop
    have hfix :
        H.subtype zH • eX i = eX i :=
      (mem_fixingSubgroup_iff P).mp zH.prop
        (eX i) (by
          rw [← heXrange]
          exact ⟨i, rfl⟩)
    rw [hzEq] at hfix
    exact hfix
  let eF : Fin 5 ↪ F := {
    toFun := fun i => ⟨eX i, heFixed i⟩
    inj' := fun i j hij =>
      eX.injective
        (congrArg (fun z : F => (z : X)) hij) }
  let sF : Set F := Set.range eF
  have hsF : sF.ncard = 5 := by
    rw [Set.ncard_range_of_injective eF.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let KJ : Subgroup J := fixingSubgroup J sF
  have hJfiveSF :
      MulAction.IsMultiplyPretransitive
        J F sF.ncard := by
    rw [hsF]
    exact hJfive
  have hKJindex :
      KJ.index =
        (Nat.card F).choose 5 *
          (5 : ℕ).factorial := by
    change
      (fixingSubgroup J sF).index =
        (Nat.card F).choose 5 *
          (5 : ℕ).factorial
    rw [hJfiveSF.index_of_fixingSubgroup_eq sF,
      hsF]
  have hfiveIndex : 5 ∣ KJ.index := by
    rw [hKJindex]
    exact dvd_mul_of_dvd_right (by norm_num) _
  have hindexProduct := KJ.index_mul_card
  have hindexDvdJ : KJ.index ∣ Nat.card J :=
    ⟨Nat.card KJ, hindexProduct.symm⟩
  have hfiveJ : 5 ∣ Nat.card J :=
    hfiveIndex.trans hindexDvdJ
  have hρproduct := ρ.ker.card_mul_index
  rw [Subgroup.index_ker] at hρproduct
  have hJdvdN : Nat.card J ∣ Nat.card N :=
    by
      change Nat.card ρ.range ∣ Nat.card N
      refine ⟨Nat.card ρ.ker, ?_⟩
      rw [Nat.mul_comm]
      exact hρproduct.symm
  have hfiveN : 5 ∣ Nat.card N :=
    hfiveJ.trans hJdvdN
  have hnotFiveKappaRange :
      ¬5 ∣ Nat.card κ.range := by
    intro hfiveRange
    exact hnotFiveAutR
      (hfiveRange.trans
        (Subgroup.card_subgroup_dvd_card κ.range))
  have hκproduct := κ.ker.card_mul_index
  rw [Subgroup.index_ker] at hκproduct
  have hfiveProduct :
      5 ∣ Nat.card κ.ker * Nat.card κ.range := by
    rw [hκproduct]
    exact hfiveN
  have hfiveKer : 5 ∣ Nat.card κ.ker :=
    ((show Nat.Prime 5 by norm_num).dvd_mul.mp
      hfiveProduct).resolve_right
        hnotFiveKappaRange
  let centralMap :
      κ.ker →*
        Subgroup.centralizer (R : Set P) :=
    (N.subtype.comp κ.ker.subtype).codRestrict
      (Subgroup.centralizer (R : Set P)) (by
        intro c
        have hc :
            (c.1 : N) ∈
              (Subgroup.centralizer (R : Set P)).subgroupOf N := by
          rw [← R.normalizerMonoidHom_ker]
          exact c.prop
        exact hc)
  have hcentralMapInjective :
      Function.Injective centralMap := by
    intro a b hab
    have habP :
        ((centralMap a :
            Subgroup.centralizer (R : Set P)) : P) =
          ((centralMap b :
            Subgroup.centralizer (R : Set P)) : P) :=
      congrArg
        (fun z :
          Subgroup.centralizer (R : Set P) =>
            (z : P)) hab
    apply Subtype.ext
    exact N.subtype_injective habP
  have hkerDvdCentral :
      Nat.card κ.ker ∣
        Nat.card
          (Subgroup.centralizer (R : Set P)) :=
    Subgroup.card_dvd_of_injective
      centralMap hcentralMapInjective
  have hfiveCentral :
      5 ∣ Nat.card
        (Subgroup.centralizer (R : Set P)) :=
    hfiveKer.trans hkerDvdCentral
  exact
    (five_not_dvd_centralizer_of_subgroup_card_nine
      X P hcard h5 hnotAlt s hs hnotFiveH
        R hRcard) hfiveCentral

end FiveTransitive.Degree24

end CFSG
