module

public import CFSG.Permutation.FiveTransitive.Degree20ReducedCases

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twenty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
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
  have hCases :
      (h = 27 ∨ h = 54 ∨ h = 768 ∨ h = 248832) ∨
      (h = 180 ∨ h = 360 ∨ h = 58320 ∨
        h = 116640 ∨ h = 5120) ∨
      (h = 2400 ∨ h = 21600 ∨ h = 777600) := by
    simpa only [H, h] using
      five_point_stabilizer_card_reduced_cases
        X P hcard h5 hnotAlt s hs
  have hnotSeventeen : ¬17 ∣ h := by
    intro hdiv
    rcases hCases with
        (h | h | h | h) |
        (h | h | h | h | h) |
        (h | h | h)
    all_goals omega
  have heNonempty : Nonempty (Fin 3 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 3 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP3.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 6840 := by
    change
      (fixingSubgroup P (Set.range e)).index = 6840
    omega
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 1860480 := by
    change (fixingSubgroup P s).index = 1860480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1860480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 272 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let T : Sylow 17 J := Sylow.nonempty.some
  have hh : h ≠ 0 :=
    Nat.ne_of_gt Nat.card_pos
  have hfactorization :
      (272 * h).factorization 17 = 1 := by
    rw [show 272 = 17 * 16 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 17 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotSeventeen]
    norm_num
  have hTcard : Nat.card T = 17 := by
    rw [T.card_eq_multiplicity, hJcard,
      hfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 17 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 17 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 17 := huorderT
  have huorderP : orderOf ((u : J) : P) = 17 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 17 := huorderJ
  let C : Subgroup J :=
    Subgroup.centralizer (T : Set J)
  let N : Subgroup J :=
    Subgroup.normalizer (T : Set J)
  have hTleC : (T : Subgroup J) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  let globalC : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hglobalCcard : Nat.card globalC = 17 := by
    simpa only [globalC] using
      FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
        X P (p := 17) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : C →* P :=
    J.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈ globalC := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : C →* globalC :=
    baseMap.codRestrict globalC hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective
      (J.subtype_injective hab')
  have hCdiv : Nat.card C ∣ 17 := by
    rw [← hglobalCcard]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hSeventeenDvdC : 17 ∣ Nat.card C := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleC
  have hCcard : Nat.card C = 17 :=
    Nat.dvd_antisymm hCdiv hSeventeenDvdC
  have hAutCard : Nat.card (MulAut T) = 16 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime (show Nat.Prime 17 by norm_num)]
  have hrangeDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 16 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card T.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (T : Set J)).relIndex
          (Subgroup.normalizer (T : Set J)) =
        Nat.card T.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      T.normalizerMonoidHom_ker]
    simp only [T.coe_coe]
  have hrDvd : C.relIndex N ∣ 16 := by
    rwa [hrEq]
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrPos : 0 < C.relIndex N :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 17 = 1 := by
    change
      (Subgroup.normalizer (T : Set J)).index % 17 = 1
    have hsylow :
        (Subgroup.normalizer (T : Set J)).index ≡ 1 [MOD 17] := by
      rw [← T.card_eq_index_normalizer]
      exact card_sylow_modEq_one 17 J
    change
      (Subgroup.normalizer (T : Set J)).index % 17 =
        1 % 17 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (T : Set J))
  have hCindex := C.index_mul_card
  have hproduct :
      C.relIndex N * N.index * 17 = Nat.card J := by
    rw [hCcard, ← hrel] at hCindex
    exact hCindex
  have hproduct' :
      C.relIndex N * N.index = 16 * h := by
    rw [hJcard] at hproduct
    nlinarith
  have hmod :
      (16 * h) % 17 = (C.relIndex N) % 17 := by
    calc
      (16 * h) % 17 =
          (C.relIndex N * N.index) % 17 :=
        congrArg (fun n => n % 17) hproduct'.symm
      _ = (C.relIndex N) % 17 := by
        rw [Nat.mul_mod, hNmod]
        simp
  have hhmod :
      (16 * h) % 17 = 7 ∨
        (16 * h) % 17 = 14 := by
    rcases hCases with
        (h | h | h | h) |
        (h | h | h | h | h) |
        (h | h | h)
    all_goals norm_num [h]
  have hrLe : C.relIndex N ≤ 16 :=
    Nat.le_of_dvd (by norm_num) hrDvd
  have hrLt : C.relIndex N < 17 := by
    omega
  rw [Nat.mod_eq_of_lt hrLt] at hmod
  have hrCases :
      C.relIndex N = 7 ∨ C.relIndex N = 14 := by
    omega
  rcases hrCases with hr | hr
  · rw [hr] at hrDvd
    norm_num at hrDvd
  · rw [hr] at hrDvd
    norm_num at hrDvd

theorem classification_of_five_transitive_of_card_eq_twenty
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 20)
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
    alternatingGroup_le_of_five_transitive_of_card_eq_twenty
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree20

end CFSG
