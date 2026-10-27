module

public import CFSG.Permutation.FiveTransitive.Degree18Centralizer
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import CFSG.Permutation.FiveTransitive.Degree18SylowSevenCard

public section

namespace CFSG

namespace FiveTransitive.Degree18

open MulAction SubMulAction Subgroup

private theorem sylowSeven_normalizer_card_le_eightyFour
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) (hScard : Nat.card S = 7) :
    Nat.card (Subgroup.normalizer (S : Set P)) ≤ 84 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder' : orderOf u = 7 := huorder.trans hScard
  have hu : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huorder'
    norm_num at huorder'
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hAutCard : Nat.card (MulAut S) = 6 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 6 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrangeLe : C.relIndex N ≤ 6 := by
    rw [hrEq]
    exact Nat.le_of_dvd (by norm_num) hrangeDvd
  have hCle :
      C ≤ Subgroup.centralizer ({(u : P)} : Set P) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hq (u : P) u.prop).symm
  have hCcardLe : Nat.card C ≤ 14 := by
    have hdiv := Subgroup.card_dvd_of_le hCle
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans
      (sylowSeven_element_centralizer_card_le_fourteen
        X P hcard h5 hnotAlt S hScard u hu)
  have hrel :
      C.relIndex N * N.index = C.index :=
    Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set P))
  have hNcardEq :
      Nat.card N = C.relIndex N * Nat.card C := by
    have hprod :
        N.index * (C.relIndex N * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (C.relIndex N * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card P := C.index_mul_card
        _ = N.index * Nat.card N := N.index_mul_card.symm
    exact (Nat.mul_left_cancel
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      hprod).symm
  rw [hNcardEq]
  exact (Nat.mul_le_mul hrangeLe hCcardLe).trans (by norm_num)

private theorem nonidentity_sylowSeven_fixed_points_of_card_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) (hScard : Nat.card S = 7)
    (u : S) (hu : u ≠ 1) :
    Fintype.card (MulAction.fixedBy X (u : P)) = 4 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let g : Equiv.Perm X := (u : P)
  have huorder : orderOf u = 7 :=
    Degree15.orderOf_eq_prime_of_card_eq_prime hScard hu
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 18 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 18 := hcard
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
    · have hgcycle : g.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm, hmOne]
        simp
      have hgsupport : g.support.card = 7 := by
        omega
      exact (hnotAlt
        (alternatingGroup_le_of_sevenCycle
          X P hcard h5 (u : P).prop hgcycle hgsupport)).elim
    · exact hmTwo
  have hgsupport : g.support.card = 14 := by
    omega
  rw [Degree15.card_fixedBy_subgroup_perm, hcard]
  change 18 - g.support.card = 4
  rw [hgsupport]

theorem alternatingGroup_le_of_five_transitive_of_card_eq_eighteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 P := Sylow.nonempty.some
  have hScard : Nat.card S = 7 :=
    sylowSeven_card_eq_seven X P hcard h5 hnotAlt S
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hNcardLe : Nat.card N ≤ 84 :=
    sylowSeven_normalizer_card_le_eightyFour
      X P hcard h5 hnotAlt S hScard
  let A := Degree15.NonidentitySylowElements 7 P
  let val : A → P :=
    Degree15.nonidentitySylowElementVal 7 P
  have hfixedPoints (a : A) :
      Fintype.card (MulAction.fixedBy X (val a)) = 4 := by
    rcases a with ⟨T, u⟩
    exact nonidentity_sylowSeven_fixed_points_of_card_seven
      X P hcard h5 hnotAlt T
        (Degree15.sylow_card_eq_of_card_eq S hScard T)
        u.1 u.2
  have hfixedFour (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (val a)) = 24 := by
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (val a)) =
          (Fintype.card
            (MulAction.fixedBy X (val a))).descFactorial
              (Fintype.card (Fin 4)) :=
        Degree15.card_fixedBy_embedding (val a)
      _ = 24 := by
        rw [hfixedPoints, Fintype.card_fin]
        norm_num
  have hvalInjective : Function.Injective val :=
    Degree15.nonidentitySylowElementVal_injective S hScard
  have hAcard : Fintype.card A = N.index * 6 := by
    rw [show Fintype.card A =
        Fintype.card (Sylow 7 P) * (7 - 1) by
      exact Degree15.card_nonidentitySylowElements S hScard]
    rw [← Nat.card_eq_fintype_card,
      S.card_eq_index_normalizer]
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) =
        N.index * 6 * 24 := by
    simp_rw [hfixedFour]
    simp [hAcard]
  have hselectedLe :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
    calc
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card
              (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsMultiplyPretransitive P X 4 := hP4
  letI : Nonempty (Fin 4 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
      norm_num)
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 4 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 4 ↪ X)).mp hP4)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 4 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hcount :
      N.index * 6 * 24 ≤ Nat.card P := by
    calc
      N.index * 6 * 24 =
          ∑ a : A,
            Fintype.card
              (MulAction.fixedBy (Fin 4 ↪ X) (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  have hcount' :
      N.index * 144 ≤ N.index * Nat.card N := by
    rw [N.index_mul_card]
    simpa [Nat.mul_assoc] using hcount
  have hnormalizerLower : 144 ≤ Nat.card N :=
    Nat.le_of_mul_le_mul_left hcount'
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  omega

end FiveTransitive.Degree18

end CFSG
