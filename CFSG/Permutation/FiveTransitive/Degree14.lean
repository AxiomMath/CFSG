module

public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.PermCentralizer
public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.GroupTheory.Transfer
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.Degree14

open MulAction SubMulAction Subgroup

private theorem five_point_stabilizer_card_le_eight_or_nine_mul_divisor_eight
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≤ 8 ∨
      ∃ d : ℕ, d ∣ 8 ∧
        Nat.card (fixingSubgroup P s) = 9 * d := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 9 := by
    change Nat.card ↥(sᶜ : Set X) = 9
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  by_cases hKsmall : Nat.card K ≤ 8
  · exact Or.inl hKsmall
  right
  have hfixedSmall :
      ∀ k : K, k ≠ 1 →
        Nat.card (MulAction.fixedBy Y k) ≤ 1 := by
    intro k hk
    rw [Finite.card_le_one_iff_subsingleton]
    constructor
    rintro ⟨y, hy⟩ ⟨z, hz⟩
    apply Subtype.ext
    by_contra hyz
    let M : Subgroup K :=
      MulAction.stabilizer K y ⊓ MulAction.stabilizer K z
    letI : Subsingleton M :=
      Helpers.inf_stabilizer_subsingleton_of_not_alternating14
        X P hcard h5 hnotAlt hs y z hyz
    have hkM :
        k ∈ MulAction.stabilizer K y ⊓
          MulAction.stabilizer K z := by
      rw [Subgroup.mem_inf]
      exact ⟨MulAction.mem_stabilizer_iff.mpr hy,
        MulAction.mem_stabilizer_iff.mpr hz⟩
    let u : M := ⟨k, hkM⟩
    have hu : u = 1 := Subsingleton.elim _ _
    apply hk
    simpa [u] using congrArg (fun v : M => (v : K)) hu
  have hpretransitive : MulAction.IsPretransitive K Y := by
    apply
      OrbitBounds.isPretransitive_of_card_nine_of_large_group_of_small_fixedBy
        K Y
    · rwa [← Nat.card_eq_fintype_card]
    · exact hfixedSmall
    · rw [← Nat.card_eq_fintype_card]
      omega
  letI : MulAction.IsPretransitive K Y := hpretransitive
  letI : Nonempty Y := Finite.card_pos_iff.mp (by omega)
  let y : Y := Classical.choice inferInstance
  let L : Subgroup K := MulAction.stabilizer K y
  let Z := SubMulAction.ofStabilizer K y
  letI : MulAction L Z :=
    Subtype.coe_injective.mulAction Subtype.val (SetLike.val_smul Z)
  have hZcard : Nat.card Z = 8 := by
    have hz : Nat.card Z + 1 = Nat.card Y := by
      simpa only [Z] using
        SubMulAction.nat_card_ofStabilizer_add_one_eq K y
    rw [hYcard] at hz
    omega
  have hfixedNone :
      ∀ l : L, l ≠ 1 →
        Nat.card (MulAction.fixedBy Z l) = 0 := by
    intro l hl
    rw [Finite.card_eq_zero_iff]
    constructor
    rintro ⟨z, hz⟩
    have hyz : y ≠ (z : Y) :=
      (SubMulAction.neq_of_mem_ofStabilizer K y).symm
    let M : Subgroup K :=
      MulAction.stabilizer K y ⊓
        MulAction.stabilizer K (z : Y)
    letI : Subsingleton M :=
      Helpers.inf_stabilizer_subsingleton_of_not_alternating14
        X P hcard h5 hnotAlt hs y (z : Y) hyz
    have hzY : ((l : L) : K) • (z : Y) = z :=
      congrArg Subtype.val hz
    have hlM :
        ((l : L) : K) ∈ MulAction.stabilizer K y ⊓
          MulAction.stabilizer K (z : Y) := by
      rw [Subgroup.mem_inf]
      exact ⟨l.prop, MulAction.mem_stabilizer_iff.mpr hzY⟩
    let u : M := ⟨(l : L), hlM⟩
    have hu : u = 1 := Subsingleton.elim _ _
    apply hl
    apply Subtype.ext
    simpa [u] using congrArg (fun v : M => (v : K)) hu
  have hLdvd : Fintype.card L ∣ Fintype.card Z :=
    OrbitBounds.card_group_dvd_card_of_no_nontrivial_fixedPoints
      L Z hfixedNone
  have hLdvdEight : Nat.card L ∣ 8 := by
    have hZcardF : Fintype.card Z = 8 := by
      rwa [← Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card]
    simpa [hZcardF] using hLdvd
  have hOrbitCard : Fintype.card (MulAction.orbit K y) = 9 := by
    rw [MulAction.orbit_eq_univ K y]
    simpa using hYcard
  have hOrbitStabilizer :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group K y
  rw [hOrbitCard] at hOrbitStabilizer
  refine ⟨Nat.card L, hLdvdEight, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hOrbitStabilizer.symm

private theorem five_point_stabilizer_card_preliminary_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 1 ∨
      Nat.card (fixingSubgroup P s) = 2 ∨
      Nat.card (fixingSubgroup P s) = 3 ∨
      Nat.card (fixingSubgroup P s) = 4 ∨
      Nat.card (fixingSubgroup P s) = 6 ∨
      Nat.card (fixingSubgroup P s) = 8 ∨
      Nat.card (fixingSubgroup P s) = 9 ∨
      Nat.card (fixingSubgroup P s) = 18 ∨
      Nat.card (fixingSubgroup P s) = 36 ∨
      Nat.card (fixingSubgroup P s) = 72 := by
  let K : Subgroup P := fixingSubgroup P s
  change Nat.card K = 1 ∨ Nat.card K = 2 ∨
    Nat.card K = 3 ∨ Nat.card K = 4 ∨
    Nat.card K = 6 ∨ Nat.card K = 8 ∨
    Nat.card K = 9 ∨ Nat.card K = 18 ∨
    Nat.card K = 36 ∨ Nat.card K = 72
  rcases five_point_stabilizer_card_le_eight_or_nine_mul_divisor_eight
      X P hcard h5 hnotAlt hs with hKsmall | ⟨d, hd, hKcard⟩
  · have hKpos : 0 < Nat.card K := Nat.card_pos
    have hKneFive : Nat.card K ≠ 5 := by
      intro hKeq
      have hp :=
        Helpers.prime_dvd_five_point_stabilizer_eq_two_or_three_of_not_alternating14
          X P hcard h5 hnotAlt hs (p := 5) (by norm_num) (by
            change 5 ∣ Nat.card K
            rw [hKeq])
      omega
    have hKneSeven : Nat.card K ≠ 7 := by
      intro hKeq
      have hp :=
        Helpers.prime_dvd_five_point_stabilizer_eq_two_or_three_of_not_alternating14
          X P hcard h5 hnotAlt hs (p := 7) (by norm_num) (by
            change 7 ∣ Nat.card K
            rw [hKeq])
      omega
    interval_cases hKeq : Nat.card K <;> omega
  · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hdle : d ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    change Nat.card K = 9 * d at hKcard
    interval_cases d <;> norm_num at hd
    all_goals norm_num [hKcard]

private theorem stabilizer_factor_cases_after_sylow_thirteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (k : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
      k = 6 ∨ k = 8 ∨ k = 9 ∨ k = 18 ∨
      k = 36 ∨ k = 72)
    (hPcard : Nat.card P = 240240 * k) :
    k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 := by
  classical
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try norm_num
  all_goals
    letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    let S : Sylow 13 P := Sylow.nonempty.some
    have hScard : Nat.card S = 13 := by
      rw [S.card_eq_multiplicity, hPcard]
      rw [show 240240 = 13 * 18480 by norm_num, Nat.mul_assoc,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    letI : IsCyclic S := isCyclic_of_prime_card hScard
    letI : IsMulCommutative S := IsCyclic.isMulCommutative
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have huorder : orderOf u = 13 := hu.trans hScard
    let g : Equiv.Perm X := (u : P)
    have hgorder : orderOf g = 13 := by
      calc
        orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
        _ = orderOf u := Subgroup.orderOf_coe _
        _ = 13 := huorder
    have hgprime : (orderOf g).Prime := by
      rw [hgorder]
      norm_num
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' hgprime (by
        rw [hcard, hgorder]
        norm_num)
    have hgsupport : g.support.card = 13 := by
      rw [← hgcycle.orderOf, hgorder]
    have hcentralizerPerm :
        Nat.card (Subgroup.centralizer
          ({g} : Set (Equiv.Perm X))) = 13 := by
      rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
        hgsupport, hcard]
      norm_num
    let C : Subgroup P :=
      Subgroup.centralizer (S : Set P)
    have hSC : (S : Subgroup P) ≤ C :=
      Subgroup.le_centralizer (S : Subgroup P)
    let baseMap : C →* Equiv.Perm X :=
      P.subtype.comp C.subtype
    have hbaseMapMem :
        ∀ c : C, baseMap c ∈
          Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
      intro c
      change ((c.1 : P) : Equiv.Perm X) ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((c.2 (u : P) u.prop).symm)
    let centMap :
        C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
      baseMap.codRestrict
        (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hbaseMapMem
    have hcentMapInjective : Function.Injective centMap := by
      intro a b hab
      have hab' := congrArg Subtype.val hab
      change baseMap a = baseMap b at hab'
      exact C.subtype_injective (P.subtype_injective hab')
    have hCdiv13 : Nat.card C ∣ 13 := by
      rw [← hcentralizerPerm]
      exact Subgroup.card_dvd_of_injective centMap hcentMapInjective
    have h13divC : 13 ∣ Nat.card C := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le hSC
    have hCcard : Nat.card C = 13 :=
      Nat.dvd_antisymm hCdiv13 h13divC
    have hAutCard : Nat.card (MulAut S) = 12 := by
      rw [IsCyclic.card_mulAut S, hScard,
        Nat.totient_prime (by norm_num)]
    have hrangeDvd :
        Nat.card S.normalizerMonoidHom.range ∣ 12 := by
      rw [← hAutCard]
      exact Subgroup.card_subgroup_dvd_card _
    have hrEq :
        C.relIndex (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range := by
      change
        (Subgroup.centralizer (S : Set P)).relIndex
            (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range
      rw [Subgroup.relIndex, ← Subgroup.index_ker,
        S.normalizerMonoidHom_ker]
      simp only [S.coe_coe]
    have hrDvd :
        C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 12 := by
      rwa [hrEq]
    have hsmod :
        (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 13] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 13 P
    have hrel :
        C.relIndex (Subgroup.normalizer (S : Set P)) *
            (Subgroup.normalizer (S : Set P)).index =
          C.index := by
      simpa only [C] using Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S : Set P))
    have hCindex := C.index_mul_card
    rw [hCcard, hPcard, ← hrel] at hCindex
    letI :
        C.IsFiniteRelIndex (Subgroup.normalizer (S : Set P)) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    have hrpos :
        0 < C.relIndex (Subgroup.normalizer (S : Set P)) :=
      Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have hrle :
        C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 12 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    change
      (Subgroup.normalizer (S : Set P)).index % 13 = 1 at hsmod
    interval_cases C.relIndex (Subgroup.normalizer (S : Set P))
    all_goals try norm_num at hrDvd
    all_goals try norm_num at hCindex
    all_goals omega

private theorem stabilizer_factor_eight_impossible_by_sylow_eleven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (hPcard : Nat.card P = 240240 * 8) :
    False := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S : Sylow 11 P := Sylow.nonempty.some
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 240240 = 11 * 21840 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 11 := hu.trans hScard
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      norm_num)
  have hgsupport : g.support.card = 11 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 66 := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  have hSC : (S : Subgroup P) ≤ C :=
    Subgroup.le_centralizer (S : Subgroup P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro c
    change ((c.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((c.2 (u : P) u.prop).symm)
  let centMap :
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv66 : Nat.card C ∣ 66 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective centMap hcentMapInjective
  have h11divC : 11 ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSC
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle : Nat.card C ≤ 66 :=
    Nat.le_of_dvd (by norm_num) hCdiv66
  have hCcases :
      Nat.card C = 11 ∨ Nat.card C = 22 ∨
        Nat.card C = 33 ∨ Nat.card C = 66 := by
    interval_cases hCcard : Nat.card C
    all_goals try norm_num at hCdiv66
    all_goals try norm_num at h11divC
    all_goals norm_num [hCcard]
  have hAutCard : Nat.card (MulAut S) = 10 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 10 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd :
      C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 10 := by
    rwa [hrEq]
  have hsmod :
      (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 11] := by
    rw [← S.card_eq_index_normalizer]
    exact card_sylow_modEq_one 11 P
  have hrel :
      C.relIndex (Subgroup.normalizer (S : Set P)) *
          (Subgroup.normalizer (S : Set P)).index =
        C.index := by
    simpa only [C] using Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set P))
  have hCindex := C.index_mul_card
  rw [hPcard, ← hrel] at hCindex
  letI :
      C.IsFiniteRelIndex (Subgroup.normalizer (S : Set P)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrpos :
      0 < C.relIndex (Subgroup.normalizer (S : Set P)) :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrle :
      C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 10 :=
    Nat.le_of_dvd (by norm_num) hrDvd
  change
    (Subgroup.normalizer (S : Set P)).index % 11 = 1 at hsmod
  rcases hCcases with hCcard | hCcard | hCcard | hCcard
  all_goals rw [hCcard] at hCindex
  all_goals
    interval_cases C.relIndex (Subgroup.normalizer (S : Set P))
  all_goals try norm_num at hrDvd
  all_goals try norm_num at hCindex
  all_goals omega

private theorem sylow_eleven_centralizer_card_eq_eleven_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 11 P) (hScard : Nat.card S = 11) :
    Nat.card (Subgroup.centralizer (S : Set P)) = 11 := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 11 := hu.trans hScard
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      norm_num)
  have hgsupport : g.support.card = 11 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 66 := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  have hSC : (S : Subgroup P) ≤ C :=
    Subgroup.le_centralizer (S : Subgroup P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro c
    change ((c.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((c.2 (u : P) u.prop).symm)
  let centMap :
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv66 : Nat.card C ∣ 66 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective centMap hcentMapInjective
  have h11divC : 11 ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSC
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle : Nat.card C ≤ 66 :=
    Nat.le_of_dvd (by norm_num) hCdiv66
  have hCcases :
      Nat.card C = 11 ∨ Nat.card C = 22 ∨
        Nat.card C = 33 ∨ Nat.card C = 66 := by
    interval_cases hCcard : Nat.card C
    all_goals try norm_num at hCdiv66
    all_goals try norm_num at h11divC
    all_goals norm_num [hCcard]
  have himpossible {q : ℕ} (hq : q.Prime) (hqcop : Nat.Coprime q 11)
      (hqdvd : q ∣ Nat.card C) : False := by
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    let w : Equiv.Perm X := (v : P)
    have hworder : orderOf w = q := by
      calc
        orderOf w = orderOf (v : P) := Subgroup.orderOf_coe _
        _ = orderOf v := Subgroup.orderOf_coe _
        _ = q := hv
    have hcomm : Commute w g := by
      exact congrArg Subtype.val ((v.prop (u : P) u.prop).symm)
    have hcoprime : Nat.Coprime (orderOf w) (orderOf g) := by
      rw [hworder, hgorder]
      exact hqcop
    have hsuppSubset :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hgcycle hcomm hcoprime
    have hsuppCard : w.support.card ≤ 3 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 3 := by
          rw [Finset.card_compl, hgsupport, hcard]
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    have hwP : w ∈ P := (v : P).prop
    exact hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) hwP hwNe (by omega))
  rcases hCcases with hCcard | hCcard | hCcard | hCcard
  · exact hCcard
  · exfalso
    exact himpossible (q := 2) (by norm_num) (by norm_num) (by
      rw [hCcard]
      norm_num)
  · exfalso
    exact himpossible (q := 3) (by norm_num) (by norm_num) (by
      rw [hCcard]
      norm_num)
  · exfalso
    exact himpossible (q := 2) (by norm_num) (by norm_num) (by
      rw [hCcard]
      norm_num)

private theorem stabilizer_factor_eq_two_after_sylow_eleven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (k : ℕ) (hk : k = 2 ∨ k = 4 ∨ k = 6)
    (hPcard : Nat.card P = 240240 * k) :
    k = 2 := by
  classical
  rcases hk with rfl | rfl | rfl
  · rfl
  all_goals
    letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    let S : Sylow 11 P := Sylow.nonempty.some
    have hScard : Nat.card S = 11 := by
      rw [S.card_eq_multiplicity, hPcard]
      rw [show 240240 = 11 * 21840 by norm_num, Nat.mul_assoc,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    letI : IsCyclic S := isCyclic_of_prime_card hScard
    letI : IsMulCommutative S := IsCyclic.isMulCommutative
    let C : Subgroup P :=
      Subgroup.centralizer (S : Set P)
    have hCcard : Nat.card C = 11 := by
      exact sylow_eleven_centralizer_card_eq_eleven_of_not_alternating
        X P hcard h5 hnotAlt S hScard
    have hAutCard : Nat.card (MulAut S) = 10 := by
      rw [IsCyclic.card_mulAut S, hScard,
        Nat.totient_prime (by norm_num)]
    have hrangeDvd :
        Nat.card S.normalizerMonoidHom.range ∣ 10 := by
      rw [← hAutCard]
      exact Subgroup.card_subgroup_dvd_card _
    have hrEq :
        C.relIndex (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range := by
      change
        (Subgroup.centralizer (S : Set P)).relIndex
            (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range
      rw [Subgroup.relIndex, ← Subgroup.index_ker,
        S.normalizerMonoidHom_ker]
      simp only [S.coe_coe]
    have hrDvd :
        C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 10 := by
      rwa [hrEq]
    have hsmod :
        (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 11] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 11 P
    have hrel :
        C.relIndex (Subgroup.normalizer (S : Set P)) *
            (Subgroup.normalizer (S : Set P)).index =
          C.index := by
      simpa only [C] using Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S : Set P))
    have hCindex := C.index_mul_card
    rw [hCcard, hPcard, ← hrel] at hCindex
    letI :
        C.IsFiniteRelIndex (Subgroup.normalizer (S : Set P)) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    have hrpos :
        0 < C.relIndex (Subgroup.normalizer (S : Set P)) :=
      Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have hrle :
        C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 10 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    change
      (Subgroup.normalizer (S : Set P)).index % 11 = 1 at hsmod
    interval_cases C.relIndex (Subgroup.normalizer (S : Set P))
    all_goals try norm_num at hrDvd
    all_goals try norm_num at hCindex
    all_goals omega

private theorem five_point_stabilizer_card_eq_two_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 2 := by
  let K : Subgroup P := fixingSubgroup P s
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 240240 := by
    omega
  have hKindex := K.index_mul_card
  have hPcard : Nat.card P = 240240 * Nat.card K := by
    change
      (fixingSubgroup P s).index *
          Nat.card (fixingSubgroup P s) =
        Nat.card P at hKindex
    rw [hfixIndex'] at hKindex
    exact hKindex.symm
  have hpreliminary :=
    five_point_stabilizer_card_preliminary_cases
      X P hcard h5 hnotAlt hs
  change Nat.card K = 1 ∨ Nat.card K = 2 ∨
    Nat.card K = 3 ∨ Nat.card K = 4 ∨
    Nat.card K = 6 ∨ Nat.card K = 8 ∨
    Nat.card K = 9 ∨ Nat.card K = 18 ∨
    Nat.card K = 36 ∨ Nat.card K = 72 at hpreliminary
  have hafterThirteen :=
    stabilizer_factor_cases_after_sylow_thirteen
      X P hcard (Nat.card K) hpreliminary hPcard
  have hnotEight : Nat.card K ≠ 8 := by
    intro hKeight
    apply stabilizer_factor_eight_impossible_by_sylow_eleven
      X P hcard
    rw [hPcard, hKeight]
  have hsmall : Nat.card K = 2 ∨ Nat.card K = 4 ∨
      Nat.card K = 6 := by
    rcases hafterThirteen with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (hnotEight h).elim
  have htwo :=
    stabilizer_factor_eq_two_after_sylow_eleven
      X P hcard h5 hnotAlt (Nat.card K) hsmall hPcard
  exact htwo

private theorem sylow_thirteen_normalizer_le_centralizer_of_factor_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (hPcard : Nat.card P = 240240 * 2)
    (S : Sylow 13 P) :
    Subgroup.normalizer (S : Set P) ≤
      Subgroup.centralizer (S : Set P) := by
  classical
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hScard : Nat.card S = 13 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 240240 = 13 * 18480 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 13 := hu.trans hScard
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 13 := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  have hSC : (S : Subgroup P) ≤ C :=
    Subgroup.le_centralizer (S : Subgroup P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro c
    change ((c.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((c.2 (u : P) u.prop).symm)
  let centMap :
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv13 : Nat.card C ∣ 13 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective centMap hcentMapInjective
  have h13divC : 13 ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSC
  have hCcard : Nat.card C = 13 :=
    Nat.dvd_antisymm hCdiv13 h13divC
  have hAutCard : Nat.card (MulAut S) = 12 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 12 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd :
      C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 12 := by
    rwa [hrEq]
  have hsmod :
      (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 13] := by
    rw [← S.card_eq_index_normalizer]
    exact card_sylow_modEq_one 13 P
  have hrel :
      C.relIndex (Subgroup.normalizer (S : Set P)) *
          (Subgroup.normalizer (S : Set P)).index =
        C.index := by
    simpa only [C] using Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set P))
  have hCindex := C.index_mul_card
  rw [hCcard, hPcard, ← hrel] at hCindex
  letI :
      C.IsFiniteRelIndex (Subgroup.normalizer (S : Set P)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrpos :
      0 < C.relIndex (Subgroup.normalizer (S : Set P)) :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrle :
      C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 12 :=
    Nat.le_of_dvd (by norm_num) hrDvd
  change
    (Subgroup.normalizer (S : Set P)).index % 13 = 1 at hsmod
  have hrone :
      C.relIndex (Subgroup.normalizer (S : Set P)) = 1 := by
    interval_cases C.relIndex (Subgroup.normalizer (S : Set P))
    all_goals try norm_num at hrDvd
    all_goals try norm_num at hCindex
    all_goals omega
  exact Subgroup.relIndex_eq_one.mp hrone

theorem alternatingGroup_le_of_five_transitive_of_card_eq_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      omega)
  let K : Subgroup P := fixingSubgroup P s
  have hKcard : Nat.card K = 2 := by
    exact five_point_stabilizer_card_eq_two_of_not_alternating
      X P hcard h5 hnotAlt hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hKindex : K.index = 240240 := by
    change (fixingSubgroup P s).index = 240240
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 240240 * 2 := by
    rw [hKindex, hKcard] at hKindexCard
    exact hKindexCard.symm
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let S : Sylow 13 P := Sylow.nonempty.some
  have hScard : Nat.card S = 13 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 240240 = 13 * 18480 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnormalizer :
      Subgroup.normalizer (S : Set P) ≤
        Subgroup.centralizer (S : Set P) :=
    sylow_thirteen_normalizer_le_centralizer_of_factor_two
      X P hcard hPcard S
  let f : P →* S := MonoidHom.transferSylow S hnormalizer
  let N : Subgroup P := f.ker
  have hcomplement : N.IsComplement' S := by
    exact MonoidHom.ker_transferSylow_isComplement' S hnormalizer
  have hNcard : Nat.card N = 36960 := by
    have hproduct := hcomplement.card_mul
    rw [hScard, hPcard] at hproduct
    omega
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsMultiplyPretransitive P X 2 := hP2
  letI : MulAction.IsPretransitive P X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  letI : MulAction.IsPreprimitive P X :=
    MulAction.isPreprimitive_of_is_two_pretransitive hP2
  letI : N.Normal := by
    dsimp only [N]
    infer_instance
  have hNnotFixed : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    letI : Subsingleton N := ⟨fun a b => by
      apply Subtype.ext
      apply P.subtype_injective
      ext x
      have hx : x ∈ MulAction.fixedPoints N X := by
        rw [hfixed]
        exact Set.mem_univ x
      have ha := (MulAction.mem_fixedPoints.mp hx) a
      have hb := (MulAction.mem_fixedPoints.mp hx) b
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm⟩
    have hNle : Nat.card N ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  have hNtransitive : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hNnotFixed
  letI : MulAction.IsPretransitive N X := hNtransitive
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let x : X := Classical.choice inferInstance
  have hNOrbitCard :
      Fintype.card (MulAction.orbit N x) = 14 := by
    rw [MulAction.orbit_eq_univ N x]
    simpa using hcard
  have hNOrbitStabilizer :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group N x
  have hNcardF : Fintype.card N = 36960 := by
    rwa [← Nat.card_eq_fintype_card]
  rw [hNOrbitCard, hNcardF] at hNOrbitStabilizer
  have hNstabilizerCard :
      Fintype.card (MulAction.stabilizer N x) = 2640 := by
    omega
  let Px : Subgroup P := MulAction.stabilizer P x
  let Y := SubMulAction.ofStabilizer P x
  have hYcard : Nat.card Y = 13 := by
    have hXcardNat : Nat.card X = 14 := by
      rwa [Nat.card_eq_fintype_card]
    dsimp only [Y]
    rw [SubMulAction.nat_card_ofStabilizer_eq, hXcardNat]
  have hPx4 : MulAction.IsMultiplyPretransitive Px Y 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := P) (α := X) (n := 4) (a := x)).mp hP5
  letI : MulAction.IsMultiplyPretransitive Px Y 4 := hPx4
  have hPx2 : MulAction.IsMultiplyPretransitive Px Y 2 := by
    exact MulAction.isMultiplyPretransitive_of_le
      (G := Px) (α := Y) (m := 2) (n := 4) (by omega) (by
        rw [hYcard]
        omega)
  letI : MulAction.IsMultiplyPretransitive Px Y 2 := hPx2
  letI : MulAction.IsPretransitive Px Y :=
    MulAction.isPretransitive_of_is_two_pretransitive
  letI : MulAction.IsPreprimitive Px Y :=
    MulAction.isPreprimitive_of_is_two_pretransitive hPx2
  letI : Nonempty Y := Finite.card_pos_iff.mp (by omega)
  let Nst : Subgroup Px := N.comap Px.subtype
  letI : Nst.Normal := by
    dsimp only [Nst]
    infer_instance
  have hNstCard : Nat.card Nst = 2640 := by
    calc
      Nat.card Nst =
          Nat.card (MulAction.stabilizer N x) :=
        Nat.card_congr
          (OrbitBounds.normalComapStabilizerEquivStabilizer
            P X N x).toEquiv
      _ = Fintype.card (MulAction.stabilizer N x) :=
        Nat.card_eq_fintype_card
      _ = 2640 := hNstabilizerCard
  have hPxFaithful :
      ∀ p : Px, (∀ y : Y, p • y = y) → p = 1 := by
    intro p hp
    apply Subtype.ext
    apply P.subtype_injective
    ext z
    by_cases hz : z = x
    · subst z
      have hpfix : (p : P) • x = x :=
        MulAction.mem_stabilizer_iff.mp p.prop
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hpfix
    · let y : Y := ⟨z, hz⟩
      have hy := congrArg Subtype.val (hp y)
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using hy
  have hdichotomy :=
    OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
      Px Y hPxFaithful Nst
  rw [hNstCard, hYcard] at hdichotomy
  norm_num at hdichotomy

theorem classification_of_five_transitive_of_card_eq_fourteen
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hAlt : alternatingGroup X ≤ P :=
    alternatingGroup_le_of_five_transitive_of_card_eq_fourteen
      X P hcard h5P
  exact Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree14

end CFSG
