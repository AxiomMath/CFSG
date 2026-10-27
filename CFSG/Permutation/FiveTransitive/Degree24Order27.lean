module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints
public import CFSG.Permutation.FiveTransitive.Degree19CoprimeComplement
public import CFSG.Permutation.FiveTransitive.Degree19FourPointIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

@[expose] def rotateFive : Equiv.Perm (Fin 5) :=
  finRotate 5

theorem rotateFive_pow_five :
    rotateFive ^ 5 = 1 := by
  decide

private theorem rotateFive_pow_twenty_seven_fixedPointFree :
    ∀ i : Fin 5, (rotateFive ^ 27) i ≠ i := by
  rw [show (27 : ℕ) = 5 * 5 + 2 from rfl, pow_add, pow_mul, rotateFive_pow_five]
  simp only [one_pow, one_mul]
  decide

private theorem order_five_normalizer_centralizes_card_twenty_seven
    (G : Type) [Group G] [Fintype G]
    (H : Subgroup G)
    (hHcard : Nat.card H = 27)
    (r : G) (hrOrder : orderOf r = 5)
    (hrNormalizer : r ∈ Subgroup.normalizer H) :
    ∀ h : H, Commute r (h : G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer H
  let rN : N := ⟨r, hrNormalizer⟩
  let T : Subgroup N := Subgroup.zpowers rN
  have hrNOrder : orderOf rN = 5 := by
    calc
      orderOf rN = orderOf r :=
        (Subgroup.orderOf_coe rN).symm
      _ = 5 := hrOrder
  have hTcard : Nat.card T = 5 := by
    rw [Nat.card_zpowers, hrNOrder]
  have hTp : IsPGroup 5 T := by
    apply IsPGroup.of_card (n := 1)
    rw [hTcard]
    norm_num
  have htrivial :=
    FiveTransitive.Degree19.five_group_action_on_small_group_is_trivial
      T H hTp (Or.inr (Or.inr (Or.inr hHcard)))
  intro h
  have hrT : rN ∈ T :=
    Subgroup.mem_zpowers rN
  have hfixed :=
    htrivial (⟨rN, hrT⟩ : T) h
  have hfixedG :=
    congrArg (fun k : H => (k : G)) hfixed
  change r * (h : G) * r⁻¹ = (h : G) at hfixedG
  rw [mul_inv_eq_iff_eq_mul] at hfixedG
  exact hfixedG

private theorem fixed_card_arithmetic :
    ∀ f : Fin 24,
      5 ≤ f.val →
      f.val % 3 = 0 →
      f.val.descFactorial 5 ∣ 5100480 →
      f.val = 6 := by
  decide

private theorem five_point_stabilizer_fixed_points_card_eq_six_of_card_eq_twenty_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard :
      Nat.card (fixingSubgroup P s) = 27) :
    Nat.card
        (MulAction.fixedPoints
          (fixingSubgroup P s) X) = 6 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let F : Set X := MulAction.fixedPoints H X
  let f := Nat.card F
  change f = 6
  have hsFixed : s ⊆ F := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro h
    exact
      (mem_fixingSubgroup_iff P).mp h.prop x hx
  have hfFive : 5 ≤ f := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ F.ncard :=
        Set.ncard_le_ncard hsFixed
      _ = f := (Nat.card_coe_set_eq F).symm
  have hfLe : f ≤ 24 := by
    calc
      f = F.ncard := Nat.card_coe_set_eq F
      _ ≤ (Set.univ : Set X).ncard :=
        Set.ncard_le_ncard (Set.subset_univ F)
      _ = 24 := by
        rw [Set.ncard_univ,
          Nat.card_eq_fintype_card, hcard]
  have hfLt : f < 24 := by
    by_contra hlt
    have hfEq : f = 24 := by omega
    have hFuniv : F = Set.univ := by
      rw [Set.eq_univ_iff_ncard]
      calc
        F.ncard = f := (Nat.card_coe_set_eq F).symm
        _ = 24 := hfEq
        _ = Nat.card X := by
          rw [Nat.card_eq_fintype_card, hcard]
    have hHsubsingleton : Subsingleton H := by
      constructor
      intro a b
      apply Subtype.ext
      apply P.subtype_injective
      ext x
      have hx : x ∈ F := by rw [hFuniv]; simp
      have ha := hx a
      have hb := hx b
      simpa [Subgroup.smul_def,
        Equiv.Perm.smul_def] using ha.trans hb.symm
    letI : Subsingleton H := hHsubsingleton
    have hHone : Nat.card H = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨inferInstance, inferInstance⟩
    rw [hHcard] at hHone
    norm_num at hHone
  have hHp : IsPGroup 3 H := by
    apply IsPGroup.of_card (n := 3)
    rw [hHcard]
    norm_num
  have hfModRaw :=
    hHp.card_modEq_card_fixedPoints X
  have hfMod : f % 3 = 0 := by
    change Nat.card X % 3 = f % 3 at hfModRaw
    rw [Nat.card_eq_fintype_card, hcard] at hfModRaw
    norm_num at hfModRaw
    exact hfModRaw.symm
  have hfDvd :
      f.descFactorial 5 ∣ 5100480 := by
    simpa only [H, F, f] using
      five_point_stabilizer_fixed_points_descFactorial_dvd
        X P hcard h5 s hs
  let f' : Fin 24 := ⟨f, hfLt⟩
  exact
    fixed_card_arithmetic f' hfFive hfMod hfDvd

theorem five_point_stabilizer_card_ne_twenty_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 27 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  intro hHcard
  have hFcard :
      Nat.card (MulAction.fixedPoints H X) = 6 := by
    exact
      five_point_stabilizer_fixed_points_card_eq_six_of_card_eq_twenty_seven
        X P hcard h5 s hs hHcard
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have heRange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  let e' : Fin 5 ↪ X := {
    toFun := fun i => e (rotateFive i)
    inj' := e.injective.comp rotateFive.injective }
  obtain ⟨q, hq⟩ :=
    h5 e e' e.injective e'.injective
  have hqPoint (i : Fin 5) :
      q • e i = e (rotateFive i) := by
    exact hq i
  have hqIter (n : ℕ) :
      ∀ i : Fin 5,
        (q ^ n) • e i =
          e ((rotateFive ^ n) i) := by
    induction n with
    | zero =>
        intro i
        simp
    | succ n ih =>
        intro i
        rw [pow_succ, mul_smul, hqPoint, ih]
        rfl
  have hqSet : q • s = s := by
    rw [← heRange,
      FiveTransitive.Degree19.smul_range_embedding]
    apply Set.Subset.antisymm
    · rintro x ⟨i, hi⟩
      rw [← hi]
      exact ⟨rotateFive i, (hqPoint i).symm⟩
    · rintro x ⟨i, rfl⟩
      obtain ⟨j, hj⟩ :=
        rotateFive.surjective i
      refine ⟨j, ?_⟩
      change q • e j = e i
      rw [hqPoint, hj]
  have hqNormalizer :
      q ∈ Subgroup.normalizer H := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconj :=
      SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj
        s q
    rw [hqSet] at hconj
    exact hconj.symm
  have hqFiveMem : q ^ 5 ∈ H := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rw [← heRange] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hqIter, rotateFive_pow_five]
    rfl
  let qFive : H := ⟨q ^ 5, hqFiveMem⟩
  have hqFivePow :
      (q ^ 5) ^ 27 = 1 := by
    have hpow := pow_card_eq_one' (x := qFive)
    rw [hHcard] at hpow
    exact congrArg Subtype.val hpow
  let r : P := q ^ 27
  have hrPow : r ^ 5 = 1 := by
    change (q ^ 27) ^ 5 = 1
    calc
      (q ^ 27) ^ 5 = q ^ (27 * 5) :=
        (pow_mul q 27 5).symm
      _ = q ^ (5 * 27) := by norm_num
      _ = (q ^ 5) ^ 27 := pow_mul q 5 27
      _ = 1 := hqFivePow
  have hrNe : r ≠ 1 := by
    intro hrOne
    have hmove := hqIter 27 (0 : Fin 5)
    change r • e (0 : Fin 5) =
      e ((rotateFive ^ 27) (0 : Fin 5)) at hmove
    rw [hrOne, one_smul] at hmove
    exact
      rotateFive_pow_twenty_seven_fixedPointFree 0
        (e.injective hmove.symm)
  have hrOrder : orderOf r = 5 :=
    orderOf_eq_prime hrPow hrNe
  have hrNormalizer :
      r ∈ Subgroup.normalizer H := by
    change q ^ 27 ∈ Subgroup.normalizer H
    exact pow_mem hqNormalizer 27
  have hrCentral :
      ∀ h : H, Commute r (h : P) :=
    order_five_normalizer_centralizes_card_twenty_seven
      P H hHcard r hrOrder hrNormalizer
  have hrPoint (i : Fin 5) :
      r • e i = e ((rotateFive ^ 27) i) :=
    hqIter 27 i
  have hrSet : r • s = s := by
    rw [← heRange,
      FiveTransitive.Degree19.smul_range_embedding]
    apply Set.Subset.antisymm
    · rintro x ⟨i, hi⟩
      rw [← hi]
      exact
        ⟨(rotateFive ^ 27) i, (hrPoint i).symm⟩
    · rintro x ⟨i, rfl⟩
      obtain ⟨j, hj⟩ :=
        (rotateFive ^ 27).surjective i
      refine ⟨j, ?_⟩
      change r • e j = e i
      rw [hrPoint, hj]
  let F : Set X := MulAction.fixedPoints H X
  have hsFixed : s ⊆ F := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro h
    exact
      (mem_fixingSubgroup_iff P).mp h.prop x hx
  have hFncard : F.ncard = 6 := by
    calc
      F.ncard = Nat.card F :=
        (Nat.card_coe_set_eq F).symm
      _ = 6 := hFcard
  have hDcard : (F \ s).ncard = 1 := by
    rw [Set.ncard_sdiff' hsFixed, hFncard, hs]
  obtain ⟨y, hyD⟩ :=
    Set.ncard_eq_one.mp hDcard
  have hyDmem : y ∈ F \ s := by
    rw [hyD]
    simp
  have hrPreserveF :
      ∀ x ∈ F, r • x ∈ F := by
    intro x hx
    rw [MulAction.mem_fixedPoints] at hx ⊢
    intro h
    calc
      (h : P) • (r • x) =
          ((h : P) * r) • x :=
        (mul_smul (h : P) r x).symm
      _ = (r * (h : P)) • x :=
        congrArg (fun z : P => z • x)
          (hrCentral h).symm
      _ = r • ((h : P) • x) :=
        mul_smul r (h : P) x
      _ = r • x :=
        congrArg (fun z : X => r • z) (hx h)
  have hryNotS : r • y ∉ s := by
    intro hryS
    have hryTranslate : r • y ∈ r • s := by
      rwa [hrSet]
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hryTranslate
    have hyS : y ∈ s := by
      simpa using hryTranslate
    exact hyDmem.2 hyS
  have hryDmem : r • y ∈ F \ s :=
    ⟨hrPreserveF y hyDmem.1, hryNotS⟩
  have hry : r • y = y := by
    rw [hyD] at hryDmem
    simpa only [Set.mem_singleton_iff] using hryDmem
  let g : Equiv.Perm X := r
  have hrCentralPerm (h : H) :
      Commute (((h : P) : Equiv.Perm X)) g := by
    rw [commute_iff_eq]
    exact
      congrArg Subtype.val (hrCentral h).symm
  let S : Set X := (g.support : Set X)
  let supportSmul : SMul H S := {
    smul := fun h x =>
      ⟨(h : P) • x.1, by
        exact
          (Equiv.Perm.mem_support_iff_of_commute
            (hrCentralPerm h) x.1).mpr x.2⟩ }
  letI : SMul H S := supportSmul
  letI : MulAction H S :=
    Subtype.coe_injective.mulAction
      Subtype.val (fun _ _ => rfl)
  let fixedSupportEquiv :
      MulAction.fixedPoints H S ≃ s := {
    toFun := fun z =>
      ⟨z.1.1, by
        by_contra hzs
        have hzF : z.1.1 ∈ F := by
          rw [MulAction.mem_fixedPoints]
          intro h
          have hz :=
            (MulAction.mem_fixedPoints.mp z.2) h
          exact congrArg Subtype.val hz
        have hzD : z.1.1 ∈ F \ s :=
          ⟨hzF, hzs⟩
        have hzy : z.1.1 = y := by
          rw [hyD] at hzD
          simpa only [Set.mem_singleton_iff] using hzD
        have hgy : g y = y := by
          simpa [g, Subgroup.smul_def,
            Equiv.Perm.smul_def] using hry
        have hzSupport : z.1.1 ∈ g.support := by
          change z.1.1 ∈ (g.support : Set X)
          exact z.1.2
        exact
          (Equiv.Perm.mem_support.mp hzSupport)
            (by simpa [hzy] using hgy)⟩
    invFun := fun x =>
      ⟨⟨x.1, by
        change x.1 ∈ g.support
        rw [Equiv.Perm.mem_support]
        intro hgx
        have hxRange : x.1 ∈ Set.range e := by
          rw [heRange]
          exact x.prop
        obtain ⟨i, hi⟩ := hxRange
        have hmove := hrPoint i
        have heq :
            e ((rotateFive ^ 27) i) = e i := by
          rw [← hmove]
          change g (e i) = e i
          rw [hi]
          exact hgx
        exact
          rotateFive_pow_twenty_seven_fixedPointFree i
            (e.injective heq)⟩,
        by
          rw [MulAction.mem_fixedPoints]
          intro h
          apply Subtype.ext
          exact
            (mem_fixingSubgroup_iff P).mp h.prop
              x.1 x.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro x
      apply Subtype.ext
      rfl }
  have hfixedSupportCard :
      Nat.card (MulAction.fixedPoints H S) = 5 := by
    calc
      Nat.card (MulAction.fixedPoints H S) =
          Nat.card s :=
        Nat.card_congr fixedSupportEquiv
      _ = 5 := by
        rw [Nat.card_eq_fintype_card, hsCard]
  have hHp : IsPGroup 3 H := by
    apply IsPGroup.of_card (n := 3)
    rw [hHcard]
    norm_num
  have hScard :
      Nat.card S = g.support.card := by
    rw [Nat.card_coe_set_eq]
    simp [S]
  have hsupportMod :
      g.support.card % 3 = 2 := by
    have hmod :=
      hHp.card_modEq_card_fixedPoints S
    change
      Nat.card S % 3 =
        Nat.card (MulAction.fixedPoints H S) % 3 at hmod
    rw [hScard, hfixedSupportCard] at hmod
    norm_num at hmod ⊢
    exact hmod
  have hgOrder : orderOf g = 5 := by
    calc
      orderOf g = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 5 := hrOrder
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder] at hsum
  have hsupportLe : g.support.card ≤ 24 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 24 := hcard
  have hsupportCases :
      g.support.card = 5 ∨
        g.support.card = 10 ∨
        g.support.card = 15 ∨
        g.support.card = 20 := by
    omega
  have hsupport : g.support.card = 20 := by
    rcases hsupportCases with hFive | hTen | hFifteen | hTwenty
    · exact False.elim
        (hnotAlt
          (alternatingGroup_le_of_nontrivial_support_le_seven
            X P hcard h5 r.prop (by
              intro hgOne
              apply hrNe
              apply Subtype.ext
              exact hgOne) (by
              change g.support.card ≤ 7
              omega)))
    · rw [hTen] at hsupportMod
      norm_num at hsupportMod
    · rw [hFifteen] at hsupportMod
      norm_num at hsupportMod
    · exact hTwenty
  have hkFour : k + 1 = 4 := by
    omega
  have hcycleType :
      g.cycleType = {5, 5, 5, 5} := by
    rw [hk, hgOrder, hkFour]
    norm_num
  have hcentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({g} : Set (Equiv.Perm X))) =
        360000 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hcycleType, hcard]
    norm_num
  let inclusion :
      H →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := {
    toFun := fun h =>
      ⟨((h : P) : Equiv.Perm X), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hrCentralPerm h⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    have habPerm :=
      congrArg
        (fun z :
          Subgroup.centralizer
            ({g} : Set (Equiv.Perm X)) =>
          (z : Equiv.Perm X))
        hab
    change
      ((a : P) : Equiv.Perm X) =
        ((b : P) : Equiv.Perm X) at habPerm
    apply Subtype.ext
    apply Subtype.ext
    exact habPerm
  have hdiv :
      Nat.card H ∣
        Nat.card
          (Subgroup.centralizer
            ({g} : Set (Equiv.Perm X))) :=
    Subgroup.card_dvd_of_injective
      inclusion hinclusion
  rw [hHcard, hcentralizerCard] at hdiv
  norm_num at hdiv

end FiveTransitive.Degree24

end CFSG
