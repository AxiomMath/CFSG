module

public import CFSG.Permutation.FiveTransitive.Degree24FixedSetNormalizer
public import CFSG.Permutation.FiveTransitive.Degree24Order27

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private theorem rotateFive_pow_four_fixedPointFree :
    ∀ i : Fin 5, (rotateFive ^ 4) i ≠ i := by
  decide

private theorem five_group_action_on_card_four_is_trivial
    (T A : Type) [Group T] [Group A]
    [Fintype T] [Fintype A]
    [MulDistribMulAction T A]
    (hT : IsPGroup 5 T)
    (hAcard : Nat.card A = 4) :
    ∀ t : T, ∀ a : A, t • a = a := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let C : Subgroup A :=
    FiveTransitive.Degree19.fixedPointsSubgroup T A
  have hCset :
      (C : Set A) = MulAction.fixedPoints T A :=
    rfl
  let eC :
      C ≃ MulAction.fixedPoints T A :=
    Set.equivOfEq hCset
  have hmodRaw :
      Nat.card A % 5 = Nat.card C % 5 := by
    have h :=
      hT.card_modEq_card_fixedPoints A
    change
      Nat.card A % 5 =
        Nat.card (MulAction.fixedPoints T A) % 5 at h
    calc
      Nat.card A % 5 =
          Nat.card (MulAction.fixedPoints T A) % 5 :=
        h
      _ = Nat.card C % 5 :=
        congrArg (fun n => n % 5)
          (Nat.card_congr eC).symm
  have hmod : Nat.card C % 5 = 4 := by
    rw [hAcard] at hmodRaw
    norm_num at hmodRaw
    rw [Nat.card_eq_fintype_card]
    exact hmodRaw.symm
  have hdiv : Nat.card C ∣ 4 := by
    rw [← hAcard]
    exact Subgroup.card_subgroup_dvd_card C
  have hCle : Nat.card C ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hCcard : Nat.card C = 4 := by
    omega
  have hCtop : C = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hCcard, hAcard]
  intro t a
  have ha : a ∈ C := by
    rw [hCtop]
    exact Subgroup.mem_top a
  exact ha t

private theorem order_five_normalizer_centralizes_card_four
    (G : Type) [Group G] [Fintype G]
    (H : Subgroup G)
    (hHcard : Nat.card H = 4)
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
    five_group_action_on_card_four_is_trivial
      T H hTp hHcard
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

theorem five_point_stabilizer_card_ne_four
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 4 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  intro hHcard
  let F : Set X := MulAction.fixedPoints H X
  let f := Nat.card F
  have hfCases : f = 5 ∨ f = 6 ∨ f = 7 := by
    simpa only [H, F, f] using
      five_point_stabilizer_fixed_points_card_eq_five_six_or_seven
        X P hcard h5 s hs (by
          rw [hHcard]
          norm_num)
  have hHp : IsPGroup 2 H := by
    apply IsPGroup.of_card (n := 2)
    rw [hHcard]
    norm_num
  have hfModRaw :=
    hHp.card_modEq_card_fixedPoints X
  have hfMod : f % 2 = 0 := by
    change Nat.card X % 2 = f % 2 at hfModRaw
    rw [Nat.card_eq_fintype_card, hcard] at hfModRaw
    norm_num at hfModRaw
    exact hfModRaw.symm
  have hFcard : Nat.card F = 6 := by
    rcases hfCases with hfFive | hfSix | hfSeven
    · rw [hfFive] at hfMod
      norm_num at hfMod
    · exact hfSix
    · rw [hfSeven] at hfMod
      norm_num at hfMod
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
      q • e i = e (rotateFive i) :=
    hq i
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
      Degree24.smul_range_fiveEmbedding]
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
      (q ^ 5) ^ 4 = 1 := by
    have hpow := pow_card_eq_one' (x := qFive)
    rw [hHcard] at hpow
    exact congrArg Subtype.val hpow
  let r : P := q ^ 4
  have hrPow : r ^ 5 = 1 := by
    change (q ^ 4) ^ 5 = 1
    calc
      (q ^ 4) ^ 5 = q ^ (4 * 5) :=
        (pow_mul q 4 5).symm
      _ = q ^ (5 * 4) := by norm_num
      _ = (q ^ 5) ^ 4 := pow_mul q 5 4
      _ = 1 := hqFivePow
  have hrNe : r ≠ 1 := by
    intro hrOne
    have hmove := hqIter 4 (0 : Fin 5)
    change r • e (0 : Fin 5) =
      e ((rotateFive ^ 4) (0 : Fin 5)) at hmove
    rw [hrOne, one_smul] at hmove
    exact
      rotateFive_pow_four_fixedPointFree 0
        (e.injective hmove.symm)
  have hrOrder : orderOf r = 5 :=
    orderOf_eq_prime hrPow hrNe
  have hrNormalizer :
      r ∈ Subgroup.normalizer H := by
    change q ^ 4 ∈ Subgroup.normalizer H
    exact pow_mem hqNormalizer 4
  have hrCentral :
      ∀ h : H, Commute r (h : P) :=
    order_five_normalizer_centralizes_card_four
      P H hHcard r hrOrder hrNormalizer
  have hrPoint (i : Fin 5) :
      r • e i = e ((rotateFive ^ 4) i) :=
    hqIter 4 i
  have hrSet : r • s = s := by
    rw [← heRange,
      Degree24.smul_range_fiveEmbedding]
    apply Set.Subset.antisymm
    · rintro x ⟨i, hi⟩
      rw [← hi]
      exact
        ⟨(rotateFive ^ 4) i, (hrPoint i).symm⟩
    · rintro x ⟨i, rfl⟩
      obtain ⟨j, hj⟩ :=
        (rotateFive ^ 4).surjective i
      refine ⟨j, ?_⟩
      change r • e j = e i
      rw [hrPoint, hj]
  let g : Equiv.Perm X := r
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
  have hsupportNotTenOrFifteen :
      g.support.card ≠ 10 ∧
        g.support.card ≠ 15 := by
    constructor
    all_goals
      intro hsupport
      let Z : Set X :=
        MulAction.fixedBy X r
      have hZcard : Nat.card Z = 24 - g.support.card := by
        rw [Nat.card_eq_fintype_card]
        change
          Fintype.card (MulAction.fixedBy X r) =
            24 - g.support.card
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard]
      have hZfive : 5 ≤ Nat.card Z := by
        rw [hZcard, hsupport]
        norm_num
      have heZ : Nonempty (Fin 5 ↪ Z) := by
        apply Fintype.card_pos_iff.mp
        rw [Fintype.card_embedding_eq,
          Fintype.card_fin,
          ← Nat.card_eq_fintype_card,
          Nat.descFactorial_pos]
        exact hZfive
      let ez : Fin 5 ↪ Z := Classical.choice heZ
      let ezX : Fin 5 ↪ X := {
        toFun := fun i => (ez i).1
        inj' := fun i j hij =>
          ez.injective (Subtype.ext hij) }
      have hezRange :
          (Set.range ezX).ncard = 5 := by
        rw [Set.ncard_range_of_injective ezX.injective,
          Nat.card_eq_fintype_card, Fintype.card_fin]
      let J : Subgroup P :=
        fixingSubgroup P (Set.range ezX)
      have hJcard : Nat.card J = 4 := by
        calc
          Nat.card J =
              Nat.card (fixingSubgroup P s) :=
            five_point_stabilizers_have_equal_card
              X P h5 (Set.range ezX) s
                hezRange hs
          _ = 4 := hHcard
      have hrJ : r ∈ J := by
        rw [mem_fixingSubgroup_iff]
        rintro _ ⟨i, rfl⟩
        exact (ez i).2
      let rJ : J := ⟨r, hrJ⟩
      have hrJorder : orderOf rJ = 5 := by
        calc
          orderOf rJ = orderOf r :=
            (Subgroup.orderOf_coe rJ).symm
          _ = 5 := hrOrder
      have horderDvd :
          orderOf rJ ∣ Fintype.card J :=
        orderOf_dvd_card
      rw [hrJorder, ← Nat.card_eq_fintype_card,
        hJcard] at horderDvd
      norm_num at horderDvd
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
    · exact (hsupportNotTenOrFifteen.1 hTen).elim
    · exact (hsupportNotTenOrFifteen.2 hFifteen).elim
    · exact hTwenty
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
        congrArg (fun z : X => r • z)
          (MulAction.mem_fixedPoints.mp hx h)
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
            e ((rotateFive ^ 4) i) = e i := by
          rw [← hmove]
          change g (e i) = e i
          rw [hi]
          exact hgx
        exact
          rotateFive_pow_four_fixedPointFree i
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
  have hScard :
      Nat.card S = g.support.card := by
    rw [Nat.card_coe_set_eq]
    simp [S]
  have hmod :=
    hHp.card_modEq_card_fixedPoints S
  change
    Nat.card S % 2 =
      Nat.card (MulAction.fixedPoints H S) % 2 at hmod
  rw [hScard, hfixedSupportCard, hsupport] at hmod
  norm_num at hmod

end FiveTransitive.Degree24

end CFSG
