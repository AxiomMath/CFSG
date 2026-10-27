module

public import CFSG.Permutation.FiveTransitive.Degree25ArithmeticFive
public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeSylow
public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeCentralizer
public import CFSG.Permutation.FiveTransitive.Degree20ExcludeFiveExponentThree

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup
open FiveTransitive.Degree24

private theorem alternatingGroup_le_of_sylow_five_card_one_hundred_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 125) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  let R : Subgroup P :=
    Degree24.sylowImage X P s S
  let eSR : S ≃* R :=
    (S : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  obtain ⟨A, eAR, d, hAcard, hsupport,
      hequivariant⟩ :=
    exists_fourFive_model_of_sylowImage_card_one_hundred_twenty_five
      X P hcard s hs S hScard
  have hnoWeightOne :
      ¬∃ a : A,
        fiveWeight
          ((a : A) : Degree20.FourFiveBase) = 1 := by
    rintro ⟨a, ha⟩
    let g : Equiv.Perm X :=
      (((eAR a : R) : P) : Equiv.Perm X)
    have hgsupport : g.support.card = 5 := by
      rw [show g.support.card =
          5 * fiveWeight
            ((a : A) : Degree20.FourFiveBase) by
        exact hsupport a,
        ha]
    have hgNe : g ≠ 1 := by
      intro hg
      rw [hg, Equiv.Perm.support_one] at hgsupport
      norm_num at hgsupport
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5
          ((eAR a : R) : P).prop hgNe (by
            change g.support.card ≤ 7
            omega))
  obtain ⟨a₀, ha₀Weight⟩ :=
    fourFive_subgroup_exists_weight_four
      A hAcard hnoWeightOne
  let r : R := eAR a₀
  let g : Equiv.Perm X := ((r : R) : P)
  have hgSupport : g.support.card = 20 := by
    rw [show g.support.card =
        5 * fiveWeight
          ((a₀ : A) : Degree20.FourFiveBase) by
      exact hsupport a₀,
      ha₀Weight]
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  have hsFixed : s ⊆ F := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨u, huS, hu⟩ :=
      Subgroup.mem_map.mp z.prop
    have hfix :=
      (mem_fixingSubgroup_iff P).mp u.prop x hx
    change ((z : N) : P) • x = x
    rw [show ((z : N) : P) = (u : H) by
      exact hu.symm]
    exact hfix
  have hFleFixed :
      (F : Set X) ⊆ Function.fixedPoints g := by
    intro x hx
    rw [Function.mem_fixedPoints_iff]
    have hrNormal : (r : P) ∈ N :=
      R.le_normalizer r.prop
    let rN : N := ⟨(r : P), hrNormal⟩
    let rSN : SN := ⟨rN, r.prop⟩
    exact (MulAction.mem_fixedPoints.mp hx) rSN
  have hfixedCard :
      (Function.fixedPoints g).ncard = 5 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints,
      Equiv.Perm.sum_cycleType, hcard, hgSupport]
  have hfixedSet :
      Function.fixedPoints g = s := by
    have hsSubset :
        s ⊆ Function.fixedPoints g :=
      hsFixed.trans hFleFixed
    exact
      (Set.eq_of_subset_of_ncard_le
        hsSubset (by rw [hfixedCard, hs])
        (Function.fixedPoints g).toFinite).symm
  have hfixed :
      F = Function.fixedPoints g := by
    apply Set.Subset.antisymm hFleFixed
    rw [hfixedSet]
    exact hsFixed
  have hFcard : Fintype.card F = 5 := by
    rw [← Nat.card_eq_fintype_card]
    rw [Nat.card_coe_set_eq, hfixed, hfixedCard]
  let J : Subgroup (Equiv.Perm F) :=
    ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      Degree24.sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    exact ⟨⟨ρ q, ⟨q, rfl⟩⟩, hq⟩
  have hJmt :
      MulAction.IsMultiplyPretransitive J F 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      hJ5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  have hJfour :
      MulAction.IsMultiplyPretransitive J F 4 := by
    letI : MulAction.IsMultiplyPretransitive J F 5 := hJmt
    apply MulAction.isMultiplyPretransitive_of_le
      (G := J) (α := F) (m := 4) (n := 5)
    · norm_num
    · simp [Nat.card_eq_fintype_card, hFcard]
  have hJtop : J = ⊤ := by
    apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
    simp only [Nat.card_eq_fintype_card, hFcard]
    exact hJfour
  have hAlt :
      alternatingGroup F ≤ ρ.range := by
    change alternatingGroup F ≤ J
    rw [hJtop]
    exact le_top
  have hAltCard :
      Nat.card (alternatingGroup F) = 60 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        rw [hFcard]
        norm_num)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFcard]
    norm_num
  have hκNotFive : ¬5 ∣ Nat.card κ.range := by
    intro hfive
    obtain ⟨b, hbOrder⟩ :=
      exists_prime_orderOf_dvd_card'
        (G := κ.range) 5 hfive
    let autR : MulAut R := b.1
    let autA : MulAut A :=
      MulAut.congr eAR.symm autR
    have hautOrder : orderOf autA = 5 := by
      calc
        orderOf autA = orderOf autR :=
          (MulAut.congr eAR.symm).orderOf_eq autR
        _ = orderOf b := Subgroup.orderOf_coe b
        _ = 5 := hbOrder
    have hautWeight :
        ∀ a : A,
          fiveWeight
              (((autA a : A) : A) :
                Degree20.FourFiveBase) =
            fiveWeight
              ((a : A) :
                Degree20.FourFiveBase) := by
      intro a
      have heARaut :
          eAR (autA a) = autR (eAR a) := by
        change
          eAR (eAR.symm (autR (eAR a))) =
            autR (eAR a)
        exact eAR.apply_symm_apply _
      obtain ⟨n, hn⟩ := b.prop
      have hconjR :
          κ n (eAR a) = autR (eAR a) :=
        congrArg (fun f : MulAut R => f (eAR a)) hn
      have hconjP :
          ((autR (eAR a) : R) : P) =
            (n : P) * ((eAR a : R) : P) *
              (n : P)⁻¹ :=
        congrArg Subtype.val hconjR.symm
      have hsupportEq :
          ((((eAR (autA a) : R) : P) :
              Equiv.Perm X).support.card) =
            ((((eAR a : R) : P) :
              Equiv.Perm X).support.card) := by
        rw [heARaut, hconjP]
        exact Equiv.Perm.card_support_conj
      have hleft := hsupport (autA a)
      have hright := hsupport a
      omega
    exact
      fourFive_subgroup_weight_preserving_mulAut_order_ne_five
        A hAcard hnoWeightOne autA hautWeight hautOrder
  have hκNotDvd :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card κ.range := by
    rw [hAltCard]
    intro hdvd
    exact hκNotFive ((by norm_num : 5 ∣ 60).trans hdvd)
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, hFcard])
  let C : Subgroup N := κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  have hAltC :
      alternatingGroup F ≤ ρC.range := by
    intro q hq
    obtain ⟨n, hnFixed, hnCentral⟩ :=
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
        N (Equiv.Perm F) (MulAut R)
          ρ κ (alternatingGroup F) hAlt
            hκNotDvd q hq
    exact ⟨⟨n, hnCentral⟩, hnFixed⟩
  have hFset : (F : Set X) = s := by
    rw [hfixed, hfixedSet]
  have hNpreservesF (n : N) (x : X) :
      ((((n : N) : P) : Equiv.Perm X) x ∈ F) ↔
        x ∈ F := by
    constructor
    · intro hx
      have hinverse :
          ((((n⁻¹ : N) : P) : Equiv.Perm X)
              ((((n : N) : P) : Equiv.Perm X) x)) ∈ F :=
        ((n⁻¹ : N) •
          (⟨(((n : N) : P) : Equiv.Perm X) x,
            hx⟩ : F)).prop
      simpa using hinverse
    · intro hx
      exact
        (n • (⟨x, hx⟩ : F)).prop
  have hNpreservesY (n : N) (x : X) :
      ((((n : N) : P) : Equiv.Perm X) x ∈ Y) ↔
        x ∈ Y := by
    change
      ((((n : N) : P) : Equiv.Perm X) x ∉ s) ↔
        x ∉ s
    rw [← hFset]
    exact not_congr (hNpreservesF n x)
  let restrictionN : N →* Equiv.Perm Y := {
    toFun := fun n =>
      (((n : N) : P) : Equiv.Perm X).subtypePerm
        (hNpreservesY n)
    map_one' := by
      ext y
      rfl
    map_mul' := by
      intro n m
      ext y
      rfl }
  let modelMap : A →* Equiv.Perm Y :=
    (MulAction.toPermHom H Y).comp
      ((S : Subgroup H).subtype.comp
        (eSR.symm.toMonoidHom.comp eAR.toMonoidHom))
  have hmodelVal (a : A) (y : Y) :
      (modelMap a y).1 =
        ((((eAR a : R) : P) : Equiv.Perm X) y.1) := by
    have hcoe :
        ((((eSR.symm (eAR a) : S) : H) : P)) =
          ((eAR a : R) : P) := by
      calc
        (((eSR.symm (eAR a) : S) : H) : P) =
            ((eSR (eSR.symm (eAR a)) : R) : P) := by
          symm
          exact
            Subgroup.coe_equivMapOfInjective_apply
              (S : Subgroup H) H.subtype
                H.subtype_injective
                  (eSR.symm (eAR a))
        _ = ((eAR a : R) : P) := by
          rw [eSR.apply_symm_apply]
    change
      ((((eSR.symm (eAR a) : S) : H) : P) :
          Equiv.Perm X) y.1 =
        ((((eAR a : R) : P) : Equiv.Perm X) y.1)
    rw [hcoe]
  have hmodelInjective :
      Function.Injective modelMap := by
    intro a b hab
    apply A.subtype_injective
    apply
      (MulAction.toPerm_injective
        (α := Degree20.FourFiveBase)
        (β := Degree20.TwentyFivePoints))
    apply Equiv.ext
    intro z
    obtain ⟨y, rfl⟩ := d.surjective z
    change
      (MulAction.toPermHom
          Degree20.FourFiveBase
          Degree20.TwentyFivePoints)
            ((a : A) : Degree20.FourFiveBase) (d y) =
        (MulAction.toPermHom
          Degree20.FourFiveBase
          Degree20.TwentyFivePoints)
            ((b : A) : Degree20.FourFiveBase) (d y)
    rw [← hequivariant a y, ← hequivariant b y]
    exact congrArg d
      (congrFun (congrArg DFunLike.coe hab) y)
  let RY : Subgroup (Equiv.Perm Y) :=
    modelMap.range
  let eAY : A ≃* RY :=
    MonoidHom.ofInjective hmodelInjective
  have heAY (a : A) (y : Y) :
      d (((eAY a : RY) : Equiv.Perm Y) y) =
        (MulAction.toPermHom
          Degree20.FourFiveBase
          Degree20.TwentyFivePoints)
            ((a : A) : Degree20.FourFiveBase) (d y) := by
    rw [MonoidHom.ofInjective_apply]
    exact hequivariant a y
  have hRYcentralizer :
      Nat.card
          (Subgroup.centralizer
            (RY : Set (Equiv.Perm Y))) ∣
        625 :=
    subgroup_centralizer_card_dvd_six_hundred_twenty_five_of_equivariant
      Y A hAcard hnoWeightOne RY eAY d heAY
  let auxMap : C →* Equiv.Perm Y :=
    restrictionN.comp C.subtype
  have hAuxVal (c : C) (y : Y) :
      (auxMap c y).1 =
        ((((c.1 : N) : P) : Equiv.Perm X) y.1) := by
    rfl
  have hAuxCentralizer :
      auxMap.range ≤
        Subgroup.centralizer
          (RY : Set (Equiv.Perm Y)) := by
    intro z hz
    obtain ⟨c, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨a, rfl⟩ := hp
    have hcCentral :
        (c.1 : N) ∈
          (Subgroup.centralizer (R : Set P)).subgroupOf N := by
      rw [← R.normalizerMonoidHom_ker]
      exact c.prop
    have hcCommute :
        Commute ((c.1 : N) : P)
          ((eAR a : R) : P) :=
      (hcCentral ((eAR a : R) : P)
        (eAR a).prop).symm
    apply Commute.symm
    apply Equiv.ext
    intro y
    have happ :=
      congrFun
        (congrArg DFunLike.coe
          (congrArg Subtype.val hcCommute)) (y : X)
    apply Subtype.ext
    change
      (auxMap c (modelMap a y)).1 =
        (modelMap a (auxMap c y)).1
    rw [hAuxVal c (modelMap a y),
      hmodelVal a y, hmodelVal a (auxMap c y),
      hAuxVal c y]
    exact happ
  have hAuxRangeDvd :
      Nat.card auxMap.range ∣ 625 :=
    (Subgroup.card_dvd_of_le
      hAuxCentralizer).trans hRYcentralizer
  have hAuxNotDvd :
      ¬Nat.card (alternatingGroup F) ∣
        Nat.card auxMap.range := by
    rw [hAltCard]
    intro hdvd
    have : 60 ∣ 625 :=
      hdvd.trans hAuxRangeDvd
    norm_num at this
  have hSupportLift :
      ∀ q : Equiv.Perm F,
        q ∈ alternatingGroup F →
        ∃ c : N, ρ c = q ∧
          ∀ x ∈ g.support,
            (((c : N) : P) : Equiv.Perm X) x = x := by
    intro q hq
    obtain ⟨c, hcFixed, hcAux⟩ :=
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
        C (Equiv.Perm F) (Equiv.Perm Y)
          ρC auxMap (alternatingGroup F)
            hAltC hAuxNotDvd q hq
    refine ⟨(c : N), ?_, ?_⟩
    · change ρ ((c : C) : N) = q at hcFixed
      exact hcFixed
    · intro x hx
      have hxY : x ∈ Y := by
        change x ∉ s
        intro hxs
        have hxFixed :
            x ∈ Function.fixedPoints g := by
          rw [hfixedSet]
          exact hxs
        exact
          Equiv.Perm.mem_support.mp hx
            (Function.mem_fixedPoints_iff.mp hxFixed)
      let y : Y := ⟨x, hxY⟩
      have happ :=
        congrFun
          (congrArg DFunLike.coe hcAux) y
      calc
        (((c : N) : P) : Equiv.Perm X) x =
            (auxMap c y).1 := by
          symm
          exact hAuxVal c y
        _ = ((1 : Equiv.Perm Y) y).1 :=
          congrArg Subtype.val happ
        _ = x := rfl
  apply
    NormalizerGoursat.alternatingGroup_le_of_fixed_action_of_support_lift
      X P (by omega) h5 R r hfixed
        (by rw [hFcard])
  simpa only [N, SN, F, ρ, g] using hSupportLift

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentyFive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i) :
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
  have hHcases :
      Nat.card H = 12000 ∨
        Nat.card H = 1944000 ∨
        Nat.card H = 288000 ∨
        Nat.card H = 46656000 ∨
        Nat.card H = 1024000 ∨
        Nat.card H = 165888000 := by
    simpa only [H] using
      five_point_stabilizer_card_cases_five_cubed
        X P hcard h5 hnotAlt s hs
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 H := Sylow.nonempty.some
  have hScard : Nat.card S = 125 := by
    rw [S.card_eq_multiplicity]
    rcases hHcases with
      hH | hH | hH | hH | hH | hH
    · rw [hH, show 12000 =
          5 * (5 * (5 * 96)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          96 (by norm_num) (by norm_num)]
      norm_num
    · rw [hH, show 1944000 =
          5 * (5 * (5 * 15552)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          15552 (by norm_num) (by norm_num)]
      norm_num
    · rw [hH, show 288000 =
          5 * (5 * (5 * 2304)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          2304 (by norm_num) (by norm_num)]
      norm_num
    · rw [hH, show 46656000 =
          5 * (5 * (5 * 373248)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          373248 (by norm_num) (by norm_num)]
      norm_num
    · rw [hH, show 1024000 =
          5 * (5 * (5 * 8192)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          8192 (by norm_num) (by norm_num)]
      norm_num
    · rw [hH, show 165888000 =
          5 * (5 * (5 * 1327104)) by norm_num,
        Degree20.factorization_five_cube_mul_of_not_dvd
          1327104 (by norm_num) (by norm_num)]
      norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_five_card_one_hundred_twenty_five
      X P hcard h5 hnotAlt s hs S hScard)

theorem classification_of_five_transitive_of_card_eq_twentyFive
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 25)
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
    alternatingGroup_le_of_five_transitive_of_card_eq_twentyFive
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree25

end CFSG
