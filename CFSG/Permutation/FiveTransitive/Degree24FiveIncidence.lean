module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCode
public import CFSG.Permutation.FiveTransitive.Degree20ExcludeFiveExponentThree
public import CFSG.Permutation.FiveTransitive.Degree24ThreePointPrimitive

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem sylow_five_card_one_hundred_twenty_five_data
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (t : Set X) (ht : t.ncard = 3)
    (S : Sylow 5 (fixingSubgroup P t))
    (hScard : Nat.card S = 125) :
    let inclusion : S →* Equiv.Perm X :=
      P.subtype.comp
        ((fixingSubgroup P t).subtype.comp
          (S : Subgroup (fixingSubgroup P t)).subtype)
    Nat.card {u : S // (inclusion u).support.card = 10} = 24 ∧
      Nat.card
        (MulAction.fixedPoints S
          (SubMulAction.ofFixingSubgroup P t)) = 1 := by
  classical
  dsimp
  let L : Subgroup P := fixingSubgroup P t
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp
      (L.subtype.comp (S : Subgroup L).subtype)
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) :=
    inclusion.range
  let eSR : S ≃* R :=
    MonoidHom.ofInjective hinclusion
  have hRcard : Nat.card R = 125 := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr eSR.symm.toEquiv
      _ = 125 := hScard
  rcases
      subgroup_support_five_or_twenty_four_support_ten
        X hcard R hRcard with hone | ⟨hten, hfixedR⟩
  · obtain ⟨r, hr⟩ := hone
    obtain ⟨u, hu⟩ := r.prop
    have hmem :
        (r.1 : Equiv.Perm X) ∈ P := by
      rw [← hu]
      exact
        (((S : Subgroup L).subtype u : L) : P).prop
    have hne : (r.1 : Equiv.Perm X) ≠ 1 := by
      intro hrone
      rw [hrone, Equiv.Perm.support_one] at hr
      norm_num at hr
    exact False.elim (hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 hmem hne (by omega)))
  · refine ⟨?_, ?_⟩
    let C :=
      {u : S // (inclusion u).support.card = 10}
    let D :=
      {r : R // r.1.support.card = 10}
    let Esupport : C ≃ D := {
      toFun := fun u => ⟨eSR u.1, by
        change (inclusion u.1).support.card = 10
        exact u.prop⟩
      invFun := fun r => ⟨eSR.symm r.1, by
        rw [show inclusion (eSR.symm r.1) = r.1 by
          exact congrArg Subtype.val
            (eSR.apply_symm_apply r.1)]
        exact r.prop⟩
      left_inv := fun u => by
        apply Subtype.ext
        exact eSR.symm_apply_apply u.1
      right_inv := fun r => by
        apply Subtype.ext
        exact eSR.apply_symm_apply r.1 }
    show Nat.card C = 24
    calc
      Nat.card C = Nat.card D :=
        Nat.card_congr Esupport
      _ = 24 := hten
    have hfixedSX :
        Nat.card (MulAction.fixedPoints S X) = 4 := by
      let Efixed :
          MulAction.fixedPoints R X ≃
            MulAction.fixedPoints S X := {
        toFun := fun x => ⟨x.1, by
          have hxp := x.prop
          rw [MulAction.mem_fixedPoints] at hxp ⊢
          intro u
          have hx := hxp (eSR u)
          change (inclusion u) x.1 = x.1
          exact hx⟩
        invFun := fun x => ⟨x.1, by
          have hxp := x.prop
          rw [MulAction.mem_fixedPoints] at hxp ⊢
          intro r
          have hx := hxp (eSR.symm r)
          change (r.1 : Equiv.Perm X) x.1 = x.1
          change
            (inclusion (eSR.symm r)) x.1 = x.1 at hx
          rw [show inclusion (eSR.symm r) = r.1 by
            exact congrArg Subtype.val
              (eSR.apply_symm_apply r)] at hx
          exact hx⟩
        left_inv := fun x => by
          apply Subtype.ext
          rfl
        right_inv := fun x => by
          apply Subtype.ext
          rfl }
      calc
        Nat.card (MulAction.fixedPoints S X) =
            Nat.card (MulAction.fixedPoints R X) :=
          Nat.card_congr Efixed.symm
        _ = 4 := hfixedR
    have htFixed :
        t ⊆ MulAction.fixedPoints S X := by
      intro x hx
      rw [MulAction.mem_fixedPoints]
      intro u
      have hfix :=
        (mem_fixingSubgroup_iff P).mp
          (((S : Subgroup L).subtype u : L).prop)
          x hx
      simpa [L, Subgroup.smul_def,
        Equiv.Perm.smul_def] using hfix
    let Y := SubMulAction.ofFixingSubgroup P t
    let Eremaining :
        MulAction.fixedPoints S Y ≃
          {x : X //
            x ∈ MulAction.fixedPoints S X \ t} := {
      toFun := fun y => ⟨y.1.1, by
        refine ⟨?_, ?_⟩
        · have hyp := y.prop
          rw [MulAction.mem_fixedPoints] at hyp ⊢
          intro u
          have hy := hyp u
          exact congrArg Subtype.val hy
        · exact
            (SubMulAction.mem_ofFixingSubgroup_iff
              (M := P) (s := t)).mp y.1.prop⟩
      invFun := fun x => ⟨
        ⟨x.1,
          (SubMulAction.mem_ofFixingSubgroup_iff
            (M := P) (s := t)).mpr x.prop.2⟩, by
          have hxp := x.prop.1
          rw [MulAction.mem_fixedPoints] at hxp ⊢
          intro u
          apply Subtype.ext
          exact hxp u⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl }
    have hremaining :
        Nat.card (MulAction.fixedPoints S Y) =
          (MulAction.fixedPoints S X \ t).ncard := by
      calc
        Nat.card (MulAction.fixedPoints S Y) =
            Nat.card {x : X //
              x ∈ MulAction.fixedPoints S X \ t} :=
          Nat.card_congr Eremaining
        _ = (MulAction.fixedPoints S X \ t).ncard :=
          Nat.card_coe_set_eq
            (MulAction.fixedPoints S X \ t)
    have hfixedNcard :
        (MulAction.fixedPoints S X).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hfixedSX
    have hsplit :=
      Set.ncard_sdiff_add_ncard_of_subset htFixed
    rw [ht, hfixedNcard] at hsplit
    calc
      Nat.card
          (MulAction.fixedPoints S
            (SubMulAction.ofFixingSubgroup P t)) =
          Nat.card (MulAction.fixedPoints S Y) := by
        rfl
      _ = (MulAction.fixedPoints S X \ t).ncard :=
        hremaining
      _ = 1 := by omega

private theorem sylow_five_count_eq_twenty_one_of_card_ten_thousand_five_hundred_or_twenty_one_thousand
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (t : Set X) (ht : t.ncard = 3)
    (hLcard :
      Nat.card (fixingSubgroup P t) = 10500 ∨
        Nat.card (fixingSubgroup P t) = 21000) :
    Nat.card (Sylow 5 (fixingSubgroup P t)) = 21 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let L : Subgroup P := fixingSubgroup P t
  let Y := SubMulAction.ofFixingSubgroup P t
  let S : Sylow 5 L := Sylow.nonempty.some
  have hfactorization10500 :
      (10500 : ℕ).factorization 5 = 3 := by
    rw [show 10500 = 5 * (5 * (5 * 84)) by
      norm_num]
    exact
      Degree20.factorization_five_cube_mul_of_not_dvd
        84 (by norm_num) (by norm_num)
  have hfactorization21000 :
      (21000 : ℕ).factorization 5 = 3 := by
    rw [show 21000 = 5 * (5 * (5 * 168)) by
      norm_num]
    exact
      Degree20.factorization_five_cube_mul_of_not_dvd
        168 (by norm_num) (by norm_num)
  have hScard : Nat.card S = 125 := by
    rw [S.card_eq_multiplicity]
    rcases hLcard with hLcard | hLcard
    · rw [show Nat.card L = 10500 by
        exact hLcard, hfactorization10500]
      norm_num
    · rw [show Nat.card L = 21000 by
        exact hLcard, hfactorization21000]
      norm_num
  have hfixed :
      Nat.card (MulAction.fixedPoints S Y) = 1 := by
    exact
      (sylow_five_card_one_hundred_twenty_five_data
        X P hcard h5 hnotAlt t ht S hScard).2
  obtain ⟨hfixedSubsingleton, hfixedNonempty⟩ :=
    Nat.card_eq_one_iff_unique.mp hfixed
  let y₀ : MulAction.fixedPoints S Y :=
    Classical.choice hfixedNonempty
  let y : Y := y₀.1
  let N : Subgroup L :=
    Subgroup.normalizer (S : Set L)
  have hpreserve (n : N) :
      (n : L) • y ∈
        MulAction.fixedPoints S Y := by
    rw [MulAction.mem_fixedPoints]
    intro u
    have hconj :
        (n : L)⁻¹ * (u : S) * (n : L) ∈
          (S : Subgroup L) := by
      exact
        (Subgroup.mem_normalizer_iff''.mp n.prop
          (u : S)).mp u.prop
    let u' : S :=
      ⟨(n : L)⁻¹ * (u : S) * (n : L), hconj⟩
    have hcommute :
        (u : S) * (n : L) =
          (n : L) * (u' : S) := by
      change
        (u : L) * (n : L) =
          (n : L) *
            ((n : L)⁻¹ * (u : L) * (n : L))
      simp [mul_assoc]
    calc
      (u : S) • ((n : L) • y) =
          ((u : L) * (n : L)) • y :=
        (mul_smul (u : L) (n : L) y).symm
      _ = ((n : L) * (u' : L)) • y :=
        congrArg (fun z : L => z • y) hcommute
      _ = (n : L) • ((u' : S) • y) :=
        mul_smul _ _ _
      _ = (n : L) • y := by
        rw [y₀.prop u']
  have hNle :
      N ≤ MulAction.stabilizer L y := by
    intro n hn
    rw [MulAction.mem_stabilizer_iff]
    let n' : N := ⟨n, hn⟩
    have heq :
        (⟨n • y, hpreserve n'⟩ :
          MulAction.fixedPoints S Y) = y₀ :=
      hfixedSubsingleton.elim _ _
    exact congrArg Subtype.val heq
  have hprimitive :
      MulAction.IsPreprimitive L Y := by
    exact three_point_stabilizer_is_preprimitive
      X P hcard h5 t ht
  letI : MulAction.IsPreprimitive L Y :=
    hprimitive
  have hYcard : Nat.card Y = 21 :=
    three_point_remaining_card X P hcard t ht
  have hstabilizerIndex :
      (MulAction.stabilizer L y).index = 21 := by
    rw [MulAction.index_stabilizer_of_transitive,
      hYcard]
  letI :
      N.IsFiniteRelIndex
        (MulAction.stabilizer L y) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hindexProduct :
      N.relIndex (MulAction.stabilizer L y) *
          (MulAction.stabilizer L y).index =
        N.index :=
    Subgroup.relIndex_mul_index hNle
  have htwentyOneIndex : 21 ∣ N.index := by
    refine ⟨N.relIndex
      (MulAction.stabilizer L y), ?_⟩
    rw [← hindexProduct, hstabilizerIndex,
      Nat.mul_comm]
  have htwentyOneSylow :
      21 ∣ Nat.card (Sylow 5 L) := by
    rw [S.card_eq_index_normalizer]
    exact htwentyOneIndex
  have hSindex :
      S.index = 84 ∨ S.index = 168 := by
    have hproduct := S.index_mul_card
    rw [hScard] at hproduct
    rcases hLcard with hLcard | hLcard
    · left
      rw [show Nat.card L = 10500 by
        exact hLcard] at hproduct
      omega
    · right
      rw [show Nat.card L = 21000 by
        exact hLcard] at hproduct
      omega
  have hsylowDvd :
      Nat.card (Sylow 5 L) ∣ 168 := by
    have hdiv := S.card_dvd_index
    rcases hSindex with hindex | hindex
    · rw [hindex] at hdiv
      exact hdiv.trans (by norm_num)
    · simpa [hindex] using hdiv
  have hsylowMod :
      Nat.card (Sylow 5 L) % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 L
    change
      Nat.card (Sylow 5 L) % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [Nat.card_eq_fintype_card] using hmod
  obtain ⟨k, hk⟩ := htwentyOneSylow
  have hsylowPos :
      0 < Nat.card (Sylow 5 L) :=
    Nat.card_pos
  have hsylowLe :
      Nat.card (Sylow 5 L) ≤ 168 :=
    Nat.le_of_dvd (by norm_num) hsylowDvd
  have hkPos : 0 < k := by
    omega
  have hkLe : k ≤ 8 := by
    omega
  rw [Nat.card_eq_fintype_card] at hk
  rw [Nat.card_eq_fintype_card] at hsylowMod
  rw [Nat.card_eq_fintype_card] at hsylowDvd
  rw [hk] at hsylowMod
  rw [hk] at hsylowDvd
  have hkEq : k = 1 := by
    have hkCases : k = 1 ∨ k = 6 := by
      omega
    rcases hkCases with hkOne | hkSix
    · exact hkOne
    · rw [hkSix] at hsylowDvd
      norm_num at hsylowDvd
  rw [hkEq] at hk
  norm_num at hk
  rw [Nat.card_eq_fintype_card]
  simpa only [L] using hk

private theorem sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
    (G : Type) [Group G] [Fintype G]
    (m : ℕ) (hm : m ≠ 0) (hnotFive : ¬5 ∣ m)
    (hGcard : Nat.card G = 125 * m)
    (S : Sylow 5 G) :
    Nat.card S = 125 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfactorization :
      (125 * m).factorization 5 = 3 := by
    rw [show 125 * m = 5 * (5 * (5 * m)) by
      ring]
    exact
      Degree20.factorization_five_cube_mul_of_not_dvd
        m hm hnotFive
  rw [S.card_eq_multiplicity, hGcard,
    hfactorization]
  norm_num

noncomputable def extendSylowThroughSubtypeSameCard
    {G : Type} [Group G] {p : ℕ}
    (H : Subgroup G) (T : Sylow p H) :
    Sylow p G :=
  Classical.choose T.exists_comap_subtype_eq

theorem extendSylowThroughSubtypeSameCard_comap
    {G : Type} [Group G] {p : ℕ}
    (H : Subgroup G) (T : Sylow p H) :
    (extendSylowThroughSubtypeSameCard H T).comap
        H.subtype = T :=
  Classical.choose_spec T.exists_comap_subtype_eq

theorem extendSylowThroughSubtypeSameCard_le
    {G : Type} [Group G] [Fintype G] {p c : ℕ}
    (H : Subgroup G)
    (hglobal : ∀ Q : Sylow p G, Nat.card Q = c)
    (hlocal : ∀ T : Sylow p H, Nat.card T = c)
    (T : Sylow p H) :
    (extendSylowThroughSubtypeSameCard H T :
      Subgroup G) ≤ H := by
  let Q := extendSylowThroughSubtypeSameCard H T
  have hmapLe :
      (T : Subgroup H).map H.subtype ≤
        (Q : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap,
      extendSylowThroughSubtypeSameCard_comap]
  have hmapCard :
      Nat.card ((T : Subgroup H).map H.subtype) = c := by
    calc
      Nat.card ((T : Subgroup H).map H.subtype) =
          Nat.card T :=
        Nat.card_congr
          ((T : Subgroup H).equivMapOfInjective
            H.subtype H.subtype_injective).toEquiv.symm
      _ = c := hlocal T
  have hmapEq :
      (T : Subgroup H).map H.subtype =
        (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hmapLe (by
      rw [hmapCard, hglobal Q])
  rw [← hmapEq]
  exact Subgroup.map_subtype_le (T : Subgroup H)

private theorem point_stabilizer_sylow_five_card_eq_one
    (L Y : Type) [Group L] [Fintype L] [Fintype Y]
    [MulAction L Y] [MulAction.IsPretransitive L Y]
    (hYcard : Nat.card Y = 21)
    (hLcard : Nat.card L = 10500 ∨
      Nat.card L = 21000)
    (y : Y) :
    Nat.card
      (Sylow 5 (MulAction.stabilizer L y)) = 1 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let K : Subgroup L := MulAction.stabilizer L y
  have hKindex : K.index = 21 := by
    rw [MulAction.index_stabilizer_of_transitive,
      hYcard]
  have hKindexCard := K.index_mul_card
  have hKcard :
      Nat.card K = 500 ∨ Nat.card K = 1000 := by
    rw [hKindex] at hKindexCard
    rcases hLcard with hLcard | hLcard
    · left
      rw [hLcard] at hKindexCard
      omega
    · right
      rw [hLcard] at hKindexCard
      omega
  let T : Sylow 5 K := Sylow.nonempty.some
  have hTcard : Nat.card T = 125 := by
    rcases hKcard with hKcard | hKcard
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          K 4 (by norm_num) (by norm_num)
          (by simpa using hKcard) T
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          K 8 (by norm_num) (by norm_num)
          (by simpa using hKcard) T
  have hTindex :
      T.index = 4 ∨ T.index = 8 := by
    have hproduct := T.index_mul_card
    rw [hTcard] at hproduct
    rcases hKcard with hKcard | hKcard
    · left
      rw [hKcard] at hproduct
      omega
    · right
      rw [hKcard] at hproduct
      omega
  let n := Nat.card (Sylow 5 K)
  have hnDvd : n ∣ 8 := by
    have hdiv := T.card_dvd_index
    rcases hTindex with hindex | hindex
    · rw [hindex] at hdiv
      exact hdiv.trans (by norm_num)
    · simpa [n, hindex] using hdiv
  have hnMod : n % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 K
    change n % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnPos : 0 < n := Nat.card_pos
  have hnLe : n ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hnDvd
  have hnCases : n = 1 ∨ n = 6 := by
    omega
  rcases hnCases with hnOne | hnSix
  · exact hnOne
  · rw [hnSix] at hnDvd
    norm_num at hnDvd

private theorem card_fixedBy_three_point_complement_of_support_ten
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (t : Set X) (ht : t.ncard = 3)
    (u : fixingSubgroup P t)
    (hu :
      (((u : fixingSubgroup P t) : P) :
        Equiv.Perm X).support.card = 10) :
    Nat.card
        (MulAction.fixedBy
          (SubMulAction.ofFixingSubgroup P t) u) =
      11 := by
  classical
  let Y := SubMulAction.ofFixingSubgroup P t
  let q : P := (u : P)
  let E :
      MulAction.fixedBy Y u ≃
        {x : X // x ∈ MulAction.fixedBy X q \ t} := {
    toFun := fun y => ⟨y.1.1, by
      refine ⟨?_, ?_⟩
      · have hy := y.prop
        rw [MulAction.mem_fixedBy] at hy ⊢
        exact congrArg Subtype.val hy
      · exact
          (SubMulAction.mem_ofFixingSubgroup_iff
            (M := P) (s := t)).mp y.1.prop⟩
    invFun := fun x => ⟨
      ⟨x.1,
        (SubMulAction.mem_ofFixingSubgroup_iff
          (M := P) (s := t)).mpr x.prop.2⟩, by
        have hx := x.prop.1
        rw [MulAction.mem_fixedBy] at hx ⊢
        apply Subtype.ext
        exact hx⟩
    left_inv := fun y => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := fun x => by
      apply Subtype.ext
      rfl }
  have htFixed :
      t ⊆ MulAction.fixedBy X q := by
    intro x hx
    rw [MulAction.mem_fixedBy]
    exact
      (mem_fixingSubgroup_iff P).mp u.prop
        x hx
  have hfixedNcard :
      (MulAction.fixedBy X q).ncard = 14 := by
    rw [← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,
      Degree15.card_fixedBy_subgroup_perm P q,
      hcard]
    change 24 -
        ((((u : fixingSubgroup P t) : P) :
          Equiv.Perm X).support.card) = 14
    rw [hu]
  have hsplit :=
    Set.ncard_sdiff_add_ncard_of_subset htFixed
  rw [ht, hfixedNcard] at hsplit
  calc
    Nat.card (MulAction.fixedBy Y u) =
        Nat.card
          {x : X //
            x ∈ MulAction.fixedBy X q \ t} :=
      Nat.card_congr E
    _ = (MulAction.fixedBy X q \ t).ncard :=
      Nat.card_coe_set_eq _
    _ = 11 := by omega

private theorem point_stabilizer_sylow_five_card_eq_one_hundred_twenty_five
    (L Y : Type) [Group L] [Fintype L] [Fintype Y]
    [MulAction L Y] [MulAction.IsPretransitive L Y]
    (hYcard : Nat.card Y = 21)
    (hLcard : Nat.card L = 10500 ∨
      Nat.card L = 21000)
    (y : Y)
    (T : Sylow 5 (MulAction.stabilizer L y)) :
    Nat.card T = 125 := by
  classical
  let K : Subgroup L := MulAction.stabilizer L y
  have hKindex : K.index = 21 := by
    rw [MulAction.index_stabilizer_of_transitive,
      hYcard]
  have hKindexCard := K.index_mul_card
  have hKcard :
      Nat.card K = 500 ∨ Nat.card K = 1000 := by
    rw [hKindex] at hKindexCard
    rcases hLcard with hLcard | hLcard
    · left
      rw [hLcard] at hKindexCard
      omega
    · right
      rw [hLcard] at hKindexCard
      omega
  rcases hKcard with hKcard | hKcard
  · exact
      sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
        K 4 (by norm_num) (by norm_num)
        (by simpa using hKcard) T
  · exact
      sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
        K 8 (by norm_num) (by norm_num)
        (by simpa using hKcard) T

private theorem card_sylow_five_containing_support_ten
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (t : Set X) (ht : t.ncard = 3)
    (hLcard :
      Nat.card (fixingSubgroup P t) = 10500 ∨
        Nat.card (fixingSubgroup P t) = 21000)
    (u : fixingSubgroup P t)
    (huSupport :
      (((u : fixingSubgroup P t) : P) :
        Equiv.Perm X).support.card = 10)
    (huSylow :
      ∃ S : Sylow 5 (fixingSubgroup P t),
        u ∈ (S : Subgroup (fixingSubgroup P t))) :
    Nat.card
        {S : Sylow 5 (fixingSubgroup P t) //
          u ∈ (S : Subgroup
            (fixingSubgroup P t))} =
      11 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let L : Subgroup P := fixingSubgroup P t
  let Y := SubMulAction.ofFixingSubgroup P t
  have hprimitive :
      MulAction.IsPreprimitive L Y :=
    three_point_stabilizer_is_preprimitive
      X P hcard h5 t ht
  letI : MulAction.IsPreprimitive L Y :=
    hprimitive
  have hYcard : Nat.card Y = 21 :=
    three_point_remaining_card X P hcard t ht
  have hglobal (S : Sylow 5 L) :
      Nat.card S = 125 := by
    rcases hLcard with hLcard | hLcard
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          L 84 (by norm_num) (by norm_num)
          (by simpa [L] using hLcard) S
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          L 168 (by norm_num) (by norm_num)
          (by simpa [L] using hLcard) S
  have hlocal (y : Y)
      (T : Sylow 5 (MulAction.stabilizer L y)) :
      Nat.card T = 125 :=
    point_stabilizer_sylow_five_card_eq_one_hundred_twenty_five
      L Y hYcard (by simpa [L] using hLcard) y T
  have hfixedCard (S : Sylow 5 L) :
      Nat.card (MulAction.fixedPoints S Y) = 1 := by
    exact
      (sylow_five_card_one_hundred_twenty_five_data
        X P hcard h5 hnotAlt t ht S
          (hglobal S)).2
  let fixedPoint :
      ∀ S : Sylow 5 L,
        MulAction.fixedPoints S Y :=
    fun S =>
      Classical.choice
        (Nat.card_eq_one_iff_unique.mp
          (hfixedCard S)).2
  let center : Sylow 5 L → Y :=
    fun S => (fixedPoint S).1
  let f :
      {S : Sylow 5 L //
        u ∈ (S : Subgroup L)} →
        MulAction.fixedBy Y u :=
    fun S => ⟨center S.1, by
      change u • center S.1 = center S.1
      exact
        (fixedPoint S.1).prop
          ⟨u, S.prop⟩⟩
  have hfInjective : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    let y : Y := center A.1
    have hcenter :
        center B.1 = y := by
      exact
        (congrArg Subtype.val hAB).symm
    have hAle :
        (A.1 : Subgroup L) ≤
          MulAction.stabilizer L y := by
      intro a ha
      rw [MulAction.mem_stabilizer_iff]
      exact
        (fixedPoint A.1).prop
          ⟨a, ha⟩
    have hBle :
        (B.1 : Subgroup L) ≤
          MulAction.stabilizer L y := by
      intro b hb
      rw [MulAction.mem_stabilizer_iff]
      have hfix :=
        (fixedPoint B.1).prop
          ⟨b, hb⟩
      change b • center B.1 = center B.1 at hfix
      simpa [hcenter] using hfix
    have hlocalOne :
        Nat.card
            (Sylow 5
              (MulAction.stabilizer L y)) =
          1 :=
      point_stabilizer_sylow_five_card_eq_one
        L Y hYcard (by simpa [L] using hLcard) y
    have hsubtype :
        A.1.subtype hAle =
          B.1.subtype hBle :=
      (Nat.card_eq_one_iff_unique.mp
        hlocalOne).1.elim _ _
    exact Sylow.subtype_injective hsubtype
  have hfSurjective : Function.Surjective f := by
    intro z
    obtain ⟨S₀, huS₀⟩ := huSylow
    let K : Subgroup L :=
      MulAction.stabilizer L z.1
    let uK : K := ⟨u, by
      rw [MulAction.mem_stabilizer_iff]
      exact z.prop⟩
    let A : Subgroup K :=
      (S₀ : Subgroup L).comap K.subtype
    have hAisP : IsPGroup 5 A :=
      S₀.isPGroup'.comap_subtype
    obtain ⟨T, hAT⟩ :=
      hAisP.exists_le_sylow
    have huA : uK ∈ A := by
      exact huS₀
    have huT : uK ∈ (T : Subgroup K) :=
      hAT huA
    let Q : Sylow 5 L :=
      extendSylowThroughSubtypeSameCard K T
    have hQle :
        (Q : Subgroup L) ≤ K :=
      extendSylowThroughSubtypeSameCard_le
        K hglobal (hlocal z.1) T
    have hQcomap :
        (Q : Subgroup L).comap K.subtype =
          (T : Subgroup K) :=
      extendSylowThroughSubtypeSameCard_comap
        K T
    have huQ :
        u ∈ (Q : Subgroup L) := by
      have huComap :
          uK ∈
            (Q : Subgroup L).comap K.subtype := by
        rw [hQcomap]
        exact huT
      exact huComap
    let zQ :
        MulAction.fixedPoints Q Y :=
      ⟨z.1, by
        intro q
        have hqK : (q : L) ∈ K :=
          hQle q.prop
        rw [MulAction.mem_stabilizer_iff] at hqK
        exact hqK⟩
    have hfixedEq :
        fixedPoint Q = zQ :=
      (Nat.card_eq_one_iff_unique.mp
        (hfixedCard Q)).1.elim _ _
    refine ⟨⟨Q, huQ⟩, ?_⟩
    apply Subtype.ext
    change center Q = z.1
    simpa [center, zQ] using
      congrArg Subtype.val hfixedEq
  calc
    Nat.card
        {S : Sylow 5 (fixingSubgroup P t) //
          u ∈ (S : Subgroup
            (fixingSubgroup P t))} =
        Nat.card
          {S : Sylow 5 L //
            u ∈ (S : Subgroup L)} := by
      rfl
    _ = Nat.card (MulAction.fixedBy Y u) :=
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
    _ = 11 :=
      card_fixedBy_three_point_complement_of_support_ten
        X P hcard t ht u huSupport

private theorem three_point_stabilizer_card_not_ten_thousand_five_hundred_or_twenty_one_thousand
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (t : Set X) (ht : t.ncard = 3)
    (hLcard :
      Nat.card (fixingSubgroup P t) = 10500 ∨
        Nat.card (fixingSubgroup P t) = 21000) :
    False := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let L : Subgroup P := fixingSubgroup P t
  have hglobal (S : Sylow 5 L) :
      Nat.card S = 125 := by
    rcases hLcard with hLcard | hLcard
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          L 84 (by norm_num) (by norm_num)
          (by simpa [L] using hLcard) S
    · exact
        sylow_five_card_eq_one_hundred_twenty_five_of_card_eq_one_hundred_twenty_five_mul
          L 168 (by norm_num) (by norm_num)
          (by simpa [L] using hLcard) S
  have hSylowCount :
      Nat.card (Sylow 5 L) = 21 := by
    exact
      sylow_five_count_eq_twenty_one_of_card_ten_thousand_five_hundred_or_twenty_one_thousand
        X P hcard h5 hnotAlt t ht
          (by simpa [L] using hLcard)
  let A :=
    Σ S : Sylow 5 L,
      {u : S //
        (((((u : S) : L) : P) :
          Equiv.Perm X).support.card = 10)}
  let U :=
    {u : L //
      (((u : L) : P) :
          Equiv.Perm X).support.card = 10 ∧
        ∃ S : Sylow 5 L,
          u ∈ (S : Subgroup L)}
  let B :=
    Σ u : U,
      {S : Sylow 5 L //
        u.1 ∈ (S : Subgroup L)}
  have hFiberA (S : Sylow 5 L) :
      Nat.card
          {u : S //
            (((((u : S) : L) : P) :
              Equiv.Perm X).support.card = 10)} =
        24 := by
    exact
      (sylow_five_card_one_hundred_twenty_five_data
        X P hcard h5 hnotAlt t ht S
          (hglobal S)).1
  have hAcard : Nat.card A = 504 := by
    rw [Nat.card_sigma]
    simp_rw [hFiberA]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hSylowCount]
    norm_num
  have hFiberB (u : U) :
      Nat.card
          {S : Sylow 5 L //
            u.1 ∈ (S : Subgroup L)} =
        11 := by
    exact
      card_sylow_five_containing_support_ten
        X P hcard h5 hnotAlt t ht
          (by simpa [L] using hLcard)
          u.1 u.prop.1 u.prop.2
  let e : A ≃ B := {
    toFun := fun a =>
      ⟨⟨(a.2.1 : L),
          ⟨a.2.prop,
            ⟨a.1, a.2.1.prop⟩⟩⟩,
        ⟨a.1, a.2.1.prop⟩⟩
    invFun := fun b =>
      ⟨b.2.1,
        ⟨⟨b.1.1, b.2.prop⟩,
          b.1.prop.1⟩⟩
    left_inv := by
      rintro ⟨S, ⟨u, hu⟩⟩
      rfl
    right_inv := by
      rintro ⟨u, ⟨S, hu⟩⟩
      rfl }
  have hBcard : Nat.card B = 504 := by
    calc
      Nat.card B = Nat.card A :=
        Nat.card_congr e.symm
      _ = 504 := hAcard
  have helevenDvd : 11 ∣ Nat.card B := by
    refine ⟨Nat.card U, ?_⟩
    rw [Nat.card_sigma]
    simp_rw [hFiberB]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul,
      Nat.mul_comm]
    norm_num
  rw [hBcard] at helevenDvd
  norm_num at helevenDvd

theorem five_point_stabilizer_card_ne_twenty_five_and_ne_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 25 ∧
      Nat.card (fixingSubgroup P s) ≠ 50 := by
  classical
  obtain ⟨t, _, ht⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 3) (by
        rw [Set.ncard_univ,
          Nat.card_eq_fintype_card, hcard]
        omega)
  have hLcard :=
    three_point_stabilizer_card_eq_four_hundred_twenty_mul
      X P hcard h5 s hs t ht
  constructor
  · intro hHcard
    apply
      three_point_stabilizer_card_not_ten_thousand_five_hundred_or_twenty_one_thousand
        X P hcard h5 hnotAlt t ht
    left
    calc
      Nat.card (fixingSubgroup P t) =
          420 * Nat.card (fixingSubgroup P s) :=
        hLcard
      _ = 10500 := by
        rw [hHcard]
  · intro hHcard
    apply
      three_point_stabilizer_card_not_ten_thousand_five_hundred_or_twenty_one_thousand
        X P hcard h5 hnotAlt t ht
    right
    calc
      Nat.card (fixingSubgroup P t) =
          420 * Nat.card (fixingSubgroup P s) :=
        hLcard
      _ = 21000 := by
        rw [hHcard]

end FiveTransitive.Degree24

end CFSG
