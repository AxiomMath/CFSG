module

public import CFSG.Permutation.FiveTransitive.Degree15FixedPoint
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private theorem perm_order_ne_twenty_five_of_card_sixteen
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 16)
    (g : Equiv.Perm X) :
    orderOf g ≠ 25 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hgorder
  have hpow : g ^ 5 ≠ 1 := by
    intro h
    have hdvd : orderOf g ∣ 5 :=
      orderOf_dvd_of_pow_eq_one h
    rw [hgorder] at hdvd
    norm_num at hdvd
  have hexists :
      ∃ c ∈ g.cycleType, c ≠ 5 := by
    by_contra h
    push Not at h
    apply hpow
    rw [Equiv.Perm.pow_prime_eq_one_iff]
    exact h
  obtain ⟨c, hc, hcne⟩ := hexists
  have hcdvd : c ∣ 25 := by
    rw [← hgorder]
    exact Equiv.Perm.dvd_of_mem_cycleType hc
  have hctwo : 2 ≤ c :=
    Equiv.Perm.two_le_of_mem_cycleType hc
  have hcle : c ≤ 16 := by
    rw [Equiv.Perm.cycleType_def] at hc
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hc
    change d.support.card ≤ 16
    calc
      d.support.card ≤ Fintype.card X :=
        Finset.card_le_univ d.support
      _ = 16 := hcard
  let c' : Fin 17 := ⟨c, by omega⟩
  have hfinite :
      ∀ d : Fin 17, 2 ≤ d.val → d.val ∣ 25 →
        d.val ≠ 5 → False := by
    decide
  exact hfinite c' hctwo hcdvd hcne

theorem sylow_five_nonidentity_order
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (S : Sylow 5 P) (hScard : Nat.card S = 25)
    {u : S} (hu : u ≠ 1) :
    orderOf u = 5 := by
  have hudvd : orderOf u ∣ 5 ^ 2 := by
    norm_num
    rw [← hScard]
    exact _root_.orderOf_dvd_natCard u
  obtain ⟨i, hi, horder⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hudvd
  interval_cases i
  · norm_num only [pow_zero] at horder
    exact (hu (orderOf_eq_one_iff.mp horder)).elim
  · norm_num only [pow_one] at horder
    exact horder
  · have hpermOrder :
        orderOf (((u : S) : P) : Equiv.Perm X) = 25 := by
      calc
        orderOf (((u : S) : P) : Equiv.Perm X) =
            orderOf ((u : S) : P) := Subgroup.orderOf_coe _
        _ = orderOf u := Subgroup.orderOf_coe _
        _ = 25 := by norm_num at horder ⊢; omega
    exact
      (perm_order_ne_twenty_five_of_card_sixteen
        X hcard (((u : S) : P) : Equiv.Perm X) hpermOrder).elim

private theorem nonidentity_sylow_five_fixed_point_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 5 P) (hScard : Nat.card S = 25)
    {u : S} (hu : u ≠ 1) :
    Fintype.card (MulAction.fixedBy X (u : P)) = 6 ∨
      Fintype.card (MulAction.fixedBy X (u : P)) = 1 := by
  let g : Equiv.Perm X := ((u : S) : P)
  have huorder : orderOf u = 5 :=
    sylow_five_nonidentity_order X P hcard S hScard hu
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf ((u : S) : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 16 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 16 := hcard
  have hmLe : m + 1 ≤ 3 := by
    nlinarith
  have hmCases : m + 1 = 1 ∨ m + 1 = 2 ∨ m + 1 = 3 := by
    omega
  rcases hmCases with hmOne | hmTwo | hmThree
  · have hsupport : g.support.card = 5 := by
      omega
    have hgNe : g ≠ 1 := by
      intro hg
      rw [hg, orderOf_one] at hgorder
      norm_num at hgorder
    exact (hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) (u : P).prop hgNe (by
          change g.support.card ≤ 5
          omega))).elim
  · left
    rw [Degree15.card_fixedBy_subgroup_perm, hcard]
    change 16 - g.support.card = 6
    omega
  · right
    rw [Degree15.card_fixedBy_subgroup_perm, hcard]
    change 16 - g.support.card = 1
    omega

@[expose] def DoubleFiveElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (S : Sylow 5 P) :=
  {u : S //
    u ≠ 1 ∧
      Fintype.card (MulAction.fixedBy X (u : P)) = 6}

noncomputable instance doubleFiveElementsFintype
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (S : Sylow 5 P) :
    Fintype (DoubleFiveElements X P S) := by
  classical
  change Fintype {u : S //
    u ≠ 1 ∧ Fintype.card (MulAction.fixedBy X (u : P)) = 6}
  exact Fintype.ofFinite _

theorem card_doubleFiveElements_eq_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 5 P) (hScard : Nat.card S = 25) :
    Fintype.card (DoubleFiveElements X P S) = 12 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let Ω := MulAction.orbitRel.Quotient S X
  have horbitLe (x : X) :
      Fintype.card (MulAction.orbit S x) ≤ 5 := by
    have hle :
        Fintype.card (MulAction.orbit S x) ≤ 16 := by
      calc
        Fintype.card (MulAction.orbit S x) ≤ Fintype.card X :=
          Fintype.card_le_of_injective
            (fun y : MulAction.orbit S x => (y : X))
            Subtype.val_injective
        _ = 16 := by
          rw [hcard]
    obtain ⟨n, hn⟩ := S.isPGroup'.card_orbit x
    rw [Nat.card_eq_fintype_card] at hn
    have hnle : n ≤ 1 := by
      by_contra hn'
      have htwo : 2 ≤ n := by omega
      have hpow :
          5 ^ 2 ≤ 5 ^ n :=
        Nat.pow_le_pow_right (by norm_num) htwo
      rw [← hn] at hpow
      omega
    rw [hn]
    interval_cases n <;> norm_num
  have horbitCases (x : X) :
      Fintype.card (MulAction.orbit S x) = 1 ∨
        Fintype.card (MulAction.orbit S x) = 5 := by
    obtain ⟨n, hn⟩ := S.isPGroup'.card_orbit x
    rw [Nat.card_eq_fintype_card] at hn
    have hnle : n ≤ 1 := by
      have hle := horbitLe x
      by_contra hn'
      have htwo : 2 ≤ n := by omega
      have hpow :
          5 ^ 2 ≤ 5 ^ n :=
        Nat.pow_le_pow_right (by norm_num) htwo
      rw [← hn] at hpow
      omega
    rw [hn]
    interval_cases n <;> norm_num
  have hdecompose :
      Fintype.card X =
        ∑ w : Ω,
          Fintype.card (MulAction.orbit S w.out) := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr
      (MulAction.selfEquivSigmaOrbits S X)
  have hfourOrbits : 4 ≤ Fintype.card Ω := by
    have hsumLe :
        (∑ w : Ω,
            Fintype.card (MulAction.orbit S w.out)) ≤
          ∑ _w : Ω, 5 :=
      Finset.sum_le_sum fun w _ => horbitLe w.out
    rw [hcard] at hdecompose
    rw [← hdecompose] at hsumLe
    simp only [Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at hsumLe
    omega
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group S X
  have hsumLower :
      100 ≤
        ∑ u : S,
          Fintype.card (MulAction.fixedBy X u) := by
    rw [hburnside]
    rw [show Fintype.card S = 25 by
      rw [← Nat.card_eq_fintype_card]
      exact hScard]
    nlinarith
  have hfixedOne :
      Fintype.card (MulAction.fixedBy X (1 : S)) = 16 := by
    calc
      Fintype.card (MulAction.fixedBy X (1 : S)) =
        Fintype.card (Set.univ : Set X) :=
        Fintype.card_congr
          (Set.equivOfEq
            (MulAction.fixedBy_one_eq_univ (M := S) (α := X)))
      _ = Fintype.card X :=
        Fintype.card_congr (Equiv.Set.univ X)
      _ = 16 := hcard
  have hpointwise (u : S) :
      Fintype.card (MulAction.fixedBy X u) =
        1 + (if u = 1 then 15 else 0) +
          (if u ≠ 1 ∧
              Fintype.card (MulAction.fixedBy X u) = 6
            then 5 else 0) := by
    by_cases hu : u = 1
    · subst u
      rw [hfixedOne]
      norm_num
    · rcases nonidentity_sylow_five_fixed_point_cases
        X P hcard h5 hnotAlt S hScard hu with hfix | hfix
      · have hfix' :
            Fintype.card (MulAction.fixedBy X u) = 6 := hfix
        rw [hfix']
        simp [hu]
      · have hfix' :
            Fintype.card (MulAction.fixedBy X u) = 1 := hfix
        rw [hfix']
        simp [hu]
  have hsumUpper :
      (∑ u : S,
          Fintype.card (MulAction.fixedBy X u)) ≤ 160 := by
    calc
      (∑ u : S,
          Fintype.card (MulAction.fixedBy X u)) ≤
          ∑ u : S, (6 + if u = 1 then 10 else 0) :=
        Finset.sum_le_sum fun u _ => by
          by_cases hu : u = 1
          · subst u
            rw [hfixedOne]
            norm_num
          · rcases nonidentity_sylow_five_fixed_point_cases
              X P hcard h5 hnotAlt S hScard hu with hfix | hfix
            · have hfix' :
                  Fintype.card (MulAction.fixedBy X u) = 6 := hfix
              rw [hfix']
              simp [hu]
            · have hfix' :
                  Fintype.card (MulAction.fixedBy X u) = 1 := hfix
              rw [hfix']
              simp [hu]
      _ = 160 := by
        rw [Finset.sum_add_distrib]
        have hsumConst : (∑ _u : S, 6) = 150 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [show Fintype.card S = 25 by
            rw [← Nat.card_eq_fintype_card]
            exact hScard]
          norm_num
        have hsumIdentity :
            (∑ u : S, if u = 1 then 10 else 0) = 10 := by
          simp
        rw [hsumConst, hsumIdentity]
  have hsixOrbits : Fintype.card Ω ≤ 6 := by
    rw [hburnside] at hsumUpper
    rw [show Fintype.card S = 25 by
      rw [← Nat.card_eq_fintype_card]
      exact hScard] at hsumUpper
    nlinarith
  let F := MulAction.fixedPoints S X
  have hFcardLe : Fintype.card F ≤ 16 := by
    calc
      Fintype.card F ≤ Fintype.card X :=
        Fintype.card_le_of_injective
          (fun x : F => (x : X)) Subtype.val_injective
      _ = 16 := hcard
  have hFne : F ≠ Set.univ := by
    have hScardF : Fintype.card S = 25 := by
      rw [← Nat.card_eq_fintype_card]
      exact hScard
    have hSnontrivial : Nontrivial S :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial S := hSnontrivial
    obtain ⟨u, hu⟩ := exists_ne (1 : S)
    intro hFuniv
    have hfixedU : MulAction.fixedBy X u = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ F := by
        rw [hFuniv]
        trivial
      exact hx u
    exact hu
      ((MulAction.fixedBy_eq_univ_iff_eq_one
        (M := S) (α := X)).mp hfixedU)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ F := by
    by_contra h
    push Not at h
    exact hFne (Set.eq_univ_of_forall h)
  let orbitMap : F → Ω :=
    fun y => Quotient.mk'' (y : X)
  have horbitMapInjective : Function.Injective orbitMap := by
    intro y z hyz
    apply Subtype.ext
    exact MulAction.mem_fixedPoints'.mp z.prop y.1
      (Quotient.exact' hyz)
  have hxNotRange :
      (Quotient.mk'' x : Ω) ∉ Set.range orbitMap := by
    rintro ⟨y, hy⟩
    have hxy : x = y.1 :=
      MulAction.mem_fixedPoints'.mp y.prop x
        (Quotient.exact' hy.symm)
    apply hx
    rw [hxy]
    exact y.prop
  have hFcardLtOrbits : Fintype.card F < Fintype.card Ω :=
    Fintype.card_lt_of_injective_of_notMem
      orbitMap horbitMapInjective hxNotRange
  have hFcardLtSix : Fintype.card F < 6 := by
    omega
  have hFmod :=
    S.isPGroup'.card_modEq_card_fixedPoints X
  have hFmod' : 16 % 5 = Fintype.card F % 5 := by
    change Nat.card X % 5 = Nat.card F % 5 at hFmod
    rw [Nat.card_eq_fintype_card, hcard,
      Nat.card_eq_fintype_card] at hFmod
    exact hFmod
  have hFcard : Fintype.card F = 1 := by
    have hFneFive : Fintype.card F ≠ 5 := by
      intro h
      norm_num [h] at hFmod'
    have hFltFive : Fintype.card F < 5 := by
      omega
    rw [Nat.mod_eq_of_lt hFltFive] at hFmod'
    norm_num at hFmod'
    simpa only [Fintype.card_subtype] using hFmod'.symm
  let B :=
    {w : Ω //
      Fintype.card (MulAction.orbit S w.out) = 1}
  let orbitOneToFixed : B → F :=
    fun w => ⟨w.1.out,
      MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr w.2⟩
  have horbitOneToFixedInjective :
      Function.Injective orbitOneToFixed := by
    intro w z hwz
    apply Subtype.ext
    calc
      w.1 = Quotient.mk'' w.1.out :=
        (Quotient.out_eq' w.1).symm
      _ = Quotient.mk'' z.1.out := congrArg Quotient.mk''
        (congrArg Subtype.val hwz)
      _ = z.1 := Quotient.out_eq' z.1
  have hBcard : Fintype.card B ≤ 1 := by
    calc
      Fintype.card B ≤ Fintype.card F :=
        Fintype.card_le_of_injective
          orbitOneToFixed horbitOneToFixedInjective
      _ = 1 := hFcard
  have hsumOrbitLower :
      5 * Fintype.card Ω ≤
        (∑ w : Ω,
          Fintype.card (MulAction.orbit S w.out)) + 4 := by
    let oneOrbit : Ω → Prop := fun w =>
      Fintype.card (MulAction.orbit S w.out) = 1
    have hindicator :
        (∑ w : Ω, if oneOrbit w then 4 else 0) ≤ 4 := by
      have hBSubsingleton : Subsingleton B :=
        Fintype.card_le_one_iff_subsingleton.mp hBcard
      have hunique {w z : Ω}
          (hw : oneOrbit w) (hz : oneOrbit z) : w = z := by
        have hwB :
            Fintype.card (MulAction.orbit S w.out) = 1 := hw
        have hzB :
            Fintype.card (MulAction.orbit S z.out) = 1 := hz
        exact congrArg Subtype.val
          (@Subsingleton.elim B hBSubsingleton
            ⟨w, hwB⟩ ⟨z, hzB⟩)
      by_cases hex : ∃ w, oneOrbit w
      · obtain ⟨w₀, hw₀⟩ := hex
        calc
          (∑ w : Ω, if oneOrbit w then 4 else 0) =
              ∑ w : Ω, if w = w₀ then 4 else 0 := by
            apply Finset.sum_congr rfl
            intro w _
            by_cases hw : oneOrbit w
            · have heq : w = w₀ := hunique hw hw₀
              subst w
              simp [hw₀]
            · have hne : w ≠ w₀ := by
                intro heq
                exact hw (heq ▸ hw₀)
              simp [hw, hne]
          _ = 4 := by
            rw [Fintype.sum_ite_eq']
          _ ≤ 4 := le_rfl
      · push Not at hex
        simp [hex]
    calc
      5 * Fintype.card Ω = ∑ _w : Ω, 5 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ w : Ω,
          (Fintype.card (MulAction.orbit S w.out) +
            if oneOrbit w then 4 else 0) :=
        Finset.sum_le_sum fun w _ => by
          rcases horbitCases w.out with h | h
          · dsimp only [oneOrbit]
            simp only [h]
            norm_num
          · dsimp only [oneOrbit]
            simp only [h]
            norm_num
      _ = (∑ w : Ω,
            Fintype.card (MulAction.orbit S w.out)) +
          (∑ w : Ω, if oneOrbit w then 4 else 0) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ w : Ω,
            Fintype.card (MulAction.orbit S w.out)) + 4 :=
        Nat.add_le_add_left hindicator _
  have hfourOrbitsEq : Fintype.card Ω = 4 := by
    rw [← hdecompose, hcard] at hsumOrbitLower
    omega
  have hsumValue :
      (∑ u : S,
          Fintype.card (MulAction.fixedBy X u)) = 100 := by
    rw [hburnside, hfourOrbitsEq]
    rw [show Fintype.card S = 25 by
      rw [← Nat.card_eq_fintype_card]
      exact hScard]
  have hsumExact :
      (∑ u : S,
          Fintype.card (MulAction.fixedBy X u)) =
        40 + 5 * Fintype.card (DoubleFiveElements X P S) := by
    let good : S → Prop := fun u =>
      u ≠ 1 ∧ Fintype.card (MulAction.fixedBy X u) = 6
    let A : Finset S := Finset.univ.filter good
    have hAcard :
        A.card = Fintype.card (DoubleFiveElements X P S) := by
      let e :
          DoubleFiveElements X P S ≃ {u : S // good u} :=
        { toFun := fun u => ⟨u.1, u.2⟩
          invFun := fun u => ⟨u.1, u.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      calc
        A.card = Fintype.card {u : S // good u} := by
          dsimp only [A]
          exact (Fintype.card_subtype good).symm
        _ = Fintype.card (DoubleFiveElements X P S) :=
          Fintype.card_congr e.symm
    have honeSum : (∑ _u : S, 1) = 25 := by
      simp [show Fintype.card S = 25 by
        rw [← Nat.card_eq_fintype_card]
        exact hScard]
    have heqSum :
        (∑ u : S, if u = 1 then 15 else 0) = 15 := by
      simp
    have hgoodSum :
        (∑ u : S, if good u then 5 else 0) = 5 * A.card := by
      rw [← Finset.sum_filter]
      rw [show Finset.univ.filter good = A by
        ext u
        simp [A]]
      rw [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_comm _ _
    calc
      (∑ u : S,
          Fintype.card (MulAction.fixedBy X u)) =
          ∑ u : S,
            (1 + (if u = 1 then 15 else 0) +
              (if good u then 5 else 0)) :=
        Finset.sum_congr rfl (fun u _ => hpointwise u)
      _ = (∑ _u : S, 1) +
            (∑ u : S, if u = 1 then 15 else 0) +
          (∑ u : S, if good u then 5 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = 40 + 5 * Fintype.card
          (DoubleFiveElements X P S) := by
        rw [honeSum, heqSum, hgoodSum, hAcard]
  have hcount := hsumExact
  rw [hsumValue] at hcount
  omega

end FiveTransitive.Degree16

end CFSG
