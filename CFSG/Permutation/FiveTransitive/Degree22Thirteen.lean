module

public import CFSG.Permutation.FiveTransitive.Degree22SmallSupport
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree22

open MulAction SubMulAction Subgroup

private theorem thirteen_cycle_centralizer_card_le
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 22)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 13) :
    Nat.card
        (Subgroup.centralizer ({u} : Set P)) ≤ 936 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let F := MulAction.fixedBy X u
  have hFcard : Nat.card F = 9 := by
    rw [Nat.card_eq_fintype_card,
      Degree15.card_fixedBy_subgroup_perm,
      hcard, hgsupport]
  letI : Nonempty F :=
    Finite.card_pos_iff.mp (by omega)
  let y : F := Classical.choice inferInstance
  have hFnontrivial : Nontrivial F :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hFcard]
      norm_num)
  letI : Nontrivial F := hFnontrivial
  let z : F := Classical.choose (exists_ne y)
  have hyz : y ≠ z :=
    (Classical.choose_spec (exists_ne y)).symm
  let L : Subgroup C :=
    MulAction.stabilizer C (y : X)
  let M : Subgroup L :=
    MulAction.stabilizer L (z : X)
  have hOrbitY :
      MulAction.orbit C (y : X) ⊆ F := by
    intro x hx
    obtain ⟨c, hc⟩ :=
      MulAction.mem_orbit_iff.mp hx
    let cP : P := (c : C)
    have hcomm : Commute cP u :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (c : C).prop
    have hyfixed : (u : P) • (y : X) = y :=
      y.prop
    change (u : P) • x = x
    rw [← hc]
    calc
      (u : P) • (cP • (y : X)) =
          ((u : P) * cP) • (y : X) :=
        (mul_smul _ _ _).symm
      _ = (cP * (u : P)) • (y : X) := by
        rw [hcomm.eq.symm]
      _ = cP • ((u : P) • (y : X)) :=
        mul_smul _ _ _
      _ = cP • (y : X) := by rw [hyfixed]
  have hLindex :
      L.index = (MulAction.orbit C (y : X)).ncard := by
    simpa only [L] using
      MulAction.index_stabilizer C (y : X)
  have hLindexLe : L.index ≤ 9 := by
    calc
      L.index =
          (MulAction.orbit C (y : X)).ncard :=
        hLindex
      _ ≤ F.ncard :=
        Set.ncard_le_ncard hOrbitY
      _ = Nat.card F := by
        rw [Nat.card_coe_set_eq]
      _ = 9 := hFcard
  have hOrbitZ :
      MulAction.orbit L (z : X) ⊆
        F \ {(y : X)} := by
    intro x hx
    obtain ⟨l, hl⟩ :=
      MulAction.mem_orbit_iff.mp hx
    let lC : C := (l : L)
    let lP : P := lC
    have hcomm : Commute lP u :=
      Subgroup.mem_centralizer_singleton_iff.mp
        lC.prop
    have hzfixed : (u : P) • (z : X) = z :=
      z.prop
    have hxF : x ∈ F := by
      change (u : P) • x = x
      rw [← hl]
      calc
        (u : P) • (lP • (z : X)) =
            ((u : P) * lP) • (z : X) :=
          (mul_smul _ _ _).symm
        _ = (lP * (u : P)) • (z : X) := by
          rw [hcomm.eq.symm]
        _ = lP • ((u : P) • (z : X)) :=
          mul_smul _ _ _
        _ = lP • (z : X) := by rw [hzfixed]
    refine ⟨hxF, ?_⟩
    rw [Set.mem_singleton_iff]
    intro hxy
    have hly : lC • (y : X) = y :=
      MulAction.mem_stabilizer_iff.mp l.prop
    apply hyz
    apply Subtype.ext
    apply (MulAction.injective lC)
    calc
      lC • (y : X) = y := hly
      _ = x := hxy.symm
      _ = lC • (z : X) := hl.symm
  have hyF : (y : X) ∈ F := y.prop
  have hFdiffCard : (F \ {(y : X)}).ncard = 8 := by
    have hremove :=
      Set.ncard_sdiff_singleton_add_one hyF
    rw [show F.ncard = Nat.card F by
      rw [Nat.card_coe_set_eq], hFcard] at hremove
    omega
  have hMindex :
      M.index = (MulAction.orbit L (z : X)).ncard := by
    simpa only [M] using
      MulAction.index_stabilizer L (z : X)
  have hMindexLe : M.index ≤ 8 := by
    calc
      M.index =
          (MulAction.orbit L (z : X)).ncard :=
        hMindex
      _ ≤ (F \ {(y : X)}).ncard :=
        Set.ncard_le_ncard hOrbitZ
      _ = 8 := hFdiffCard
  have hMleZpowers :
      ∀ m : M,
        (((((m : M) : L) : C) : P) :
          Equiv.Perm X) ∈ Subgroup.zpowers g := by
    intro m
    let v : Equiv.Perm X :=
      ((((m : M) : L) : C) : P)
    have hcomm : Commute v g := by
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp
          (((m : M) : L) : C).prop)
    obtain ⟨hinvariant, hrestricted⟩ :=
      hgcycle.commute_iff.mp hcomm
    let r : Equiv.Perm X :=
      Equiv.Perm.ofSubtype
        (v.subtypePerm hinvariant)
    have hrZ : r ∈ Subgroup.zpowers g := by
      simpa only [r] using hrestricted
    have hrP : r ∈ P := by
      obtain ⟨k, hk⟩ :=
        Subgroup.mem_zpowers_iff.mp hrZ
      rw [← hk]
      exact P.zpow_mem u.prop k
    let w : Equiv.Perm X := r⁻¹ * v
    have hwP : w ∈ P :=
      P.mul_mem (P.inv_mem hrP)
        ((((m : M) : L) : C) : P).prop
    have hrv (x : X) (hx : x ∈ g.support) :
        r x = v x := by
      exact
        Equiv.Perm.ofSubtype_subtypePerm_of_mem
          hinvariant hx
    have hwfixSupport :
        ∀ x ∈ g.support, w x = x := by
      intro x hx
      change r⁻¹ (v x) = x
      rw [← hrv x hx]
      exact r.symm_apply_apply x
    have hyNotSupport : (y : X) ∉ g.support := by
      rw [Equiv.Perm.notMem_support]
      exact y.prop
    have hzNotSupport : (z : X) ∉ g.support := by
      rw [Equiv.Perm.notMem_support]
      exact z.prop
    have hrfixY : r (y : X) = y := by
      exact Equiv.Perm.ofSubtype_apply_of_not_mem
        _ hyNotSupport
    have hrfixZ : r (z : X) = z := by
      exact Equiv.Perm.ofSubtype_apply_of_not_mem
        _ hzNotSupport
    have hrinvfixY : r⁻¹ (y : X) = y := by
      calc
        r⁻¹ (y : X) = r⁻¹ (r (y : X)) :=
          congrArg (fun x => r⁻¹ x) hrfixY.symm
        _ = y := r.symm_apply_apply _
    have hrinvfixZ : r⁻¹ (z : X) = z := by
      calc
        r⁻¹ (z : X) = r⁻¹ (r (z : X)) :=
          congrArg (fun x => r⁻¹ x) hrfixZ.symm
        _ = z := r.symm_apply_apply _
    have hvfixY : v (y : X) = y := by
      change (((m : M) : L) : C) • (y : X) = y
      exact MulAction.mem_stabilizer_iff.mp
        ((m : M) : L).prop
    have hvfixZ : v (z : X) = z := by
      change ((m : M) : L) • (z : X) = z
      exact MulAction.mem_stabilizer_iff.mp m.prop
    have hwfixY : w (y : X) = y := by
      change r⁻¹ (v (y : X)) = y
      rw [hvfixY]
      exact hrinvfixY
    have hwfixZ : w (z : X) = z := by
      change r⁻¹ (v (z : X)) = z
      rw [hvfixZ]
      exact hrinvfixZ
    let R : Set X :=
      (((g.supportᶜ : Finset X) : Set X) \
        {(y : X)}) \ {(z : X)}
    have hcompCard :
        (((g.supportᶜ : Finset X) : Set X)).ncard = 9 := by
      rw [Set.ncard_coe_finset, Finset.card_compl,
        hcard, hgsupport]
    have hyComp :
        (y : X) ∈ ((g.supportᶜ : Finset X) : Set X) := by
      simpa only [Finset.mem_coe, Finset.mem_compl]
        using hyNotSupport
    have hzComp :
        (z : X) ∈ ((g.supportᶜ : Finset X) : Set X) := by
      simpa only [Finset.mem_coe, Finset.mem_compl]
        using hzNotSupport
    have hzAfterY :
        (z : X) ∈
          (((g.supportᶜ : Finset X) : Set X) \
            {(y : X)}) := by
      refine ⟨hzComp, ?_⟩
      rw [Set.mem_singleton_iff]
      exact fun hzy => hyz (Subtype.ext hzy.symm)
    have hRcard : R.ncard = 7 := by
      have hyRemove :=
        Set.ncard_sdiff_singleton_add_one hyComp
      have hzRemove :=
        Set.ncard_sdiff_singleton_add_one hzAfterY
      change
        ((((g.supportᶜ : Finset X) : Set X) \
          {(y : X)}) \ {(z : X)}).ncard = 7
      rw [hcompCard] at hyRemove
      omega
    have hsupportSubset : (w.support : Set X) ⊆ R := by
      intro x hx
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hxNotSupport : x ∉ g.support := by
          intro hxg
          exact Equiv.Perm.mem_support.mp hx
            (hwfixSupport x hxg)
        simpa only [Finset.mem_coe, Finset.mem_compl]
          using hxNotSupport
      · rw [Set.mem_singleton_iff]
        intro hxy
        subst x
        exact Equiv.Perm.mem_support.mp hx hwfixY
      · rw [Set.mem_singleton_iff]
        intro hxz
        subst x
        exact Equiv.Perm.mem_support.mp hx hwfixZ
    have hwsupport : w.support.card ≤ 7 := by
      rw [← Set.ncard_coe_finset]
      exact
        (Set.ncard_le_ncard hsupportSubset).trans_eq
          hRcard
    have hwOne : w = 1 := by
      by_contra hwNe
      exact hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 hwP hwNe hwsupport)
    have hvr : v = r := by
      change r⁻¹ * v = 1 at hwOne
      exact (eq_of_inv_mul_eq_one hwOne).symm
    change v ∈ Subgroup.zpowers g
    rw [hvr]
    exact hrZ
  let baseMap : M →* Equiv.Perm X :=
    P.subtype.comp
      (C.subtype.comp
        (L.subtype.comp M.subtype))
  let zMap : M →* Subgroup.zpowers g :=
    baseMap.codRestrict
      (Subgroup.zpowers g) (by
        intro m
        change (((((m : M) : L) : C) : P) :
          Equiv.Perm X) ∈ Subgroup.zpowers g
        exact hMleZpowers m)
  have hzMapInjective : Function.Injective zMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact M.subtype_injective
      (L.subtype_injective
        (C.subtype_injective
          (P.subtype_injective hab')))
  have hMcardLe : Nat.card M ≤ 13 := by
    calc
      Nat.card M ≤
          Nat.card (Subgroup.zpowers g) :=
        Nat.card_le_card_of_injective
          zMap hzMapInjective
      _ = orderOf g := by rw [Nat.card_zpowers]
      _ = 13 := hgorder
  have hLcard := L.index_mul_card
  have hMcard := M.index_mul_card
  calc
    Nat.card C = L.index * Nat.card L :=
      hLcard.symm
    _ = L.index * (M.index * Nat.card M) := by
      rw [hMcard]
    _ ≤ 9 * (8 * 13) :=
      Nat.mul_le_mul hLindexLe
        (Nat.mul_le_mul hMindexLe hMcardLe)
    _ = 936 := by norm_num

private theorem card_fixedBy_five_of_mem_thirteen_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 22)
    (u : P) (huorder : orderOf u = 13)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 15120 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  obtain ⟨q, hq⟩ :=
    isConj_iff.mp
      (ConjAct.mem_orbit_conjAct.mp a.prop)
  have hconjPerm :
      ((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹ =
          g :=
    congrArg Subtype.val hq
  have hasupport :
      ((a.1 : P) : Equiv.Perm X).support.card = 13 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 13 := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 9 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 15120 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem thirteen_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 22)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬13 ∣ Nat.card P := by
  classical
  intro h13
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 13 h13
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  have hcentralizer : Nat.card C ≤ 936 :=
    thirteen_cycle_centralizer_card_le
      X P hcard h5 hnotAlt u huorder
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hAcard :
      Fintype.card A * Nat.card C = Nat.card P := by
    letI :
        Fintype (MulAction.stabilizer (ConjAct P) u) :=
      Fintype.ofFinite _
    have hstabilizer :
        Fintype.card
            (MulAction.stabilizer (ConjAct P) u) =
          Nat.card C := by
      rw [← Nat.card_eq_fintype_card,
        ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    have horbitCard :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [hstabilizer, ConjAct.card,
      ← Nat.card_eq_fintype_card] at horbitCard
    simpa [A, Nat.card_eq_fintype_card] using horbitCard
  have hfixed (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) (val a)) = 15120 :=
    card_fixedBy_five_of_mem_thirteen_conjugacy_orbit
      X P hcard u huorder a
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
        Fintype.card A * 15120 := by
    simp_rw [hfixed]
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
    calc
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨p, hp⟩ :=
      h5 a b a.injective b.injective
    refine ⟨p, ?_⟩
    ext i
    exact hp i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  letI : Nonempty (Fin 5 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        hcard]
      norm_num)
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 5 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 5 ↪ X)).mp hP5)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 5 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hoverfill :
      Fintype.card A * 15120 ≤ Nat.card P := by
    calc
      Fintype.card A * 15120 =
          ∑ a : A,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  rw [← hAcard] at hoverfill
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  have hupper :
      Fintype.card A * Nat.card C ≤
        Fintype.card A * 936 :=
    Nat.mul_le_mul_left _ hcentralizer
  omega

end FiveTransitive.Degree22

end CFSG
