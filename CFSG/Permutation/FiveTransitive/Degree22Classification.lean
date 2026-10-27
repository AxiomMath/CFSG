module

public import CFSG.Permutation.FiveTransitive.Degree22Nineteen
public import CFSG.Permutation.FiveTransitive.CyclicThreePointObstruction
public import Mathlib.RingTheory.ZMod.UnitsCyclic

public section

namespace CFSG

namespace FiveTransitive.Degree22

open MulAction SubMulAction Subgroup

private theorem card_of_relindex_nineteen
    {G : Type} [Group G] [Finite G]
    (C N : Subgroup G) (hCN : C ≤ N)
    (hc : Nat.card C = 19) (r : ℕ) (hr : C.relIndex N = r) :
    Nat.card N = r * 19 := by
  have hsub : Nat.card (C.subgroupOf N) = 19 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv).trans hc
  have hproduct := (C.subgroupOf N).index_mul_card
  change C.relIndex N * Nat.card (C.subgroupOf N) = Nat.card N at hproduct
  rw [hr, hsub] at hproduct
  exact hproduct.symm

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentyTwo
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 22)
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
  have hdiv : h ∣ 1609445376000 :=
    five_point_stabilizer_card_dvd_reduced
      X P hcard h5 hnotAlt s hs
  have hnotNineteen : ¬19 ∣ h := by
    intro hnineteen
    have : 19 ∣ 1609445376000 :=
      hnineteen.trans hdiv
    norm_num at this
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  have hmod : h % 19 = 16 := by
    simpa only [H, h] using
      five_point_stabilizer_card_mod_nineteen
        X P hcard h5 hnotAlt s hs
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
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 3160080 := by
    change (fixingSubgroup P s).index = 3160080
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 3160080 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hPfactorization :
      (3160080 * h).factorization 19 = 1 :=
    FiveTransitive.Degree22.factorization_nineteen_mul 166320 h
      (by norm_num) hh (by norm_num) hnotNineteen
  have heNonempty : Nonempty (Fin 3 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 3 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP3.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 9240 := by
    change
      (fixingSubgroup P (Set.range e)).index = 9240
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 342 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  let T : Sylow 19 J := Sylow.nonempty.some
  have hJfactorization :
      (342 * h).factorization 19 = 1 :=
    FiveTransitive.Degree22.factorization_nineteen_mul 18 h
      (by norm_num) hh (by norm_num) hnotNineteen
  have hTcard : Nat.card T = 19 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 19 :=
    huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 19 := by
    calc
      orderOf (u : J) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 19 := huorderT
  have huorderP : orderOf ((u : J) : P) = 19 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 19 := huorderJ
  let CJ : Subgroup J :=
    Subgroup.centralizer ((T : Subgroup J) : Set J)
  let NJ : Subgroup J :=
    Subgroup.normalizer ((T : Subgroup J) : Set J)
  have hTleCJ : (T : Subgroup J) ≤ CJ := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  let globalCu : Subgroup P :=
    Subgroup.centralizer
      ({((u : J) : P)} : Set P)
  have hglobalCucard : Nat.card globalCu = 19 := by
    simpa only [globalCu] using
      FewFixedPrimeCycle.centralizer_card_eq_prime_of_not_alternating
        X P (p := 19) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) h5 hnotAlt ((u : J) : P) huorderP
  let baseMap : CJ →* P :=
    J.subtype.comp CJ.subtype
  have hbaseMapMem :
      ∀ c : CJ, baseMap c ∈ globalCu := by
    intro c
    change ((c.1 : J) : P) ∈
      Subgroup.centralizer
        ({((u : J) : P)} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (c.prop (u : J) u.prop).symm
  let centMap : CJ →* globalCu :=
    baseMap.codRestrict globalCu hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact CJ.subtype_injective
      (J.subtype_injective hab')
  have hCJdiv : Nat.card CJ ∣ 19 := by
    rw [← hglobalCucard]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hNineteenDvdCJ : 19 ∣ Nat.card CJ := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleCJ
  have hCJcard : Nat.card CJ = 19 :=
    Nat.dvd_antisymm hCJdiv hNineteenDvdCJ
  have hAutTcard : Nat.card (MulAut T) = 18 := by
    rw [IsCyclic.card_mulAut T, hTcard,
      Nat.totient_prime (show Nat.Prime 19 by norm_num)]
  have hrangeTDvd :
      Nat.card T.normalizerMonoidHom.range ∣ 18 := by
    rw [← hAutTcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrJEq :
      CJ.relIndex NJ =
        Nat.card T.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (T : Set J)).relIndex
          (Subgroup.normalizer (T : Set J)) =
        Nat.card T.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      T.normalizerMonoidHom_ker]
    simp only [T.coe_coe]
  have hrJDvd : CJ.relIndex NJ ∣ 18 := by
    rw [hrJEq]
    exact hrangeTDvd
  letI : CJ.IsFiniteRelIndex NJ :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hNJmod : NJ.index % 19 = 1 := by
    change
      (Subgroup.normalizer (T : Set J)).index % 19 = 1
    have hsylow :
        (Subgroup.normalizer (T : Set J)).index ≡
          1 [MOD 19] := by
      rw [← T.card_eq_index_normalizer]
      exact card_sylow_modEq_one 19 J
    change
      (Subgroup.normalizer (T : Set J)).index % 19 =
        1 % 19 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrelJ :
      CJ.relIndex NJ * NJ.index = CJ.index := by
    simpa only [CJ, NJ, T.coe_coe] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (T : Set J))
  have hCJindex := CJ.index_mul_card
  have hlocalProduct :
      CJ.relIndex NJ * NJ.index * 19 = Nat.card J := by
    rw [hCJcard, ← hrelJ] at hCJindex
    exact hCJindex
  have hlocalDivided :
      CJ.relIndex NJ * NJ.index = 18 * h := by
    rw [hJcard] at hlocalProduct
    omega
  have hlocalMod :
      (18 * h) % 19 = (CJ.relIndex NJ) % 19 := by
    calc
      (18 * h) % 19 =
          (CJ.relIndex NJ * NJ.index) % 19 :=
        congrArg (fun n => n % 19)
          hlocalDivided.symm
      _ = (CJ.relIndex NJ) % 19 := by
        rw [Nat.mul_mod, hNJmod]
        simp
  have hrJpos : 0 < CJ.relIndex NJ :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrJle : CJ.relIndex NJ ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hrJDvd
  have hrJ : CJ.relIndex NJ = 3 := by
    have hlocalMod' := hlocalMod
    rw [Nat.mul_mod, hmod] at hlocalMod'
    norm_num at hlocalMod'
    have hrJlt : CJ.relIndex NJ < 19 := by omega
    rw [Nat.mod_eq_of_lt hrJlt] at hlocalMod'
    exact hlocalMod'.symm
  have hNJcard : Nat.card NJ = 57 :=
    card_of_relindex_nineteen CJ NJ
      (Subgroup.centralizer_le_normalizer (T : Set J)) hCJcard 3 hrJ
  obtain ⟨S, hScomap⟩ :=
    T.exists_comap_subtype_eq
  have hScard : Nat.card S = 19 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let R : Subgroup P :=
    (T : Subgroup J).map J.subtype
  have hRcard : Nat.card R = 19 := by
    change
      Nat.card ((T : Subgroup J).map J.subtype) = 19
    rw [Subgroup.card_map_of_injective J.subtype_injective,
      hTcard]
  have hRleS : R ≤ (S : Subgroup P) := by
    change
      (T : Subgroup J).map J.subtype ≤
        (S : Subgroup P)
    rw [Subgroup.map_le_iff_le_comap, hScomap]
  have hRS : R = (S : Subgroup P) := by
    apply Subgroup.eq_of_le_of_card_ge hRleS
    rw [hRcard, hScard]
  have hSleRange :
      (S : Subgroup P) ≤ J.subtype.range := by
    rw [← hRS]
    exact Subgroup.map_le_range J.subtype (T : Subgroup J)
  let CG : Subgroup P :=
    Subgroup.centralizer ((S : Subgroup P) : Set P)
  let NG : Subgroup P :=
    Subgroup.normalizer ((S : Subgroup P) : Set P)
  let rG := CG.relIndex NG
  have hglobal :
      rG ∣ 18 ∧
        0 < rG ∧
        NG.index % 19 = 1 ∧
        rG * NG.index * 19 = Nat.card P := by
    simpa only [CG, NG, rG, S.coe_coe] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 19) (f := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hglobalDivided :
      rG * NG.index = 166320 * h := by
    rw [hPcard] at hglobal
    omega
  have hglobalMod :
      (13 * h) % 19 = rG % 19 := by
    calc
      (13 * h) % 19 = (166320 * h) % 19 := by
        simp [Nat.mul_mod]
      _ = (rG * NG.index) % 19 :=
        congrArg (fun n => n % 19)
          hglobalDivided.symm
      _ = rG % 19 := by
        rw [Nat.mul_mod, hglobal.2.2.1]
        simp
  have hrGle : rG ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hglobal.1
  have hrG : rG = 18 := by
    have hglobalMod' := hglobalMod
    rw [Nat.mul_mod, hmod] at hglobalMod'
    norm_num at hglobalMod'
    have hrGlt : rG < 19 := by omega
    rw [Nat.mod_eq_of_lt hrGlt] at hglobalMod'
    exact hglobalMod'.symm
  have hSleCG : (S : Subgroup P) ≤ CG := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hCGcard : Nat.card CG = 19 := by
    have hCGdvd : Nat.card CG ∣ 19 := by
      let g : Equiv.Perm X := ((u : J) : P)
      have hgS : ((u : J) : P) ∈ (S : Subgroup P) := by
        rw [← hRS]
        exact Subgroup.mem_map_of_mem
          J.subtype u.prop
      have hCGle :
          CG ≤ Subgroup.centralizer
            ({((u : J) : P)} : Set P) := by
        intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc ((u : J) : P) hgS).symm
      rw [← hglobalCucard]
      exact Subgroup.card_dvd_of_le hCGle
    have hSdvd : 19 ∣ Nat.card CG := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le hSleCG
    exact Nat.dvd_antisymm hCGdvd hSdvd
  have hNGcard : Nat.card NG = 342 :=
    card_of_relindex_nineteen CG NG
      (Subgroup.centralizer_le_normalizer (S : Set P)) hCGcard 18 hrG
  have hCGS : CG = (S : Subgroup P) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hSleCG
    rw [hCGcard, hScard]
  let g : Equiv.Perm X := ((u : J) : P)
  have hgorder : orderOf g = 19 := by
    calc
      orderOf g = orderOf ((u : J) : P) :=
        Subgroup.orderOf_coe _
      _ = 19 := huorderP
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 19 := by
    rw [← hgcycle.orderOf, hgorder]
  let F : Set X := MulAction.fixedBy X ((u : J) : P)
  have hFcard : Fintype.card F = 3 := by
    rw [Degree15.card_fixedBy_subgroup_perm,
      hcard, hgsupport]
  have hrangeSubsetF :
      Set.range e ⊆ F := by
    intro x hx
    change ((u : J) : P) • x = x
    exact
      (mem_fixingSubgroup_iff P).mp (u : J).prop
        x hx
  have hFrange : F = Set.range e := by
    symm
    apply Set.eq_of_subset_of_ncard_le hrangeSubsetF
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      hFcard, hecard]
  have hfixedPoints :
      MulAction.fixedPoints S X = F := by
    apply Set.Subset.antisymm
    · intro x hx
      have hgS : ((u : J) : P) ∈ (S : Subgroup P) := by
        rw [← hRS]
        exact Subgroup.mem_map_of_mem
          J.subtype u.prop
      exact MulAction.mem_fixedPoints.mp hx
        ⟨((u : J) : P), hgS⟩
    · intro x hx
      rw [hFrange] at hx
      rw [MulAction.mem_fixedPoints]
      intro q
      have hqR : (q : P) ∈ R := by
        rw [hRS]
        exact q.prop
      obtain ⟨t, ht, hqt⟩ :=
        Subgroup.mem_map.mp hqR
      have htfix :=
        (mem_fixingSubgroup_iff P).mp t.prop
          x hx
      simpa [Subgroup.smul_def] using
        hqt ▸ htfix
  have hpreserve :
      ∀ n : NG, ∀ x : X, x ∈ F →
        ((n : NG) : P) • x ∈ F := by
    intro n x hx
    rw [← hfixedPoints] at hx ⊢
    rw [MulAction.mem_fixedPoints] at hx ⊢
    intro q
    have hconj :
        ((n : NG) : P)⁻¹ * (q : S) *
            ((n : NG) : P) ∈ (S : Subgroup P) := by
      exact
        (Subgroup.mem_normalizer_iff''.mp n.prop
          (q : S)).mp q.prop
    let q' : S :=
      ⟨((n : NG) : P)⁻¹ * (q : S) *
          ((n : NG) : P), hconj⟩
    have hcommute :
        ((q : S) : P) * ((n : NG) : P) =
          ((n : NG) : P) * ((q' : S) : P) := by
      change
        ((q : S) : P) * ((n : NG) : P) =
          ((n : NG) : P) *
            (((n : NG) : P)⁻¹ * ((q : S) : P) *
              ((n : NG) : P))
      simp [mul_assoc]
    calc
      (q : S) • (((n : NG) : P) • x) =
          (((q : S) : P) * ((n : NG) : P)) • x :=
        (mul_smul ((q : S) : P) ((n : NG) : P) x).symm
      _ = (((n : NG) : P) * (q' : S)) • x :=
        congrArg (fun z : P => z • x) hcommute
      _ = ((n : NG) : P) • ((q' : S) • x) :=
        mul_smul _ _ _
      _ = ((n : NG) : P) • x := by
        rw [hx q']
  let ρ : NG →* Equiv.Perm F :=
    { toFun := fun n =>
        Equiv.Perm.subtypePermOfFintype
          (((n : NG) : P) : Equiv.Perm X)
          (hpreserve n)
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
  have hkerRho :
      ρ.ker = J.comap NG.subtype := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hn
      rw [mem_fixingSubgroup_iff P]
      intro x hx
      have hxF : x ∈ F := by
        rw [hFrange]
        exact hx
      let xF : F := ⟨x, hxF⟩
      have hnx :=
        congrArg (fun v : Equiv.Perm F => v xF) hn
      have hnx' := congrArg Subtype.val hnx
      simpa [ρ, xF,
        Equiv.Perm.subtypePermOfFintype_apply,
        Subgroup.smul_def, Equiv.Perm.smul_def] using hnx'
    · intro hn
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have hfix :=
        (mem_fixingSubgroup_iff P).mp hn
          x (by
            rw [← hFrange]
            exact x.prop)
      simpa [ρ, Equiv.Perm.subtypePermOfFintype_apply,
        Subgroup.smul_def, Equiv.Perm.smul_def] using hfix
  have hNgComap :
      NG.comap J.subtype = NJ := by
    have hnormalizerComap :=
      Subgroup.comap_normalizer_eq_of_le_range
        (H := (S : Subgroup P)) hSleRange
    simpa only [NG, NJ, hScomap] using
      hnormalizerComap
  let swapComap :
      J.comap NG.subtype ≃*
        NG.comap J.subtype :=
    { toFun := fun a =>
        (⟨(⟨a.1.1, a.prop⟩ : J), a.1.prop⟩ :
          NG.comap J.subtype)
      invFun := fun b =>
        (⟨(⟨b.1.1, b.prop⟩ : NG), b.1.prop⟩ :
          J.comap NG.subtype)
      left_inv := by
        intro a
        rfl
      right_inv := by
        intro b
        rfl
      map_mul' := by
        intro a b
        rfl }
  have hkerCard : Nat.card ρ.ker = 57 := by
    rw [hkerRho]
    calc
      Nat.card (J.comap NG.subtype) =
          Nat.card (NG.comap J.subtype) :=
        Nat.card_congr swapComap.toEquiv
      _ = Nat.card NJ := by rw [hNgComap]
      _ = 57 := hNJcard
  have hrhoRangeCard : Nat.card ρ.range = 6 := by
    have hkerIndexCard := ρ.ker.index_mul_card
    rw [hkerCard] at hkerIndexCard
    have hkerIndex : ρ.ker.index = 6 := by
      rw [hNGcard] at hkerIndexCard
      omega
    rw [← Subgroup.index_ker, hkerIndex]
  let η : NG →* MulAut S :=
    S.normalizerMonoidHom
  have hηrangeCard : Nat.card η.range = 18 := by
    have hrangeEq :
        CG.relIndex NG =
          Nat.card S.normalizerMonoidHom.range := by
      change
        (Subgroup.centralizer (S : Set P)).relIndex
            (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range
      rw [Subgroup.relIndex, ← Subgroup.index_ker,
        S.normalizerMonoidHom_ker]
      simp only [S.coe_coe]
    change rG = Nat.card S.normalizerMonoidHom.range at hrangeEq
    rw [hrG] at hrangeEq
    simpa only [η] using hrangeEq.symm
  have hMulAutCard : Nat.card (MulAut S) = 18 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (show Nat.Prime 19 by norm_num)]
  have hηrangeTop :
      η.range = (⊤ : Subgroup (MulAut S)) := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hMulAutCard,
      hηrangeCard]
  have hηsurjective : Function.Surjective η := by
    rw [← MonoidHom.range_eq_top]
    exact hηrangeTop
  have hkerEtaRho : η.ker ≤ ρ.ker := by
    rw [hkerRho]
    intro n hn
    have hnCG : ((n : NG) : P) ∈ CG := by
      change ((n : NG) : P) ∈
        Subgroup.centralizer (S : Set P)
      have hn' : n ∈ S.normalizerMonoidHom.ker := by
        simpa only [η] using hn
      rw [S.normalizerMonoidHom_ker] at hn'
      exact hn'
    rw [hCGS] at hnCG
    change ((n : NG) : P) ∈ J
    obtain ⟨j, hj⟩ := hSleRange hnCG
    rw [← hj]
    exact j.prop
  letI : IsCyclic (ZMod (Nat.card S))ˣ := by
    rw [hScard]
    exact ZMod.isCyclic_units_prime (by norm_num)
  letI : IsCyclic (MulAut S) :=
    isCyclic_of_surjective
      (IsCyclic.mulAutMulEquiv S).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv S).symm.surjective
  exact
    CyclicThreePointObstruction.false_of_cyclic_factor_range_card_six
      NG (MulAut S) F η hηsurjective ρ hkerEtaRho
        hFcard hrhoRangeCard

theorem classification_of_five_transitive_of_card_eq_twentyTwo
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 22)
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
    alternatingGroup_le_of_five_transitive_of_card_eq_twentyTwo
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree22

end CFSG
