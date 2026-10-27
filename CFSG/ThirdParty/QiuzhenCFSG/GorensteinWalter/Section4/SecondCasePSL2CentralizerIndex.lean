module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (9): the PSL₂ centralizer index `|M : H ∩ M| = q · k'`

The source's equation-(10) line
`|G : H| = |H : H ∩ M|⁻¹ |M : H ∩ M| |G : M| = (u p₀)⁻¹ q k' |G : M|`
needs the index `|M : H ∩ M| = q · k'`, where `q = |K|` and `k'` is the odd
member of `(q ± 1)/2`.  This module derives it without assuming `Z(E) = 1`:

* `H ∩ M = C_M(t)` (`c.H_eq_centralizer`);
* `|M : C_M(t)| = |E : C_E(t)|` from the landed factorization
  `M = E · C_M(t)` (`secondCase_M_eq_component_sup_centralizer`) and the
  cardinal part of the second isomorphism theorem (a normal subgroup
  generating the ambient group with a subgroup gives that subgroup the
  index of its intersection with the normal subgroup);
* `|E : C_E(t)| = |E/Z(E) : C_{E/Z(E)}(t̄)|`: the quotient map
  `E → E/Z(E)` is surjective with kernel the center, which lies in
  `C_E(t)`; the centralizers correspond because `t` is an involution and
  `Z(E)` has odd order (`Subgroup.index_map_eq`);
* `|E/Z(E) : C(t̄)| = q · k'` from the PSL₂ order formula
  `|PSL₂(K)| = q(q² − 1)/2` (`psl2_card_formula`), the exact
  involution-centralizer cardinal `|C(t̄)| = 2·|T|` of
  `SecondCasePSL2QuotientTorusCard` (the torus `T` through `t̄` of even
  order `(q ± 1)/2`), and the complementary-half arithmetic
  `2|T| · 2k' = q² − 1`.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

namespace CFSG.GorensteinWalter

universe u

/-! ## Second isomorphism theorem (cardinal part) -/

/-- If a normal subgroup `E` generates the whole group with a subgroup `C`,
then `C` has the same index as `E ∩ C` in `E`.  This is the cardinal part
of the second isomorphism theorem for the non-normal factor `C`. -/
private lemma index_eq_index_of_normal_sup_local
    {G : Type u} [Group G] [Finite G]
    (E C : Subgroup G) (hE : E.Normal) (hEC : E ⊔ C = ⊤) :
    C.index = ((E ⊓ C).subgroupOf E).index := by
  classical
  let : E.Normal := hE
  let b : G ⧸ C := QuotientGroup.mk (1 : G)
  have horbit : MulAction.orbit E b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    have hg : g ∈ E ⊔ C := by
      rw [hEC]
      trivial
    rcases ((@Subgroup.mem_sup_of_normal_left G _ E C hE g).mp hg) with ⟨e, he, c, hc, rfl⟩
    refine ⟨⟨e, he⟩, ?_⟩
    change (e : G) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
      (QuotientGroup.mk (e * c : G) : G ⧸ C)
    have hsmul : (e : G) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
        QuotientGroup.mk (e * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simpa using hc
  have hstab : MulAction.stabilizer E b = C.subgroupOf E := by
    ext e
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf]
    change (e : E) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
      (QuotientGroup.mk (1 : G) : G ⧸ C) ↔ (e : G) ∈ C
    have hsmul : (e : E) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
        QuotientGroup.mk ((e : G) * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simp
  have hindex : (MulAction.stabilizer E b).index = C.index := by
    rw [MulAction.index_stabilizer]
    rw [horbit, Set.ncard_univ]
    rfl
  rw [← hindex]
  rw [hstab, ← Subgroup.inf_subgroupOf_right, inf_comm]

/-! ## Arithmetic of the complementary halves -/

private lemma odd_card_field {K : Type u} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  rcases hodd with ⟨p, n, hp, hpOdd, hn, hcard⟩
  rw [hcard]
  exact hpOdd.pow

/-- `(n / 2) * 2 = n` for even `n`. -/
private lemma two_mul_div_two_of_even {n : ℕ} (hn : Even n) : (n / 2) * 2 = n := by
  rcases hn with ⟨k, hk⟩
  omega

/-- With `a` the even half and `b` the odd half of `(q ± 1)/2` for odd `q`,
one has `2a · 2b = q² − 1`. -/
private lemma complementary_half_product {q a b : ℕ} (hq : Odd q)
    (ha : a = (q - 1) / 2 ∨ a = (q + 1) / 2)
    (hb : b = (q - 1) / 2 ∨ b = (q + 1) / 2)
    (haEven : Even a) (hbOdd : Odd b) :
    2 * a * (2 * b) = q ^ 2 - 1 := by
  rcases ha with ha1 | ha2
  · rcases hb with hb1 | hb2
    · exfalso
      have hEq : a = b := ha1.trans hb1.symm
      have hEven' : Even b := by simpa [hEq] using haEven
      rcases hbOdd with ⟨k, hk⟩
      rcases hEven' with ⟨l, hl⟩
      omega
    · have h2a : 2 * a = q - 1 := by
        rw [ha1, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m
          omega)
      have h2b : 2 * b = q + 1 := by
        rw [hb2, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m + 1
          omega)
      calc
        2 * a * (2 * b) = (q - 1) * (q + 1) := by rw [h2a, h2b]
        _ = q ^ 2 - 1 := by
          rcases hq with ⟨m, hm⟩
          rw [hm]
          have h : (2 * m + 1) ^ 2 = 2 * m * (2 * m + 2) + 1 := by ring
          calc
            (2 * m) * (2 * m + 2) = (2 * m * (2 * m + 2) + 1) - 1 := by omega
            _ = (2 * m + 1) ^ 2 - 1 := by rw [h]
  · rcases hb with hb1 | hb2
    · have h2a : 2 * a = q + 1 := by
        rw [ha2, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m + 1
          omega)
      have h2b : 2 * b = q - 1 := by
        rw [hb1, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m
          omega)
      calc
        2 * a * (2 * b) = (q + 1) * (q - 1) := by rw [h2a, h2b]
        _ = q ^ 2 - 1 := by
          rcases hq with ⟨m, hm⟩
          rw [hm]
          have h : (2 * m + 1) ^ 2 = 2 * m * (2 * m + 2) + 1 := by ring
          calc
            (2 * m + 2) * (2 * m) = 2 * m * (2 * m + 2) := by ring
            _ = (2 * m * (2 * m + 2) + 1) - 1 := by omega
            _ = (2 * m + 1) ^ 2 - 1 := by rw [h]
    · exfalso
      have hEq : a = b := ha2.trans hb2.symm
      have hEven' : Even b := by simpa [hEq] using haEven
      rcases hbOdd with ⟨k, hk⟩
      rcases hEven' with ⟨l, hl⟩
      omega

/-! ## The centralizer-index theorem -/

/-- Equation (9): with `k'` the odd member of `(q ± 1)/2`, the relative
index `|M : H ∩ M|` of the second-case maximal subgroup equals `q · k'`.

`qt` is the quotient torus data of `SecondCasePSL2QuotientTorusCard` (the
cyclic torus of `E/Z(E)` through the image of `t`, of even order
`(q ± 1)/2`); `hk'` fixes `k'` to one of the two halves and `hodd'` selects
the odd one.  No `Z(E) = 1` hypothesis is needed: the odd center is
factored out by the quotient transport. -/
public theorem secondCase_psl2_centralizer_index
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (qt : SecondCasePSL2QuotientTorusCard d K)
    {k' : ℕ}
    (hk' : k' = (Nat.card K - 1) / 2 ∨ k' = (Nat.card K + 1) / 2)
    (hodd' : Odd k') :
    (c.H ⊓ w.M).relIndex w.M = Nat.card K * k' := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  let tQ : Q := q tE
  let CE : Subgroup G := centralizerIn d.E c.t
  let CQ : Subgroup Q := Subgroup.centralizer ({tQ} : Set Q)
  let E0 : Subgroup (↥w.M) := d.E.subgroupOf w.M
  let C0 : Subgroup (↥w.M) := (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M
  -- step 1: `H ∩ M = C_M(t)`
  have hHM : (c.H ⊓ w.M).relIndex w.M = C0.index := by
    calc
      (c.H ⊓ w.M).relIndex w.M = ((c.H ⊓ w.M).subgroupOf w.M).index := rfl
      _ = ((Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M).index := by
        rw [c.H_eq_centralizer]
      _ = C0.index := rfl
  -- step 2: `|M : C_M(t)| = |E : C_E(t)|` (from `M = E · C_M(t)`)
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro h k hh hk
    exact d.E_normal.2 k hk h hh
  have hE0top : E0 ⊔ C0 = ⊤ := by
    have hM : w.M = d.E ⊔ (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) :=
      secondCase_M_eq_component_sup_centralizer w d
    have hsub : (d.E ⊔ (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M)).subgroupOf w.M = ⊤ := by
      rw [← hM]
      exact Subgroup.subgroupOf_self w.M
    simpa [E0, C0, Subgroup.subgroupOf_sup d.E_component.1 inf_le_right] using hsub
  have hIdx0 : C0.index = ((E0 ⊓ C0).subgroupOf E0).index :=
    index_eq_index_of_normal_sup_local E0 C0 hE0normal hE0top
  have hE0C0 : E0 ⊓ C0 = CE.subgroupOf w.M := by
    ext x
    simp [E0, C0, CE, centralizerIn, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
  have hIdxE : ((E0 ⊓ C0).subgroupOf E0).index = (CE.subgroupOf d.E).index := by
    calc
      ((E0 ⊓ C0).subgroupOf E0).index = (E0 ⊓ C0).relIndex E0 := rfl
      _ = (CE.subgroupOf w.M).relIndex (d.E.subgroupOf w.M) := by rw [hE0C0]
      _ = CE.relIndex d.E := Subgroup.relIndex_subgroupOf (hKL := d.E_component.1)
      _ = (CE.subgroupOf d.E).index := rfl
  -- step 3: quotient transport `|E : C_E(t)| = |E/Z(E) : C(t̄)|`
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective (Subgroup.center d.E)
  have hqker : q.ker = Subgroup.center d.E := QuotientGroup.ker_mk' (N := Subgroup.center d.E)
  have hZleCE : q.ker ≤ (CE.subgroupOf d.E) := by
    rw [hqker]
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    unfold CE centralizerIn
    rw [Subgroup.mem_inf]
    constructor
    · exact z.2
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with rfl
      have hzcomm : tE * z = z * tE := (Subgroup.mem_center_iff.mp hz) tE
      have hct : c.t * (z : G) = (z : G) * c.t := by
        have h := congrArg Subtype.val hzcomm
        simpa [tE] using h
      exact hct
  have hIdxMap : ((CE.subgroupOf d.E).map q).index = (CE.subgroupOf d.E).index :=
    Subgroup.index_map_eq (H := CE.subgroupOf d.E) hqsurj hZleCE
  have hmapCQ : (CE.subgroupOf d.E).map q = CQ := by
    ext y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with rfl
      have hxCE : (x : G) ∈ CE := Subgroup.mem_subgroupOf.mp hx
      have hxcommE : tE * x = x * tE := by
        apply Subtype.ext
        unfold CE centralizerIn at hxCE
        rw [Subgroup.mem_inf] at hxCE
        rw [Subgroup.mem_centralizer_iff] at hxCE
        have hct : c.t * (x : G) = (x : G) * c.t := hxCE.2 c.t (by simp)
        simpa [tE] using hct
      calc
        tQ * q x = q (tE * x) := (map_mul q tE x).symm
        _ = q (x * tE) := by rw [hxcommE]
        _ = q x * tQ := map_mul q x tE
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy
      rcases hqsurj y with ⟨x, rfl⟩
      have hxcommQ : q (x * tE) = q (tE * x) := by
        have h' : tQ * q x = q x * tQ := hy tQ (by simp)
        calc
          q (x * tE) = q x * tQ := (map_mul q x tE).symm
          _ = tQ * q x := h'.symm
          _ = q (tE * x) := map_mul q tE x
      have hqcomm : q (x * tE * (tE * x)⁻¹) = 1 := by
        rw [map_mul, map_inv, hxcommQ]
        simp
      have hzmem : (x * tE * (tE * x)⁻¹) ∈ Subgroup.center d.E :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center d.E)
          (x := x * tE * (tE * x)⁻¹)).mp hqcomm
      let z : d.E := x * tE * (tE * x)⁻¹
      have hz : z ∈ Subgroup.center d.E := hzmem
      have hztE : tE * z = z * tE := (Subgroup.mem_center_iff.mp hz) tE
      have hxzt : x * tE * x⁻¹ = z * tE := by
        calc
          x * tE * x⁻¹ = (x * tE * (tE * x)⁻¹) * tE := by group
          _ = z * tE := rfl
      have h1 : (x * tE * x⁻¹) * (x * tE * x⁻¹) = 1 := by
        have htE2 : tE * tE = 1 := by
          apply Subtype.ext
          simpa [tE, pow_two] using c.t_involution.2
        calc
          (x * tE * x⁻¹) * (x * tE * x⁻¹) = x * (tE * tE) * x⁻¹ := by group
          _ = x * 1 * x⁻¹ := by rw [htE2]
          _ = 1 := by simp
      have h2 : (z * tE) * (z * tE) = 1 := by
        rwa [hxzt] at h1
      have hzsq : z * z = 1 := by
        have h3 : z * z * (tE * tE) = 1 := by
          have h3' : (z * tE) * (z * tE) = z * z * (tE * tE) := by
            calc
              (z * tE) * (z * tE) = z * (tE * z) * tE := by group
              _ = z * (z * tE) * tE := by rw [hztE]
              _ = z * z * (tE * tE) := by group
          rwa [h3'] at h2
        have htE2 : tE * tE = 1 := by
          apply Subtype.ext
          simpa [tE, pow_two] using c.t_involution.2
        rw [htE2] at h3
        simpa using h3
      have hz1 : z = 1 := by
        let zZ : Subgroup.center d.E := ⟨z, hz⟩
        have hzZ2 : zZ ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_pow, pow_two] using hzsq
        have hoddZ : Odd (Nat.card (Subgroup.center d.E)) := d.center_odd
        have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center d.E)) :=
          Nat.coprime_two_left.mpr hoddZ
        have hzZ1 := eq_one_of_sq_eq_one_of_coprime_two (G := Subgroup.center d.E)
          hcop hzZ2
        exact congrArg Subtype.val hzZ1
      have hxcommE : x * tE = tE * x := by
        have h' : x * tE * x⁻¹ = tE := by
          calc
            x * tE * x⁻¹ = z * tE := hxzt
            _ = 1 * tE := by rw [hz1]
            _ = tE := by simp
        calc
          x * tE = (x * tE * x⁻¹) * x := by group
          _ = tE * x := by rw [h']
      rw [Subgroup.mem_map]
      refine ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      unfold CE centralizerIn
      rw [Subgroup.mem_inf]
      constructor
      · exact x.2
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases hy with rfl
        have hxcommG : c.t * (x : G) = (x : G) * c.t := by
          have h := congrArg Subtype.val hxcommE
          simpa [tE] using h.symm
        exact hxcommG
  -- step 4: `|E/Z(E) : C(t̄)| = q · k'`
  have hqodd : Odd (Nat.card K) := odd_card_field hK
  have hQcard : Nat.card Q = Nat.card (PSL2 K) := Nat.card_congr e.some.toEquiv
  have hQcard' : Nat.card Q = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    rw [hQcard]
    exact psl2_card_formula K hK
  have hCQcard : Nat.card (Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
        Set (d.E ⧸ Subgroup.center d.E))) = 2 * Nat.card qt.T :=
    qt.T_centralizer_card
  have hIdxQ : CQ.index * Nat.card CQ = Nat.card Q := by
    have h := Subgroup.card_mul_index (H := CQ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h4 : 2 * Nat.card qt.T * (2 * k') = Nat.card K ^ 2 - 1 :=
    complementary_half_product hqodd qt.T_card hk' qt.T_even hodd'
  have hq4 : Nat.card K * (Nat.card K ^ 2 - 1) =
      2 * (2 * Nat.card K * Nat.card qt.T * k') := by
    rw [← h4]
    ring
  have hQcard'' : Nat.card Q = 2 * Nat.card K * Nat.card qt.T * k' := by
    calc
      Nat.card Q = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := hQcard'
      _ = (2 * (2 * Nat.card K * Nat.card qt.T * k')) / 2 := by rw [hq4]
      _ = 2 * Nat.card K * Nat.card qt.T * k' := by omega
  have hIdxK : CQ.index = Nat.card K * k' := by
    have h := hIdxQ
    rw [hCQcard, hQcard''] at h
    have hTne : 2 * Nat.card qt.T ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Nat.card_pos.ne')
    exact mul_right_cancel₀ hTne (by
      calc
        CQ.index * (2 * Nat.card qt.T) = 2 * Nat.card K * Nat.card qt.T * k' := h
        _ = (Nat.card K * k') * (2 * Nat.card qt.T) := by ring)
  -- assemble
  exact calc
    (c.H ⊓ w.M).relIndex w.M = C0.index := hHM
    _ = ((E0 ⊓ C0).subgroupOf E0).index := hIdx0
    _ = (CE.subgroupOf d.E).index := hIdxE
    _ = ((CE.subgroupOf d.E).map q).index := hIdxMap.symm
    _ = CQ.index := by rw [hmapCQ]
    _ = Nat.card K * k' := hIdxK

/-- The odd half `k'` of `(q ± 1)/2` paired with the even-order torus `T`:
since `|T|` is the even half (`qt.T_even`, `qt.T_card`), the other half is odd
and the two halves multiply to `(q² − 1)/4`, i.e. `2|T| · 2k' = q² − 1`.
This selects the `k'` of equation (9) without a choice on the caller side. -/
public theorem secondCase_psl2_odd_centralizer_index_half
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (qt : SecondCasePSL2QuotientTorusCard d K) :
    ∃ k' : ℕ, (k' = (Nat.card K - 1) / 2 ∨ k' = (Nat.card K + 1) / 2) ∧
      Odd k' ∧ 2 * Nat.card qt.T * (2 * k') = Nat.card K ^ 2 - 1 := by
  classical
  have hq : Odd (Nat.card K) := odd_card_field qt.primePower
  rcases qt.T_card with hT | hT
  · have hodd : Odd ((Nat.card K + 1) / 2) := by
      have hTeven2 : Even ((Nat.card K - 1) / 2) := by
        rw [← hT]
        simpa [Nat.card_eq_fintype_card] using qt.T_even
      rcases hq with ⟨m, hm⟩
      rcases hTeven2 with ⟨k, hk⟩
      rw [hm] at hk
      have hm2 : m = 2 * k := by omega
      have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [hm, hdiv]
      use k
      omega
    refine ⟨(Nat.card K + 1) / 2, Or.inr rfl, hodd, ?_⟩
    exact complementary_half_product hq (Or.inl hT) (Or.inr rfl) qt.T_even hodd
  · have hodd : Odd ((Nat.card K - 1) / 2) := by
      have hTeven2 : Even ((Nat.card K + 1) / 2) := by
        rw [← hT]
        simpa [Nat.card_eq_fintype_card] using qt.T_even
      rcases hq with ⟨m, hm⟩
      rcases hTeven2 with ⟨k, hk⟩
      rw [hm] at hk
      have hm1 : m + 1 = 2 * k := by omega
      have hdiv : (2 * m + 1 - 1) / 2 = m := by omega
      rw [hm, hdiv]
      use k - 1
      omega
    refine ⟨(Nat.card K - 1) / 2, Or.inl rfl, hodd, ?_⟩
    exact complementary_half_product hq (Or.inr hT) (Or.inl rfl) qt.T_even hodd

end CFSG.GorensteinWalter
