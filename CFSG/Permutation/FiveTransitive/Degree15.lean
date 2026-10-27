module

public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.PermCentralizer
public import CFSG.Permutation.FiveTransitive.OrbitBounds
public import Mathlib.GroupTheory.Transfer
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.Degree15

open MulAction SubMulAction Subgroup

private theorem exists_controlled_conjugator
    (P : Subgroup (Equiv.Perm (Fin 15)))
    (h5 : ∀ a b : Fin 5 → Fin 15,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 15)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 15)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 15)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 15)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 15)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple15 FiniteChecks.targetTuple15
    FiniteChecks.sourceTuple15_injective
    FiniteChecks.targetTuple15_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiniteChecks.sourceTuple15, FiniteChecks.targetTuple15,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [FiniteChecks.sourceTuple15, FiniteChecks.targetTuple15,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [FiniteChecks.sourceTuple15, FiniteChecks.targetTuple15,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [FiniteChecks.sourceTuple15, FiniteChecks.targetTuple15,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [FiniteChecks.sourceTuple15, FiniteChecks.targetTuple15,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)

private theorem five_le_image_of_controlled_conjugator
    (p : Equiv.Perm (Fin 15))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 15)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply FiniteChecks.five_le_of_ne_zero_one_two_three_four15
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem alternatingGroup_le_of_sevenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 15)))
    (h5 : ∀ a b : Fin 5 → Fin 15,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle15 ∈ P) :
    alternatingGroup (Fin 15) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 15 := (p : Equiv.Perm (Fin 15)) 4
  let y : Fin 15 := (p : Equiv.Perm (Fin 15)) 5
  let z : Fin 15 := (p : Equiv.Perm (Fin 15)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 15)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 15)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 15)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 15) :=
    (p : Equiv.Perm (Fin 15)) * FiniteChecks.sevenCycle15 *
      (p : Equiv.Perm (Fin 15))⁻¹
  have hh : h = FiniteChecks.comparisonCycle15 x y z := by
    change
      (p : Equiv.Perm (Fin 15)) * FiniteChecks.sevenCycle15 *
          (p : Equiv.Perm (Fin 15))⁻¹ =
        FiniteChecks.comparisonCycle15 x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle15,
      Helpers.permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle15, x, y, z,
      hp0, hp1, hp2, hp3]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure15
      x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle15,
            FiniteChecks.comparisonCycle15 x y z} :
            Set (Equiv.Perm (Fin 15))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rw [← hh]
      exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 15) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

private theorem alternatingGroup_le_of_tripleSwap_mem
    (P : Subgroup (Equiv.Perm (Fin 15)))
    (h5 : ∀ a b : Fin 5 → Fin 15,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.tripleSwap15 ∈ P) :
    alternatingGroup (Fin 15) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 15 := (p : Equiv.Perm (Fin 15)) 4
  let y : Fin 15 := (p : Equiv.Perm (Fin 15)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 15)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 15) :=
    (p : Equiv.Perm (Fin 15)) * FiniteChecks.tripleSwap15 *
      (p : Equiv.Perm (Fin 15))⁻¹
  have hh : h = FiniteChecks.comparisonTripleSwap15 x y := by
    change
      (p : Equiv.Perm (Fin 15)) * FiniteChecks.tripleSwap15 *
          (p : Equiv.Perm (Fin 15))⁻¹ =
        FiniteChecks.comparisonTripleSwap15 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.tripleSwap15,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm]
    simp [FiniteChecks.comparisonTripleSwap15, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.tripleSwap15 *
      (FiniteChecks.comparisonTripleSwap15 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.tripleSwap15_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 15) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 15)))
    (h5 : ∀ a b : Fin 5 → Fin 15,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.doubleThreeCycle15 ∈ P) :
    alternatingGroup (Fin 15) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 15 := (p : Equiv.Perm (Fin 15)) 4
  let y : Fin 15 := (p : Equiv.Perm (Fin 15)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 15)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 15)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 15) :=
    (p : Equiv.Perm (Fin 15)) *
      FiniteChecks.doubleThreeCycle15 *
      (p : Equiv.Perm (Fin 15))⁻¹
  have hh : h = FiniteChecks.comparisonDoubleThreeCycle15 x y := by
    change
      (p : Equiv.Perm (Fin 15)) *
            FiniteChecks.doubleThreeCycle15 *
          (p : Equiv.Perm (Fin 15))⁻¹ =
        FiniteChecks.comparisonDoubleThreeCycle15 x y
    rw [← Equiv.permCongr_eq_mul,
      FiniteChecks.doubleThreeCycle15, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm]
    simp [FiniteChecks.comparisonDoubleThreeCycle15, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.doubleThreeCycle15 *
      (FiniteChecks.comparisonDoubleThreeCycle15 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.doubleThreeCycle15_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 15) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_cycleType_eq
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 15))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 15)),
        (∀ a b : Fin 5 → Fin 15,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 15) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 15 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 15) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 15 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 15)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 15,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 15) :=
      e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      exact Subgroup.mem_map_of_mem
        e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) =
          e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 15) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 15) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 15) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

private theorem alternatingGroup_le_of_prime_order_support_le_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hsupport : g.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  have hgNe : g ≠ 1 := by
    intro hgone
    rw [hgone, orderOf_one] at hgorder
    exact hp.ne_one hgorder.symm
  by_cases hsmall : g.support.card ≤ 5
  · exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) hg hgNe hsmall
  have hsupp : g.support.card = 6 ∨ g.support.card = 7 := by
    omega
  let e₀ : X ≃ Fin 15 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 15) := e₀.permCongr g
  have hg₁order : orderOf g₁ = p := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = p := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    exact hp
  have hsupportMap :
      g₁.support = g.support.map e₀.toEmbedding := by
    ext y
    simp [g₁, Equiv.Perm.mem_support, Equiv.permCongr_apply]
    constructor
    · intro h h'
      apply h
      rw [h', e₀.apply_symm_apply]
    · intro h h'
      apply h
      apply e₀.injective
      simpa using h'
  have hg₁support : g₁.support.card = g.support.card := by
    rw [hsupportMap, Finset.card_map]
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hg₁prime
  have hsum := g₁.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    hg₁order, hg₁support] at hsum
  rcases hsupp with hsupp | hsupp
  · have hp_le : p ≤ 6 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · have hm' : m + 1 = 3 := by omega
      have hcycle :
          g₁.cycleType =
            FiniteChecks.tripleSwap15.cycleType := by
        rw [hm, hg₁order, hm',
          FiniteChecks.tripleSwap15_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg FiniteChecks.tripleSwap15
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_tripleSwap_mem
    · have hm' : m + 1 = 2 := by omega
      have hcycle :
          g₁.cycleType =
            FiniteChecks.doubleThreeCycle15.cycleType := by
        rw [hm, hg₁order, hm',
          FiniteChecks.doubleThreeCycle15_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg FiniteChecks.doubleThreeCycle15
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_doubleThreeCycle_mem
    · omega
  · have hp_le : p ≤ 7 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · omega
    · omega
    · omega
    · have hm' : m + 1 = 1 := by omega
      have hg₁cycle : g₁.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm,
          Multiset.card_replicate, hm']
      have hcycle :
          g₁.cycleType =
            FiniteChecks.sevenCycle15.cycleType := by
        rw [hg₁cycle.cycleType,
          FiniteChecks.sevenCycle15_isCycle.cycleType,
          hg₁support, hsupp,
          FiniteChecks.sevenCycle15_card_support]
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg FiniteChecks.sevenCycle15
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_sevenCycle_mem

private theorem three_point_stabilizer_subsingleton_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5)
    (y z w : SubMulAction.ofFixingSubgroup P s)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Subsingleton ↥
      ((MulAction.stabilizer (fixingSubgroup P s) y ⊓
        MulAction.stabilizer (fixingSubgroup P s) z) ⊓
        MulAction.stabilizer (fixingSubgroup P s) w) := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let M : Subgroup K :=
    (MulAction.stabilizer K y ⊓ MulAction.stabilizer K z) ⊓
      MulAction.stabilizer K w
  rw [← not_nontrivial_iff_subsingleton]
  intro hM
  have hMcard : 1 < Nat.card M :=
    Finite.one_lt_card_iff_nontrivial.mpr hM
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card M) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ :=
    exists_prime_orderOf_dvd_card' p hpdvd
  let g : Equiv.Perm X := (((u : M) : K) : P)
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf (((u : M) : K) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf ((u : M) : K) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = p := hu
  have hgP : g ∈ P := (((u : M) : K) : P).prop
  have hfix :
      ∀ x ∈ s, (((u : M) : K) : P) • x = x :=
    (mem_fixingSubgroup_iff P).mp ((u : M) : K).prop
  have huStabilizers :
      (((u : M) : K) ∈ MulAction.stabilizer K y ∧
        ((u : M) : K) ∈ MulAction.stabilizer K z) ∧
        ((u : M) : K) ∈ MulAction.stabilizer K w := by
    exact Subgroup.mem_inf.mp u.prop
  have hyfix :
      (((u : M) : K) : P) • (y : X) = y :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.1.1)
  have hzfix :
      (((u : M) : K) : P) • (z : X) = z :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.1.2)
  have hwfix :
      (((u : M) : K) : P) • (w : X) = w :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.2)
  have hyzX : (y : X) ≠ (z : X) :=
    fun h => hyz (Subtype.ext h)
  have hywX : (y : X) ≠ (w : X) :=
    fun h => hyw (Subtype.ext h)
  have hzwX : (z : X) ≠ (w : X) :=
    fun h => hzw (Subtype.ext h)
  let t : Set X :=
    Set.insert (y : X)
      (Set.insert (z : X) (Set.insert (w : X) s))
  have hwNotS : (w : X) ∉ s := w.prop
  have hzNotInsert : (z : X) ∉ Set.insert (w : X) s := by
    intro hz
    change (z : X) = (w : X) ∨ (z : X) ∈ s at hz
    exact hz.elim hzwX z.prop
  have hyNotInsert :
      (y : X) ∉ Set.insert (z : X) (Set.insert (w : X) s) := by
    intro hy
    change
      (y : X) = (z : X) ∨ (y : X) = (w : X) ∨
        (y : X) ∈ s at hy
    exact hy.elim hyzX (fun hy => hy.elim hywX y.prop)
  have htcard : t.ncard = 8 := by
    change
      (Set.insert (y : X)
        (Set.insert (z : X) (Set.insert (w : X) s))).ncard = 8
    calc
      _ =
          (Set.insert (z : X)
            (Set.insert (w : X) s)).ncard + 1 :=
        Set.ncard_insert_of_notMem hyNotInsert
      _ = ((Set.insert (w : X) s).ncard + 1) + 1 :=
        congrArg (fun n => n + 1)
          (Set.ncard_insert_of_notMem hzNotInsert)
      _ = ((s.ncard + 1) + 1) + 1 :=
        congrArg (fun n => (n + 1) + 1)
          (Set.ncard_insert_of_notMem hwNotS)
      _ = 8 := by omega
  have hsuppSubset : (g.support : Set X) ⊆ tᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxt
    change
      x = (y : X) ∨ x = (z : X) ∨ x = (w : X) ∨ x ∈ s at hxt
    rcases hxt with rfl | rfl | rfl | hxs
    · exact Equiv.Perm.mem_support.mp hx hyfix
    · exact Equiv.Perm.mem_support.mp hx hzfix
    · exact Equiv.Perm.mem_support.mp hx hwfix
    · exact Equiv.Perm.mem_support.mp hx (hfix x hxs)
  have htcomplement : tᶜ.ncard = 7 := by
    have htotal := Set.ncard_add_ncard_compl t
    rw [Nat.card_eq_fintype_card, hcard, htcard] at htotal
    omega
  have hsuppCard : g.support.card ≤ 7 := by
    rw [← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hsuppSubset).trans_eq htcomplement
  exact hnotAlt
    (alternatingGroup_le_of_prime_order_support_le_seven
      X P hcard h5 hgP hp hgorder hsuppCard)

private theorem five_point_stabilizer_card_dvd_seven_hundred_twenty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 720 := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 10 := by
    change Nat.card ↥(sᶜ : Set X) = 10
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  let A := Fin 3 ↪ Y
  have hfixed :
      ∀ k : K, k ≠ 1 →
        Nat.card (MulAction.fixedBy A k) = 0 := by
    intro k hk
    rw [Finite.card_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩
    have hfix (i : Fin 3) : k • a i = a i := by
      change (k • a : A) i = a i
      exact congrArg (fun e : A => e i) ha
    have h01 : a (0 : Fin 3) ≠ a (1 : Fin 3) :=
      a.injective.ne (by decide)
    have h02 : a (0 : Fin 3) ≠ a (2 : Fin 3) :=
      a.injective.ne (by decide)
    have h12 : a (1 : Fin 3) ≠ a (2 : Fin 3) :=
      a.injective.ne (by decide)
    let M : Subgroup K :=
      (MulAction.stabilizer K (a (0 : Fin 3)) ⊓
        MulAction.stabilizer K (a (1 : Fin 3))) ⊓
        MulAction.stabilizer K (a (2 : Fin 3))
    letI : Subsingleton M :=
      three_point_stabilizer_subsingleton_of_not_alternating
        X P hcard h5 hnotAlt hs
          (a 0) (a 1) (a 2) h01 h02 h12
    have hkM :
        k ∈ (MulAction.stabilizer K (a (0 : Fin 3)) ⊓
          MulAction.stabilizer K (a (1 : Fin 3))) ⊓
          MulAction.stabilizer K (a (2 : Fin 3)) := by
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact ⟨⟨MulAction.mem_stabilizer_iff.mpr (hfix 0),
        MulAction.mem_stabilizer_iff.mpr (hfix 1)⟩,
        MulAction.mem_stabilizer_iff.mpr (hfix 2)⟩
    let u : M := ⟨k, hkM⟩
    have hu : u = 1 := Subsingleton.elim _ _
    apply hk
    simpa [u] using congrArg (fun v : M => (v : K)) hu
  have hdvd :
      Fintype.card K ∣ Fintype.card A :=
    OrbitBounds.card_group_dvd_card_of_no_nontrivial_fixedPoints
      K A hfixed
  have hYcardF : Fintype.card Y = 10 := by
    rwa [← Nat.card_eq_fintype_card]
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    hYcardF] at hdvd
  norm_num at hdvd
  rwa [Nat.card_eq_fintype_card]

private theorem sylow_centralizer_card_eq_prime_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {p : ℕ} (hp : p.Prime) (hpCases : p = 11 ∨ p = 13)
    (S : Sylow p P) (hScard : Nat.card S = p) :
    Nat.card (Subgroup.centralizer (S : Set P)) = p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = p := hu.trans hScard
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = p := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    exact hp
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      rcases hpCases with rfl | rfl <;> norm_num)
  have hgsupport : g.support.card = p := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) =
          p * (15 - p).factorial := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    rcases hpCases with rfl | rfl <;> norm_num
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
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv :
      Nat.card C ∣ p * (15 - p).factorial := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hpdivC : p ∣ Nat.card C := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le hSC
  have himpossible {q : ℕ} (hq : q.Prime)
      (hqcop : Nat.Coprime q p)
      (hqdvd : q ∣ Nat.card C) : False := by
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨v, hv⟩ :=
      exists_prime_orderOf_dvd_card' q hqdvd
    let w : Equiv.Perm X := (v : P)
    have hworder : orderOf w = q := by
      calc
        orderOf w = orderOf (v : P) := Subgroup.orderOf_coe _
        _ = orderOf v := Subgroup.orderOf_coe _
        _ = q := hv
    have hcomm : Commute w g :=
      congrArg Subtype.val ((v.prop (u : P) u.prop).symm)
    have hcoprime :
        Nat.Coprime (orderOf w) (orderOf g) := by
      rw [hworder, hgorder]
      exact hqcop
    have hsuppSubset :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hgcycle hcomm hcoprime
    have hsuppCard : w.support.card ≤ 4 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 15 - p := by
          rw [Finset.card_compl, hgsupport, hcard]
        _ ≤ 4 := by
          rcases hpCases with rfl | rfl <;> norm_num
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    exact hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) (v : P).prop hwNe (by
          have hvSupport :
              ((v : P) : Equiv.Perm X).support.card ≤ 4 := by
            simpa only [w] using hsuppCard
          omega))
  have hnotTwo : ¬2 ∣ Nat.card C := by
    apply himpossible (q := 2) (by norm_num)
    rcases hpCases with rfl | rfl <;> norm_num
  have hnotThree : ¬3 ∣ Nat.card C := by
    apply himpossible (q := 3) (by norm_num)
    rcases hpCases with rfl | rfl <;> norm_num
  rcases hpCases with rfl | rfl
  · have hCle : Nat.card C ≤ 264 :=
      Nat.le_of_dvd (by norm_num) (by
        norm_num at hCdiv ⊢
        exact hCdiv)
    have hCpos : 0 < Nat.card C := Nat.card_pos
    interval_cases hCeq : Nat.card C
    all_goals try norm_num [hCeq] at hCdiv
    all_goals try norm_num [hCeq] at hpdivC
    all_goals try norm_num [hCeq] at hnotTwo
    all_goals try norm_num [hCeq] at hnotThree
    all_goals norm_num [hCeq]
  · have hCle : Nat.card C ≤ 26 :=
      Nat.le_of_dvd (by norm_num) (by
        norm_num at hCdiv ⊢
        exact hCdiv)
    have hCpos : 0 < Nat.card C := Nat.card_pos
    interval_cases hCeq : Nat.card C
    all_goals try norm_num [hCeq] at hCdiv
    all_goals try norm_num [hCeq] at hpdivC
    all_goals try norm_num [hCeq] at hnotTwo
    all_goals norm_num [hCeq]

theorem sylow_normalizer_constraints_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {p : ℕ} (hp : p.Prime) (hpCases : p = 11 ∨ p = 13)
    (S : Sylow p P) (hScard : Nat.card S = p) :
    let C := Subgroup.centralizer (S : Set P)
    let N := Subgroup.normalizer (S : Set P)
    C.relIndex N ∣ p - 1 ∧
      0 < C.relIndex N ∧
      N.index % p = 1 ∧
      C.relIndex N * N.index * p = Nat.card P := by
  classical
  dsimp
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hCcard : Nat.card C = p :=
    sylow_centralizer_card_eq_prime_of_not_alternating
      X P hcard h5 hnotAlt hp hpCases S hScard
  have hAutCard : Nat.card (MulAut S) = p - 1 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime hp]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ p - 1 := by
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
  have hrDvd : C.relIndex N ∣ p - 1 := by
    rwa [hrEq]
  have hsmod : N.index % p = 1 := by
    change
      (Subgroup.normalizer (S : Set P)).index % p = 1
    have hsylow :
        (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD p] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one p P
    change
      (Subgroup.normalizer (S : Set P)).index % p =
        1 % p at hsylow
    rw [Nat.mod_eq_of_lt hp.one_lt] at hsylow
    exact hsylow
  have hrel : C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S : Set P))
  have hCindex := C.index_mul_card
  rw [hCcard, ← hrel] at hCindex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact ⟨hrDvd,
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero,
    hsmod, hCindex⟩

private theorem sylow_eleven_normalizer_le_centralizer_of_factor_seventy_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 360360 * 72)
    (S : Sylow 11 P) :
    Subgroup.normalizer (S : Set P) ≤
      Subgroup.centralizer (S : Set P) := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 360360 = 11 * 32760 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let d := C.relIndex N
  have hconstraints :
      d ∣ 10 ∧ 0 < d ∧ N.index % 11 = 1 ∧
        d * N.index * 11 = Nat.card P := by
    simpa only [C, N, d] using
      sylow_normalizer_constraints_of_not_alternating
        X P hcard h5 hnotAlt (p := 11) (by norm_num)
          (Or.inl rfl) S hScard
  have hdle : d ≤ 10 :=
    Nat.le_of_dvd (by norm_num) hconstraints.1
  have heq := hconstraints.2.2.2
  rw [hPcard] at heq
  have hdOne : d = 1 := by
    interval_cases d
    all_goals try norm_num at hconstraints
    all_goals try norm_num at heq
    all_goals omega
  exact Subgroup.relIndex_eq_one.mp hdOne

private theorem stabilizer_factor_seventy_two_impossible
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 360360 * 72) :
    False := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S : Sylow 11 P := Sylow.nonempty.some
  have hScard : Nat.card S = 11 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 360360 = 11 * 32760 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 11 := hu.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at huorder
    norm_num at huorder
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
  let s : Set X := (g.support : Set X)ᶜ
  have hs : s.ncard = 4 := by
    have htotal :=
      Set.ncard_add_ncard_compl (g.support : Set X)
    rw [Set.ncard_coe_finset, hgsupport,
      Nat.card_eq_fintype_card, hcard] at htotal
    change ((g.support : Set X)ᶜ).ncard = 4
    omega
  let K : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ := h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  have hfixIndex := hP4.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hKindex : K.index = 32760 := by
    change (fixingSubgroup P s).index = 32760
    omega
  have hKindexCard := K.index_mul_card
  have hKcard : Nat.card K = 792 := by
    rw [hKindex, hPcard] at hKindexCard
    omega
  have huK : ((u : S) : P) ∈ K := by
    change (u : P) ∈ fixingSubgroup P s
    rw [mem_fixingSubgroup_iff]
    intro y hy
    change g y = y
    apply Equiv.Perm.notMem_support.mp
    simpa only [s, Set.mem_compl_iff, Finset.mem_coe] using hy
  have hSK : (S : Subgroup P) ≤ K := by
    intro v hv
    let vS : S := ⟨v, hv⟩
    have hvgen : vS ∈ Subgroup.zpowers u :=
      mem_zpowers_of_prime_card hScard huNe
    obtain ⟨z, hz⟩ :=
      Subgroup.mem_zpowers_iff.mp hvgen
    change (vS : P) ∈ K
    rw [← hz]
    exact K.zpow_mem huK z
  have hnormalizer :
      Subgroup.normalizer (S : Set P) ≤
        Subgroup.centralizer (S : Set P) :=
    sylow_eleven_normalizer_le_centralizer_of_factor_seventy_two
      X P hcard h5 hnotAlt hPcard S
  let f : P →* S := MonoidHom.transferSylow S hnormalizer
  have htransfer (v : S) :
      f (v : P) = v ^ S.index := by
    dsimp only [f]
    exact MonoidHom.transferSylow_eq_pow
      S hnormalizer (v : P) v.prop
  have hfSbijective :
      Function.Bijective (f.domRestrict (S : Subgroup P)) := by
    let e := S.2.powEquiv' S.not_dvd_index
    constructor
    · intro a b hab
      apply e.injective
      change a ^ S.index = b ^ S.index
      rw [← htransfer a, ← htransfer b]
      exact hab
    · intro y
      obtain ⟨v, hv⟩ := e.surjective y
      refine ⟨v, ?_⟩
      change f (v : P) = y
      rw [htransfer]
      exact hv
  let fK : K →* S := f.comp K.subtype
  have hfKsurjective : Function.Surjective fK := by
    intro y
    obtain ⟨v, hv⟩ := hfSbijective.2 y
    let q : K := ⟨(v : P), hSK v.prop⟩
    refine ⟨q, ?_⟩
    change f (v : P) = y
    change f (v : P) = y at hv
    exact hv
  have hfKrange : fK.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hfKsurjective
  have hkerIndex : fK.ker.index = 11 := by
    rw [Subgroup.index_ker, hfKrange, Subgroup.card_top, hScard]
  have hkerIndexCard := fK.ker.index_mul_card
  have hkerCard : Nat.card fK.ker = 72 := by
    rw [hkerIndex, hKcard] at hkerIndexCard
    omega
  have hYcard : Nat.card Y = 11 := by
    change Nat.card ↥(sᶜ : Set X) = 11
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  have hK1 :
      MulAction.IsMultiplyPretransitive K Y 1 :=
    SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
      (m := 1) (n := 5) P s (by omega)
  letI : MulAction.IsPretransitive K Y :=
    MulAction.is_one_pretransitive_iff.mp hK1
  letI : MulAction.IsPreprimitive K Y := by
    apply IsPreprimitive.of_prime_card
    rw [hYcard]
    norm_num
  letI : Nonempty Y := Finite.card_pos_iff.mp (by omega)
  have hKFaithful :
      ∀ q : K, (∀ y : Y, q • y = y) → q = 1 := by
    intro q hq
    apply Subtype.ext
    apply P.subtype_injective
    ext z
    by_cases hz : z ∈ s
    · have hqfix : (q : P) • z = z :=
        (mem_fixingSubgroup_iff P).mp q.prop z hz
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hqfix
    · let y : Y :=
        ⟨z, (SubMulAction.mem_ofFixingSubgroup_iff
          (M := P) (s := s)).mpr hz⟩
      have hy := congrArg Subtype.val (hq y)
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using hy
  have hdichotomy :=
    OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
      K Y hKFaithful fK.ker
  rw [hkerCard, hYcard] at hdichotomy
  norm_num at hdichotomy

private theorem sylow_seven_normalizer_le_centralizer_of_factor_sixty_or_one_forty_four
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (k : ℕ) (hk : k = 60 ∨ k = 144)
    (hPcard : Nat.card P = 360360 * k)
    (S : Sylow 7 P) :
    Subgroup.normalizer (S : Set P) ≤
      Subgroup.centralizer (S : Set P) := by
  classical
  rcases hk with rfl | rfl
  all_goals
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hScard : Nat.card S = 7 := by
      rw [S.card_eq_multiplicity, hPcard]
      rw [show 360360 = 7 * 51480 by norm_num, Nat.mul_assoc,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, (show Nat.Prime 7 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    letI : IsCyclic S := isCyclic_of_prime_card hScard
    letI : IsMulCommutative S := IsCyclic.isMulCommutative
    obtain ⟨u, hu⟩ :=
      IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have huorder : orderOf u = 7 := hu.trans hScard
    let g : Equiv.Perm X := (u : P)
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
    rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
      hgorder] at hsum
    have hsupportLe : g.support.card ≤ 15 := by
      calc
        g.support.card ≤ Fintype.card X :=
          Finset.card_le_univ g.support
        _ = 15 := hcard
    have hmTwo : m + 1 = 2 := by
      have hmLe : m + 1 ≤ 2 := by
        nlinarith
      rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
      · have hsupport : g.support.card ≤ 7 := by
          omega
        exact (hnotAlt
          (alternatingGroup_le_of_prime_order_support_le_seven
            X P hcard h5 (u : P).prop (by norm_num)
              hgorder hsupport)).elim
      · exact hmTwo
    have hcycleType :
        g.cycleType = {7, 7} := by
      rw [hm, hgorder, hmTwo]
      norm_num
    have hcentralizerPerm :
        Nat.card (Subgroup.centralizer
          ({g} : Set (Equiv.Perm X))) = 98 := by
      rw [Equiv.Perm.nat_card_centralizer, hcycleType, hcard]
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
        (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
        hbaseMapMem
    have hcentMapInjective : Function.Injective centMap := by
      intro a b hab
      have hab' := congrArg Subtype.val hab
      change baseMap a = baseMap b at hab'
      exact C.subtype_injective (P.subtype_injective hab')
    have hCdiv98 : Nat.card C ∣ 98 := by
      rw [← hcentralizerPerm]
      exact Subgroup.card_dvd_of_injective
        centMap hcentMapInjective
    have h7divC : 7 ∣ Nat.card C := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le hSC
    have hCdivP : Nat.card C ∣ Nat.card P :=
      Subgroup.card_subgroup_dvd_card C
    rw [hPcard] at hCdivP
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hCle : Nat.card C ≤ 98 :=
      Nat.le_of_dvd (by norm_num) hCdiv98
    have hCcases :
        Nat.card C = 7 ∨ Nat.card C = 14 := by
      interval_cases hCeq : Nat.card C
      all_goals try norm_num [hCeq] at hCdiv98
      all_goals try norm_num [hCeq] at h7divC
      all_goals try norm_num [hCeq] at hCdivP
      all_goals norm_num [hCeq]
    have hAutCard : Nat.card (MulAut S) = 6 := by
      rw [IsCyclic.card_mulAut S, hScard,
        Nat.totient_prime (by norm_num)]
    have hrangeDvd :
        Nat.card S.normalizerMonoidHom.range ∣ 6 := by
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
        C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 6 := by
      rwa [hrEq]
    have hsmod :
        (Subgroup.normalizer (S : Set P)).index % 7 = 1 := by
      have hsylow :
          (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 7] := by
        rw [← S.card_eq_index_normalizer]
        exact card_sylow_modEq_one 7 P
      change
        (Subgroup.normalizer (S : Set P)).index % 7 =
          1 % 7 at hsylow
      norm_num at hsylow
      exact hsylow
    have hrel :
        C.relIndex (Subgroup.normalizer (S : Set P)) *
            (Subgroup.normalizer (S : Set P)).index =
          C.index := by
      simpa only [C] using
        Subgroup.relIndex_mul_index
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
        C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    have hrone :
        C.relIndex (Subgroup.normalizer (S : Set P)) = 1 := by
      rcases hCcases with hCcard | hCcard
      all_goals rw [hCcard] at hCindex
      all_goals
        interval_cases C.relIndex
          (Subgroup.normalizer (S : Set P))
      all_goals try norm_num at hrDvd
      all_goals try norm_num at hCindex
      all_goals omega
    exact Subgroup.relIndex_eq_one.mp hrone

private theorem stabilizer_factor_sixty_or_one_forty_four_impossible
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (k : ℕ) (hk : k = 60 ∨ k = 144)
    (hPcard : Nat.card P = 360360 * k) :
    False := by
  classical
  have hkpos : 0 < k := by
    rcases hk with rfl | rfl <;> norm_num
  have hkNot7 : ¬7 ∣ k := by
    rcases hk with rfl | rfl <;> norm_num
  have hresidualNot7 : ¬7 ∣ 51480 * k := by
    intro h
    have hcases :=
      (show Nat.Prime 7 by norm_num).dvd_mul.mp h
    exact hcases.elim (by norm_num) hkNot7
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 P := Sylow.nonempty.some
  have hScard : Nat.card S = 7 := by
    rw [S.card_eq_multiplicity, hPcard]
    rw [show 360360 = 7 * 51480 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hkpos)),
      Finsupp.add_apply, (show Nat.Prime 7 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hresidualNot7]
    norm_num
  have hnormalizer :
      Subgroup.normalizer (S : Set P) ≤
        Subgroup.centralizer (S : Set P) :=
    sylow_seven_normalizer_le_centralizer_of_factor_sixty_or_one_forty_four
      X P hcard h5 hnotAlt k hk hPcard S
  let f : P →* S := MonoidHom.transferSylow S hnormalizer
  let N : Subgroup P := f.ker
  have hcomplement : N.IsComplement' S :=
    MonoidHom.ker_transferSylow_isComplement' S hnormalizer
  have hNcard : Nat.card N = 51480 * k := by
    have hproduct := hcomplement.card_mul
    rw [hScard, hPcard] at hproduct
    omega
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
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
    rw [hNcard] at hNle
    omega
  have hNtransitive : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hNnotFixed
  letI : MulAction.IsPretransitive N X := hNtransitive
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let x : X := Classical.choice inferInstance
  have hNOrbitCard :
      Fintype.card (MulAction.orbit N x) = 15 := by
    rw [MulAction.orbit_eq_univ N x]
    simpa using hcard
  have hNOrbitStabilizer :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group N x
  have hNcardF : Fintype.card N = 51480 * k := by
    rwa [← Nat.card_eq_fintype_card]
  rw [hNOrbitCard, hNcardF] at hNOrbitStabilizer
  have hNstabilizerCard :
      Fintype.card (MulAction.stabilizer N x) = 3432 * k := by
    omega
  let Px : Subgroup P := MulAction.stabilizer P x
  let Y := SubMulAction.ofStabilizer P x
  have hYcard : Nat.card Y = 14 := by
    have hXcardNat : Nat.card X = 15 := by
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
  have hNstCard : Nat.card Nst = 3432 * k := by
    calc
      Nat.card Nst =
          Nat.card (MulAction.stabilizer N x) :=
        Nat.card_congr
          (OrbitBounds.normalComapStabilizerEquivStabilizer
            P X N x).toEquiv
      _ = Fintype.card (MulAction.stabilizer N x) :=
        Nat.card_eq_fintype_card
      _ = 3432 * k := hNstabilizerCard
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
  rcases hk with rfl | rfl <;> norm_num at hdichotomy

private def degreeFifteenDivisor720 (i : Fin 30) : ℕ :=
  ![1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24,
    30, 36, 40, 45, 48, 60, 72, 80, 90, 120, 144, 180, 240,
    360, 720] i

private def degreeFifteenDivisor12 (i : Fin 6) : ℕ :=
  ![1, 2, 3, 4, 6, 12] i

private def degreeFifteenDivisor10 (i : Fin 4) : ℕ :=
  ![1, 2, 5, 10] i

private def degreeFifteenDivisorIndexPredicate (k : Fin 721) : Prop :=
  k.val ∣ 720 →
    ∃ i : Fin 30, degreeFifteenDivisor720 i = k.val

private theorem degree_fifteen_divisor_720_index :
    ∀ k : Fin 721, degreeFifteenDivisorIndexPredicate k := by
  unfold degreeFifteenDivisorIndexPredicate
  decide +kernel

private def degreeFifteenSmallDivisorIndexPredicate
    (x : Fin 13 × Fin 11) : Prop :=
  (0 < x.1.val → x.1.val ∣ 12 →
      ∃ i : Fin 6, degreeFifteenDivisor12 i = x.1.val) ∧
    (0 < x.2.val → x.2.val ∣ 10 →
      ∃ i : Fin 4, degreeFifteenDivisor10 i = x.2.val)

private theorem degree_fifteen_small_divisor_indices :
    ∀ x : Fin 13 × Fin 11,
      degreeFifteenSmallDivisorIndexPredicate x := by
  unfold degreeFifteenSmallDivisorIndexPredicate
  decide +kernel

private theorem degree_fifteen_divisor_12_index
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12) :
    ∃ i : Fin 6, degreeFifteenDivisor12 i = d := by
  have hdle : d ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  let d' : Fin 13 := ⟨d, by omega⟩
  exact (degree_fifteen_small_divisor_indices
    (d', (0 : Fin 11))).1 hdpos hd

private theorem degree_fifteen_divisor_10_index
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 10) :
    ∃ i : Fin 4, degreeFifteenDivisor10 i = d := by
  have hdle : d ≤ 10 := Nat.le_of_dvd (by norm_num) hd
  let d' : Fin 11 := ⟨d, by omega⟩
  exact (degree_fifteen_small_divisor_indices
    ((0 : Fin 13), d')).2 hdpos hd

private def degreeFifteenArithmeticPredicate
    (x : Fin 30 × Fin 6 × Fin 4) : Prop :=
  let k := degreeFifteenDivisor720 x.1
  let d13 := degreeFifteenDivisor12 x.2.1
  let d11 := degreeFifteenDivisor10 x.2.2
  (360360 * k / (13 * d13)) % 13 = 1 →
    (360360 * k / (11 * d11)) % 11 = 1 →
    k = 1 ∨ k = 8 ∨ k = 16 ∨ k = 30 ∨
      k = 60 ∨ k = 72 ∨ k = 144

private theorem degree_fifteen_arithmetic_candidates :
    ∀ x : Fin 30 × Fin 6 × Fin 4,
      degreeFifteenArithmeticPredicate x := by
  unfold degreeFifteenArithmeticPredicate
  decide +kernel

private theorem five_point_stabilizer_card_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 1 ∨
      Nat.card (fixingSubgroup P s) = 8 ∨
      Nat.card (fixingSubgroup P s) = 16 ∨
      Nat.card (fixingSubgroup P s) = 30 ∨
      Nat.card (fixingSubgroup P s) = 60 ∨
      Nat.card (fixingSubgroup P s) = 72 ∨
      Nat.card (fixingSubgroup P s) = 144 := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let k := Nat.card K
  have hkpos : 0 < k := by
    dsimp only [k]
    exact Nat.card_pos
  have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
  have hkdiv : k ∣ 720 :=
    five_point_stabilizer_card_dvd_seven_hundred_twenty
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
  have hKindex : K.index = 360360 := by
    change (fixingSubgroup P s).index = 360360
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 360360 * k := by
    rw [hKindex] at hKindexCard
    exact hKindexCard.symm
  have hkNot13 : ¬13 ∣ k := by
    intro h
    exact (by norm_num : ¬13 ∣ 720) (h.trans hkdiv)
  have hkNot11 : ¬11 ∣ k := by
    intro h
    exact (by norm_num : ¬11 ∣ 720) (h.trans hkdiv)
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let S13 : Sylow 13 P := Sylow.nonempty.some
  have hS13card : Nat.card S13 = 13 := by
    rw [S13.card_eq_multiplicity, hPcard]
    rw [show 360360 = 13 * 27720 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hkne),
      Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hkne,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hkNot13]
    norm_num
  let C13 : Subgroup P :=
    Subgroup.centralizer (S13 : Set P)
  let N13 : Subgroup P :=
    Subgroup.normalizer (S13 : Set P)
  let d13 := C13.relIndex N13
  have h13 :
      d13 ∣ 12 ∧ 0 < d13 ∧ N13.index % 13 = 1 ∧
        d13 * N13.index * 13 = Nat.card P := by
    simpa only [C13, N13, d13] using
      sylow_normalizer_constraints_of_not_alternating
        X P hcard h5 hnotAlt (p := 13) (by norm_num)
          (Or.inr rfl) S13 hS13card
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S11 : Sylow 11 P := Sylow.nonempty.some
  have hS11card : Nat.card S11 = 11 := by
    rw [S11.card_eq_multiplicity, hPcard]
    rw [show 360360 = 11 * 32760 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hkne),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hkne,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hkNot11]
    norm_num
  let C11 : Subgroup P :=
    Subgroup.centralizer (S11 : Set P)
  let N11 : Subgroup P :=
    Subgroup.normalizer (S11 : Set P)
  let d11 := C11.relIndex N11
  have h11 :
      d11 ∣ 10 ∧ 0 < d11 ∧ N11.index % 11 = 1 ∧
        d11 * N11.index * 11 = Nat.card P := by
    simpa only [C11, N11, d11] using
      sylow_normalizer_constraints_of_not_alternating
        X P hcard h5 hnotAlt (p := 11) (by norm_num)
          (Or.inl rfl) S11 hS11card
  have hquot13 :
      360360 * k / (13 * d13) = N13.index := by
    have hmul :
        (13 * d13) * N13.index = 360360 * k := by
      rw [← hPcard]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h13.2.2.2
    rw [← hmul]
    exact Nat.mul_div_cancel_left _
      (Nat.mul_pos (by norm_num) h13.2.1)
  have hquot11 :
      360360 * k / (11 * d11) = N11.index := by
    have hmul :
        (11 * d11) * N11.index = 360360 * k := by
      rw [← hPcard]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h11.2.2.2
    rw [← hmul]
    exact Nat.mul_div_cancel_left _
      (Nat.mul_pos (by norm_num) h11.2.1)
  have hkle : k ≤ 720 := Nat.le_of_dvd (by norm_num) hkdiv
  let kFin : Fin 721 := ⟨k, by omega⟩
  obtain ⟨ik, hik⟩ :=
    degree_fifteen_divisor_720_index kFin hkdiv
  obtain ⟨i13, hi13⟩ :=
    degree_fifteen_divisor_12_index d13 h13.2.1 h13.1
  obtain ⟨i11, hi11⟩ :=
    degree_fifteen_divisor_10_index d11 h11.2.1 h11.1
  have harith :=
    degree_fifteen_arithmetic_candidates (ik, i13, i11)
  dsimp only [degreeFifteenArithmeticPredicate] at harith
  rw [hik, hi13, hi11] at harith
  have hcases := harith (by rw [hquot13]; exact h13.2.2.1)
    (by rw [hquot11]; exact h11.2.2.1)
  simpa only [K, k] using hcases

theorem five_point_stabilizer_card_cases_after_transfer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 1 ∨
      Nat.card (fixingSubgroup P s) = 8 ∨
      Nat.card (fixingSubgroup P s) = 16 ∨
      Nat.card (fixingSubgroup P s) = 30 := by
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
  have hKindex : K.index = 360360 := by
    change (fixingSubgroup P s).index = 360360
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 360360 * Nat.card K := by
    rw [hKindex] at hKindexCard
    exact hKindexCard.symm
  have hcases :=
    five_point_stabilizer_card_cases
      X P hcard h5 hnotAlt hs
  change Nat.card K = 1 ∨ Nat.card K = 8 ∨
    Nat.card K = 16 ∨ Nat.card K = 30 ∨
    Nat.card K = 60 ∨ Nat.card K = 72 ∨
    Nat.card K = 144 at hcases
  rcases hcases with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (stabilizer_factor_sixty_or_one_forty_four_impossible
      X P hcard h5 hnotAlt (Nat.card K) (Or.inl h) hPcard).elim
  · exact (stabilizer_factor_seventy_two_impossible
      X P hcard h5 hnotAlt (by rw [hPcard, h])).elim
  · exact (stabilizer_factor_sixty_or_one_forty_four_impossible
      X P hcard h5 hnotAlt (Nat.card K) (Or.inr h) hPcard).elim

end FiveTransitive.Degree15

end CFSG
