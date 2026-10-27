module

public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.Degree16FiniteChecks
public import CFSG.Permutation.FiveTransitive.PermCentralizer
public import CFSG.Permutation.FiveTransitive.OrbitBounds

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private theorem exists_controlled_conjugator
    (P : Subgroup (Equiv.Perm (Fin 16)))
    (h5 : ∀ a b : Fin 5 → Fin 16,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 16)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 16)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 16)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 16)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 16)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    Degree16FiniteChecks.sourceTuple
    Degree16FiniteChecks.targetTuple
    Degree16FiniteChecks.sourceTuple_injective
    Degree16FiniteChecks.targetTuple_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Degree16FiniteChecks.sourceTuple,
      Degree16FiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [Degree16FiniteChecks.sourceTuple,
      Degree16FiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [Degree16FiniteChecks.sourceTuple,
      Degree16FiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [Degree16FiniteChecks.sourceTuple,
      Degree16FiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [Degree16FiniteChecks.sourceTuple,
      Degree16FiniteChecks.targetTuple, Subgroup.smul_def,
      Equiv.Perm.smul_def] using hp (4 : Fin 5)

private theorem five_le_image_of_controlled_conjugator
    (p : Equiv.Perm (Fin 16))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 16)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply Degree16FiniteChecks.five_le_of_ne_zero_one_two_three_four
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem alternatingGroup_le_of_sevenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 16)))
    (h5 : ∀ a b : Fin 5 → Fin 16,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : Degree16FiniteChecks.sevenCycle ∈ P) :
    alternatingGroup (Fin 16) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 16 := (p : Equiv.Perm (Fin 16)) 4
  let y : Fin 16 := (p : Equiv.Perm (Fin 16)) 5
  let z : Fin 16 := (p : Equiv.Perm (Fin 16)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 16)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 16)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 16)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 16) :=
    (p : Equiv.Perm (Fin 16)) * Degree16FiniteChecks.sevenCycle *
      (p : Equiv.Perm (Fin 16))⁻¹
  have hh : h = Degree16FiniteChecks.comparisonCycle x y z := by
    change
      (p : Equiv.Perm (Fin 16)) * Degree16FiniteChecks.sevenCycle *
          (p : Equiv.Perm (Fin 16))⁻¹ =
        Degree16FiniteChecks.comparisonCycle x y z
    rw [← Equiv.permCongr_eq_mul, Degree16FiniteChecks.sevenCycle,
      Helpers.permCongr_formPerm]
    simp [Degree16FiniteChecks.comparisonCycle, x, y, z,
      hp0, hp1, hp2, hp3]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    Degree16FiniteChecks.exists_small_mem_closure
      x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({Degree16FiniteChecks.sevenCycle,
            Degree16FiniteChecks.comparisonCycle x y z} :
            Set (Equiv.Perm (Fin 16))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rw [← hh]
      exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 16) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

private theorem alternatingGroup_le_of_tripleSwap_mem
    (P : Subgroup (Equiv.Perm (Fin 16)))
    (h5 : ∀ a b : Fin 5 → Fin 16,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : Degree16FiniteChecks.tripleSwap ∈ P) :
    alternatingGroup (Fin 16) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 16 := (p : Equiv.Perm (Fin 16)) 4
  let y : Fin 16 := (p : Equiv.Perm (Fin 16)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 16)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 16) :=
    (p : Equiv.Perm (Fin 16)) * Degree16FiniteChecks.tripleSwap *
      (p : Equiv.Perm (Fin 16))⁻¹
  have hh : h = Degree16FiniteChecks.comparisonTripleSwap x y := by
    change
      (p : Equiv.Perm (Fin 16)) * Degree16FiniteChecks.tripleSwap *
          (p : Equiv.Perm (Fin 16))⁻¹ =
        Degree16FiniteChecks.comparisonTripleSwap x y
    rw [← Equiv.permCongr_eq_mul, Degree16FiniteChecks.tripleSwap,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm,
      Helpers.permCongr_formPerm]
    simp [Degree16FiniteChecks.comparisonTripleSwap, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    Degree16FiniteChecks.tripleSwap *
      (Degree16FiniteChecks.comparisonTripleSwap x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    Degree16FiniteChecks.tripleSwap_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 16) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 16)))
    (h5 : ∀ a b : Fin 5 → Fin 16,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : Degree16FiniteChecks.doubleThreeCycle ∈ P) :
    alternatingGroup (Fin 16) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator P h5
  let x : Fin 16 := (p : Equiv.Perm (Fin 16)) 4
  let y : Fin 16 := (p : Equiv.Perm (Fin 16)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator
      (p : Equiv.Perm (Fin 16)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 16)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 16) :=
    (p : Equiv.Perm (Fin 16)) *
      Degree16FiniteChecks.doubleThreeCycle *
      (p : Equiv.Perm (Fin 16))⁻¹
  have hh : h = Degree16FiniteChecks.comparisonDoubleThreeCycle x y := by
    change
      (p : Equiv.Perm (Fin 16)) *
            Degree16FiniteChecks.doubleThreeCycle *
          (p : Equiv.Perm (Fin 16))⁻¹ =
        Degree16FiniteChecks.comparisonDoubleThreeCycle x y
    rw [← Equiv.permCongr_eq_mul,
      Degree16FiniteChecks.doubleThreeCycle, Equiv.permCongr_mul,
      Helpers.permCongr_formPerm, Helpers.permCongr_formPerm]
    simp [Degree16FiniteChecks.comparisonDoubleThreeCycle, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    Degree16FiniteChecks.doubleThreeCycle *
      (Degree16FiniteChecks.comparisonDoubleThreeCycle x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    Degree16FiniteChecks.doubleThreeCycle_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 16) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_cycleType_eq
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 16))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 16)),
        (∀ a b : Fin 5 → Fin 16,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 16) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 16 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 16) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 16 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 16)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 16,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 16) :=
      e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' :=
      Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) =
          e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 16) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 16) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 16) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

theorem alternatingGroup_le_of_prime_order_support_le_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
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
  let e₀ : X ≃ Fin 16 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 16) := e₀.permCongr g
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
            Degree16FiniteChecks.tripleSwap.cycleType := by
        rw [hm, hg₁order, hm',
          Degree16FiniteChecks.tripleSwap_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg Degree16FiniteChecks.tripleSwap
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_tripleSwap_mem
    · have hm' : m + 1 = 2 := by omega
      have hcycle :
          g₁.cycleType =
            Degree16FiniteChecks.doubleThreeCycle.cycleType := by
        rw [hm, hg₁order, hm',
          Degree16FiniteChecks.doubleThreeCycle_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg Degree16FiniteChecks.doubleThreeCycle
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
            Degree16FiniteChecks.sevenCycle.cycleType := by
        rw [hg₁cycle.cycleType,
          Degree16FiniteChecks.sevenCycle_isCycle.cycleType,
          hg₁support, hsupp,
          Degree16FiniteChecks.sevenCycle_card_support]
      apply alternatingGroup_le_of_cycleType_eq
        X P hcard h5 hg Degree16FiniteChecks.sevenCycle
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_sevenCycle_mem

private theorem four_point_stabilizer_subsingleton_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5)
    (y z w v : SubMulAction.ofFixingSubgroup P s)
    (hyz : y ≠ z) (hyw : y ≠ w) (hyv : y ≠ v)
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v) :
    Subsingleton ↥
      (((MulAction.stabilizer (fixingSubgroup P s) y ⊓
        MulAction.stabilizer (fixingSubgroup P s) z) ⊓
        MulAction.stabilizer (fixingSubgroup P s) w) ⊓
        MulAction.stabilizer (fixingSubgroup P s) v) := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let M : Subgroup K :=
    ((MulAction.stabilizer K y ⊓ MulAction.stabilizer K z) ⊓
      MulAction.stabilizer K w) ⊓ MulAction.stabilizer K v
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
      ((((u : M) : K) ∈ MulAction.stabilizer K y ∧
        ((u : M) : K) ∈ MulAction.stabilizer K z) ∧
        ((u : M) : K) ∈ MulAction.stabilizer K w) ∧
        ((u : M) : K) ∈ MulAction.stabilizer K v := by
    exact Subgroup.mem_inf.mp u.prop
  have hyfix :
      (((u : M) : K) : P) • (y : X) = y :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.1.1.1)
  have hzfix :
      (((u : M) : K) : P) • (z : X) = z :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.1.1.2)
  have hwfix :
      (((u : M) : K) : P) • (w : X) = w :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.1.2)
  have hvfix :
      (((u : M) : K) : P) • (v : X) = v :=
    congrArg Subtype.val
      (MulAction.mem_stabilizer_iff.mp huStabilizers.2)
  have hyzX : (y : X) ≠ (z : X) :=
    fun h => hyz (Subtype.ext h)
  have hywX : (y : X) ≠ (w : X) :=
    fun h => hyw (Subtype.ext h)
  have hyvX : (y : X) ≠ (v : X) :=
    fun h => hyv (Subtype.ext h)
  have hzwX : (z : X) ≠ (w : X) :=
    fun h => hzw (Subtype.ext h)
  have hzvX : (z : X) ≠ (v : X) :=
    fun h => hzv (Subtype.ext h)
  have hwvX : (w : X) ≠ (v : X) :=
    fun h => hwv (Subtype.ext h)
  let t : Set X :=
    Set.insert (y : X) (Set.insert (z : X)
      (Set.insert (w : X) (Set.insert (v : X) s)))
  have hvNotS : (v : X) ∉ s := v.prop
  have hwNotInsert : (w : X) ∉ Set.insert (v : X) s := by
    intro hw
    change (w : X) = (v : X) ∨ (w : X) ∈ s at hw
    exact hw.elim hwvX w.prop
  have hzNotInsert :
      (z : X) ∉ Set.insert (w : X) (Set.insert (v : X) s) := by
    intro hz
    change
      (z : X) = (w : X) ∨ (z : X) = (v : X) ∨
        (z : X) ∈ s at hz
    exact hz.elim hzwX (fun hz => hz.elim hzvX z.prop)
  have hyNotInsert :
      (y : X) ∉ Set.insert (z : X)
        (Set.insert (w : X) (Set.insert (v : X) s)) := by
    intro hy
    change
      (y : X) = (z : X) ∨ (y : X) = (w : X) ∨
        (y : X) = (v : X) ∨ (y : X) ∈ s at hy
    exact hy.elim hyzX (fun hy =>
      hy.elim hywX (fun hy => hy.elim hyvX y.prop))
  have htcard : t.ncard = 9 := by
    change
      (Set.insert (y : X) (Set.insert (z : X)
        (Set.insert (w : X) (Set.insert (v : X) s)))).ncard = 9
    calc
      _ =
          (Set.insert (z : X)
            (Set.insert (w : X) (Set.insert (v : X) s))).ncard + 1 :=
        Set.ncard_insert_of_notMem hyNotInsert
      _ =
          ((Set.insert (w : X)
            (Set.insert (v : X) s)).ncard + 1) + 1 :=
        congrArg (fun n => n + 1)
          (Set.ncard_insert_of_notMem hzNotInsert)
      _ = (((Set.insert (v : X) s).ncard + 1) + 1) + 1 :=
        congrArg (fun n => (n + 1) + 1)
          (Set.ncard_insert_of_notMem hwNotInsert)
      _ = ((((s.ncard + 1) + 1) + 1) + 1) :=
        congrArg (fun n => ((n + 1) + 1) + 1)
          (Set.ncard_insert_of_notMem hvNotS)
      _ = 9 := by omega
  have hsuppSubset : (g.support : Set X) ⊆ tᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxt
    change
      x = (y : X) ∨ x = (z : X) ∨ x = (w : X) ∨
        x = (v : X) ∨ x ∈ s at hxt
    rcases hxt with rfl | rfl | rfl | rfl | hxs
    · exact Equiv.Perm.mem_support.mp hx hyfix
    · exact Equiv.Perm.mem_support.mp hx hzfix
    · exact Equiv.Perm.mem_support.mp hx hwfix
    · exact Equiv.Perm.mem_support.mp hx hvfix
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

theorem five_point_stabilizer_card_dvd_seven_thousand_nine_hundred_twenty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 7920 := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 11 := by
    change Nat.card ↥(sᶜ : Set X) = 11
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  let A := Fin 4 ↪ Y
  have hfixed :
      ∀ k : K, k ≠ 1 →
        Nat.card (MulAction.fixedBy A k) = 0 := by
    intro k hk
    rw [Finite.card_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩
    have hfix (i : Fin 4) : k • a i = a i := by
      change (k • a : A) i = a i
      exact congrArg (fun e : A => e i) ha
    have h01 : a (0 : Fin 4) ≠ a (1 : Fin 4) :=
      a.injective.ne (by decide)
    have h02 : a (0 : Fin 4) ≠ a (2 : Fin 4) :=
      a.injective.ne (by decide)
    have h03 : a (0 : Fin 4) ≠ a (3 : Fin 4) :=
      a.injective.ne (by decide)
    have h12 : a (1 : Fin 4) ≠ a (2 : Fin 4) :=
      a.injective.ne (by decide)
    have h13 : a (1 : Fin 4) ≠ a (3 : Fin 4) :=
      a.injective.ne (by decide)
    have h23 : a (2 : Fin 4) ≠ a (3 : Fin 4) :=
      a.injective.ne (by decide)
    let M : Subgroup K :=
      ((MulAction.stabilizer K (a (0 : Fin 4)) ⊓
        MulAction.stabilizer K (a (1 : Fin 4))) ⊓
        MulAction.stabilizer K (a (2 : Fin 4))) ⊓
        MulAction.stabilizer K (a (3 : Fin 4))
    letI : Subsingleton M :=
      four_point_stabilizer_subsingleton_of_not_alternating
        X P hcard h5 hnotAlt hs
          (a 0) (a 1) (a 2) (a 3)
          h01 h02 h03 h12 h13 h23
    have hkM :
        k ∈ ((MulAction.stabilizer K (a (0 : Fin 4)) ⊓
          MulAction.stabilizer K (a (1 : Fin 4))) ⊓
          MulAction.stabilizer K (a (2 : Fin 4))) ⊓
          MulAction.stabilizer K (a (3 : Fin 4)) := by
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
      exact ⟨⟨⟨MulAction.mem_stabilizer_iff.mpr (hfix 0),
        MulAction.mem_stabilizer_iff.mpr (hfix 1)⟩,
        MulAction.mem_stabilizer_iff.mpr (hfix 2)⟩,
        MulAction.mem_stabilizer_iff.mpr (hfix 3)⟩
    let u : M := ⟨k, hkM⟩
    have hu : u = 1 := Subsingleton.elim _ _
    apply hk
    simpa [u] using congrArg (fun q : M => (q : K)) hu
  have hdvd :
      Fintype.card K ∣ Fintype.card A :=
    OrbitBounds.card_group_dvd_card_of_no_nontrivial_fixedPoints
      K A hfixed
  have hYcardF : Fintype.card Y = 11 := by
    rwa [← Nat.card_eq_fintype_card]
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    hYcardF] at hdvd
  norm_num at hdvd
  rwa [Nat.card_eq_fintype_card]

private theorem sylow_centralizer_card_eq_prime_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
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
          p * (16 - p).factorial := by
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
      Nat.card C ∣ p * (16 - p).factorial := by
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
    have hsuppCard : w.support.card ≤ 5 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 16 - p := by
          rw [Finset.card_compl, hgsupport, hcard]
        _ ≤ 5 := by
          rcases hpCases with rfl | rfl <;> norm_num
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    exact hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) (v : P).prop hwNe (by
          simpa only [w] using hsuppCard))
  have hnotTwo : ¬2 ∣ Nat.card C := by
    apply himpossible (q := 2) (by norm_num)
    rcases hpCases with rfl | rfl <;> norm_num
  have hnotThree : ¬3 ∣ Nat.card C := by
    apply himpossible (q := 3) (by norm_num)
    rcases hpCases with rfl | rfl <;> norm_num
  rcases hpCases with rfl | rfl
  · have hnotFive : ¬5 ∣ Nat.card C := by
      apply himpossible (q := 5) (by norm_num) (by norm_num)
    have hCle : Nat.card C ≤ 1320 :=
      Nat.le_of_dvd (by norm_num) (by
        norm_num at hCdiv ⊢
        exact hCdiv)
    have hCpos : 0 < Nat.card C := Nat.card_pos
    interval_cases hCeq : Nat.card C
    all_goals try norm_num [hCeq] at hCdiv
    all_goals try norm_num [hCeq] at hpdivC
    all_goals try norm_num [hCeq] at hnotTwo
    all_goals try norm_num [hCeq] at hnotThree
    all_goals try norm_num [hCeq] at hnotFive
    all_goals norm_num [hCeq]
  · have hCle : Nat.card C ≤ 78 :=
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

theorem sylow_normalizer_constraints_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
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

@[expose] def degreeSixteenDivisor7920 (i : Fin 60) : ℕ :=
  ![1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 15, 16, 18, 20,
    22, 24, 30, 33, 36, 40, 44, 45, 48, 55, 60, 66, 72,
    80, 88, 90, 99, 110, 120, 132, 144, 165, 176, 180,
    198, 220, 240, 264, 330, 360, 396, 440, 495, 528,
    660, 720, 792, 880, 990, 1320, 1584, 1980, 2640,
    3960, 7920] i

@[expose] def degreeSixteenDivisor12 (i : Fin 6) : ℕ :=
  ![1, 2, 3, 4, 6, 12] i

@[expose] def degreeSixteenDivisor10 (i : Fin 4) : ℕ :=
  ![1, 2, 5, 10] i

@[expose] def degreeSixteenDivisorIndexPredicate (k : Fin 7921) : Prop :=
  k.val ∣ 7920 →
    ∃ i : Fin 60, degreeSixteenDivisor7920 i = k.val

theorem degree_sixteen_divisor_7920_index :
    ∀ k : Fin 7921, degreeSixteenDivisorIndexPredicate k := by
  have hblocks : ∀ a : Fin 80, ∀ b : Fin 100,
      a.val * 100 + b.val ∣ 7920 →
      ∃ i : Fin 60, degreeSixteenDivisor7920 i = a.val * 100 + b.val := by
    decide +kernel
  intro k hk
  have ha : k.val / 100 < 80 := by omega
  have hb : k.val % 100 < 100 := Nat.mod_lt _ (by omega)
  have hdecomp : k.val / 100 * 100 + k.val % 100 = k.val := by omega
  obtain ⟨i, hi⟩ := hblocks ⟨k.val / 100, ha⟩ ⟨k.val % 100, hb⟩ (by
    simpa only [hdecomp] using hk)
  exact ⟨i, by simpa only [hdecomp] using hi⟩

private def degreeSixteenSmallDivisorIndexPredicate
    (x : Fin 13 × Fin 11) : Prop :=
  (0 < x.1.val → x.1.val ∣ 12 →
      ∃ i : Fin 6, degreeSixteenDivisor12 i = x.1.val) ∧
    (0 < x.2.val → x.2.val ∣ 10 →
      ∃ i : Fin 4, degreeSixteenDivisor10 i = x.2.val)

private theorem degree_sixteen_small_divisor_indices :
    ∀ x : Fin 13 × Fin 11,
      degreeSixteenSmallDivisorIndexPredicate x := by
  unfold degreeSixteenSmallDivisorIndexPredicate
  decide +kernel

theorem degree_sixteen_divisor_12_index
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12) :
    ∃ i : Fin 6, degreeSixteenDivisor12 i = d := by
  have hdle : d ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  let d' : Fin 13 := ⟨d, by omega⟩
  exact (degree_sixteen_small_divisor_indices
    (d', (0 : Fin 11))).1 hdpos hd

theorem degree_sixteen_divisor_10_index
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 10) :
    ∃ i : Fin 4, degreeSixteenDivisor10 i = d := by
  have hdle : d ≤ 10 := Nat.le_of_dvd (by norm_num) hd
  let d' : Fin 11 := ⟨d, by omega⟩
  exact (degree_sixteen_small_divisor_indices
    ((0 : Fin 13), d')).2 hdpos hd

end FiveTransitive.Degree16

end CFSG
