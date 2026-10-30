module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

public section

namespace CFSG

namespace FiveTransitive.Research.SharpFourBound

open MulAction
open scoped Pointwise

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private theorem four_embedding_stabilizer_eq_bot
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    MulAction.stabilizer G e = ⊥ := by
  classical
  let _ : MulAction.IsMultiplyPretransitive G X 4 := h4
  have hindex :
      (MulAction.stabilizer G e).index = Nat.card (Fin 4 ↪ X) :=
    MulAction.index_stabilizer_of_transitive G e
  have hembCard :
      Nat.card (Fin 4 ↪ X) = (Fintype.card X).descFactorial 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
      Fintype.card_fin]
  have hdescPos : 0 < (Fintype.card X).descFactorial 4 := by
    rw [← hcard]
    exact Nat.card_pos
  have hmul := (MulAction.stabilizer G e).card_mul_index
  rw [hindex, hembCard, hcard] at hmul
  have hstabCard : Nat.card (MulAction.stabilizer G e) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hdescPos
    simpa using hmul
  exact Subgroup.eq_bot_of_card_eq _ hstabCard

theorem eq_one_of_fixes_four
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (g : G)
    (hfix : ∀ i, g • e i = e i) :
    g = 1 := by
  have hg : g ∈ MulAction.stabilizer G e := by
    rw [MulAction.mem_stabilizer_iff]
    ext i
    exact hfix i
  rw [four_embedding_stabilizer_eq_bot h4 hcard e,
    Subgroup.mem_bot] at hg
  exact hg

theorem eq_of_agrees_four
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (g h : G)
    (hagrees : ∀ i, g • e i = h • e i) :
    g = h := by
  apply inv_mul_eq_one.mp
  apply eq_one_of_fixes_four h4 hcard e (g⁻¹ * h)
  intro i
  rw [mul_smul, ← hagrees]
  simp

theorem exists_maps_embedding
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (a b : Fin 4 ↪ X) :
    ∃ g : G, ∀ i, g • a i = b i := by
  letI : MulAction.IsMultiplyPretransitive G X 4 := h4
  obtain ⟨g, hg⟩ := h4.exists_smul_eq a b
  refine ⟨g, ?_⟩
  intro i
  have hi := congrArg (fun e : Fin 4 ↪ X ↦ e i) hg
  simpa [Function.Embedding.smul_apply] using hi

@[expose] noncomputable def sharpLift
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (σ : Equiv.Perm (Fin 4)) : G :=
  Classical.choose
    (exists_maps_embedding h4 e (σ.toEmbedding.trans e))

@[simp] theorem sharpLift_smul_apply
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    sharpLift h4 hcard e σ • e i = e (σ i) := by
  exact Classical.choose_spec
    (exists_maps_embedding h4 e (σ.toEmbedding.trans e)) i

@[expose] noncomputable def sharpLiftHom
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) : Equiv.Perm (Fin 4) →* G where
  toFun := sharpLift h4 hcard e
  map_one' := by
    apply eq_one_of_fixes_four h4 hcard e
    intro i
    simp
  map_mul' σ τ := by
    apply eq_of_agrees_four h4 hcard e
    intro i
    rw [mul_smul]
    simp

private theorem sharpLiftHom_injective
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    Function.Injective (sharpLiftHom h4 hcard e) := by
  intro σ τ hστ
  change sharpLift h4 hcard e σ = sharpLift h4 hcard e τ at hστ
  apply Equiv.ext
  intro i
  apply e.injective
  rw [← sharpLift_smul_apply h4 hcard e σ i,
    ← sharpLift_smul_apply h4 hcard e τ i, hστ]

noncomputable def baseKleinSubgroup : Subgroup (Equiv.Perm (Fin 4)) :=
  Subgroup.map (alternatingGroup (Fin 4)).subtype
    (alternatingGroup.kleinFour (Fin 4))

@[simp] theorem baseKleinSubgroup_card :
    Nat.card baseKleinSubgroup = 4 := by
  rw [baseKleinSubgroup,
    Subgroup.card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)

noncomputable def sharpKleinSubgroup
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) : Subgroup G :=
  Subgroup.map (sharpLiftHom h4 hcard e)
    baseKleinSubgroup

noncomputable def sharpSymmetricSubgroup
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) : Subgroup G :=
  (sharpLiftHom h4 hcard e).range

@[simp] theorem sharpKleinSubgroup_card
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    Nat.card (sharpKleinSubgroup h4 hcard e) = 4 := by
  rw [sharpKleinSubgroup,
    Subgroup.card_map_of_injective (sharpLiftHom_injective h4 hcard e)]
  exact baseKleinSubgroup_card

@[simp] theorem sharpSymmetricSubgroup_card
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    Nat.card (sharpSymmetricSubgroup h4 hcard e) = 24 := by
  rw [sharpSymmetricSubgroup,
    Nat.card_congr
      (MonoidHom.ofInjective
        (sharpLiftHom_injective h4 hcard e)).toEquiv.symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

theorem fixedBy_ncard_le_three_of_ne_one
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (g : G) (hg : g ≠ 1) :
    (MulAction.fixedBy X g).ncard ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤ (MulAction.fixedBy X g).ncard := by omega
  letI : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  have heNonempty : Nonempty (Fin 4 ↪ MulAction.fixedBy X g) := by
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hfour
  let f : Fin 4 ↪ MulAction.fixedBy X g := Classical.choice heNonempty
  let eFix : Fin 4 ↪ X := f.trans (Function.Embedding.subtype _)
  apply hg
  apply eq_one_of_fixes_four h4 hcard eFix g
  intro i
  exact (f i).property

private theorem exists_two_disjoint_involution_pairs
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (hX : 8 ≤ Fintype.card X)
    (g : G) (hgTwo : g ^ 2 = 1) (hg : g ≠ 1) :
    ∃ x z : X,
      g • x ≠ x ∧ g • z ≠ z ∧
      z ≠ x ∧ z ≠ g • x ∧ g • z ≠ x ∧ g • z ≠ g • x := by
  classical
  let M : Set X := (MulAction.fixedBy X g)ᶜ
  have hfixed := fixedBy_ncard_le_three_of_ne_one h4 hcard g hg
  have hsum := Set.ncard_add_ncard_compl (MulAction.fixedBy X g)
  rw [Nat.card_eq_fintype_card] at hsum
  have hMcard : 5 ≤ M.ncard := by
    dsimp [M]
    omega
  have hMnonempty : M.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨x, hxM⟩ := hMnonempty
  have hx : g • x ≠ x := by
    simpa [M] using hxM
  have hinvol : ∀ y : X, g • (g • y) = y := by
    intro y
    rw [← mul_smul, ← pow_two, hgTwo, one_smul]
  have hgxM : g • x ∈ M := by
    simp only [M, Set.mem_compl_iff, MulAction.mem_fixedBy]
    intro hfix
    have hxeq : x = g • x := (hinvol x).symm.trans hfix
    exact hx hxeq.symm
  have hzExists : ∃ z ∈ M, z ≠ x ∧ z ≠ g • x := by
    by_contra hnone
    push Not at hnone
    have hsub : M ⊆ ({x, g • x} : Set X) := by
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      right
      exact hnone y hy hyx
    have hle := Set.ncard_le_ncard hsub
    have hpair : ({x, g • x} : Set X).ncard = 2 := by
      simp [Ne.symm hx]
    rw [hpair] at hle
    omega
  obtain ⟨z, hzM, hzx, hzgx⟩ := hzExists
  have hz : g • z ≠ z := by
    simpa [M] using hzM
  have hgzx : g • z ≠ x := by
    intro heq
    have hzx' : z = g • x := by
      calc
        z = g • (g • z) := (hinvol z).symm
        _ = g • x := congrArg (fun y : X => g • y) heq
    exact hzgx hzx'
  have hgzgx : g • z ≠ g • x := by
    intro heq
    exact hzx ((MulAction.injective g) heq)
  exact ⟨x, z, hx, hz, hzx, hzgx, hgzx, hgzgx⟩

@[expose] def baseDoubleSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3

@[expose] def baseSingleSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3

@[expose] noncomputable def sharpDoubleInvolution
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) : G :=
  sharpLiftHom h4 hcard e baseDoubleSwap

@[expose] noncomputable def sharpSingleInvolution
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) : G :=
  sharpLiftHom h4 hcard e baseSingleSwap

@[simp] theorem sharpDoubleInvolution_sq
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    sharpDoubleInvolution h4 hcard e ^ 2 = 1 := by
  have hbase : baseDoubleSwap ^ 2 =
      (1 : Equiv.Perm (Fin 4)) := by
    decide
  calc
    sharpDoubleInvolution h4 hcard e ^ 2 =
        sharpLiftHom h4 hcard e (baseDoubleSwap ^ 2) := by
      simp only [sharpDoubleInvolution, map_pow]
    _ = sharpLiftHom h4 hcard e 1 := congrArg _ hbase
    _ = 1 := map_one _

@[simp] theorem sharpSingleInvolution_sq
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    sharpSingleInvolution h4 hcard e ^ 2 = 1 := by
  have hbase : baseSingleSwap ^ 2 =
      (1 : Equiv.Perm (Fin 4)) := by
    decide
  calc
    sharpSingleInvolution h4 hcard e ^ 2 =
        sharpLiftHom h4 hcard e (baseSingleSwap ^ 2) := by
      simp only [sharpSingleInvolution, map_pow]
    _ = sharpLiftHom h4 hcard e 1 := congrArg _ hbase
    _ = 1 := map_one _

theorem sharpSingleInvolution_ne_one
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (e : Fin 4 ↪ X) :
    sharpSingleInvolution h4 hcard e ≠ 1 := by
  intro heq
  apply (show baseSingleSwap ≠ 1 by decide)
  apply sharpLiftHom_injective h4 hcard e
  simpa [sharpSingleInvolution] using heq

theorem involution_conjugate_sharpDouble
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hcard : Nat.card G = (Fintype.card X).descFactorial 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (g : G) (hgTwo : g ^ 2 = 1) (hg : g ≠ 1) :
    ∃ q : G, q * g * q⁻¹ = sharpDoubleInvolution h4 hcard e := by
  classical
  obtain ⟨x, z, hx, hz, hzx, hzgx, hgzx, hgzgx⟩ :=
    exists_two_disjoint_involution_pairs h4 hcard hX g hgTwo hg
  have hinvol : ∀ y : X, g • (g • y) = y := by
    intro y
    rw [← mul_smul, ← pow_two, hgTwo, one_smul]
  let f : Fin 4 → X := ![x, g • x, z, g • z]
  have hf : Function.Injective f := by
    have hx' : x ≠ g • x := hx.symm
    have hz' : z ≠ g • z := hz.symm
    have hxz : x ≠ z := hzx.symm
    have hxgz : x ≠ g • z := hgzx.symm
    have hgxz : g • x ≠ z := hzgx.symm
    have hgxgz : g • x ≠ g • z := hgzgx.symm
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let ef : Fin 4 ↪ X := ⟨f, hf⟩
  obtain ⟨q, hq⟩ := exists_maps_embedding h4 ef e
  have hqinv : ∀ i : Fin 4, q⁻¹ • e i = ef i := by
    intro i
    rw [← hq]
    simp
  have hq0 : q • x = e 0 := by
    simpa [ef, f] using hq 0
  have hq1 : q • (g • x) = e 1 := by
    simpa [ef, f] using hq 1
  have hq2 : q • z = e 2 := by
    simpa [ef, f] using hq 2
  have hq3 : q • (g • z) = e 3 := by
    simpa [ef, f] using hq 3
  have hd0 : sharpDoubleInvolution h4 hcard e • e 0 = e 1 := by
    have hb : baseDoubleSwap (0 : Fin 4) = 1 := by decide
    change sharpLift h4 hcard e baseDoubleSwap • e 0 = e 1
    rw [sharpLift_smul_apply, hb]
  have hd1 : sharpDoubleInvolution h4 hcard e • e 1 = e 0 := by
    have hb : baseDoubleSwap (1 : Fin 4) = 0 := by decide
    change sharpLift h4 hcard e baseDoubleSwap • e 1 = e 0
    rw [sharpLift_smul_apply, hb]
  have hd2 : sharpDoubleInvolution h4 hcard e • e 2 = e 3 := by
    have hb : baseDoubleSwap (2 : Fin 4) = 3 := by decide
    change sharpLift h4 hcard e baseDoubleSwap • e 2 = e 3
    rw [sharpLift_smul_apply, hb]
  have hd3 : sharpDoubleInvolution h4 hcard e • e 3 = e 2 := by
    have hb : baseDoubleSwap (3 : Fin 4) = 2 := by decide
    change sharpLift h4 hcard e baseDoubleSwap • e 3 = e 2
    rw [sharpLift_smul_apply, hb]
  refine ⟨q, eq_of_agrees_four h4 hcard e _ _ ?_⟩
  intro i
  rw [mul_smul, mul_smul, hqinv]
  fin_cases i <;> simp [ef, f, hinvol, hq0, hq1, hq2, hq3,
    hd0, hd1, hd2, hd3]

end FiveTransitive.Research.SharpFourBound

end CFSG
