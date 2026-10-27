module

public import CFSG.Permutation.FiveTransitive.Reduction
public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG

namespace FiveTransitive.SharpThreeNormalObstruction

private theorem tuple_eval_injective (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] (k : ℕ) (htrans : MulAction.IsMultiplyPretransitive G X k)
    (hcard : Nat.card G = (Fintype.card X).descFactorial k) (a : Fin k ↪ X) :
    Function.Injective (fun g : G => g • a) := by
  classical
  let _ := Fintype.ofFinite G
  let _ : MulAction.IsMultiplyPretransitive G X k := htrans
  apply ((Fintype.bijective_iff_surjective_and_card (fun g : G => g • a)).mpr ?_).injective
  constructor
  · intro b
    exact MulAction.exists_smul_eq G a b
  · simpa only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
      using hcard

private theorem exists_swap_of_normal_sharp_three
    (G X : Type*) [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X]
    (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal]
    (h3 : MulAction.IsMultiplyPretransitive N X 3)
    (hN : Nat.card N = (Fintype.card X).descFactorial 3) :
    ∃ (t : N) (a b : X), a ≠ b ∧
      MulAction.toPermHom G X (t : G) = Equiv.swap a b := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ X) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  let a := e 0
  let b := e 1
  let c := e 2
  have hab : a ≠ b := e.injective.ne (by decide)
  have hac : a ≠ c := e.injective.ne (by decide)
  have hbc : b ≠ c := e.injective.ne (by decide)
  let target : Fin 3 ↪ X := e.trans (Equiv.swap a b).toEmbedding
  let _ : MulAction.IsMultiplyPretransitive N X 3 := h3
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq N e target
  have hta : (t : G) • a = b := by
    have := DFunLike.congr_fun ht 0
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, target, a] using this
  have htb : (t : G) • b = a := by
    have := DFunLike.congr_fun ht 1
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, target, b] using this
  have htc : (t : G) • c = c := by
    have := DFunLike.congr_fun ht 2
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def, target, c, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] using this
  have heval := tuple_eval_injective N X 3 h3 hN e
  have hcomm : ∀ g : G, g • a = a → g • b = b → g • c = c →
      g * (t : G) = (t : G) * g := by
    intro g hga hgb hgc
    have hga' : g⁻¹ • a = a := by rw [← smul_left_cancel_iff g]; simpa using hga.symm
    have hgb' : g⁻¹ • b = b := by rw [← smul_left_cancel_iff g]; simpa using hgb.symm
    have hgc' : g⁻¹ • c = c := by rw [← smul_left_cancel_iff g]; simpa using hgc.symm
    let u : N := ⟨g * (t : G) * g⁻¹,
      (inferInstance : N.Normal).conj_mem (t : G) t.property g⟩
    have hut : u = t := by
      apply heval
      apply Function.Embedding.ext
      intro i
      fin_cases i <;>
        simp only [Function.Embedding.smul_apply, Subgroup.smul_def]
      · change (g * (t : G) * g⁻¹) • a = (t : G) • a
        simp only [mul_smul, hga', hta, hgb]
      · change (g * (t : G) * g⁻¹) • b = (t : G) • b
        simp only [mul_smul, hgb', htb, hga]
      · change (g * (t : G) * g⁻¹) • c = (t : G) • c
        simp only [mul_smul, hgc', htc, hgc]
    have hconj : g * (t : G) * g⁻¹ = (t : G) := congrArg Subtype.val hut
    have := congrArg (fun z : G => z * g) hconj
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
  have hfix : ∀ x : X, x ≠ a → x ≠ b → x ≠ c → (t : G) • x = x := by
    intro x hxa hxb hxc
    by_contra htx
    let y := (t : G) • x
    have hya : y ≠ a := by
      intro hy
      exact hxb (smul_left_cancel (t : G) (hy.trans htb.symm))
    have hyb : y ≠ b := by
      intro hy
      exact hxa (smul_left_cancel (t : G) (hy.trans hta.symm))
    have hyc : y ≠ c := by
      intro hy
      exact hxc (smul_left_cancel (t : G) (hy.trans htc.symm))
    have hyx : y ≠ x := htx
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a, b, c, x, y}) (t := (Finset.univ : Finset X))
      (lt_of_le_of_lt Finset.card_le_five (by simp only [Finset.card_univ]; omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    let v : Fin 5 → X := ![a, b, c, x, y]
    let w : Fin 5 → X := ![a, b, c, x, z]
    have hv : Function.Injective v := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [v, hab, hab.symm, hac, hac.symm, hbc, hbc.symm,
          hxa, hxa.symm, hxb, hxb.symm, hxc, hxc.symm,
          hya, hya.symm, hyb, hyb.symm, hyc, hyc.symm, hyx, hyx.symm] at hij ⊢
    have hw : Function.Injective w := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [w, hab, hab.symm, hac, hac.symm, hbc, hbc.symm,
          hxa, hxa.symm, hxb, hxb.symm, hxc, hxc.symm,
          hz.1, Ne.symm hz.1, hz.2.1, Ne.symm hz.2.1, hz.2.2.1, Ne.symm hz.2.2.1,
          hz.2.2.2.1, Ne.symm hz.2.2.2.1] at hij ⊢
    obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp h5)
      (⟨v, hv⟩ : Fin 5 ↪ X) (⟨w, hw⟩ : Fin 5 ↪ X)
    have hgpoint (i : Fin 5) : g • v i = w i := DFunLike.congr_fun hg i
    have hga : g • a = a := by simpa [v, w] using hgpoint 0
    have hgb : g • b = b := by simpa [v, w] using hgpoint 1
    have hgc : g • c = c := by simpa [v, w] using hgpoint 2
    have hgx : g • x = x := by simpa [v, w] using hgpoint 3
    have hgy : g • y = z := by simpa [v, w] using hgpoint 4
    have heq := congrArg (fun k : G => k • x) (hcomm g hga hgb hgc)
    have heq' : g • y = y := by simpa only [mul_smul, hgx] using heq
    have hzy : z = y := hgy.symm.trans heq'
    exact hz.2.2.2.2 hzy
  refine ⟨t, a, b, hab, ?_⟩
  ext x
  change (t : G) • x = Equiv.swap a b x
  by_cases hxa : x = a
  · subst x
    simpa using hta
  by_cases hxb : x = b
  · subst x
    simpa using htb
  by_cases hxc : x = c
  · subst x
    simpa [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm] using htc
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  exact hfix x hxa hxb hxc

theorem eq_top_of_normal_sharp_three
    (X : Type*) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (N : Subgroup P) [N.Normal]
    (h3 : MulAction.IsMultiplyPretransitive N X 3)
    (hN : Nat.card N = (Fintype.card X).descFactorial 3) : P = ⊤ := by
  obtain ⟨t, a, b, hab, ht⟩ := exists_swap_of_normal_sharp_three P X hcard h5 N h3 hN
  have ht' : ((t : P) : Equiv.Perm X) = Equiv.swap a b := ht
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 2) (n := 5) (by omega)
      (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  apply Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (MulAction.isPreprimitive_of_is_two_pretransitive h2) (Equiv.swap a b)
    ⟨a, b, hab, rfl⟩
  exact ht' ▸ (t : P).property

end FiveTransitive.SharpThreeNormalObstruction

end CFSG
