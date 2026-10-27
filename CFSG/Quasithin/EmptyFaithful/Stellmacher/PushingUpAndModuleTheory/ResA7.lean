module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53Mod

open Equiv CFSG.Quasithin

@[expose] def epsVec (i : Fin 5) : G6.PermMod 5 :=
  Multiplicative.ofAdd (fun j => if j = i then (0 : ZMod 2) else 1)

theorem epsVec_mem : ∀ i : Fin 5, epsVec i ∈ G6.coreMod 5 := by
  intro i
  rw [G6.mem_coreMod]
  revert i
  unfold epsVec
  decide +kernel

@[expose] def eps (i : Fin 5) : orth.W := ⟨epsVec i, epsVec_mem i⟩

theorem act_eps (g : Perm (Fin 5)) (i : Fin 5) : orth.act g (eps i) = eps (g i) := by
  apply Subtype.ext
  show G6.permAct 5 g (epsVec i) = epsVec (g i)
  apply Multiplicative.toAdd.injective
  funext j
  show (if g⁻¹ j = i then (0 : ZMod 2) else 1) = if j = g i then 0 else 1
  by_cases h : j = g i
  · subst h; simp
  · have : g⁻¹ j ≠ i := fun h' => h (by rw [← h']; simp)
    simp only [this, h, ↓reduceIte]

@[expose] def vec (w : orth.W) : G6.PermMod 5 := Subtype.val w

theorem prod_eps (w : orth.W) :
    ∏ i : Fin 5, (eps i) ^ (Multiplicative.toAdd (vec w) i).val = w := by
  revert w
  decide +kernel


theorem pow_mod_two {Mg : Type*} [CommGroup Mg] {y : Mg} (hy : y * y = 1) (n : ℕ) :
    y ^ (n % 2) = y ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, sq, hy, one_pow, mul_one]

theorem pow_val_add {Mg : Type*} [CommGroup Mg] {y : Mg} (hy : y * y = 1) (a b : ZMod 2) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  rw [ZMod.val_add, pow_mod_two hy, pow_add]

@[expose] def t012 : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def t013 : Perm (Fin 5) := swap 0 1 * swap 1 3

@[expose, irreducible] def a4Words : Finset (Perm (Fin 5)) := wordSet [t012, t013] 4

set_option maxRecDepth 100000 in
theorem a4_wordSet : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ 4 = 4 → σ ∈ a4Words := by
  unfold a4Words t012 t013
  decide +kernel

private theorem a4Words_subset : ∀ x ∈ a4Words, x ∈ Subgroup.closure {t012, t013} := by
  unfold a4Words
  have e : {g | g ∈ [t012, t013]} = ({t012, t013} : Set (Perm (Fin 5))) := by
    ext g; simp
  rw [← e]
  exact wordSet_subset_closure [t012, t013] 4

theorem a4_le_closure {σ : Perm (Fin 5)} (h1 : Perm.sign σ = 1) (h2 : σ 4 = 4) :
    σ ∈ Subgroup.closure {t012, t013} := a4Words_subset σ (a4_wordSet σ h1 h2)

theorem t012_prop : t012 ^ 3 = 1 ∧ Perm.sign t012 = 1 ∧ t012 4 = 4 := by
  unfold t012; decide +kernel

theorem t013_prop : t013 ^ 3 = 1 ∧ Perm.sign t013 = 1 ∧ t013 4 = 4 := by
  unfold t013; decide +kernel

theorem exists_alt_with_apply : ∀ i : Fin 5, ∃ g : Perm (Fin 5), Perm.sign g = 1 ∧ g 4 = i := by
  decide +kernel


theorem exists_section (M : Model 5) (π : M.W →* orth.W) (hπs : Function.Surjective π)
    (hπe : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w, π (M.act σ w) = orth.act σ (π w))
    (hker : ∀ w, π w = 1 → ∀ σ ∈ alternatingGroup (Fin 5), M.act σ w = w) :
    ∃ s : orth.W →* M.W, (∀ w, π (s w) = w) ∧
      ∀ σ ∈ alternatingGroup (Fin 5), ∀ w, M.act σ (s w) = s (orth.act σ w) := by
  classical
  obtain ⟨x, hx⟩ := hπs (eps 4)
  have hgen : ∀ a : Perm (Fin 5), a ^ 3 = 1 → Perm.sign a = 1 → a 4 = 4 → M.act a x = x := by
    intro a ha3 hsg ha4
    have haA : a ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr hsg
    set y := M.act a x * x⁻¹ with hy
    have hπy : π y = 1 := by
      rw [hy, map_mul, map_inv, hπe a haA, hx, act_eps, ha4, mul_inv_cancel]
    have hya : M.act a y = y := hker y hπy a haA
    have hy2 : y * y = 1 := M.sq y
    have h1 : M.act a x = y * x := by rw [hy]; group
    have h2 : M.act (a ^ 2) x = x := by
      rw [pow_two, map_mul, MulAut.mul_apply, h1, map_mul, hya, h1, ← mul_assoc, hy2, one_mul]
    have h3 : M.act (a ^ 3) x = M.act a x := by
      rw [pow_succ', map_mul, MulAut.mul_apply, h2]
    rw [ha3, map_one, MulAut.one_apply] at h3
    have h4 : y = 1 := by
      have : y * x = x := by rw [← h1, ← h3]
      simpa using this
    rw [h1, h4, one_mul]
  have hA4 : ∀ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) → σ 4 = 4 → M.act σ x = x := by
    intro σ hσ h4
    let Stab : Subgroup (Perm (Fin 5)) :=
      { carrier := {σ | M.act σ x = x}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          show M.act (a * b) x = x
          rw [map_mul, MulAut.mul_apply]
          have hb' : M.act b x = x := hb
          have ha' : M.act a x = x := ha
          rw [hb', ha']
        inv_mem' := by
          intro a ha
          show M.act a⁻¹ x = x
          have ha' : M.act a x = x := ha
          calc M.act a⁻¹ x = M.act a⁻¹ (M.act a x) := by rw [ha']
            _ = x := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    have hcl : Subgroup.closure {t012, t013} ≤ Stab := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hgen _ t012_prop.1 t012_prop.2.1 t012_prop.2.2
      · exact hgen _ t013_prop.1 t013_prop.2.1 t013_prop.2.2
    exact hcl (a4_le_closure (Perm.mem_alternatingGroup.mp hσ) h4)
  choose g hgs hg4 using exists_alt_with_apply
  set y : Fin 5 → M.W := fun i => M.act (g i) x with hydef
  have hy2 : ∀ i, y i * y i = 1 := fun i => M.sq _
  have hyπ : ∀ i, π (y i) = eps i := by
    intro i
    rw [hydef]
    show π (M.act (g i) x) = eps i
    rw [hπe _ (Perm.mem_alternatingGroup.mpr (hgs i)), hx, act_eps, hg4]
  have hyact : ∀ σ ∈ alternatingGroup (Fin 5), ∀ i, M.act σ (y i) = y (σ i) := by
    intro σ hσ i
    set a : Perm (Fin 5) := (g (σ i))⁻¹ * (σ * g i) with ha
    have ha4 : a 4 = 4 := by
      rw [ha, Perm.mul_apply, Perm.mul_apply, hg4]
      exact Perm.inv_eq_iff_eq.mpr (hg4 (σ i)).symm
    have haA : a ∈ alternatingGroup (Fin 5) := by
      rw [ha]
      exact (alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).inv_mem
        (Perm.mem_alternatingGroup.mpr (hgs _))) ((alternatingGroup (Fin 5)).mul_mem hσ
        (Perm.mem_alternatingGroup.mpr (hgs _)))
    have h1 := hA4 a haA ha4
    show M.act σ (M.act (g i) x) = M.act (g (σ i)) x
    calc M.act σ (M.act (g i) x) = M.act (σ * g i) x := by rw [map_mul, MulAut.mul_apply]
      _ = M.act (g (σ i) * a) x := by rw [ha]; simp
      _ = M.act (g (σ i)) x := by rw [map_mul, MulAut.mul_apply, h1]
  let s0 : orth.W → M.W := fun w =>
    ∏ i : Fin 5, (y i) ^ (Multiplicative.toAdd (vec w) i).val
  have hs0 : ∀ w w', s0 (w * w') = s0 w * s0 w' := by
    intro w w'
    simp only [s0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : Multiplicative.toAdd (vec (w * w')) i =
        Multiplicative.toAdd (vec w) i + Multiplicative.toAdd (vec w') i := rfl
    rw [this, pow_val_add (hy2 i)]
  refine ⟨MonoidHom.mk' s0 hs0, fun w => ?_, fun σ hσ w => ?_⟩
  · show π (∏ i : Fin 5, (y i) ^ (Multiplicative.toAdd (vec w) i).val) = w
    rw [map_prod]
    simp only [map_pow, hyπ]
    exact prod_eps w
  · show M.act σ (∏ i : Fin 5, (y i) ^ (Multiplicative.toAdd (vec w) i).val) =
      ∏ i : Fin 5, (y i) ^ (Multiplicative.toAdd (vec (orth.act σ w)) i).val
    rw [map_prod]
    simp only [map_pow, hyact σ hσ]
    have key : ∀ j, Multiplicative.toAdd (vec (orth.act σ w)) j =
        Multiplicative.toAdd (vec w) (σ⁻¹ j) := fun j => rfl
    simp only [key]
    rw [← Equiv.prod_comp σ (fun j => y j ^ (Multiplicative.toAdd (vec w) (σ⁻¹ j)).val)]
    simp

end CFSG.Quasithin.F53Mod
