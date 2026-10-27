
module

public import CFSG.Quasithin.EmptyFaithful.SBc9Heart

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin

abbrev eVec (a : Fin 6) : Fin 6 → ZMod 2 := Pi.single a 1

@[expose] def pairVec (a b : Fin 6) : ↥(evenWeight 6) :=
  ⟨eVec a + eVec b, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Pi.add_apply,
      Finset.sum_add_distrib, eVec, Finset.sum_pi_single', Finset.mem_univ, ite_true]
    decide⟩

theorem pairVec_apply (a b i : Fin 6) :
    ((pairVec a b : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i = eVec a i + eVec b i :=
  rfl

theorem permWeight_pairVec (σ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    permWeight 6 σ (pairVec a b) = pairVec (σ a) (σ b) := by
  apply Subtype.ext
  funext i
  show ((pairVec a b : ↥(evenWeight 6)) : Fin 6 → ZMod 2) (σ⁻¹ i) =
    ((pairVec (σ a) (σ b) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) i
  rw [pairVec_apply, pairVec_apply]
  simp only [eVec, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem alt6_two_transitive {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ τ : Equiv.Perm (Fin 6), τ ∈ alternatingGroup (Fin 6) ∧ τ a = c ∧ τ b = d := by
  have h4 := alternatingGroup.isMultiplyPretransitive (Fin 6)
  have hc : Nat.card (Fin 6) - 2 = 4 := by simp
  rw [hc] at h4
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)
  let x : Fin 2 ↪ Fin 6 := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin 6 := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) x y
  refine ⟨g, g.2, ?_, ?_⟩
  · exact congrArg (fun e : Fin 2 ↪ Fin 6 => e 0) hg
  · exact congrArg (fun e : Fin 2 ↪ Fin 6 => e 1) hg

private theorem zmod2_cases (u v w : ZMod 2) (h : u ≠ v) :
    (w = u ∧ u + w = 0 ∧ v + u = 1 ∧ w + v = 1) ∨ (w = v ∧ u + w = 1 ∧ v + u = 1 ∧ w + v = 0) := by
  revert u v w; decide

theorem exists_pairVec_add (x : ↥(evenWeight 6)) {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hx : (x : Fin 6 → ZMod 2) i ≠ (x : Fin 6 → ZMod 2) j) :
    ∃ a b : Fin 6, a ≠ b ∧
      x + permWeight 6 (Equiv.swap i j * Equiv.swap j k) x = pairVec a b := by
  have hσ : ∀ p, (Equiv.swap i j * Equiv.swap j k)⁻¹ p = Equiv.swap j k (Equiv.swap i j p) := by
    intro p
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, Equiv.Perm.mul_apply]
  have hval : ∀ p, ((x + permWeight 6 (Equiv.swap i j * Equiv.swap j k) x : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) p = (x : Fin 6 → ZMod 2) p +
        (x : Fin 6 → ZMod 2) (Equiv.swap j k (Equiv.swap i j p)) := by
    intro p
    show (x : Fin 6 → ZMod 2) p + (x : Fin 6 → ZMod 2) ((Equiv.swap i j * Equiv.swap j k)⁻¹ p) = _
    rw [hσ]
  have hi : Equiv.swap j k (Equiv.swap i j i) = k := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  have hj : Equiv.swap j k (Equiv.swap i j j) = i := by
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hij hik]
  have hk : Equiv.swap j k (Equiv.swap i j k) = j := by
    rw [Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm, Equiv.swap_apply_right]
  have ho : ∀ p, p ≠ i → p ≠ j → p ≠ k → Equiv.swap j k (Equiv.swap i j p) = p := by
    intro p hpi hpj hpk
    rw [Equiv.swap_apply_of_ne_of_ne hpi hpj, Equiv.swap_apply_of_ne_of_ne hpj hpk]
  rcases zmod2_cases ((x : Fin 6 → ZMod 2) i) ((x : Fin 6 → ZMod 2) j)
    ((x : Fin 6 → ZMod 2) k) hx with ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
  · refine ⟨j, k, hjk, Subtype.ext (funext fun p => ?_)⟩
    rw [hval, pairVec_apply]
    by_cases hpi : p = i
    · subst hpi; rw [hi, h1]; simp [eVec, hij, hik]
    by_cases hpj : p = j
    · subst hpj; rw [hj, h2]; simp [eVec, hjk]
    by_cases hpk : p = k
    · subst hpk; rw [hk, h3]; simp [eVec, hjk.symm]
    rw [ho p hpi hpj hpk, CharTwo.add_self_eq_zero]
    simp [eVec, hpj, hpk]
  · refine ⟨i, j, hij, Subtype.ext (funext fun p => ?_)⟩
    rw [hval, pairVec_apply]
    by_cases hpi : p = i
    · subst hpi; rw [hi, h1]; simp [eVec, hij]
    by_cases hpj : p = j
    · subst hpj; rw [hj, h2]; simp [eVec, hij.symm]
    by_cases hpk : p = k
    · subst hpk; rw [hk, h3]; simp [eVec, hik.symm, hjk.symm]
    rw [ho p hpi hpj hpk, CharTwo.add_self_eq_zero]
    simp [eVec, hpi, hpj]

theorem eq_top_of_pairVec_mem (Y : AddSubgroup ↥(evenWeight 6))
    (h : ∀ a b, a ≠ b → pairVec a b ∈ Y) : Y = ⊤ := by
  suffices key : ∀ n, ∀ x : ↥(evenWeight 6),
      (Finset.univ.filter fun p => (x : Fin 6 → ZMod 2) p ≠ 0).card = n → x ∈ Y from
    eq_top_iff.mpr fun x _ => key _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      exact Y.zero_mem
    obtain ⟨i, hi⟩ : ∃ i, (x : Fin 6 → ZMod 2) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (Subtype.ext (funext hcon))
    have hsum : ∑ p, (x : Fin 6 → ZMod 2) p = 0 := by
      have := x.2
      simpa [evenWeight] using this
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ (x : Fin 6 → ZMod 2) j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hs : ∑ p, (x : Fin 6 → ZMod 2) p = (x : Fin 6 → ZMod 2) i :=
        Finset.sum_eq_single i (fun p _ hp => hcon p hp) (by simp)
      exact hi (hs ▸ hsum)
    have hone : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by decide
    have hxi := hone _ hi
    have hxj := hone _ hj
    set x' := x + pairVec i j with hx'def
    have hx' : x = x' + pairVec i j := by
      rw [hx'def, add_assoc, ← two_nsmul]
      have : (2 : ℕ) • pairVec i j = 0 := by
        apply Subtype.ext
        funext p
        show (2 : ℕ) • ((pairVec i j : ↥(evenWeight 6)) : Fin 6 → ZMod 2) p = 0
        rw [two_nsmul, CharTwo.add_self_eq_zero]
      rw [this, add_zero]
    have hval : ∀ p, (x' : Fin 6 → ZMod 2) p =
        (x : Fin 6 → ZMod 2) p + eVec i p + eVec j p := by
      intro p
      show (x : Fin 6 → ZMod 2) p + (eVec i p + eVec j p) = _
      rw [add_assoc]
    have hsub : (Finset.univ.filter fun p => (x' : Fin 6 → ZMod 2) p ≠ 0) ⊂
        (Finset.univ.filter fun p => (x : Fin 6 → ZMod 2) p ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, by simp [hi], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        rw [hval, hxi]
        simp [eVec, hji.symm]
        decide
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro hp0
        apply hp
        rw [hval, hp0]
        by_cases hpi : p = i
        · subst hpi
          exact absurd hp0 hi
        by_cases hpj : p = j
        · subst hpj
          exact absurd hp0 hj
        simp [eVec, hpi, hpj]
    have hlt := Finset.card_lt_card hsub
    rw [hx] at hlt
    rw [hx']
    exact Y.add_mem (ih _ hlt x' rfl) (h i j hji.symm)

theorem heart6_irreducible (Y : AddSubgroup (AltHeart 6))
    (hY : ∀ σ ∈ alternatingGroup (Fin 6), ∀ y ∈ Y, SBc9.heartAct σ y ∈ Y) :
    Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hyY⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hbot
  have hy0' : y ≠ 0 := fun h => hy0 (Subtype.ext h)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hnc : x ∉ constWeight 6 := fun h => hy0' (by
    rw [QuotientAddGroup.eq_zero_iff]
    exact h)
  obtain ⟨i, j, hij⟩ : ∃ i j, (x : Fin 6 → ZMod 2) i ≠ (x : Fin 6 → ZMod 2) j := by
    by_contra hcon
    push Not at hcon
    exact hnc hcon
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  have hthird : ∀ i j : Fin 6, ∃ k : Fin 6, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hthird i j
  have hσ : Equiv.swap i j * Equiv.swap j k ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne,
      Equiv.Perm.sign_swap (Ne.symm hkj)]
    decide
  obtain ⟨a, b, hab, he⟩ := exists_pairVec_add x hne hki.symm hkj.symm hij
  have hpair : (QuotientAddGroup.mk (pairVec a b) : AltHeart 6) ∈ Y := by
    have := Y.add_mem hyY (hY _ hσ _ hyY)
    rw [SBc9.heartAct_mk, ← QuotientAddGroup.mk_add, he] at this
    exact this
  have hall : ∀ c d, c ≠ d → (QuotientAddGroup.mk (pairVec c d) : AltHeart 6) ∈ Y := by
    intro c d hcd
    obtain ⟨τ, hτ, hτa, hτb⟩ := alt6_two_transitive hab hcd
    have := hY τ hτ _ hpair
    rwa [SBc9.heartAct_mk, permWeight_pairVec, hτa, hτb] at this
  have hY' := eq_top_of_pairVec_mem (Y.comap (QuotientAddGroup.mk' (constWeight 6)))
    (fun c d hcd => hall c d hcd)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have : w ∈ Y.comap (QuotientAddGroup.mk' (constWeight 6)) := hY' ▸ AddSubgroup.mem_top w
  exact this

end CFSG.Quasithin.MS93
