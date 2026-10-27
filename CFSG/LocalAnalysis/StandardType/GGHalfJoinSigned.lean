module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

public section

namespace CFSG.StandardType.GGHalfJoin

open CFSG.StandardType.SpJoin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem signed_mem_form {n p : ℕ} {g : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hg : g ∈ spSignedGroup n p) :
    ∃ σ : Equiv.Perm (Fin n), ∃ s : Fin n → ℤ,
      (∀ t, s t = 1 ∨ s t = -1) ∧ ∀ w t, g w t = (w (σ.symm t)) ^ (s t) := by
  classical
  let P : Equiv.Perm (Fin n → Multiplicative (ZMod p)) → Prop := fun g =>
    ∃ σ : Equiv.Perm (Fin n), ∃ s : Fin n → ℤ,
      (∀ t, s t = 1 ∨ s t = -1) ∧ ∀ w t, g w t = (w (σ.symm t)) ^ (s t)
  have hgen : ∀ x ∈ Set.range (spReflPerm n p), P x := by
    rintro x ⟨k, rfl⟩
    by_cases hk : k.val + 1 < n
    · refine ⟨Equiv.swap k ⟨k.val + 1, hk⟩, fun _ => 1, fun t => Or.inl rfl, ?_⟩
      intro w t
      rw [spReflPerm_of_lt n p k hk]
      simp
    · refine ⟨Equiv.refl (Fin n), fun t => if t = k then -1 else 1, ?_, ?_⟩
      · intro t
        by_cases h : t = k <;> simp [h]
      · intro w t
        rw [spReflPerm_of_not_lt n p k hk, coordInv_apply]
        by_cases ht : t = k
        · subst ht
          simp
        · rw [Function.update_of_ne ht]
          simp [ht]
  have hone : P 1 := by
    refine ⟨Equiv.refl (Fin n), fun _ => 1, fun t => Or.inl rfl, ?_⟩
    intro w t
    simp
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨σx, sx, hsx, hx⟩ ⟨σy, sy, hsy, hy⟩
    refine ⟨σx * σy, fun t => sy (σx.symm t) * sx t, ?_, ?_⟩
    · intro t
      change sy (σx.symm t) * sx t = 1 ∨ sy (σx.symm t) * sx t = -1
      rcases hsx t with h | h <;> rcases hsy (σx.symm t) with h' | h' <;>
        rw [h, h'] <;> norm_num
    · intro w t
      rw [Equiv.Perm.mul_apply, hx, hy]
      dsimp only
      have hsymm : (σx * σy).symm t = σy.symm (σx.symm t) := by
        change (σx * σy)⁻¹ t = σy.symm (σx.symm t)
        rw [mul_inv_rev, Equiv.Perm.mul_apply]
        simp only [Equiv.Perm.inv_def]
      rw [hsymm]
      exact (zpow_mul _ _ _).symm
  have hinv : ∀ x, P x → P x⁻¹ := by
    rintro x ⟨σ, s, hs, hx⟩
    refine ⟨σ.symm, fun t => s (σ t), fun t => hs (σ t), ?_⟩
    intro w t
    have hyform : ∀ u, x (fun v => (w (σ v)) ^ (s (σ v))) u = w u := by
      intro u
      rw [hx]
      rw [σ.apply_symm_apply]
      calc (w u ^ s u) ^ s u = w u ^ (s u * s u) := (zpow_mul _ _ _).symm
        _ = w u ^ (1 : ℤ) := by
            rw [show s u * s u = 1 by
              rcases hs u with h | h <;> rw [h] <;> norm_num]
        _ = w u := zpow_one _
    have hw_eq : w = x (fun v => (w (σ v)) ^ (s (σ v))) :=
      funext fun u => (hyform u).symm
    have hxinv : x⁻¹ w = fun v => (w (σ v)) ^ (s (σ v)) := by
      conv_lhs => rw [hw_eq]
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hxinv]
    dsimp only
    rw [Equiv.symm_symm]
  exact Subgroup.closure_induction (p := fun g _ => P g) hgen hone
    (fun x y _ _ hx hy => hmul x y hx hy) (fun x _ hx => hinv x hx) hg

theorem signed_preserves_support {n : ℕ} {g : Equiv.Perm (Fin n → Multiplicative (ZMod 3))}
    (hg : g ∈ spSignedGroup n 3) {v : Fin n → Multiplicative (ZMod 3)} {i j : Fin n}
    (hij : i ≠ j) (hvi : v i ≠ 1) (hvj : v j ≠ 1) (hsupp : ∀ l, l ≠ i → l ≠ j → v l = 1)
    (hfix : g v = v) {w : Fin n → Multiplicative (ZMod 3)} (hw : ∀ l, l ≠ i → l ≠ j → w l = 1) :
    ∀ l, l ≠ i → l ≠ j → g w l = 1 := by
  classical
  obtain ⟨σ, s, hs, hform⟩ := signed_mem_form hg
  have hsupp' : ∀ l, v l ≠ 1 ↔ (l = i ∨ l = j) := by
    intro l
    constructor
    · intro hvl
      by_contra h
      rw [not_or] at h
      exact hvl (hsupp l h.1 h.2)
    · rintro (rfl | rfl)
      · exact hvi
      · exact hvj
  have hpow : ∀ t, v t = (v (σ.symm t)) ^ (s t) := by
    intro t
    have h := hform v t
    rwa [hfix] at h
  have hiff : ∀ l, (v l ≠ 1 ↔ v (σ.symm l) ≠ 1) := by
    intro l
    rw [hpow l]
    rcases hs l with h | h
    · rw [h, zpow_one]
    · rw [h, zpow_neg_one]
      exact inv_ne_one
  have key : ∀ l, l ≠ i → l ≠ j → σ.symm l ≠ i ∧ σ.symm l ≠ j := by
    intro l hl hlj
    constructor
    · intro h
      have hv : v (σ.symm l) ≠ 1 := by rw [h]; exact hvi
      have : v l ≠ 1 := (hiff l).mpr hv
      rcases (hsupp' l).mp this with h' | h'
      · exact hl h'
      · exact hlj h'
    · intro h
      have hv : v (σ.symm l) ≠ 1 := by rw [h]; exact hvj
      have : v l ≠ 1 := (hiff l).mpr hv
      rcases (hsupp' l).mp this with h' | h'
      · exact hl h'
      · exact hlj h'
  intro l hl hlj
  obtain ⟨hnei, hnej⟩ := key l hl hlj
  rw [hform w l, hw (σ.symm l) hnei hnej]
  exact one_zpow (s l)

private theorem card_perm_pair_preserving {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∀ t, (σ t = i ∨ σ t = j) ↔ (t = i ∨ t = j)} = 2 * (n - 2).factorial := by
  classical
  let f : Fin n → Bool := fun t => decide (t = i ∨ t = j)
  have hP : ∀ σ : Equiv.Perm (Fin n),
      (∀ t, (σ t = i ∨ σ t = j) ↔ (t = i ∨ t = j)) ↔ f ∘ σ = f := by
    intro σ
    constructor
    · intro h
      funext t
      simp only [Function.comp_apply, f]
      simpa only [decide_eq_decide] using h t
    · intro h t
      have ht := congrFun h t
      simpa only [Function.comp_apply, f, decide_eq_decide] using ht
  rw [Nat.card_congr (Equiv.subtypeEquivRight hP)]
  have htrue : Fintype.card {t : Fin n // f t = true} = 2 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun t => f t = true) = {i, j} := by
      ext t
      simp [f]
    rw [heq, Finset.card_pair hij]
  have hfalse : Fintype.card {t : Fin n // f t = false} = n - 2 := by
    have heq : ∀ t : Fin n, (f t = false) ↔ ¬ f t = true := fun t => by
      cases f t <;> simp
    rw [Fintype.card_congr (Equiv.subtypeEquivRight heq),
      Fintype.card_subtype_compl, Fintype.card_fin, htrue]
  rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card f,
    Fintype.prod_bool, hfalse, htrue]
  norm_num [Nat.mul_comm]

private theorem inv_ne_self_three {a : Multiplicative (ZMod 3)} (ha : a ≠ 1) : a⁻¹ ≠ a := by
  intro h
  have hneg : -Multiplicative.toAdd a = Multiplicative.toAdd a :=
    congrArg Multiplicative.toAdd h
  have hsum : Multiplicative.toAdd a + Multiplicative.toAdd a = 0 := by
    calc Multiplicative.toAdd a + Multiplicative.toAdd a =
      Multiplicative.toAdd a + -Multiplicative.toAdd a := congrArg (fun b => Multiplicative.toAdd a + b) hneg.symm
    _ = 0 := add_neg_cancel _
  have htwo : (2 : ZMod 3) * Multiplicative.toAdd a = 0 := by
    simpa only [two_mul] using hsum
  have hzero : Multiplicative.toAdd a = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by decide)
  exact ha (Multiplicative.toAdd.injective hzero)

private theorem card_complement_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Fintype.card {t : Fin n // t ≠ i ∧ t ≠ j} = n - 2 := by
  classical
  have hp : Fintype.card {t : Fin n // t = i ∨ t = j} = 2 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun t : Fin n => t = i ∨ t = j) = {i, j} := by
      ext t; simp
    rw [heq, Finset.card_pair hij]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun t : Fin n =>
    (not_or : ¬ (t = i ∨ t = j) ↔ t ≠ i ∧ t ≠ j).symm)),
    Fintype.card_subtype_compl, Fintype.card_fin, hp]

theorem card_signed_stabilizer_two_support_le {n : ℕ}
    {v : Fin n → Multiplicative (ZMod 3)} {i j : Fin n} (hij : i ≠ j)
    (hvi : v i ≠ 1) (hvj : v j ≠ 1) (hsupp : ∀ l, l ≠ i → l ≠ j → v l = 1) :
    Nat.card ↥(spSignedGroup n 3 ⊓ MulAction.stabilizer
      (Equiv.Perm (Fin n → Multiplicative (ZMod 3))) v) ≤
      2 * (2 ^ (n - 2) * (n - 2).factorial) := by
  classical
  let H : Subgroup (Equiv.Perm (Fin n → Multiplicative (ZMod 3))) := spSignedGroup n 3 ⊓ MulAction.stabilizer
    (Equiv.Perm (Fin n → Multiplicative (ZMod 3))) v
  let P := {σ : Equiv.Perm (Fin n) //
    ∀ t, (σ t = i ∨ σ t = j) ↔ (t = i ∨ t = j)}
  let C := {t : Fin n // t ≠ i ∧ t ≠ j}
  have hfix : ∀ g : H, (g : Equiv.Perm (Fin n → Multiplicative (ZMod 3))) v = v := by
    intro g
    exact MulAction.mem_stabilizer_iff.mp g.2.2
  choose σ ss hss hform using fun g : H => signed_mem_form g.2.1
  have hsupp' : ∀ t : Fin n, v t ≠ 1 ↔ t = i ∨ t = j := by
    intro t
    constructor
    · intro h
      by_contra hc
      exact h (hsupp t (not_or.mp hc).1 (not_or.mp hc).2)
    · rintro (rfl | rfl) <;> assumption
  have hσ : ∀ g : H, ∀ t, (σ g t = i ∨ σ g t = j) ↔ (t = i ∨ t = j) := by
    intro g t
    rw [← hsupp', ← hsupp']
    have heq := hform g v (σ g t)
    rw [hfix, Equiv.symm_apply_apply] at heq
    rw [heq]
    rcases hss g (σ g t) with h | h
    · simp only [h, zpow_one]
    · rw [h, zpow_neg_one]
      constructor
      · intro hnv hval
        apply hnv
        rw [hval, inv_one]
      · intro hnv hval
        apply hnv
        have hi := congrArg (fun z : Multiplicative (ZMod 3) => z⁻¹) hval
        simpa only [inv_inv, inv_one] using hi
  let enc : H → P × (C → Bool) := fun g =>
    (⟨σ g, hσ g⟩, fun t => decide (ss g t = -1))
  have hinj : Function.Injective enc := by
    intro g g' he
    have hσσ : σ g = σ g' := congrArg (fun x : P × (C → Bool) => x.1.1) he
    have hsC : ∀ t : C, ss g t = ss g' t := by
      intro t
      have ht : decide (ss g t = -1) = decide (ss g' t = -1) :=
        congrArg (fun x : P × (C → Bool) => x.2 t) he
      have ht' : (ss g t = -1) ↔ (ss g' t = -1) := by simpa only [decide_eq_decide] using ht
      rcases hss g t with h | h <;> rcases hss g' t with h' | h'
      · rw [h, h']
      · have hc := ht'.mpr h'
        rw [h] at hc
        norm_num at hc
      · have hc := ht'.mp h
        rw [h'] at hc
        norm_num at hc
      · rw [h, h']
    have hsS : ∀ t : Fin n, v t ≠ 1 → ss g t = ss g' t := by
      intro t hv
      have hpre : v ((σ g).symm t) ≠ 1 := by
        intro hc
        have ht := hform g v t
        rw [hfix, hc] at ht
        exact hv (ht.trans (one_zpow (ss g t)))
      have heq : (v ((σ g).symm t)) ^ ss g t = (v ((σ g).symm t)) ^ ss g' t := by
        calc (v ((σ g).symm t)) ^ ss g t = (g : Equiv.Perm _) v t := (hform g v t).symm
          _ = v t := congrFun (hfix g) t
          _ = (g' : Equiv.Perm _) v t := (congrFun (hfix g') t).symm
          _ = (v ((σ g).symm t)) ^ ss g' t := by rw [hform g', ← hσσ]
      rcases hss g t with h | h <;> rcases hss g' t with h' | h'
      · rw [h, h']
      · exfalso; rw [h, h', zpow_one, zpow_neg_one] at heq
        exact inv_ne_self_three hpre heq.symm
      · exfalso; rw [h, h', zpow_one, zpow_neg_one] at heq
        exact inv_ne_self_three hpre heq
      · rw [h, h']
    have hsall : ∀ t : Fin n, ss g t = ss g' t := by
      intro t
      by_cases hti : t = i
      · exact hsS t (hti ▸ hvi)
      · by_cases htj : t = j
        · exact hsS t (htj ▸ hvj)
        · exact hsC ⟨t, hti, htj⟩
    apply Subtype.ext
    apply Equiv.ext
    intro w
    funext t
    rw [hform g w t, hform g' w t, hσσ, hsall]
  have hPcard : Nat.card P = 2 * (n - 2).factorial := card_perm_pair_preserving hij
  have hCcard : Nat.card (C → Bool) = 2 ^ (n - 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, card_complement_pair hij]
  have hcard : Nat.card ↥H ≤ Nat.card (P × (C → Bool)) :=
    Nat.card_le_card_of_injective enc hinj
  rw [Nat.card_prod, hPcard, hCcard] at hcard
  calc Nat.card ↥H ≤ 2 * (n - 2).factorial * 2 ^ (n - 2) := hcard
    _ = 2 * (2 ^ (n - 2) * (n - 2).factorial) := by ring


theorem frame_upper {G : Type} [Group G] [Finite G] {k : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType 3 (CoxeterMatrix.B (k + 1)) A)
    (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hΦ : ∀ h ∈ spSignedGroup (k + 1) 3, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a)) :
    ∀ ψ ∈ A, ∃ h ∈ spSignedGroup (k + 1) 3, ∀ a, ψ (Φ a) = Φ (h a) := by
  classical
  obtain ⟨e, _⟩ := hA
  haveI : Finite ↥Bs := Finite.of_injective (fun x : ↥Bs => (x : G)) Subtype.val_injective
  haveI : Finite ↥A := Finite.of_injective
    (fun ψ : ↥A => fun x : ↥Bs => (ψ : MulAut ↥Bs) x)
    (by
      intro ψ ψ' h
      exact Subtype.ext (DFunLike.ext _ _ (fun x => congrFun h x)))
  let S : Type := ↥(spSignedGroup (k + 1) 3)
  let ψh : S → MulAut ↥Bs := fun h => Classical.choose (hΦ h.1 h.2)
  have hψA : ∀ h : S, ψh h ∈ A := fun h => (Classical.choose_spec (hΦ h.1 h.2)).1
  have hψ : ∀ (h : S) (a : Fin (k + 1) → Multiplicative (ZMod 3)),
      ψh h (Φ a) = Φ (h.1 a) := fun h => (Classical.choose_spec (hΦ h.1 h.2)).2
  let f : S → ↥A := fun h => ⟨ψh h, hψA h⟩
  have hf : Function.Injective f := by
    intro h h' hh
    have hψeq : ψh h = ψh h' := congrArg Subtype.val hh
    have hab : ∀ a, h.1 a = h'.1 a := by
      intro a
      apply Φ.injective
      rw [← hψ h a, ← hψ h' a, hψeq]
    exact Subtype.ext (Equiv.ext hab)
  have hAle : Nat.card ↥A ≤ Nat.card S := by
    have hcard : Nat.card ↥A = Nat.card (CoxeterMatrix.B (k + 1)).Group :=
      (Nat.card_congr e.toEquiv).symm
    rw [hcard]
    calc Nat.card (CoxeterMatrix.B (k + 1)).Group
        ≤ 2 ^ (k + 1) * (k + 1).factorial := card_coxeterB_le (k + 1)
      _ ≤ Nat.card S :=
          two_pow_mul_factorial_le_card_spSignedGroup Nat.prime_three (by norm_num)
  have hbij : Function.Bijective f :=
    Function.Injective.bijective_of_nat_card_le hf hAle
  intro ψ hψmem
  obtain ⟨h, hh⟩ := hbij.2 ⟨ψ, hψmem⟩
  refine ⟨h.1, h.2, ?_⟩
  have hψeq : ψh h = ψ := congrArg Subtype.val hh
  intro a
  rw [← hψeq]
  exact hψ h a


end CFSG.StandardType.GGHalfJoin

end
