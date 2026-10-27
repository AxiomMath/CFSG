module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

variable {V : Type*} [Group V] [Finite V]

@[expose] def permNontrivial (B : Subgroup V) (φ : MulAut V) (hφ : ∀ v, φ v ∈ B ↔ v ∈ B) :
    Equiv.Perm {v : V // v ∈ B ∧ v ≠ 1} where
  toFun s := ⟨φ s.1, (hφ s.1).2 s.2.1, fun h => s.2.2 (φ.injective (by rw [h, map_one]))⟩
  invFun s := ⟨φ.symm s.1, (hφ (φ.symm s.1)).1 (by simpa using s.2.1),
    fun h => s.2.2 (by simpa using congrArg φ h)⟩
  left_inv s := Subtype.ext (by simp)
  right_inv s := Subtype.ext (by simp)

omit [Finite V] in
theorem permNontrivial_pow_apply (B : Subgroup V) (φ : MulAut V) (hφ : ∀ v, φ v ∈ B ↔ v ∈ B)
    (n : ℕ) (s : {v : V // v ∈ B ∧ v ≠ 1}) :
    (((permNontrivial B φ hφ) ^ n) s).1 = (φ ^ n) s.1 := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
    rfl

theorem card_nontrivial (B : Subgroup V) :
    Nat.card {v : V // v ∈ B ∧ v ≠ 1} = Nat.card B - 1 := by
  classical
  let e : {v : V // v ∈ B ∧ v ≠ 1} ≃ {b : B // b ≠ 1} :=
    { toFun := fun s => ⟨⟨s.1, s.2.1⟩, fun h => s.2.2 (congrArg Subtype.val h)⟩
      invFun := fun b => ⟨b.1.1, b.1.2, fun h => b.2 (Subtype.ext h)⟩
      left_inv := fun s => rfl
      right_inv := fun b => rfl }
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq (1 : B)

theorem perm_sq_eq_one_of_pow_two_pow {S : Type*} [Finite S] (hS : Nat.card S = 3)
    {f : Equiv.Perm S} {k : ℕ} (hf : f ^ 2 ^ k = 1) : f ^ 2 = 1 := by
  have h6 : orderOf f ∣ 6 := by
    have := orderOf_dvd_natCard f
    rwa [Nat.card_perm, hS] at this
  have h2k : orderOf f ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hf
  have hgcd : Nat.gcd 6 (2 ^ k) ∣ 2 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h : Nat.gcd 6 (2 ^ k) = Nat.gcd 2 (2 ^ k) := by
      rw [show (6 : ℕ) = 3 * 2 from rfl, Nat.Coprime.gcd_mul_left_cancel 2 hcop]
    rw [h]
    exact Nat.gcd_dvd_left 2 (2 ^ k)
  exact orderOf_dvd_iff_pow_eq_one.mp ((Nat.dvd_gcd h6 h2k).trans hgcd)

private theorem perm_fin_three_eq_one_of_commute :
    ∀ g h : Equiv.Perm (Fin 3), g ^ 3 = 1 → (∀ i, g i ≠ i) → h ^ 2 = 1 → g * h = h * g →
      h = 1 := by
  decide

theorem perm_eq_one_of_commute {S : Type*} [Finite S] (hS : Nat.card S = 3)
    {g h : Equiv.Perm S} (hg3 : g ^ 3 = 1) (hgfix : ∀ s, g s ≠ s) (hh2 : h ^ 2 = 1)
    (hgh : g * h = h * g) : h = 1 := by
  let e : S ≃ Fin 3 := Finite.equivFinOfCardEq hS
  have key := perm_fin_three_eq_one_of_commute (e.permCongrHom g) (e.permCongrHom h)
    (by rw [← map_pow, hg3, map_one])
    (fun i => by
      intro hi
      apply hgfix (e.symm i)
      have : e.permCongr g i = i := hi
      rw [Equiv.permCongr_apply] at this
      exact e.injective (by rw [Equiv.apply_symm_apply]; exact this))
    (by rw [← map_pow, hh2, map_one])
    (by rw [← map_mul, hgh, map_mul])
  exact e.permCongrHom.injective (by rw [key, map_one])

theorem sq_apply_eq_of_pow_two_pow (B : Subgroup V) (hB : Nat.card B = 4)
    (φ : MulAut V) (hφ : ∀ v, φ v ∈ B ↔ v ∈ B) {k : ℕ} (hk : ∀ v ∈ B, (φ ^ 2 ^ k) v = v) :
    ∀ v ∈ B, (φ ^ 2) v = v := by
  have hS : Nat.card {v : V // v ∈ B ∧ v ≠ 1} = 3 := by rw [card_nontrivial, hB]
  have hf : (permNontrivial B φ hφ) ^ 2 ^ k = 1 := by
    ext s
    rw [permNontrivial_pow_apply, hk s.1 s.2.1]
    rfl
  have hsq := perm_sq_eq_one_of_pow_two_pow hS hf
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  · have := congrArg Subtype.val (congrArg (fun f : Equiv.Perm _ => f ⟨v, hv, hv1⟩) hsq)
    simpa [permNontrivial_pow_apply] using this

theorem apply_eq_of_commute_of_cube (B : Subgroup V) (hB : Nat.card B = 4)
    (β φ : MulAut V) (hβ : ∀ v, β v ∈ B ↔ v ∈ B) (hφ : ∀ v, φ v ∈ B ↔ v ∈ B)
    (hβ3 : ∀ v ∈ B, (β ^ 3) v = v) (hβfix : ∀ v ∈ B, β v = v → v = 1)
    {k : ℕ} (hk : ∀ v ∈ B, (φ ^ 2 ^ k) v = v) (hβφ : ∀ v ∈ B, β (φ v) = φ (β v)) :
    ∀ v ∈ B, φ v = v := by
  have hS : Nat.card {v : V // v ∈ B ∧ v ≠ 1} = 3 := by rw [card_nontrivial, hB]
  have hsq := sq_apply_eq_of_pow_two_pow B hB φ hφ hk
  have h1 := perm_eq_one_of_commute hS (g := permNontrivial B β hβ)
    (h := permNontrivial B φ hφ)
    (by ext s; rw [permNontrivial_pow_apply, hβ3 s.1 s.2.1]; rfl)
    (fun s hs => s.2.2 (hβfix s.1 s.2.1 (congrArg Subtype.val hs)))
    (by ext s; rw [permNontrivial_pow_apply, hsq s.1 s.2.1]; rfl)
    (by ext s; exact hβφ s.1 s.2.1)
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  · exact congrArg Subtype.val (congrArg (fun f : Equiv.Perm _ => f ⟨v, hv, hv1⟩) h1)

theorem card_modEq_one_of_cube (B : Subgroup V) (β : MulAut V) (hβ : ∀ v, β v ∈ B ↔ v ∈ B)
    (hβ3 : ∀ v ∈ B, (β ^ 3) v = v) (hβfix : ∀ v ∈ B, β v = v → v = 1) :
    Nat.card B ≡ 1 [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype {v : V // v ∈ B ∧ v ≠ 1} := Fintype.ofFinite _
  let f := permNontrivial B β hβ
  have hf3 : f ^ 3 ^ 1 = 1 := by
    ext s
    rw [pow_one, permNontrivial_pow_apply, hβ3 s.1 s.2.1]
    rfl
  have hsupp : f.supportᶜ = ∅ := by
    ext s
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, ne_eq, not_not,
      Finset.notMem_empty, iff_false]
    intro hs
    exact s.2.2 (hβfix s.1 s.2.1 (congrArg Subtype.val hs))
  have hmod := Equiv.Perm.card_compl_support_modEq hf3
  rw [hsupp, Finset.card_empty] at hmod
  have hcard : Nat.card B = Fintype.card {v : V // v ∈ B ∧ v ≠ 1} + 1 := by
    rw [← Nat.card_eq_fintype_card, card_nontrivial]
    have : 0 < Nat.card B := Nat.card_pos
    omega
  rw [hcard]
  calc Fintype.card {v : V // v ∈ B ∧ v ≠ 1} + 1 ≡ 0 + 1 [MOD 3] :=
        Nat.ModEq.add_right 1 hmod.symm
    _ = 1 := rfl

@[expose] def fixIn (B : Subgroup V) (τ : MulAut V) : Subgroup V where
  carrier := {v | v ∈ B ∧ τ v = v}
  one_mem' := ⟨B.one_mem, map_one τ⟩
  mul_mem' := fun ha hb => ⟨B.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  inv_mem' := fun ha => ⟨B.inv_mem ha.1, by rw [map_inv, ha.2]⟩

omit [Finite V] in
theorem fixIn_le (B : Subgroup V) (τ : MulAut V) : fixIn B τ ≤ B := fun _ hv => hv.1

theorem exists_eq_mul_of_card_fix_sq_le (hV : ∀ a b : V, a * b = b * a) (B : Subgroup V)
    (τ : MulAut V) (hτ : ∀ v, τ v ∈ B ↔ v ∈ B) (hτ2 : ∀ v ∈ B, τ (τ v) = v)
    (hB2 : ∀ v ∈ B, v * v = 1) (hcard : Nat.card (fixIn B τ) ^ 2 ≤ Nat.card B) :
    ∀ v ∈ B, τ v = v → ∃ c ∈ B, v = τ c * c := by
  let ψ : ↥B →* ↥B :=
    { toFun := fun c => ⟨τ c * c, B.mul_mem ((hτ c).2 c.2) c.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change τ ((a : V) * b) * ((a : V) * b) = τ a * a * (τ b * b)
        rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (τ b) (a : V), hV (τ b) (a : V),
          mul_assoc]) }
  have hψ : ∀ c : ↥B, ((ψ c : ↥B) : V) = τ c * c := fun _ => rfl
  let F := (fixIn B τ).subgroupOf B
  have hker : ψ.ker = F := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hc
      have h1 : τ c * c = 1 := congrArg Subtype.val hc
      refine ⟨c.2, ?_⟩
      have h2 : (c : V) * c = 1 := hB2 c c.2
      calc τ c = τ c * c * c := by rw [mul_assoc, h2, mul_one]
        _ = c := by rw [h1, one_mul]
    · intro hc
      apply Subtype.ext
      change τ c * c = 1
      rw [hc.2]
      exact hB2 c c.2
  have hrange : ψ.range ≤ F := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_subgroupOf, hψ]
    refine ⟨B.mul_mem ((hτ c).2 c.2) c.2, ?_⟩
    rw [map_mul, hτ2 c c.2, hV]
  have hFcard : Nat.card F = Nat.card (fixIn B τ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fixIn_le B τ)).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hFcard] at hmul
  have hpos : 0 < Nat.card (fixIn B τ) := Nat.card_pos
  have hge : Nat.card F ≤ Nat.card ψ.range := by
    rw [hFcard]
    by_contra hlt
    push Not at hlt
    have : Nat.card (fixIn B τ) * Nat.card ψ.range < Nat.card (fixIn B τ) ^ 2 := by
      rw [sq]
      exact Nat.mul_lt_mul_of_pos_left hlt hpos
    omega
  have heq : ψ.range = F := Subgroup.eq_of_le_of_card_ge hrange hge
  intro v hv hτv
  have hmem : (⟨v, hv⟩ : ↥B) ∈ ψ.range := by
    rw [heq, Subgroup.mem_subgroupOf]
    exact ⟨hv, hτv⟩
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm⟩

theorem card_fix_sq_le_of_conj_inv (B : Subgroup V) (τ β : MulAut V)
    (hβ : ∀ v, β v ∈ B ↔ v ∈ B) (hβ3 : ∀ v ∈ B, (β ^ 3) v = v)
    (hβfix : ∀ v ∈ B, β v = v → v = 1) (hτβ : ∀ v ∈ B, τ (β v) = (β ^ 2) (τ v)) :
    Nat.card (fixIn B τ) ^ 2 ≤ Nat.card B := by
  let F := fixIn B τ
  let m : F × F → B := fun p => ⟨p.1 * β p.2, B.mul_mem p.1.2.1 ((hβ _).2 p.2.2.1)⟩
  have hm : Function.Injective m := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    have h' : (x : V) * β y = x' * β y' := congrArg Subtype.val hxy
    have hcF : (y' : V) * (y : V)⁻¹ ∈ F := F.mul_mem y'.2 (F.inv_mem y.2)
    have hw : (x' : V)⁻¹ * x = β ((y' : V) * (y : V)⁻¹) := by
      rw [map_mul, map_inv]
      calc (x' : V)⁻¹ * x = (x' : V)⁻¹ * (x * β y) * (β y)⁻¹ := by group
        _ = (x' : V)⁻¹ * (x' * β y') * (β y)⁻¹ := by rw [h']
        _ = β y' * (β y)⁻¹ := by group
    have hwF : (x' : V)⁻¹ * x ∈ F := F.mul_mem (F.inv_mem x'.2) x.2
    set c := (y' : V) * (y : V)⁻¹ with hc
    have h1 : β c = (β ^ 2) c := by
      have e1 : τ (β c) = β c := by rw [← hw]; exact hwF.2
      have e2 : τ (β c) = (β ^ 2) c := by rw [hτβ c hcF.1, hcF.2]
      rw [← e1, e2]
    have hc1 : c = 1 := by
      apply hβfix c hcF.1
      have e3 : (β ^ 3) c = c := hβ3 c hcF.1
      have e7 : (β ^ 2) c = c := by
        calc (β ^ 2) c = β (β c) := by rw [sq, MulAut.mul_apply]
          _ = β ((β ^ 2) c) := by rw [h1]
          _ = (β ^ 3) c := by rw [pow_succ' β 2, MulAut.mul_apply]
          _ = c := e3
      rw [h1, e7]
    have hyy : y' = y := by
      apply Subtype.ext
      have : (y' : V) * (y : V)⁻¹ = 1 := hc1
      exact mul_inv_eq_one.mp this
    have hxx : x' = x := by
      apply Subtype.ext
      have : (x' : V)⁻¹ * x = 1 := by rw [hw, hc1, map_one]
      exact (inv_mul_eq_one.mp this)
    rw [hxx, hyy]
  calc Nat.card F ^ 2 = Nat.card (F × F) := by rw [Nat.card_prod, sq]
    _ ≤ Nat.card B := Nat.card_le_card_of_injective m hm

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
