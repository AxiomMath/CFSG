module

public import CFSG.Quasithin.EmptyFaithful.SzN31FactRA

public section

namespace CFSG.Quasithin.SzN31

section FactRB

variable {p : ℕ} {Q : Type*} [Group Q]

@[expose] def fixSub (σ : MulAut Q) (L : Subgroup Q) : Subgroup Q where
  carrier := {x | x ∈ L ∧ σ x = x}
  mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨L.mul_mem ha hb, by rw [map_mul, ha', hb']⟩
  one_mem' := ⟨L.one_mem, map_one σ⟩
  inv_mem' := fun ⟨ha, ha'⟩ => ⟨L.inv_mem ha, by rw [map_inv, ha']⟩

@[expose] def invSub (σ : MulAut Q) (L : Subgroup Q) (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) :
    Subgroup Q where
  carrier := {x | x ∈ L ∧ σ x = x⁻¹}
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
    ⟨L.mul_mem ha hb, by
      rw [map_mul, ha', hb', mul_inv_rev]
      exact (Commute.inv_inv (hL a ha b hb)).eq⟩
  one_mem' := ⟨L.one_mem, by simp⟩
  inv_mem' := fun ⟨ha, ha'⟩ => ⟨L.inv_mem ha, by rw [map_inv, ha']⟩

theorem fixSub_le (σ : MulAut Q) (L : Subgroup Q) : fixSub σ L ≤ L := fun _ hx => hx.1

theorem invSub_le (σ : MulAut Q) (L : Subgroup Q) (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) :
    invSub σ L hL ≤ L := fun _ hx => hx.1

theorem exists_fix_inv_decomp (hp : p.Prime) (hp2 : p ≠ 2) {σ : MulAut Q} (hσ : ∀ x, σ (σ x) = x)
    {L : Subgroup Q} (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hexp : ∀ x ∈ L, x ^ p = 1)
    (hinv : ∀ x ∈ L, σ x ∈ L) {x : Q} (hx : x ∈ L) :
    ∃ u ∈ fixSub σ L, ∃ v ∈ invSub σ L hL, x = u * v := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hc : σ x ∈ L := hinv x hx
  have hac : x * σ x = σ x * x := hL _ hx _ hc
  have h1 : x * σ x ∈ L := L.mul_mem hx hc
  have h2 : x * (σ x)⁻¹ ∈ L := L.mul_mem hx (L.inv_mem hc)
  refine ⟨(x * σ x) ^ (k + 1), ⟨L.pow_mem h1 _, ?_⟩, (x * (σ x)⁻¹) ^ (k + 1),
    ⟨L.pow_mem h2 _, ?_⟩, ?_⟩
  · rw [map_pow, map_mul, hσ, hac]
  · rw [map_pow, map_mul, map_inv, hσ, ← inv_pow, mul_inv_rev, inv_inv]
  · rw [← Commute.mul_pow (hL _ h1 _ h2)]
    have e1 : (x * σ x) * (x * (σ x)⁻¹) = x * x := by
      calc (x * σ x) * (x * (σ x)⁻¹) = x * (σ x * x) * (σ x)⁻¹ := by group
        _ = x * (x * σ x) * (σ x)⁻¹ := by rw [← hac]
        _ = x * x := by group
    have e2 : 2 * (k + 1) = p + 1 := by omega
    rw [e1, ← pow_two, ← pow_mul, e2, pow_succ, hexp x hx, one_mul]

theorem scalar_of_dichotomy (hp : p.Prime) (hp2 : p ≠ 2) {σ : MulAut Q} (hσ : ∀ x, σ (σ x) = x)
    {L : Subgroup Q} (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hexp : ∀ x ∈ L, x ^ p = 1)
    (hinv : ∀ x ∈ L, σ x ∈ L) (hd : fixSub σ L = ⊥ ∨ fixSub σ L = L) :
    (∀ x ∈ L, σ x = x) ∨ (∀ x ∈ L, σ x = x⁻¹) := by
  rcases hd with h | h
  · right
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_fix_inv_decomp hp hp2 hσ hL hexp hinv hx
    rw [h, Subgroup.mem_bot] at hu
    subst hu
    simpa using hv.2
  · left
    intro x hx
    rw [← h] at hx
    exact hx.2

theorem scalar_of_card_prime (hp : p.Prime) (hp2 : p ≠ 2) [Finite Q] {σ : MulAut Q}
    (hσ : ∀ x, σ (σ x) = x) {L : Subgroup Q} (hL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hexp : ∀ x ∈ L, x ^ p = 1) (hinv : ∀ x ∈ L, σ x ∈ L) (hcard : Nat.card L = p) :
    (∀ x ∈ L, σ x = x) ∨ (∀ x ∈ L, σ x = x⁻¹) := by
  refine scalar_of_dichotomy hp hp2 hσ hL hexp hinv ?_
  have hd : Nat.card (fixSub σ L) ∣ p := hcard ▸ Subgroup.card_dvd_of_le (fixSub_le σ L)
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · left
    exact Subgroup.eq_bot_of_card_eq _ h
  · right
    exact Subgroup.eq_of_le_of_card_ge (fixSub_le σ L) (by rw [h, hcard])

variable {Bh : Type*} [Group Bh]

theorem comm_of_sq_eq_one (hB : ∀ b : Bh, b * b = 1) (b c : Bh) : b * c = c * b := by
  have h := hB (b * c)
  calc b * c = (b * c)⁻¹ := (eq_inv_of_mul_eq_one_left h)
    _ = c⁻¹ * b⁻¹ := mul_inv_rev b c
    _ = c * b := by rw [inv_eq_of_mul_eq_one_right (hB c), inv_eq_of_mul_eq_one_right (hB b)]

theorem act_invol (act : Bh →* MulAut Q) (hB : ∀ b : Bh, b * b = 1) (b : Bh) (x : Q) :
    act b (act b x) = x := by
  have := congrArg (fun f : MulAut Q => f x) (by rw [← map_mul, hB b, map_one] : act b * act b = 1)
  simpa using this

theorem act_comm (act : Bh →* MulAut Q) (hB : ∀ b : Bh, b * b = 1) (b c : Bh) (x : Q) :
    act b (act c x) = act c (act b x) := by
  have := congrArg (fun f : MulAut Q => f x) (by rw [← map_mul, ← map_mul, comm_of_sq_eq_one hB b c] :
    act b * act c = act c * act b)
  simpa using this

theorem exists_invariant_line_family (hp : p.Prime) (hp2 : p ≠ 2) [Finite Q] {I : Type*} (σ : I → MulAut Q)
    (hσ : ∀ b x, σ b (σ b x) = x) (hσc : ∀ b c x, σ b (σ c x) = σ c (σ b x))
    {W : Subgroup Q} (hW : W ≠ ⊥)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hexp : ∀ x ∈ W, x ^ p = 1)
    (hinv : ∀ b : I, ∀ x ∈ W, σ b x ∈ W) :
    ∃ L : Subgroup Q, L ≤ W ∧ Nat.card L = p ∧ ∀ b : I, ∀ x ∈ L, σ b x ∈ L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hex : ∃ n, ∃ L : Subgroup Q, (L ≤ W ∧ L ≠ ⊥ ∧ ∀ b : I, ∀ x ∈ L, σ b x ∈ L) ∧
      Nat.card L = n := ⟨_, W, ⟨le_rfl, hW, hinv⟩, rfl⟩
  obtain ⟨L, ⟨hLW, hL0, hLinv⟩, hLn⟩ := Nat.find_spec hex
  have hmin : ∀ M : Subgroup Q, M ≤ W → M ≠ ⊥ → (∀ b : I, ∀ x ∈ M, σ b x ∈ M) →
      Nat.card L ≤ Nat.card M := by
    intro M hM1 hM2 hM3
    rw [hLn]
    exact Nat.find_min' hex ⟨M, ⟨hM1, hM2, hM3⟩, rfl⟩
  have hLc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy => hcomm x (hLW hx) y (hLW hy)
  have hLe : ∀ x ∈ L, x ^ p = 1 := fun x hx => hexp x (hLW hx)
  have hscal : ∀ b : I, (∀ x ∈ L, σ b x = x) ∨ (∀ x ∈ L, σ b x = x⁻¹) := by
    intro b
    refine scalar_of_dichotomy hp hp2 (hσ b) hLc hLe (hLinv b) ?_
    by_cases hf : fixSub (σ b) L = ⊥
    · exact Or.inl hf
    · right
      refine Subgroup.eq_of_le_of_card_ge (fixSub_le _ L) (hmin _ (le_trans (fixSub_le _ L) hLW) hf ?_)
      intro c x hx
      refine ⟨hLinv c x hx.1, ?_⟩
      rw [hσc b c x, hx.2]
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL0
  have hx1' : (x : Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hZ : ∀ b : I, ∀ y ∈ Subgroup.zpowers (x : Q), σ b y ∈ Subgroup.zpowers (x : Q) := by
    intro b y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow]
    rcases hscal b with h | h
    · rw [h _ x.2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    · rw [h _ x.2, inv_zpow, ← zpow_neg]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hZL : Subgroup.zpowers (x : Q) ≤ L := (Subgroup.zpowers_le).2 x.2
  have hZ0 : Subgroup.zpowers (x : Q) ≠ ⊥ := by
    intro h
    exact hx1' ((Subgroup.mem_bot).1 (h ▸ Subgroup.mem_zpowers (x : Q)))
  have hZeq : Subgroup.zpowers (x : Q) = L :=
    Subgroup.eq_of_le_of_card_ge hZL (hmin _ (le_trans hZL hLW) hZ0 hZ)
  refine ⟨L, hLW, ?_, hLinv⟩
  rw [← hZeq, Nat.card_zpowers]
  exact orderOf_eq_prime (hLe _ x.2) hx1'

theorem exists_invariant_line_ambient (hp : p.Prime) (hp2 : p ≠ 2) [Finite Q] (act : Bh →* MulAut Q)
    (hB : ∀ b : Bh, b * b = 1) {W : Subgroup Q} (hW : W ≠ ⊥)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hexp : ∀ x ∈ W, x ^ p = 1)
    (hinv : ∀ b : Bh, ∀ x ∈ W, act b x ∈ W) :
    ∃ L : Subgroup Q, L ≤ W ∧ Nat.card L = p ∧ ∀ b : Bh, ∀ x ∈ L, act b x ∈ L :=
  exists_invariant_line_family hp hp2 (fun b => act b) (act_invol act hB) (act_comm act hB) hW hcomm
    hexp hinv

end FactRB

end CFSG.Quasithin.SzN31
