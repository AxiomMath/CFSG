module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.F53Mod

open Equiv
open scoped Pointwise

theorem act_mul_apply {n : ℕ} (M : Model n) (σ τ : Perm (Fin n)) (w : M.W) :
    M.act (σ * τ) w = M.act σ (M.act τ w) := by
  rw [map_mul]; rfl

theorem act_inv_act {n : ℕ} (M : Model n) (σ : Perm (Fin n)) (w : M.W) :
    M.act σ⁻¹ (M.act σ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem act_act_inv {n : ℕ} (M : Model n) (σ : Perm (Fin n)) (w : M.W) :
    M.act σ (M.act σ⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem mem_fixW_closure {n : ℕ} (M : Model n) {S : Set (Perm (Fin n))} {w : M.W} :
    w ∈ fixW M (Subgroup.closure S) ↔ ∀ s ∈ S, M.act s w = w := by
  constructor
  · intro h s hs
    exact h s (Subgroup.subset_closure hs)
  · intro h b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => rw [map_one]; rfl
    | mul x y _ _ hx hy => rw [map_mul]; exact (congrArg (M.act x) hy).trans hx
    | inv x _ hx =>
      calc M.act x⁻¹ w = M.act x⁻¹ (M.act x w) := by rw [hx]
        _ = w := act_inv_act M x w

theorem mem_fixW_zpowers {n : ℕ} (M : Model n) {σ : Perm (Fin n)} {w : M.W} :
    w ∈ fixW M (Subgroup.zpowers σ) ↔ M.act σ w = w := by
  rw [Subgroup.zpowers_eq_closure, mem_fixW_closure]
  simp

theorem card_fixW_zpowers {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    Nat.card (fixW M (Subgroup.zpowers σ)) = Nat.card {w : M.W // M.act σ w = w} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixW_zpowers M)

theorem idx_mul_card {n : ℕ} (M : Model n) (σ : Perm (Fin n)) :
    idx M σ * Nat.card {w : M.W // M.act σ w = w} = Nat.card M.W := by
  rw [← card_fixW_zpowers]
  exact Subgroup.index_mul_card _

abbrev DsubO : Type := X1512.Delta.Dsub 5

private def fixCountO (σ : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun x : DsubO => G6.permAct 5 σ x.1 = x.1).card

private theorem card_fix_orth (σ : Perm (Fin 5)) :
    Nat.card {w : orth.W // orth.act σ w = w} = fixCountO σ := by
  classical
  unfold fixCountO
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => ?_)
  exact Subtype.ext_iff

private theorem fo_one : ∀ σ : Perm (Fin 5), σ = 1 → fixCountO σ = 16 := by decide +kernel

private theorem fo_t : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 2 = 1 → Equiv.Perm.sign σ = -1 →
    fixCountO σ = 8 := by decide +kernel

private theorem fo_d : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 2 = 1 → Equiv.Perm.sign σ = 1 →
    fixCountO σ = 4 := by decide +kernel

private theorem fo_three : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 → fixCountO σ = 4 := by
  decide +kernel

private theorem fo_four : ∀ σ : Perm (Fin 5), σ ^ 2 ≠ 1 → σ ^ 4 = 1 → fixCountO σ = 2 := by
  decide +kernel

private theorem fo_five : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 5 = 1 → fixCountO σ = 1 := by
  decide +kernel

private theorem fo_six : ∀ σ : Perm (Fin 5), σ ^ 2 ≠ 1 → σ ^ 3 ≠ 1 → σ ^ 4 ≠ 1 → σ ^ 5 ≠ 1 →
    fixCountO σ = 2 := by decide +kernel

theorem card_orth : Nat.card orth.W = 16 := X1512.card_coreMod (Or.inr rfl)

theorem idx_orth (σ : Perm (Fin 5)) :
    idx orth σ =
      if σ = 1 then 1 else if σ ^ 2 = 1 then (if Equiv.Perm.sign σ = 1 then 4 else 2)
      else if σ ^ 3 = 1 then 4 else if σ ^ 5 = 1 then 16 else 8 := by
  have h := idx_mul_card orth σ
  rw [card_fix_orth, card_orth] at h
  by_cases h1 : σ = 1
  · subst h1; rw [fo_one 1 rfl] at h; simp only [↓reduceIte]; omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : σ ^ 2 = 1
    · simp only [h2, ↓reduceIte]
      by_cases h3 : Equiv.Perm.sign σ = 1
      · simp only [h3, ↓reduceIte]; rw [fo_d σ h1 h2 h3] at h; omega
      · simp only [h3, ↓reduceIte]
        have h3' : Equiv.Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left h3
        rw [fo_t σ h1 h2 h3'] at h; omega
    · simp only [h2, ↓reduceIte]
      by_cases h3 : σ ^ 3 = 1
      · simp only [h3, ↓reduceIte]; rw [fo_three σ h1 h3] at h; omega
      · simp only [h3, ↓reduceIte]
        by_cases h5 : σ ^ 5 = 1
        · simp only [h5, ↓reduceIte]; rw [fo_five σ h1 h5] at h; omega
        · simp only [h5, ↓reduceIte]
          by_cases h4 : σ ^ 4 = 1
          · rw [fo_four σ h2 h4] at h; omega
          · rw [fo_six σ h2 h3 h4 h5] at h; omega

private def fixCountN (σ : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun c : Fin 4 → ZMod 2 => natAct σ c = c).card

private theorem card_fix_nat (σ : Perm (Fin 5)) :
    Nat.card {w : nat.W // nat.act σ w = w} = fixCountN σ := by
  classical
  unfold fixCountN
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun w => ?_)
  show Multiplicative.ofAdd (natAct σ (Multiplicative.toAdd w)) = w ↔ _
  constructor
  · intro h; exact congrArg Multiplicative.toAdd h
  · intro h; exact congrArg Multiplicative.ofAdd h

private theorem fc_one : ∀ σ : Perm (Fin 5), σ = 1 → fixCountN σ = 16 := by decide +kernel

private theorem fc_inv : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 2 = 1 → fixCountN σ = 4 := by
  decide +kernel

private theorem fc_three : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 3 = 1 → fixCountN σ = 1 := by
  decide +kernel

private theorem fc_four : ∀ σ : Perm (Fin 5), σ ^ 2 ≠ 1 → σ ^ 4 = 1 → fixCountN σ = 2 := by
  decide +kernel

private theorem fc_five : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 5 = 1 → fixCountN σ = 1 := by
  decide +kernel

private theorem fc_six : ∀ σ : Perm (Fin 5), σ ^ 2 ≠ 1 → σ ^ 3 ≠ 1 → σ ^ 4 ≠ 1 → σ ^ 5 ≠ 1 →
    fixCountN σ = 1 := by decide +kernel

theorem card_nat : Nat.card nat.W = 16 := by
  show Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem idx_nat (σ : Perm (Fin 5)) :
    idx nat σ =
      if σ = 1 then 1 else if σ ^ 2 = 1 then 4 else if σ ^ 3 = 1 then 16
      else if σ ^ 4 = 1 then 8 else 16 := by
  have h := idx_mul_card nat σ
  rw [card_fix_nat, card_nat] at h
  by_cases h1 : σ = 1
  · subst h1; rw [fc_one 1 rfl] at h; simp only [↓reduceIte]; omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : σ ^ 2 = 1
    · simp only [h2, ↓reduceIte]; rw [fc_inv σ h1 h2] at h; omega
    · simp only [h2, ↓reduceIte]
      by_cases h3 : σ ^ 3 = 1
      · simp only [h3, ↓reduceIte]; rw [fc_three σ h1 h3] at h; omega
      · simp only [h3, ↓reduceIte]
        by_cases h4 : σ ^ 4 = 1
        · simp only [h4, ↓reduceIte]; rw [fc_four σ h2 h4] at h; omega
        · simp only [h4, ↓reduceIte]
          by_cases h5 : σ ^ 5 = 1
          · rw [fc_five σ h1 h5] at h; omega
          · rw [fc_six σ h2 h3 h4 h5] at h; omega

private def fixCount3 (σ : Perm (Fin 3)) : ℕ :=
  (Finset.univ.filter fun x : X1512.Delta.Dsub 3 => G6.permAct 3 σ x.1 = x.1).card

private theorem card_fix_nat3 (σ : Perm (Fin 3)) :
    Nat.card {w : nat3.W // nat3.act σ w = w} = fixCount3 σ := by
  classical
  unfold fixCount3
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => ?_)
  exact Subtype.ext_iff

private theorem f3_one : ∀ σ : Perm (Fin 3), σ = 1 → fixCount3 σ = 4 := by decide +kernel

private theorem f3_inv : ∀ σ : Perm (Fin 3), σ ≠ 1 → σ ^ 2 = 1 → fixCount3 σ = 2 := by
  decide +kernel

private theorem f3_three : ∀ σ : Perm (Fin 3), σ ^ 2 ≠ 1 → fixCount3 σ = 1 := by decide +kernel

theorem card_nat3 : Nat.card nat3.W = 4 := X1512.card_coreMod (Or.inl rfl)

theorem idx_nat3 (σ : Perm (Fin 3)) :
    idx nat3 σ = if σ = 1 then 1 else if σ ^ 2 = 1 then 2 else 4 := by
  have h := idx_mul_card nat3 σ
  rw [card_fix_nat3, card_nat3] at h
  by_cases h1 : σ = 1
  · subst h1; rw [f3_one 1 rfl] at h; simp only [↓reduceIte]; omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : σ ^ 2 = 1
    · simp only [h2, ↓reduceIte]; rw [f3_inv σ h1 h2] at h; omega
    · simp only [h2, ↓reduceIte]; rw [f3_three σ h2] at h; omega

private theorem swap_of_odd_involution : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 2 = 1 →
    Equiv.Perm.sign σ ≠ 1 → ∃ x y : Fin 5, x ≠ y ∧ σ = Equiv.swap x y := by decide +kernel

theorem isSwap_iff (σ : Perm (Fin 5)) :
    σ.IsSwap ↔ σ ≠ 1 ∧ σ ^ 2 = 1 ∧ Equiv.Perm.sign σ ≠ 1 := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact fun h => hxy (by simpa using (congrArg (fun f => f x) h).symm)
    · rw [pow_two]; exact Equiv.swap_mul_self x y
    · rw [Equiv.Perm.sign_swap hxy]; decide
  · rintro ⟨h1, h2, h3⟩
    exact swap_of_odd_involution σ h1 h2 h3

theorem transvections (σ : Perm (Fin 5)) (h1 : σ ≠ 1) :
    4 ≤ idx nat σ ∧ (idx orth σ = 2 ↔ σ.IsSwap) := by
  rw [isSwap_iff, idx_nat, idx_orth]
  simp only [h1, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
  refine ⟨?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;> simp_all

section Span

variable {W : Type} [CommGroup W] [DecidableEq W]

@[expose] def spanF (S : Finset W) : Finset W := ∏ x ∈ S, ({1, x} : Finset W)

theorem spanF_empty : spanF (∅ : Finset W) = {1} := by
  rw [spanF, Finset.prod_empty]; rfl

theorem mem_spanF_insert {a : W} {S : Finset W} (h : a ∉ S) {z : W} :
    z ∈ spanF (insert a S) ↔ ∃ y ∈ spanF S, z = y ∨ z = a * y := by
  unfold spanF
  rw [Finset.prod_insert h, Finset.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨y, hy, Or.inl (one_mul _)⟩
    · exact ⟨y, hy, Or.inr rfl⟩
  · rintro ⟨y, hy, hz | hz⟩
    · exact ⟨1, by simp, y, hy, by rw [hz, one_mul]⟩
    · exact ⟨a, by simp, y, hy, hz.symm⟩

theorem one_mem_spanF (S : Finset W) : (1 : W) ∈ spanF S := by
  induction S using Finset.induction_on with
  | empty => simp [spanF_empty]
  | insert a S ha ih => exact (mem_spanF_insert ha).mpr ⟨1, ih, Or.inl rfl⟩

theorem subset_spanF (S : Finset W) : ∀ x ∈ S, x ∈ spanF S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (mem_spanF_insert ha).mpr ⟨1, one_mem_spanF S, Or.inr (mul_one _).symm⟩
    · exact (mem_spanF_insert ha).mpr ⟨x, ih x hx, Or.inl rfl⟩

theorem spanF_subset_closure (S : Finset W) :
    ∀ x ∈ spanF S, x ∈ Subgroup.closure (S : Set W) := by
  induction S using Finset.induction_on with
  | empty => intro x hx; simp [spanF_empty] at hx; subst hx; exact Subgroup.one_mem _
  | insert a S ha ih =>
    intro x hx
    have hmono : Subgroup.closure (S : Set W) ≤
        Subgroup.closure ((insert a S : Finset W) : Set W) := Subgroup.closure_mono (by simp)
    obtain ⟨y, hy, hx | hx⟩ := (mem_spanF_insert ha).mp hx
    · rw [hx]; exact hmono (ih y hy)
    · rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (hmono (ih y hy))

theorem spanF_mul_mem (hsq : ∀ w : W, w * w = 1) (S : Finset W) :
    ∀ x ∈ spanF S, ∀ y ∈ spanF S, x * y ∈ spanF S := by
  induction S using Finset.induction_on with
  | empty =>
    intro x hx y hy
    simp only [spanF_empty, Finset.mem_singleton] at hx hy ⊢
    subst hx; subst hy; simp
  | insert a S ha ih =>
    intro x hx y hy
    obtain ⟨s, hs, hx | hx⟩ := (mem_spanF_insert ha).mp hx <;>
      obtain ⟨t, ht, hy | hy⟩ := (mem_spanF_insert ha).mp hy <;> rw [hx, hy]
    · exact (mem_spanF_insert ha).mpr ⟨s * t, ih s hs t ht, Or.inl rfl⟩
    · exact (mem_spanF_insert ha).mpr ⟨s * t, ih s hs t ht, Or.inr (mul_left_comm _ _ _)⟩
    · exact (mem_spanF_insert ha).mpr ⟨s * t, ih s hs t ht, Or.inr (mul_assoc _ _ _)⟩
    · refine (mem_spanF_insert ha).mpr ⟨s * t, ih s hs t ht, Or.inl ?_⟩
      rw [mul_mul_mul_comm, hsq a, one_mul]

theorem closure_eq_spanF (hsq : ∀ w : W, w * w = 1) (S : Finset W) :
    ∀ x, x ∈ Subgroup.closure (S : Set W) ↔ x ∈ spanF S := by
  intro x
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact subset_spanF S y hy
    | one => exact one_mem_spanF S
    | mul a b _ _ ha hb => exact spanF_mul_mem hsq S a ha b hb
    | inv a _ ha => rw [inv_eq_of_mul_eq_one_right (hsq a)]; exact ha
  · exact spanF_subset_closure S x

end Span

@[expose] def commGensF {n : ℕ} (M : Model n) [DecidableEq M.W] (Bf : Finset (Perm (Fin n)))
    (Uf : Finset M.W) : Finset M.W :=
  (Bf ×ˢ Uf).image fun p => M.act p.1 p.2 * p.2⁻¹

theorem commW_eq_closure {n : ℕ} (M : Model n) [DecidableEq M.W] {B : Subgroup (Perm (Fin n))}
    {U : Subgroup M.W} {Bf : Finset (Perm (Fin n))} {Uf : Finset M.W}
    (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) (hU : ∀ u, u ∈ U ↔ u ∈ Uf) :
    commW M B U = Subgroup.closure (commGensF M Bf Uf : Set M.W) := by
  unfold commW
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, commGensF, Finset.coe_image, Finset.coe_product, Set.mem_image,
    Set.mem_prod, Finset.mem_coe, Prod.exists, hB, hU]
  constructor
  · rintro ⟨b, hb, u, hu, rfl⟩; exact ⟨b, u, ⟨hb, hu⟩, rfl⟩
  · rintro ⟨b, u, ⟨hb, hu⟩, rfl⟩; exact ⟨b, hb, u, hu, rfl⟩

theorem mem_commW_iff {n : ℕ} (M : Model n) [DecidableEq M.W] {B : Subgroup (Perm (Fin n))}
    {U : Subgroup M.W} {Bf : Finset (Perm (Fin n))} {Uf : Finset M.W}
    (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) (hU : ∀ u, u ∈ U ↔ u ∈ Uf) (w : M.W) :
    w ∈ commW M B U ↔ w ∈ spanF (commGensF M Bf Uf) := by
  rw [commW_eq_closure M hB hU]
  exact closure_eq_spanF M.sq _ w

theorem card_commW {n : ℕ} (M : Model n) [DecidableEq M.W] {B : Subgroup (Perm (Fin n))}
    {U : Subgroup M.W} {Bf : Finset (Perm (Fin n))} {Uf : Finset M.W}
    (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) (hU : ∀ u, u ∈ U ↔ u ∈ Uf) :
    Nat.card (commW M B U) = (spanF (commGensF M Bf Uf)).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => mem_commW_iff M hB hU w)

theorem card_fixW {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    {B : Subgroup (Perm (Fin n))} {Bf : Finset (Perm (Fin n))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) :
    Nat.card (fixW M B) =
      (Finset.univ.filter fun w : M.W => ∀ b ∈ Bf, M.act b w = w).card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  simp only [mem_fixW, hB, Finset.mem_filter, Finset.mem_univ, true_and]

@[expose] noncomputable def profile {n : ℕ} (M : Model n) (B : Subgroup (Perm (Fin n))) :
    ℕ × ℕ × ℕ :=
  (Nat.card (commW M B ⊤), Nat.card (fixW M B), Nat.card (commW M B (commW M B ⊤)))

@[expose] def profileFn {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    (Bf : Finset (Perm (Fin n))) : ℕ × ℕ × ℕ :=
  let C := spanF (commGensF M Bf Finset.univ)
  (C.card, (Finset.univ.filter fun w : M.W => ∀ b ∈ Bf, M.act b w = w).card,
    (spanF (commGensF M Bf C)).card)

theorem profile_eq {n : ℕ} (M : Model n) [Fintype M.W] [DecidableEq M.W]
    {B : Subgroup (Perm (Fin n))} {Bf : Finset (Perm (Fin n))} (hB : ∀ σ, σ ∈ B ↔ σ ∈ Bf) :
    profile M B = profileFn M Bf := by
  have hTop : ∀ u : M.W, u ∈ (⊤ : Subgroup M.W) ↔ u ∈ (Finset.univ : Finset M.W) := by
    intro u; simp
  have hC : ∀ u, u ∈ commW M B ⊤ ↔ u ∈ spanF (commGensF M Bf Finset.univ) :=
    fun u => mem_commW_iff M hB hTop u
  unfold profile profileFn
  rw [card_commW M hB hTop, card_fixW M hB, card_commW M hB hC]

instance fintypeOrthW : Fintype orth.W := inferInstanceAs (Fintype (X1512.Delta.Dsub 5))

instance decEqOrthW : DecidableEq orth.W := inferInstanceAs (DecidableEq (X1512.Delta.Dsub 5))

instance fintypeNatW : Fintype nat.W :=
  inferInstanceAs (Fintype (Multiplicative (Fin 4 → ZMod 2)))

instance decEqNatW : DecidableEq nat.W :=
  inferInstanceAs (DecidableEq (Multiplicative (Fin 4 → ZMod 2)))

@[expose] def wordSet {G : Type} [Group G] [DecidableEq G] (gens : List G) : ℕ → Finset G
  | 0 => {1}
  | k + 1 => wordSet gens k ∪ (wordSet gens k).biUnion
      (fun x => (gens.flatMap (fun g => [x * g, x * g⁻¹])).toFinset)

theorem wordSet_subset_closure {G : Type} [Group G] [DecidableEq G] (gens : List G) (k : ℕ) :
    ∀ x ∈ wordSet gens k, x ∈ Subgroup.closure {g | g ∈ gens} := by
  induction k with
  | zero => intro x hx; simp [wordSet] at hx; subst hx; exact Subgroup.one_mem _
  | succ k ih =>
    intro x hx
    simp only [wordSet, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | ⟨y, hy, g, hg, rfl | rfl⟩
    · exact ih x hx
    · exact Subgroup.mul_mem _ (ih y hy) (Subgroup.subset_closure hg)
    · exact Subgroup.mul_mem _ (ih y hy) (Subgroup.inv_mem _ (Subgroup.subset_closure hg))

theorem mem_closure_iff_of_finset {G : Type} [Group G] [DecidableEq G] {gens : List G}
    {F : Finset G} {k : ℕ} (hgens : ∀ g ∈ gens, g ∈ F) (h1 : (1 : G) ∈ F)
    (hmul : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) (hinv : ∀ a ∈ F, a⁻¹ ∈ F)
    (hword : ∀ x ∈ F, x ∈ wordSet gens k) :
    ∀ σ, σ ∈ Subgroup.closure {g | g ∈ gens} ↔ σ ∈ F := by
  intro σ
  constructor
  · intro hσ
    induction hσ using Subgroup.closure_induction with
    | mem x hx => exact hgens x hx
    | one => exact h1
    | mul a b _ _ ha hb => exact hmul a ha b hb
    | inv a _ ha => exact hinv a ha
  · exact fun h => wordSet_subset_closure gens k σ (hword σ h)

theorem mem_zpowers_iff_of_pow_eq_one {G : Type} [Group G] {σ τ : G} {m : ℕ} (hm : σ ^ m = 1)
    (hm0 : 0 < m) : τ ∈ Subgroup.zpowers σ ↔ ∃ k < m, σ ^ k = τ := by
  constructor
  · intro hτ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm0
    have h0 := Int.emod_nonneg k hm'.ne'
    have h1 := Int.emod_lt_of_pos k hm'
    refine ⟨(k % (m : ℤ)).toNat, by omega, ?_⟩
    rw [zpow_eq_zpow_emod' k hm, ← zpow_natCast, Int.toNat_of_nonneg h0]
  · rintro ⟨k, -, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) k

@[expose] def S5g : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def S5Syl : Subgroup (Perm (Fin 5)) :=
  Subgroup.closure {swap 0 1 * swap 1 2 * swap 2 3, swap 0 2}

@[expose] def S5T : Subgroup (Perm (Fin 5)) := S5Syl ⊓ alternatingGroup (Fin 5)

@[expose] def S5That : Subgroup (Perm (Fin 5)) := Subgroup.closure {swap 0 2, swap 1 3}

@[expose] def S3Syl : Subgroup (Perm (Fin 3)) := Subgroup.zpowers (swap 0 1)

@[expose, irreducible] def S5SylF : Finset (Perm (Fin 5)) :=
  {1, S5g, S5g ^ 2, S5g ^ 3, swap 0 2, S5g * swap 0 2, S5g ^ 2 * swap 0 2, S5g ^ 3 * swap 0 2}

theorem mem_S5Syl_iff (σ : Perm (Fin 5)) : σ ∈ S5Syl ↔ σ ∈ S5SylF := by
  have h := mem_closure_iff_of_finset (gens := [S5g, swap 0 2]) (F := S5SylF) (k := 4)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) σ
  have e : ({swap 0 1 * swap 1 2 * swap 2 3, swap 0 2} : Set (Perm (Fin 5))) =
      {g | g ∈ [S5g, swap 0 2]} := by
    ext g; simp [S5g]
  unfold S5Syl
  rw [e]
  exact h

@[expose, irreducible] def S5TF : Finset (Perm (Fin 5)) :=
  {1, S5g ^ 2, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2}

theorem mem_S5T_iff (σ : Perm (Fin 5)) : σ ∈ S5T ↔ σ ∈ S5TF := by
  unfold S5T
  rw [Subgroup.mem_inf, mem_S5Syl_iff, Equiv.Perm.mem_alternatingGroup]
  revert σ
  decide +kernel

@[expose, irreducible] def S5ThatF : Finset (Perm (Fin 5)) :=
  {1, swap 0 2, swap 1 3, swap 0 2 * swap 1 3}

theorem mem_S5That_iff (σ : Perm (Fin 5)) : σ ∈ S5That ↔ σ ∈ S5ThatF := by
  have h := mem_closure_iff_of_finset (gens := [swap 0 2, swap 1 3]) (F := S5ThatF) (k := 2)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) σ
  have e : ({swap 0 2, swap 1 3} : Set (Perm (Fin 5))) = {g | g ∈ [swap 0 2, swap 1 3]} := by
    ext g; simp
  unfold S5That
  rw [e]
  exact h

private theorem zpowers_swap02 (τ : Perm (Fin 5)) :
    τ ∈ Subgroup.zpowers (swap (0 : Fin 5) 2) ↔ τ ∈ ({1, swap 0 2} : Finset (Perm (Fin 5))) := by
  rw [mem_zpowers_iff_of_pow_eq_one (m := 2) (by decide +kernel) (by norm_num)]
  revert τ
  decide +kernel

private theorem zpowers_z (τ : Perm (Fin 5)) :
    τ ∈ Subgroup.zpowers (swap (0 : Fin 5) 2 * swap 1 3) ↔
      τ ∈ ({1, swap 0 2 * swap 1 3} : Finset (Perm (Fin 5))) := by
  rw [mem_zpowers_iff_of_pow_eq_one (m := 2) (by decide +kernel) (by norm_num)]
  revert τ
  decide +kernel

private theorem zpowers_g (τ : Perm (Fin 5)) :
    τ ∈ Subgroup.zpowers (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3) ↔
      τ ∈ ({1, S5g, S5g ^ 2, S5g ^ 3} : Finset (Perm (Fin 5))) := by
  rw [mem_zpowers_iff_of_pow_eq_one (m := 4) (by decide +kernel) (by norm_num)]
  revert τ
  decide +kernel

set_option maxRecDepth 100000 in
theorem profile_orth :
    profile orth (Subgroup.zpowers (swap (0 : Fin 5) 2)) = (2, 8, 1) ∧
    profile orth (Subgroup.zpowers (swap (0 : Fin 5) 2 * swap 1 3)) = (4, 4, 1) ∧
    profile orth S5That = (4, 4, 1) ∧ profile orth S5T = (8, 2, 2) ∧
    profile orth (Subgroup.zpowers (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3)) = (8, 2, 4) ∧
    profile orth S5Syl = (8, 2, 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [profile_eq orth zpowers_swap02]; decide +kernel
  · rw [profile_eq orth zpowers_z]; decide +kernel
  · rw [profile_eq orth mem_S5That_iff]; decide +kernel
  · rw [profile_eq orth mem_S5T_iff]; decide +kernel
  · rw [profile_eq orth zpowers_g]; decide +kernel
  · rw [profile_eq orth mem_S5Syl_iff]; decide +kernel

set_option maxRecDepth 100000 in
theorem profile_nat :
    profile nat (Subgroup.zpowers (swap (0 : Fin 5) 2)) = (4, 4, 1) ∧
    profile nat (Subgroup.zpowers (swap (0 : Fin 5) 2 * swap 1 3)) = (4, 4, 1) ∧
    profile nat S5That = (8, 2, 2) ∧ profile nat S5T = (4, 4, 1) ∧
    profile nat (Subgroup.zpowers (swap (0 : Fin 5) 1 * swap 1 2 * swap 2 3)) = (8, 2, 4) ∧
    profile nat S5Syl = (8, 2, 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [profile_eq nat zpowers_swap02]; decide +kernel
  · rw [profile_eq nat zpowers_z]; decide +kernel
  · rw [profile_eq nat mem_S5That_iff]; decide +kernel
  · rw [profile_eq nat mem_S5T_iff]; decide +kernel
  · rw [profile_eq nat zpowers_g]; decide +kernel
  · rw [profile_eq nat mem_S5Syl_iff]; decide +kernel

end CFSG.Quasithin.F53Mod
