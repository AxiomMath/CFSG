module

public import CFSG.Quasithin.H13.A7Offender

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup

@[expose] def fix2 (a b : Fin 7) : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ (MulAction.stabilizer (Perm (Fin 7)) a ⊓
    MulAction.stabilizer (Perm (Fin 7)) b)

theorem mem_fix2 {a b : Fin 7} {σ : Perm (Fin 7)} :
    σ ∈ fix2 a b ↔ σ ∈ alternatingGroup (Fin 7) ∧ σ a = a ∧ σ b = b := by
  simp only [fix2, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]

theorem card_compl_pair : ∀ a b : Fin 7, a ≠ b →
    (Finset.univ.filter fun x : Fin 7 => x ≠ a ∧ x ≠ b).card = 5 := by
  decide

theorem card_fix2_le {a b : Fin 7} (hab : a ≠ b) : Nat.card (fix2 a b) ≤ 60 := by
  classical
  set p : Fin 7 → Prop := fun x => x ≠ a ∧ x ≠ b with hp
  have hpf : ∀ σ : Perm (Fin 7), σ a = a → σ b = b → ∀ x, p (σ x) ↔ p x := by
    intro σ ha hb x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (h ▸ ha), fun h => h2 (h ▸ hb)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (σ.injective (h.trans ha.symm)),
        fun h => h2 (σ.injective (h.trans hb.symm))⟩
  let f : fix2 a b → alternatingGroup {x // p x} := fun σ =>
    ⟨(σ : Perm (Fin 7)).subtypePerm (hpf σ (mem_fix2.1 σ.2).2.1 (mem_fix2.1 σ.2).2.2), by
      rw [mem_alternatingGroup, sign_subtypePerm]
      · exact (mem_fix2.1 σ.2).1
      · intro x hx
        refine ⟨fun h => hx (h ▸ (mem_fix2.1 σ.2).2.1), fun h => hx (h ▸ (mem_fix2.1 σ.2).2.2)⟩⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have h1 := congrArg (fun s : alternatingGroup {x // p x} => (s : Perm {x // p x})) h
    apply Subtype.ext
    refine Equiv.ext fun x => ?_
    by_cases hx : p x
    · have := congrArg (fun s : Perm {x // p x} => (s ⟨x, hx⟩ : Fin 7)) h1
      simpa [f] using this
    · simp only [hp, not_and_or, not_not] at hx
      rcases hx with rfl | rfl
      · rw [(mem_fix2.1 σ.2).2.1, (mem_fix2.1 τ.2).2.1]
      · rw [(mem_fix2.1 σ.2).2.2, (mem_fix2.1 τ.2).2.2]
  have hcard : Nat.card {x // p x} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_compl_pair a b hab
  have : Nontrivial {x // p x} := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  calc Nat.card (fix2 a b) ≤ Nat.card (alternatingGroup {x // p x}) :=
        Nat.card_le_card_of_injective f hf
    _ = 60 := by rw [nat_card_alternatingGroup, hcard]; rfl

theorem fix_or_swap {a b : Fin 7} (hab : a ≠ b) {x : Perm (Fin 7)}
    (hx : x * swap a b = swap a b * x) : (x a = a ∧ x b = b) ∨ (x a = b ∧ x b = a) := by
  have h1 : swap (x a) (x b) = swap a b := by
    rw [swap_apply_apply, hx, mul_inv_cancel_right]
  have hne : x a ≠ x b := fun h => hab (x.injective h)
  have hxa := congrArg (fun s : Perm (Fin 7) => s (x a)) h1
  simp only [swap_apply_left] at hxa
  by_cases h2 : x a = a
  · left
    rw [h2, swap_apply_left] at hxa
    exact ⟨h2, hxa⟩
  · by_cases h3 : x a = b
    · right
      rw [h3, swap_apply_right] at hxa
      exact ⟨h3, hxa⟩
    · rw [swap_apply_of_ne_of_ne h2 h3] at hxa
      exact absurd hxa.symm hne

theorem comm_apply_of_comm_swap {a b : Fin 7} (hab : a ≠ b) {x y : Perm (Fin 7)}
    (hx : x * swap a b = swap a b * x) (hy : y * swap a b = swap a b * y) :
    (x * y * x⁻¹ * y⁻¹) a = a := by
  have hinv : ∀ {z : Perm (Fin 7)} {u v : Fin 7}, z u = v → z⁻¹ v = u := fun h =>
    Perm.inv_eq_iff_eq.mpr h.symm
  simp only [Perm.mul_apply]
  rcases fix_or_swap hab hx with ⟨xa, xb⟩ | ⟨xa, xb⟩ <;>
    rcases fix_or_swap hab hy with ⟨ya, yb⟩ | ⟨ya, yb⟩
  · rw [hinv ya, hinv xa, ya, xa]
  · rw [hinv yb, hinv xb, yb, xa]
  · rw [hinv ya, hinv xb, yb, xb]
  · rw [hinv yb, hinv xa, ya, xb]

theorem le_fix2_of_perfect {a b : Fin 7} (hab : a ≠ b) {X : Subgroup (Perm (Fin 7))}
    (hX : ⁅X, X⁆ = X) (hXA : X ≤ alternatingGroup (Fin 7))
    (hc : ∀ x ∈ X, x * swap a b = swap a b * x) : X ≤ fix2 a b := by
  have hstab : ∀ c : Fin 7, (c = a ∨ c = b) → X ≤ MulAction.stabilizer (Perm (Fin 7)) c := by
    intro c hcab
    rw [← hX, Subgroup.commutator_le]
    intro x hx y hy
    rw [MulAction.mem_stabilizer_iff, Perm.smul_def, commutatorElement_def]
    rcases hcab with rfl | rfl
    · exact comm_apply_of_comm_swap hab (hc x hx) (hc y hy)
    · rw [swap_comm] at hc
      exact comm_apply_of_comm_swap (Ne.symm hab) (hc x hx) (hc y hy)
  exact le_inf hXA (le_inf (hstab a (Or.inl rfl)) (hstab b (Or.inr rfl)))

theorem cycle_mem_fix2 {a b i k l : Fin 7} (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) (hla : l ≠ a) (hlb : l ≠ b) (hik : i ≠ k) (hil : i ≠ l) :
    swap i l * swap i k ∈ fix2 a b := by
  rw [mem_fix2, mem_alternatingGroup, map_mul, sign_swap hil, sign_swap hik]
  refine ⟨by decide, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hia.symm hka.symm,
      swap_apply_of_ne_of_ne hia.symm hla.symm]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hib.symm hkb.symm,
      swap_apply_of_ne_of_ne hib.symm hlb.symm]

theorem fix_of_commute_fix2 {a b : Fin 7} {g : Perm (Fin 7)}
    (hg : ∀ x ∈ fix2 a b, g * x = x * g) {i : Fin 7} (hia : i ≠ a) (hib : i ≠ b) : g i = i := by
  classical
  by_contra hne
  have hs3 : 1 < (Finset.univ \ {a, b, i, g i} : Finset (Fin 7)).card := by
    have h4 : ({a, b, i, g i} : Finset (Fin 7)).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_univ_sdiff, Fintype.card_fin]
    omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 hs3
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk hl
  obtain ⟨hka, hkb, hki, hkj⟩ := hk
  obtain ⟨hla, hlb, hli, hlj⟩ := hl
  have hσ := cycle_mem_fix2 hia hib hka hkb hla hlb (Ne.symm hki) (Ne.symm hli)
  have h1 := congrArg (fun s : Perm (Fin 7) => s i) (hg _ hσ)
  simp only [Perm.mul_apply] at h1
  rw [swap_apply_left, swap_apply_of_ne_of_ne hki hkl,
    swap_apply_of_ne_of_ne hne (Ne.symm hkj), swap_apply_of_ne_of_ne hne (Ne.symm hlj)] at h1
  exact hki (g.injective h1)

@[expose] def evenOnF (a b : Fin 7) : Subgroup (Perm (Fin 7)) where
  carrier := {g | (g a = a ∧ g b = b ∧ sign g = 1) ∨ (g a = b ∧ g b = a ∧ sign g = -1)}
  one_mem' := Or.inl ⟨rfl, rfl, map_one _⟩
  mul_mem' := by
    rintro x y (⟨xa, xb, xs⟩ | ⟨xa, xb, xs⟩) (⟨ya, yb, ys⟩ | ⟨ya, yb, ys⟩)
    · exact Or.inl ⟨by rw [Perm.mul_apply, ya, xa], by rw [Perm.mul_apply, yb, xb],
        by rw [map_mul, xs, ys, mul_one]⟩
    · exact Or.inr ⟨by rw [Perm.mul_apply, ya, xb], by rw [Perm.mul_apply, yb, xa],
        by rw [map_mul, xs, ys, one_mul]⟩
    · exact Or.inr ⟨by rw [Perm.mul_apply, ya, xa], by rw [Perm.mul_apply, yb, xb],
        by rw [map_mul, xs, ys, mul_one]⟩
    · exact Or.inl ⟨by rw [Perm.mul_apply, ya, xb], by rw [Perm.mul_apply, yb, xa],
        by rw [map_mul, xs, ys]; rfl⟩
  inv_mem' := by
    rintro x (⟨xa, xb, xs⟩ | ⟨xa, xb, xs⟩)
    · exact Or.inl ⟨Perm.inv_eq_iff_eq.mpr xa.symm, Perm.inv_eq_iff_eq.mpr xb.symm,
        by rw [map_inv, xs, inv_one]⟩
    · exact Or.inr ⟨Perm.inv_eq_iff_eq.mpr xb.symm, Perm.inv_eq_iff_eq.mpr xa.symm,
        by rw [map_inv, xs]; rfl⟩

theorem fix2_le_evenOnF (a b : Fin 7) : fix2 a b ≤ evenOnF a b := fun _ hσ =>
  Or.inl ⟨(mem_fix2.1 hσ).2.1, (mem_fix2.1 hσ).2.2, (mem_fix2.1 hσ).1⟩

theorem mem_evenOnF_of_commute {a b : Fin 7} (hab : a ≠ b) {g : Perm (Fin 7)}
    (hg : ∀ x ∈ fix2 a b, g * x = x * g) : g ∈ evenOnF a b := by
  have hF : ∀ i, i ≠ a → i ≠ b → g i = i := fun i hia hib => fix_of_commute_fix2 hg hia hib
  have hga : g a = a ∨ g a = b := by
    by_contra h
    rw [not_or] at h
    exact h.1 (g.injective (hF (g a) h.1 h.2))
  rcases hga with hga | hga
  · have hgb : g b = b := by
      by_contra h
      have hb' : g b ≠ a := fun h' => hab (g.injective (hga.trans h'.symm))
      exact h (g.injective (hF (g b) hb' h))
    have hg1 : g = 1 := Equiv.ext fun i => by
      by_cases hia : i = a
      · rw [hia, hga]; rfl
      by_cases hib : i = b
      · rw [hib, hgb]; rfl
      exact hF i hia hib
    exact Or.inl ⟨hga, hgb, by rw [hg1, map_one]⟩
  · have hgb : g b = a := by
      by_contra h
      have hb' : g b ≠ b := fun h' => hab (g.injective (hga.trans h'.symm))
      exact hb' (g.injective (hF (g b) h hb'))
    have hgs : g = swap a b := Equiv.ext fun i => by
      by_cases hia : i = a
      · rw [hia, hga, swap_apply_left]
      by_cases hib : i = b
      · rw [hib, hgb, swap_apply_right]
      rw [hF i hia hib, swap_apply_of_ne_of_ne hia hib]
    exact Or.inr ⟨hga, hgb, by rw [hgs, sign_swap hab]⟩

theorem swap_not_mem_sup {a b c d : Fin 7} (hab : a ≠ b) (hca : c ≠ a) (hda : d ≠ a)
    (hcd : c ≠ d) {R : Subgroup (Perm (Fin 7))}
    (hR : ∀ r ∈ R, ∀ x ∈ fix2 a b, r * x = x * r) : swap c d ∉ fix2 a b ⊔ R := by
  intro h
  rcases sup_le (fix2_le_evenOnF a b) (fun r hr => mem_evenOnF_of_commute hab (hR r hr)) h with
    ⟨-, -, hs⟩ | ⟨h1, -, -⟩
  · rw [sign_swap hcd] at hs
    exact absurd hs (by decide)
  · rw [swap_apply_of_ne_of_ne hca.symm hda.symm] at h1
    exact hab h1

end CFSG.Quasithin.Vol2.Ch11.O10
