module

public import CFSG.Quasithin.Background.SzG11NCGalois

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin.SzG11NC

theorem two_eq_zero_of_card_four {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) :
    (2 : E) = 0 := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨p, hp⟩ := CharP.exists E
  obtain ⟨n, hpp, hn⟩ := FiniteField.card E p
  have hcard : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card]; exact hE
  have h4 : p ^ (n : ℕ) = 4 := by rw [← hn]; exact hcard
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 2 := by
      have : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
      rw [h4] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hdvd)
  subst hp2
  simpa using CharP.cast_eq_zero E 2

section

variable {E : Type} [Field E] {M : Type} [AddCommGroup M] [Module E M]

@[expose] def fixAdd (x : M →+ M) : AddSubgroup M := AddMonoidHom.eqLocus x (AddMonoidHom.id M)

theorem mem_fixAdd {x : M →+ M} {m : M} : m ∈ fixAdd x ↔ x m = m := Iff.rfl

theorem frob_decomp [Finite E] (hE : Nat.card E = 4) (x : M →+ M)
    (hx : ∀ (e : E) (m : M), x (e • m) = e ^ 2 • x m) (hxx : ∀ m, x (x m) = m) :
    ∃ ω : E, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 = ω + 1 ∧
      ∀ m : M, ∃ l₁ ∈ fixAdd x, ∃ l₂ ∈ fixAdd x, m = l₁ + ω • l₂ := by
  have h2 := two_eq_zero_of_card_four hE
  obtain ⟨ω, hω0, hω1, hωsq, -⟩ := E4_cases hE h2
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [hωsq]
    linear_combination hωsq + (ω + 1) * h2
  have hωω : ω + ω = 0 := by linear_combination ω * h2
  refine ⟨ω, hω0, hω1, hωsq, fun m => ⟨ω ^ 2 • m + ω • x m, ?_, m + x m, ?_, ?_⟩⟩
  · rw [mem_fixAdd, map_add, hx, hx, hxx, hω4, add_comm]
  · rw [mem_fixAdd, map_add, hxx, add_comm]
  · have e1 : ω ^ 2 • m + ω • m = m := by
      rw [← add_smul, hωsq]
      have : ω + 1 + ω = 1 := by linear_combination ω * h2
      rw [this, one_smul]
    have e2 : ω • x m + ω • x m = 0 := by
      rw [← add_smul, hωω, zero_smul]
    calc m = (ω ^ 2 • m + ω • m) + (ω • x m + ω • x m) := by rw [e1, e2, add_zero]
      _ = ω ^ 2 • m + ω • x m + ω • (m + x m) := by rw [smul_add]; abel

theorem card_eq_sq [Finite E] [Finite M] (hE : Nat.card E = 4) (x : M →+ M)
    (hx : ∀ (e : E) (m : M), x (e • m) = e ^ 2 • x m) (hxx : ∀ m, x (x m) = m) :
    Nat.card M = Nat.card (fixAdd x) ^ 2 := by
  obtain ⟨ω, hω0, hω1, hωsq, hdec⟩ := frob_decomp hE x hx hxx
  let Φ : fixAdd x × fixAdd x → M := fun p => (p.1 : M) + ω • (p.2 : M)
  have hinj : Function.Injective Φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Φ] at h
    have ha : x (a : M) = a := a.2
    have hb : x (b : M) = b := b.2
    have ha' : x (a' : M) = a' := a'.2
    have hb' : x (b' : M) = b' := b'.2
    have h2 := congrArg x h
    rw [map_add, map_add, hx, hx, ha, hb, ha', hb'] at h2
    have h3 : (ω ^ 2 - ω) • (b : M) = (ω ^ 2 - ω) • (b' : M) := by
      rw [sub_smul, sub_smul]
      have := congrArg₂ (· - ·) h2 h
      simpa [add_sub_add_left_eq_sub] using this
    have hω21 : ω ^ 2 - ω = 1 := by rw [hωsq]; ring
    rw [hω21, one_smul, one_smul] at h3
    have hbb : b = b' := Subtype.ext h3
    subst hbb
    have : (a : M) = a' := add_right_cancel h
    exact Prod.ext (Subtype.ext this) rfl
  have hsurj : Function.Surjective Φ := by
    intro m
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := hdec m
    exact ⟨(⟨l₁, h₁⟩, ⟨l₂, h₂⟩), rfl⟩
  rw [sq, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem card_ne_zero_subtype (L : Type) [AddCommGroup L] [Finite L] :
    Nat.card {l : L // l ≠ 0} = Nat.card L - 1 := by
  have : Fintype L := Fintype.ofFinite L
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card]

@[expose] def permFix (x : M →+ M) (a : M ≃ₗ[E] M) (ha : ∀ m, a (x m) = x (a m)) :
    Equiv.Perm (fixAdd x) where
  toFun l := ⟨a l.1, by rw [mem_fixAdd, ← ha, mem_fixAdd.1 l.2]⟩
  invFun l := ⟨a.symm l.1, by
    rw [mem_fixAdd]
    apply a.injective
    rw [ha, LinearEquiv.apply_symm_apply, mem_fixAdd.1 l.2]⟩
  left_inv l := Subtype.ext (LinearEquiv.symm_apply_apply a l.1)
  right_inv l := Subtype.ext (LinearEquiv.apply_symm_apply a l.1)

theorem card_centralizer_dvd [Finite E] [Finite M] (hE : Nat.card E = 4) (x : M →+ M)
    (hx : ∀ (e : E) (m : M), x (e • m) = e ^ 2 • x m) (hxx : ∀ m, x (x m) = m)
    (A : Subgroup (M ≃ₗ[E] M)) (hA : ∀ a ∈ A, ∀ m, a (x m) = x (a m)) :
    Nat.card A ∣ (Nat.card (fixAdd x) - 1).factorial := by
  obtain ⟨ω, hω0, hω1, hωsq, hdec⟩ := frob_decomp hE x hx hxx
  have hne : ∀ a : A, ∀ l : fixAdd x, permFix x a.1 (hA a.1 a.2) l ≠ 0 ↔ l ≠ 0 := by
    intro a l
    have h0 : (permFix x a.1 (hA a.1 a.2) l : M) = a.1 (l : M) := rfl
    constructor
    · intro h hl
      apply h
      apply Subtype.ext
      rw [h0, hl]
      simp
    · intro h hl
      apply h
      apply Subtype.ext
      have : a.1 (l : M) = 0 := by rw [← h0, hl]; rfl
      simpa using this
  let f : A →* Equiv.Perm {l : fixAdd x // l ≠ 0} :=
    { toFun := fun a => (permFix x a.1 (hA a.1 a.2)).subtypePerm (fun l => hne a l)
      map_one' := by
        ext l
        rfl
      map_mul' := fun a b => by
        ext l
        rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := hdec m
    have e : ∀ (l : M) (hl : l ∈ fixAdd x), a.1 l = b.1 l := by
      intro l hl
      by_cases h0 : l = 0
      · rw [h0, map_zero, map_zero]
      · have := congrArg (fun g : Equiv.Perm {l : fixAdd x // l ≠ 0} =>
          ((g ⟨⟨l, hl⟩, fun h => h0 (congrArg Subtype.val h)⟩ : {l : fixAdd x // l ≠ 0}) : M)) hab
        exact this
    rw [map_add, map_add, map_smul, map_smul, e l₁ h₁, e l₂ h₂]
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rwa [Nat.card_perm, card_ne_zero_subtype] at hdvd

end

end CFSG.Quasithin.G11.SzG11S.Two
