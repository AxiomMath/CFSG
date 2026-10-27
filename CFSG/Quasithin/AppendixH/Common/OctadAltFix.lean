module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ASVolI.AppH

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

theorem fixes_of_commute_alt (Z : Finset Q) (h4 : 4 ≤ Fintype.card Q - Z.card)
    {n : Equiv.Perm Q} (hn : ∀ z, n z ∈ Z ↔ z ∈ Z)
    (hc : ∀ c ∈ alternatingGroup Q, (∀ z ∈ Z, c z = z) → n * c = c * n) :
    ∀ x, x ∉ Z → n x = x := by
  intro x hx
  by_contra hne
  have hnx : n x ∉ Z := fun h => hx ((hn x).1 h)
  let T : Finset Q := insert x (insert (n x) Z)
  have hcardT : T.card ≤ Z.card + 2 := by
    have h1 := Finset.card_insert_le x (insert (n x) Z)
    have h2 := Finset.card_insert_le (n x) Z
    change (insert x (insert (n x) Z)).card ≤ Z.card + 2
    omega
  have hbig : 2 ≤ (Finset.univ \ T).card := by
    rw [Finset.card_univ_sdiff]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Finset.one_lt_card).1 (show 1 < (Finset.univ \ T).card by omega)
  have huT : u ∉ T := (Finset.mem_sdiff.1 hu).2
  have hvT : v ∉ T := (Finset.mem_sdiff.1 hv).2
  have hux : u ≠ x := fun h => huT (by simp [T, h])
  have hunx : u ≠ n x := fun h => huT (by simp [T, h])
  have huZ : u ∉ Z := fun h => huT (by simp [T, h])
  have hvx : v ≠ x := fun h => hvT (by simp [T, h])
  have hvnx : v ≠ n x := fun h => hvT (by simp [T, h])
  have hvZ : v ∉ Z := fun h => hvT (by simp [T, h])
  let c : Equiv.Perm Q := Equiv.swap x u * Equiv.swap u v
  have hcalt : c ∈ alternatingGroup Q := by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (Equiv.swap x u * Equiv.swap u v) = 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hux.symm, Equiv.Perm.sign_swap huv]
    decide
  have hcfix : ∀ z ∈ Z, c z = z := by
    intro z hz
    have hzx : z ≠ x := fun h => hx (h ▸ hz)
    have hzu : z ≠ u := fun h => huZ (h ▸ hz)
    have hzv : z ≠ v := fun h => hvZ (h ▸ hz)
    change Equiv.swap x u (Equiv.swap u v z) = z
    rw [Equiv.swap_apply_of_ne_of_ne hzu hzv, Equiv.swap_apply_of_ne_of_ne hzx hzu]
  have hcx : c x = u := by
    have hxv : x ≠ v := fun h => hvT (h ▸ Finset.mem_insert_self x (insert (n x) Z))
    change Equiv.swap x u (Equiv.swap u v x) = u
    rw [Equiv.swap_apply_of_ne_of_ne hux.symm hxv, Equiv.swap_apply_left]
  have hcy : c (n x) = n x := by
    have hnxu : n x ≠ u := fun h => hunx h.symm
    have hnxv : n x ≠ v := fun h => hvT (h ▸ (by simp [T]))
    change Equiv.swap x u (Equiv.swap u v (n x)) = n x
    rw [Equiv.swap_apply_of_ne_of_ne hnxu hnxv, Equiv.swap_apply_of_ne_of_ne hne hnxu]
  have hcomm := hc c hcalt hcfix
  have heval := congrArg (fun p : Equiv.Perm Q => p x) hcomm
  have hleft : (n * c) x = n u := by rw [Equiv.Perm.mul_apply, hcx]
  have hright : (c * n) x = n x := by rw [Equiv.Perm.mul_apply, hcy]
  exact hux (n.injective (hleft.symm.trans (heval.trans hright)))

theorem eq_one_of_even_of_fix_compl (Z : Finset Q) (hZ : Z.card ≤ 2) {n : Equiv.Perm Q}
    (hn : n ∈ alternatingGroup Q) (hfix : ∀ x, x ∉ Z → n x = x) : n = 1 := by
  by_contra hne
  have hsub : n.support ⊆ Z := by
    intro x hx
    by_contra hxZ
    exact (Equiv.Perm.mem_support.1 hx) (hfix x hxZ)
  have hle : n.support.card ≤ 2 := le_trans (Finset.card_le_card hsub) hZ
  have hne0 : n.support.card ≠ 0 := fun h =>
    hne ((Equiv.Perm.card_support_eq_zero).1 h)
  have hne1 : n.support.card ≠ 1 := Equiv.Perm.card_support_ne_one n
  have h2 : n.support.card = 2 := by omega
  have hswap : n.IsSwap := (Equiv.Perm.card_support_eq_two).1 h2
  have hsign : Equiv.Perm.sign n = -1 := hswap.sign_eq
  have hsign1 : Equiv.Perm.sign n = 1 := (Equiv.Perm.mem_alternatingGroup).1 hn
  exact (by decide : (1 : ℤˣ) ≠ -1) (hsign1 ▸ hsign)

theorem ofSubtype_mem_alt (Z : Finset Q) (c : alternatingGroup {x : Q // x ∉ Z}) :
    Equiv.Perm.ofSubtype (c : Equiv.Perm {x : Q // x ∉ Z}) ∈ alternatingGroup Q ∧
      ∀ z ∈ Z, Equiv.Perm.ofSubtype (c : Equiv.Perm {x : Q // x ∉ Z}) z = z := by
  constructor
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact (Equiv.Perm.mem_alternatingGroup).1 c.2
  · intro z hz
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hz)

theorem exists_alt_ofSubtype (Z : Finset Q) {σ : Equiv.Perm Q} (hσ : σ ∈ alternatingGroup Q)
    (hZ : ∀ z ∈ Z, σ z = z) :
    ∃ c : alternatingGroup {x : Q // x ∉ Z},
      Equiv.Perm.ofSubtype (c : Equiv.Perm {x : Q // x ∉ Z}) = σ := by
  have h₁ : ∀ x, (σ x ∉ Z) ↔ (x ∉ Z) := by
    intro x
    constructor
    · intro hx hxZ
      exact hx (by rw [hZ x hxZ]; exact hxZ)
    · intro hx hσxZ
      have h1 : σ (σ x) = σ x := hZ (σ x) hσxZ
      have h2 : σ x = x := σ.injective h1
      exact hx (h2 ▸ hσxZ)
  have h₂ : ∀ x, σ x ≠ x → x ∉ Z := fun x hx hxZ => hx (hZ x hxZ)
  have hc' : σ.subtypePerm h₁ ∈ alternatingGroup {x : Q // x ∉ Z} := by
    rw [Equiv.Perm.mem_alternatingGroup,
      ← Equiv.Perm.sign_ofSubtype (f := σ.subtypePerm h₁),
      Equiv.Perm.ofSubtype_subtypePerm h₁ h₂]
    exact (Equiv.Perm.mem_alternatingGroup).1 hσ
  exact ⟨⟨σ.subtypePerm h₁, hc'⟩, Equiv.Perm.ofSubtype_subtypePerm h₁ h₂⟩

end CFSG.ASVolI.AppH
