module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open Equiv

private lemma two_mul_le_two_pow {j : ℕ} (hj : 1 ≤ j) : 2 * j ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega

private lemma exists_card_eq_two_pow {G : Type*} [Group G] [Finite G]
    (h2 : ∀ a : G, a * a = 1) : ∃ k, Nat.card G = 2 ^ k := by
  have : IsPGroup 2 G := fun g => ⟨1, by simpa [pow_two] using h2 g⟩
  exact this.exists_card_eq

private lemma arith_step {j n : ℕ} (hj : 1 ≤ j) (hn : 2 ^ j ≤ n) :
    2 ^ j * 2 ^ ((n - 2 ^ j) / 2) ≤ 2 ^ (n / 2) := by
  have h := two_mul_le_two_pow hj
  have : (2 : ℕ) ^ (j + (n - 2 ^ j) / 2) ≤ 2 ^ (n / 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rwa [pow_add] at this

private lemma orbit_split {α : Type} [Fintype α] [DecidableEq α] {B : Subgroup (Equiv.Perm α)}
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (x : α) :
    ∃ K : Subgroup (Equiv.Perm α), K ≤ B ∧ (∀ k ∈ K, ∀ y ∈ MulAction.orbit B x, k y = y) ∧
      Nat.card B = Nat.card (MulAction.orbit B x) * Nat.card K := by
  classical
  have hfix : ∀ k : B, k ∈ MulAction.stabilizer B x → ∀ y ∈ MulAction.orbit B x,
      (k : Equiv.Perm α) y = y := by
    rintro k hk _ ⟨c, rfl⟩
    have hkc : k * c = c * k := Subtype.ext (hc _ k.2 _ c.2)
    have h1 : k • x = x := hk
    show k • (c • x) = c • x
    rw [← mul_smul, hkc, mul_smul, h1]
  refine ⟨(MulAction.stabilizer B x).map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rintro _ ⟨k, hk, rfl⟩
    exact hfix k hk
  · have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group B x
    rw [Subgroup.card_map_of_injective (f := B.subtype) B.subtype_injective]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h1]

theorem card_le_of_elemAbelian_perm {α : Type} [Fintype α] [DecidableEq α]
    {B : Subgroup (Equiv.Perm α)} (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ B, a * a = 1) : Nat.card B ≤ 2 ^ (Fintype.card α / 2) := by
  suffices H : ∀ n : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (B : Subgroup (Equiv.Perm α)),
      Fintype.card α = n → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
        Nat.card B ≤ 2 ^ (n / 2) from H _ α B rfl hc h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α _ _ B hn hc h2
  classical
  by_cases hB : ∀ b ∈ B, b = 1
  · have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hB
    subst this
    simpa using Nat.one_le_two_pow
  push Not at hB
  obtain ⟨b, hbB, hb1⟩ := hB
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hb1 (Equiv.ext hcon)
  obtain ⟨K, hKB, hKfix, hcard⟩ := orbit_split hc x
  obtain ⟨k, hk⟩ : ∃ k, Nat.card B = 2 ^ k :=
    exists_card_eq_two_pow (G := B) fun a => Subtype.ext (h2 a a.2)
  obtain ⟨j, -, hOj⟩ : ∃ j ≤ k, Nat.card (MulAction.orbit B x) = 2 ^ j :=
    (Nat.dvd_prime_pow Nat.prime_two).1 ⟨Nat.card K, hk ▸ hcard⟩
  have hnt : Nontrivial (MulAction.orbit B x) :=
    ⟨⟨x, MulAction.mem_orbit_self _⟩, ⟨b x, ⟨⟨b, hbB⟩, rfl⟩⟩,
      fun h => hx (congrArg Subtype.val h).symm⟩
  have hj : 1 ≤ j := by
    have := Finite.one_lt_card_iff_nontrivial.2 hnt
    rw [hOj] at this
    by_contra h0
    rw [show j = 0 by omega] at this
    simp at this
  have hOn : Nat.card (MulAction.orbit B x) ≤ n := by
    rw [Nat.card_eq_fintype_card, ← hn]
    exact Fintype.card_subtype_le _
  rw [hOj] at hOn hcard
  have hPcard : Fintype.card {y // y ∉ MulAction.orbit B x} = n - 2 ^ j := by
    rw [Fintype.card_subtype_compl, hn, ← hOj, Nat.card_eq_fintype_card]
  have hfixed : ∀ g ∈ K, ∀ y, g y ≠ y → y ∉ MulAction.orbit B x :=
    fun g hg y hy hyO => hy (hKfix g hg y hyO)
  have hrange : K ≤ (Equiv.Perm.ofSubtype : Perm {y // y ∉ MulAction.orbit B x} →* Perm α).range :=
    fun g hg => Equiv.Perm.mem_range_ofSubtype_iff.2 fun y hy =>
      hfixed g hg y (Equiv.Perm.mem_support.1 hy)
  let K' : Subgroup (Perm {y // y ∉ MulAction.orbit B x}) := K.comap Equiv.Perm.ofSubtype
  have hmap : K'.map Equiv.Perm.ofSubtype = K := Subgroup.map_comap_eq_self hrange
  have hK'card : Nat.card K' = Nat.card K := by
    rw [← Subgroup.card_map_of_injective Equiv.Perm.ofSubtype_injective, hmap]
  have hK'c : ∀ a ∈ K', ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    apply Equiv.Perm.ofSubtype_injective
    rw [map_mul, map_mul]
    exact hc _ (hKB ha) _ (hKB hb)
  have hK'2 : ∀ a ∈ K', a * a = 1 := by
    intro a ha
    apply Equiv.Perm.ofSubtype_injective
    rw [map_mul, map_one]
    exact h2 _ (hKB ha)
  have hlt : n - 2 ^ j < n := by
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hih := ih _ hlt {y // y ∉ MulAction.orbit B x} K' hPcard hK'c hK'2
  rw [hK'card] at hih
  rw [hcard]
  exact (Nat.mul_le_mul_left _ hih).trans (arith_step hj hOn)

theorem card_le_sixteen_of_elemAbelian_perm8 {B : Subgroup (Equiv.Perm (Fin 8))}
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ B, a * a = 1) : Nat.card B ≤ 16 := by
  simpa using card_le_of_elemAbelian_perm hc h2

theorem card_le_sixteen_of_mulAut_alt8 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 8)) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 16 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num)
  let f : Equiv.Perm (Fin 8) →* MulAut X :=
    (MulAut.congr e).symm.toMonoidHom.comp
      (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
  have hf : Function.Bijective f :=
    (MulEquiv.bijective (MulAut.congr e).symm).comp hbij
  have hmap : (B.comap f).map f = B := Subgroup.map_comap_eq_self_of_surjective hf.2 B
  have hcard : Nat.card (B.comap f) = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hf.1, hmap]
  have hc' : ∀ a ∈ B.comap f, ∀ b ∈ B.comap f, a * b = b * a := by
    intro a ha b hb
    apply hf.1
    rw [map_mul, map_mul]
    exact hc _ ha _ hb
  have h2' : ∀ a ∈ B.comap f, a * a = 1 := by
    intro a ha
    apply hf.1
    rw [map_mul, map_one]
    exact h2 _ ha
  rw [← hcard]
  exact card_le_sixteen_of_elemAbelian_perm8 hc' h2'

end CFSG.Quasithin.G11.Harris.Ln2
