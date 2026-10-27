module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.ThreePrimeFourPGroup

open MulAction

private theorem fixed_card_arithmetic {p f : ℕ} (hp : 17 ≤ p)
    (hlo : 5 ≤ f) (hhi : f ≤ (3 * p + 4) / 2)
    (hmod : (3 * p + 4) % p = f % p) : f = p + 4 := by
  have hfour : 4 < p := by omega
  have hleft : (3 * p + 4) % p = 4 := by simp [Nat.add_mod, Nat.mod_eq_of_lt hfour]
  rw [hleft] at hmod
  have hfp : p ≤ f := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega : f < p)] at hmod
    omega
  have hsub : f - p < p := by omega
  have hfmod : f % p = f - p := by
    rw [Nat.mod_eq_sub_mod hfp, Nat.mod_eq_of_lt hsub]
  omega

theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ} [Fact p.Prime]
    (hp : 17 ≤ p) (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥)
    (hfix : 5 ≤ Nat.card (fixedPoints Q X)) :
    Nat.card (fixedPoints Q X) = p + 4 := by
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hne
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card, hcard] at hmod
  rw [hcard] at hupper
  exact fixed_card_arithmetic hp hfix hupper hmod

private theorem free_complement
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ} [Fact p.Prime]
    (hp : 17 ≤ p) (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q)
    (hfix : Nat.card (fixedPoints Q X) = p + 4) :
    ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
  intro q x hx hqx
  by_contra hq
  let R : Subgroup P := (Subgroup.zpowers q).map Q.subtype
  have hR : IsPGroup p R := (hQ.to_subgroup (Subgroup.zpowers q)).map Q.subtype
  have hqR : q.val ∈ R := ⟨q, Subgroup.mem_zpowers q, rfl⟩
  have hne : R ≠ ⊥ := by
    intro he
    have h := hqR
    rw [he, Subgroup.mem_bot] at h
    exact hq (Subtype.ext h)
  have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
    intro y hy r
    obtain ⟨a, ha, hea⟩ := r.property
    change r.val • y = y
    rw [← hea]
    rcases hy with rfl | hy
    · exact (Subgroup.zpowers_le.mpr (show q ∈ stabilizer Q y from hqx)) ha
    · exact hy a
  have hlo := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hx, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq, hfix] at hlo
  have hrfix := fixed_card hp P hcard h5 hnotAlt R hR hne (by omega)
  omega

theorem card_eq_prime
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ} [Fact p.Prime]
    (hp : 17 ≤ p) (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup p Q) (hne : Q ≠ ⊥)
    (hfix : 5 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q = p := by
  have hf := fixed_card hp P hcard h5 hnotAlt Q hQ hne hfix
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (by intro q x hx; simpa only [hx q] using hx)
    (free_complement hp P hcard h5 hnotAlt Q hQ hf)
  rw [← Nat.card_coe_set_eq, hf, show Nat.card X = Fintype.card X from Nat.card_eq_fintype_card, hcard,
    show 3 * p + 4 - (p + 4) = 2 * p by omega] at hd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQ)
  have hpos : 0 < k := by
    by_contra hn
    have hzero : k = 0 := by omega
    rw [hzero, pow_zero] at hk
    exact hne (Subgroup.eq_bot_of_card_eq Q hk)
  have hpdiv : p ^ k ∣ 2 * p := by rwa [← hk]
  have hnot : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by norm_num : 0 < 2) h; omega
  have hkle : k ≤ 1 := by
    by_contra hn
    have htwo : p ^ 2 ∣ 2 * p := (pow_dvd_pow p (by omega : 2 ≤ k)).trans hpdiv
    have hpd : p ∣ 2 := by
      apply (Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < p))
      simpa [pow_two] using htwo
    exact hnot hpd
  have hkone : k = 1 := by omega
  simpa [hkone] using hk

end FiveTransitive.ThreePrimeFourPGroup

end CFSG
