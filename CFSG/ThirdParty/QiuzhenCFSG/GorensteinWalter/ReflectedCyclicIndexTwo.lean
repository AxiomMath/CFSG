module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicSylow

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning a reflected cyclic subgroup with an index-two subgroup

If a cyclic subgroup has order twice an odd number and crosses an index-two
subgroup, then its unique involution is outside the index-two subgroup.  Any
external involution which reflects the cyclic subgroup can be adjusted by that
torus involution so that the reflector lies inside the index-two subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Let `H` have index two and let `U` be a cyclic subgroup of order `2m`,
with `m` odd, not contained in `H`.  An external involution reflecting `U`
can be aligned with `H`: the involution `s` of `U` lies outside `H`, while
either the original reflector or its product with `s` is a reflector `t`
inside `H`. -/
public theorem exists_aligned_involutions_of_cyclic_reflection_index_two
    {G : Type u} [Group G] [Finite G]
    (H U : Subgroup G)
    (hHindex : H.index = 2)
    (hUcyclic : IsCyclic U)
    (m : ℕ) (hmOdd : Odd m)
    (hUcard : Nat.card U = 2 * m)
    (hUnot : ¬ U ≤ H)
    (w : G) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) :
    ∃ s t : G,
      s ∈ U ∧ s ∉ H ∧ s ≠ 1 ∧ s * s = 1 ∧
      t ∈ H ∧ t ∉ U ∧ t * t = 1 ∧
      (∀ x : G, x ∈ U → t * x * t⁻¹ = x⁻¹) ∧
      (t = w ∨ t = w * s) := by
  let : IsCyclic U := hUcyclic
  let : CommGroup U := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := U)
  have hgorder : orderOf g = Nat.card U := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    rcases hg x with ⟨n, hn⟩
    exact ⟨(n : ℤ), by simpa using hn⟩
  have hmpos : 0 < m := by
    have hcardpos : 0 < Nat.card U := Nat.card_pos
    omega
  have hgU : (g : G) ∈ U := g.2
  have hgnotH : (g : G) ∉ H := by
    intro hgH
    apply hUnot
    intro x hxU
    let xU : U := ⟨x, hxU⟩
    rcases hg xU with ⟨n, hn⟩
    have hpow : (g : G) ^ n ∈ H := H.pow_mem hgH n
    have hx : (xU : G) = (g : G) ^ n := congrArg Subtype.val hn.symm
    change (xU : G) ∈ H
    rw [hx]
    exact hpow
  let s : G := (g : G) ^ m
  have hsU : s ∈ U := by
    dsimp [s]
    exact U.pow_mem hgU m
  have hsne : s ≠ 1 := by
    intro hsone
    have hdvd : orderOf g ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      exact hsone
    rw [hgorder, hUcard] at hdvd
    have hle : 2 * m ≤ m := Nat.le_of_dvd hmpos hdvd
    omega
  have hssq : s * s = 1 := by
    dsimp [s]
    rw [← pow_two, ← pow_mul]
    have hpow : (g : G) ^ (2 * m) = 1 := by
      have hgpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
      rw [hgorder, hUcard] at hgpow
      exact congrArg Subtype.val hgpow
    simpa [mul_comm] using hpow
  have hsnotH : s ∉ H := by
    rcases hmOdd with ⟨k, hk⟩
    intro hsH
    have hg2H : (g : G) ^ 2 ∈ H :=
      H.sq_mem_of_index_two hHindex (g : G)
    have hevenH : (g : G) ^ (2 * k) ∈ H := by
      rw [pow_mul]
      exact H.pow_mem hg2H k
    have hfactor : (g : G) ^ m = (g : G) ^ (2 * k) * (g : G) := by
      rw [hk, pow_add, pow_one]
    have hgH : (g : G) ∈ H := by
      change (g : G) ^ m ∈ H at hsH
      rw [hfactor] at hsH
      exact (H.mul_mem_cancel_left hevenH).mp hsH
    exact hgnotH hgH
  have hwInv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hwsq).symm
  by_cases hwH : w ∈ H
  · exact ⟨s, w, hsU, hsnotH, hsne, hssq, hwH, hwU, hwsq, hwinv,
      Or.inl rfl⟩
  · let t : G := w * s
    have htH : t ∈ H := by
      dsimp [t]
      exact (H.mul_mem_iff_of_index_two hHindex).2
        (iff_of_false hwH hsnotH)
    have htU : t ∉ U := by
      intro htU
      apply hwU
      have hsinvU : s⁻¹ ∈ U := U.inv_mem hsU
      have hprod : t * s⁻¹ ∈ U := U.mul_mem htU hsinvU
      have hts : t * s⁻¹ = w := by
        dsimp [t]
        group
      simpa [hts] using hprod
    have hwSinv : w * s * w⁻¹ = s⁻¹ := hwinv s hsU
    have htsq : t * t = 1 := by
      dsimp [t]
      calc
        (w * s) * (w * s) = (w * s * w⁻¹) * s := by
          rw [hwInv]
          group
        _ = s⁻¹ * s := by rw [hwSinv]
        _ = 1 := by simp
    have htinv : ∀ x : G, x ∈ U → t * x * t⁻¹ = x⁻¹ := by
      intro x hxU
      let xU : U := ⟨x, hxU⟩
      let sU : U := ⟨s, hsU⟩
      have hsx : s * x = x * s :=
        congrArg Subtype.val (mul_comm sU xU)
      have hsconj : s * x * s⁻¹ = x := by
        calc
          s * x * s⁻¹ = x * s * s⁻¹ := by rw [hsx]
          _ = x := by simp
      dsimp [t]
      calc
        (w * s) * x * (w * s)⁻¹ =
            w * (s * x * s⁻¹) * w⁻¹ := by group
        _ = w * x * w⁻¹ := by rw [hsconj]
        _ = x⁻¹ := hwinv x hxU
    exact ⟨s, t, hsU, hsnotH, hsne, hssq, htH, htU, htsq, htinv,
      Or.inr rfl⟩

end CFSG.GorensteinWalter
