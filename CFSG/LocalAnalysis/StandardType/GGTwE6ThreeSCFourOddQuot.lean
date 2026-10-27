module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.StandardType.SCFourOdd

theorem exists_twoPart {L' : Type} [Group L'] {Z : Subgroup L'} (hZ : Z ≤ Subgroup.center L') :
    ∃ K₂ : Subgroup L', K₂ ≤ Z ∧ IsPGroup 2 K₂ ∧
      ∀ z ∈ Z, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ K₂ := by
  let K₂ : Subgroup L' :=
    { carrier := {z : L' | z ∈ Z ∧ ∃ k : ℕ, z ^ 2 ^ k = 1}
      one_mem' := ⟨Z.one_mem, ⟨0, by simp⟩⟩
      mul_mem' := by
        rintro a b ⟨haZ, ⟨k, ha⟩⟩ ⟨hbZ, ⟨l, hb⟩⟩
        refine ⟨Z.mul_mem haZ hbZ, ⟨k + l, ?_⟩⟩
        have hcomm : Commute a b := (Subgroup.mem_center_iff.mp (hZ hbZ)) a
        have ha1 : a ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
        have hb1 : b ^ 2 ^ (k + l) = 1 := by
          rw [pow_add, mul_comm (2 ^ k) (2 ^ l), pow_mul, hb, one_pow]
        rw [hcomm.mul_pow, ha1, hb1, one_mul]
      inv_mem' := by
        rintro a ⟨haZ, ⟨k, ha⟩⟩
        exact ⟨Z.inv_mem haZ, ⟨k, by rw [inv_pow, ha, inv_one]⟩⟩ }
  refine ⟨K₂, fun z hz => hz.1, ?_, fun z hz h => ⟨hz, h⟩⟩
  intro g
  obtain ⟨-, k, hk⟩ := g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem odd_card_ker_lift {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    {K₂ : Subgroup L'} [K₂.Normal] (hle : K₂ ≤ ψ.ker) (hp : IsPGroup 2 K₂)
    (hall : ∀ z ∈ ψ.ker, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ K₂) :
    Odd (Nat.card (QuotientGroup.lift K₂ ψ hle).ker) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ :=
    exists_prime_orderOf_dvd_card' (G := (QuotientGroup.lift K₂ ψ hle).ker) 2 hdvd
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (u : L' ⧸ K₂)
  have hzker : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    calc ψ z = QuotientGroup.lift K₂ ψ hle (z : L' ⧸ K₂) :=
          (QuotientGroup.lift_mk (φ := ψ) K₂ hle z).symm
      _ = QuotientGroup.lift K₂ ψ hle (u : L' ⧸ K₂) := by rw [hz]
      _ = 1 := MonoidHom.mem_ker.mp u.2
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hz2K : z ^ 2 ∈ K₂ := by
    rw [← QuotientGroup.eq_one_iff]
    have hq : (z : L' ⧸ K₂) ^ 2 = 1 := by
      rw [hz, ← Subgroup.coe_pow (QuotientGroup.lift K₂ ψ hle).ker u 2, hu2]
      rfl
    simpa only [pow_two, QuotientGroup.mk_mul] using hq
  obtain ⟨k, hk⟩ := hp ⟨z ^ 2, hz2K⟩
  have hk' : (z ^ 2) ^ 2 ^ k = 1 := by
    have := congrArg (Subtype.val) hk
    simpa using this
  have hzK : z ∈ K₂ := by
    refine hall z hzker ⟨k + 1, ?_⟩
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
    rw [h2, pow_mul]
    exact hk'
  have hz1 : (z : L' ⧸ K₂) = 1 := (QuotientGroup.eq_one_iff z).mpr hzK
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [← hz, hz1]
    rfl
  rw [hu1, orderOf_one] at hu
  omega

theorem lift_surjective {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) {K₂ : Subgroup L'} [K₂.Normal] (hle : K₂ ≤ ψ.ker) :
    Function.Surjective (QuotientGroup.lift K₂ ψ hle) := by
  intro r
  obtain ⟨l, hl⟩ := hψ r
  exact ⟨(l : L' ⧸ K₂), by rw [QuotientGroup.lift_mk (φ := ψ) K₂ hle l, hl]⟩

theorem lift_ker_le_center {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hc : ψ.ker ≤ Subgroup.center L') {K₂ : Subgroup L'} [K₂.Normal] (hle : K₂ ≤ ψ.ker) :
    (QuotientGroup.lift K₂ ψ hle).ker ≤ Subgroup.center (L' ⧸ K₂) := by
  intro x hx
  rw [QuotientGroup.ker_lift] at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
  rw [QuotientGroup.mk'_apply] at hzx
  rw [← hzx, Subgroup.mem_center_iff]
  intro g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  show (l : L' ⧸ K₂) * (z : L' ⧸ K₂) = (z : L' ⧸ K₂) * (l : L' ⧸ K₂)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    (Subgroup.mem_center_iff.mp (hc hz)) l]

theorem quotient_commutator_eq_top {L' : Type} [Group L'] (hL : commutator L' = ⊤)
    (K₂ : Subgroup L') [K₂.Normal] : commutator (L' ⧸ K₂) = ⊤ := by
  have hmap : Subgroup.map (QuotientGroup.mk' K₂) (commutator L') = commutator (L' ⧸ K₂) := by
    change Subgroup.map (QuotientGroup.mk' K₂) ⁅(⊤ : Subgroup L'), ⊤⁆ =
      ⁅(⊤ : Subgroup (L' ⧸ K₂)), ⊤⁆
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K₂)]
  rw [← hmap, hL, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K₂)]

end CFSG.StandardType.SCFourOdd
