module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.SBd14

open scoped commutatorElement

theorem mem_commutator_of_central {L : Type*} [Group L] [Finite L] (hL : Group.IsPerfect L)
    {Q : Subgroup L} (hQ : IsPGroup 2 Q) (hodd : ¬ 2 ∣ Q.index) {z : L}
    (hz : z ∈ Subgroup.center L) (hzQ : z ∈ Q) : z ∈ ⁅Q, Q⁆ := by
  classical
  have : Q.FiniteIndex := Subgroup.finiteIndex_of_finite
  let φ : Q →* Abelianization Q := Abelianization.of
  have h1 : MonoidHom.transfer φ = 1 := by
    ext g
    have hker := Abelianization.commutator_subset_ker (MonoidHom.transfer φ)
    have hg : g ∈ commutator L := by rw [hL.commutator_eq_top]; trivial
    simpa using hker hg
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ Q → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center L := Subgroup.pow_mem _ hz k
    have := Subgroup.mem_center_iff.mp hc g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [this]
      _ = z ^ k := by group
  have h2 := MonoidHom.transfer_eq_pow φ z key
  rw [h1] at h2
  have h3 : φ ⟨z ^ Q.index, MonoidHom.transfer_eq_pow_aux z key⟩ = 1 := by
    simpa using h2.symm
  set z' : Q := ⟨z, hzQ⟩ with hz'
  have hpow : z' ^ Q.index = ⟨z ^ Q.index, MonoidHom.transfer_eq_pow_aux z key⟩ :=
    Subtype.ext (by simp [z'])
  have h5 : φ z' ^ Q.index = 1 := by rw [← map_pow, hpow]; exact h3
  have hAb : IsPGroup 2 (Abelianization Q) :=
    hQ.of_surjective φ (QuotientGroup.mk_surjective)
  obtain ⟨k, hk⟩ := hAb (φ z')
  have hcop : Nat.Coprime Q.index (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  have hdvd : orderOf (φ z') ∣ Nat.gcd Q.index (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one hk)
  rw [hcop.gcd_eq_one] at hdvd
  have h6 : φ z' = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have h7 : z' ∈ commutator Q := by
    have : z' ∈ (Abelianization.of : Q →* Abelianization Q).ker := h6
    rwa [Abelianization.ker_of] at this
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨z', h7, rfl⟩

end CFSG.Quasithin.SBd14
