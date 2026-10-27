module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Out

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s218_exists_pair_of_commuting {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K)
    {E₀ Q₀ : Subgroup (↥L ⧸ K)} (hE₀ : IsElemAbelian r E₀) (hE₀c : Nat.card E₀ = r ^ 2)
    (hQ₀ : IsElemAbelian p Q₀) (hQ₀c : Nat.card Q₀ = p ^ 2)
    (hcomm : ∀ x ∈ Q₀, ∀ e ∈ E₀, x * e = e * x) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hcop : Nat.Coprime (Nat.card Q₀) (Nat.card K) := by
    rw [hQ₀c]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  obtain ⟨β, -, hβ⟩ := uc22s218_exists_lift_hom_of_coprime K ⊤
    (fun l => ⟨l, mem_top l, by simp⟩) Q₀ hcop
  have hβinj : Function.Injective β := fun a b hab =>
    Subtype.ext ((hβ a).symm.trans ((congrArg (QuotientGroup.mk' K) hab).trans (hβ b)))
  let χ : ↥Q₀ →* G := L.subtype.comp β
  have hχinj : Function.Injective χ := L.subtype_injective.comp hβinj
  have : IsMulCommutative ↥Q₀ := hQ₀.1
  have hQel : IsElemAbelian p χ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm' u v]
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
      rw [← map_pow]
      have : u ^ p = 1 := Subtype.ext (hQ₀.2 _ u.2)
      rw [this, map_one]
  have hQc : Nat.card χ.range = p ^ 2 := by
    rw [← hQ₀c]
    exact (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hQL : χ.range ≤ L := by
    rintro _ ⟨u, rfl⟩
    exact (β u).2
  obtain ⟨E, hEL, hEel, hEc, hEpow⟩ := uc22s218_exists_lift_of_power_maps hLM K hp hr hpr hpK hrK
    (hQL.trans hLM) hQel hE₀ hE₀c (fun x hx => by
      refine ⟨1, fun e he => ?_⟩
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective e
      have hconj : Subgroup.normalizerMonoidHom L ⟨χ u, hML (hQL.trans hLM ⟨u, rfl⟩)⟩ l =
          β u * l * (β u)⁻¹ := Subtype.ext (by simp [χ])
      rw [pow_one, uc22s218_rhoK_mk, hconj, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      have hu : (QuotientGroup.mk (β u) : ↥L ⧸ K) = (u : ↥L ⧸ K) := hβ u
      rw [hu]
      exact mul_inv_eq_iff_eq_mul.2 (hcomm u u.2 _ he))
  exact ⟨E, χ.range, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hEpow⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
