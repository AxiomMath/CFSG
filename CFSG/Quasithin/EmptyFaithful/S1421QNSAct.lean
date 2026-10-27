module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

namespace S1421NS

variable {G : Type*} [Group G]

noncomputable def actHom (Q K : Subgroup G) (hKN : K ≤ Subgroup.normalizer (Q : Set G)) :
    K →* MulAut Q :=
  Q.normalizerMonoidHom.comp (Subgroup.inclusion hKN)

theorem mem_ker_actHom {Q K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (Q : Set G)) (k : K) :
    k ∈ (actHom Q K hKN).ker ↔ (k : G) ∈ Subgroup.centralizer (Q : Set G) := by
  have h := Subgroup.normalizerMonoidHom_ker (H := Q)
  rw [MonoidHom.mem_ker, actHom, MonoidHom.comp_apply, ← MonoidHom.mem_ker, h,
    Subgroup.mem_subgroupOf]
  rfl

theorem isPGroup_ker_actHom {Q K : Subgroup G} (hQ : IsPGroup 2 Q)
    (hKN : K ≤ Subgroup.normalizer (Q : Set G))
    (hC : K ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) : IsPGroup 2 (actHom Q K hKN).ker := by
  intro g
  obtain ⟨n, hn⟩ := hQ ⟨(g : K), hC ⟨(g : K).2, (mem_ker_actHom hKN g).mp g.2⟩⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg (fun x : Q => (x : G)) hn
  simpa using this

variable [Finite G]

theorem dvd_natCard_mulAut_of_odd_dvd {Q K : Subgroup G} (hQ : IsPGroup 2 Q)
    (hKN : K ≤ Subgroup.normalizer (Q : Set G))
    (hC : K ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) {m : ℕ} (hm : Odd m)
    (hmK : m ∣ Nat.card K) : m ∣ Nat.card (MulAut Q) := by
  set ρ := actHom Q K hKN with hρ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_ker_actHom hQ hKN hC)
  have h1 : Nat.card K = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hcop : Nat.Coprime m (Nat.card ρ.ker) := by
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  rw [h1] at hmK
  have h2 : m ∣ Nat.card ρ.range := hcop.dvd_of_dvd_mul_right hmK
  exact h2.trans (Subgroup.card_subgroup_dvd_card ρ.range)

theorem exists_subgroup_card_of_dvd {A : Type*} [Group A] [Finite A] {r : ℕ} (hr : r.Prime)
    (h : r ^ 2 ∣ Nat.card A) : ∃ E : Subgroup A, Nat.card E = r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  exact Sylow.exists_subgroup_card_pow_prime r h

end S1421NS

end CFSG.Quasithin
