module

public import CFSG.Quasithin.Vol2.Ch10SecASL2Over

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

theorem le_of_two_pow_dvd {a b c : ℕ} (hc : Odd c) (h : 2 ^ a ∣ 2 ^ b * c) : a ≤ b := by
  have hcop : Nat.Coprime (2 ^ a) c := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hc)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

variable {G : Type} [Group G]

theorem le_normalizer_of_normal_subgroupOf {S X : Subgroup G} (hSX : S ≤ X)
    (h : (S.subgroupOf X).Normal) : X ≤ Subgroup.normalizer (S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 := h.conj_mem ⟨s, hSX hs⟩ (by rw [Subgroup.mem_subgroupOf]; exact hs) ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro hs
    have hsX : s ∈ X := by
      have := X.mul_mem (X.mul_mem (X.inv_mem hx) (hSX hs)) hx
      simpa [mul_assoc] using this
    have h1 := h.conj_mem ⟨x * s * x⁻¹, hSX hs⟩ (by rw [Subgroup.mem_subgroupOf]; exact hs)
      ⟨x⁻¹, X.inv_mem hx⟩
    rw [Subgroup.mem_subgroupOf] at h1
    simpa [mul_assoc] using h1

theorem normal_of_mulEquiv_alt4 {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* ↥(alternatingGroup (Fin 4))) {S : Subgroup Q} (hS : Nat.card S = 4) : S.Normal := by
  have hsq : ∀ s ∈ S, s ^ 2 = 1 := by
    intro s hs
    have h4 : (⟨s, hs⟩ : ↥S) ^ 4 = 1 := by
      rw [← hS]
      exact pow_card_eq_one'
    have h4' : s ^ 4 = 1 := by simpa using congrArg Subtype.val h4
    have := alt4_sq (e s) (by rw [← map_pow, h4', map_one])
    rw [← map_pow] at this
    exact e.injective (this.trans (map_one e).symm)
  have hQ : Set.ncard {q : Q | q ^ 2 = 1} = 4 := by
    rw [← card_alt4_sq, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun q => by
      show q ^ 2 = 1 ↔ (e q) ^ 2 = 1
      rw [← map_pow]
      exact ⟨fun h => by rw [h, map_one], fun h => e.injective (h.trans (map_one e).symm)⟩)
  have hsub : (S : Set Q) ⊆ {q : Q | q ^ 2 = 1} := fun s hs => hsq s hs
  have heq : (S : Set Q) = {q : Q | q ^ 2 = 1} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hQ, ← hS, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨fun s hs g => ?_⟩
  have hs2 : s ∈ ({q : Q | q ^ 2 = 1} : Set Q) := heq ▸ hs
  have h2 : s ^ 2 = 1 := hs2
  have : g * s * g⁻¹ ∈ ({q : Q | q ^ 2 = 1} : Set Q) := by
    show (g * s * g⁻¹) ^ 2 = 1
    rw [conj_pow, h2, mul_one, mul_inv_cancel]
  rw [← heq] at this
  exact this

theorem eq_of_normal_complement {Q : Type} [Group Q] [Finite Q] {S N C : Subgroup Q}
    [hNn : N.Normal] (hS : IsPGroup 2 S) (hN : IsPGroup 2 N) (hC : Odd (Nat.card C))
    (hsup : N ⊔ C = ⊤) (hmax : ∀ P : Subgroup Q, IsPGroup 2 P → Nat.card P ≤ Nat.card S) :
    S = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNS : N ≤ S := by
    have hSN := hS.to_sup_of_normal_right hN
    have heq : S = S ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left (hmax _ hSN)
    rw [heq]
    exact le_sup_right
  refine le_antisymm ?_ hNS
  set π := QuotientGroup.mk' N
  have hC' : C.map π = ⊤ := by
    have h1 : (N ⊔ C).map π = ⊤ := by
      rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hodd : Odd (Nat.card (Q ⧸ N)) := by
    have h1 : Nat.card (Q ⧸ N) = Nat.card (C.map π) := by
      rw [hC', Subgroup.card_top]
    rw [h1]
    exact Odd.of_dvd_nat hC (Subgroup.card_map_dvd C π)
  have hπS : S.map π = ⊥ := by
    have h2 := hS.map π
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have hdvd : Nat.card (S.map π) ∣ Nat.card (Q ⧸ N) := Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ Nat.card (Q ⧸ N) :=
        (dvd_pow_self 2 hk0).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  intro s hs
  have : π s ∈ S.map π := Subgroup.mem_map_of_mem π hs
  rw [hπS, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff s).mp this

end CFSG.Quasithin.Vol2.Ch10.SecA
