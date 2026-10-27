module

public import CFSG.RankThree.GF2n.Stroth80.Sec86UnitaryCount
public import CFSG.RankThree.GF2n.Stroth80.Sec86SolvQuot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem step86_abstract {G : Type} [Group G] [Finite G] {R N Z0 Q : Subgroup G}
    {Y S : Type} [Group Y] [Finite Y] [Group S] [Finite S] [IsSimpleGroup S]
    {F : Subgroup Y} [F.Normal] {f m e kk o₁ o₂ : ℕ}
    (hQZ0 : Q ≤ Z0) (hZ0N : Z0 ≤ N) (hNR : N ≤ R)
    (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hZn : ∀ r ∈ R, ∀ z ∈ Z0, r * z * r⁻¹ ∈ Z0)
    (hirr : IsIrredModule R N Z0) (hN2 : IsPGroup 2 ↥N) (hf : 2 ≤ f) (he : 1 ≤ e)
    (hQcard : Nat.card ↥Q = 2 ^ kk) (hNcard : Nat.card ↥N = Nat.card ↥Q * (2 ^ f) ^ (e + 1))
    (hZ0card : Nat.card ↥Z0 = Nat.card ↥Q * 2 ^ f)
    (θ : ↥R →* Y) (hθ : ∀ r : ↥R, θ r = 1 ↔ (r : G) ∈ Q) (hsolv : IsSolvable (Y ⧸ F))
    (π : ↥R →* S) (hπ : Function.Surjective π) (hπN : ∀ r : ↥R, π r = 1 ↔ (r : G) ∈ N)
    (hS : ¬ IsSolvable S) (hSord : Nat.card S = (2 ^ f) ^ (m ^ 2) * o₁) (ho₁ : Odd o₁)
    (hFord : Nat.card ↥F = (2 ^ f) ^ 15 * o₂) (ho₂ : Odd o₂) (hme : 15 < m ^ 2 + e) :
    False := by
  classical
  have hQR : Q ≤ R := hQZ0.trans (hZ0N.trans hNR)
  let ψ : ↥R →* Y ⧸ F := (QuotientGroup.mk' F).comp θ
  have hsup : ψ.ker ⊔ π.ker = ⊤ := sup_ker_eq_top_of_solvable hS π hπ ψ hsolv
  have hπker : π.ker = N.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, hπN, Subgroup.mem_subgroupOf]
  set K' : Subgroup G := ψ.ker.map R.subtype with hK'def
  have hKR : K' ≤ R := Subgroup.map_subtype_le _
  have hR : R = K' ⊔ N := by
    have h1 : (ψ.ker ⊔ π.ker).map R.subtype = K' ⊔ N := by
      rw [Subgroup.map_sup, hπker, Subgroup.map_subgroupOf_eq_of_le hNR]
    rw [hsup, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hmemKer : ∀ r : ↥R, r ∈ ψ.ker ↔ θ r ∈ F := by
    intro r
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (θ r)
  have hQK : Q ≤ K' := by
    intro q hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hQR hq⟩, ?_, rfl⟩
    rw [hmemKer, (hθ ⟨q, hQR hq⟩).mpr hq]
    exact F.one_mem
  have hKinv : ∀ r ∈ R, ∀ k ∈ K', r * k * r⁻¹ ∈ K' := by
    intro r hr k hk
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
    have h1 : (⟨r, hr⟩ : ↥R) * k₀ * (⟨r, hr⟩ : ↥R)⁻¹ ∈ ψ.ker :=
      (MonoidHom.normal_ker ψ).conj_mem k₀ hk₀ ⟨r, hr⟩
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have hKn : ∀ r ∈ R, conjSubgroup r K' = K' := fun r hr =>
    conjSubgroup_eq_of_conj_mem (hKinv r hr)
  have hNn' : ∀ r ∈ R, conjSubgroup r N = N := fun r hr =>
    conjSubgroup_eq_of_conj_mem (hNn r hr)
  have hZn' : ∀ r ∈ R, conjSubgroup r Z0 = Z0 := fun r hr =>
    conjSubgroup_eq_of_conj_mem (hZn r hr)
  have hRcard : Nat.card ↥R = Nat.card ↥N * ((2 ^ f) ^ (m ^ 2) * o₁) := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hπ
    rw [hπker, hSord] at h1
    have h2 : Nat.card ↥(N.subgroupOf R) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hKdvd : Nat.card ↥K' ∣ Nat.card ↥Q * ((2 ^ f) ^ 15 * o₂) := by
    have hcardK' : Nat.card ↥K' = Nat.card ↥ψ.ker :=
      Subgroup.card_map_of_injective R.subtype_injective
    let θK : ↥ψ.ker →* Y := θ.comp ψ.ker.subtype
    have h1 := Subgroup.card_ker_mul_card_range θK
    have hrange : θK.range ≤ F := by
      rintro _ ⟨k, rfl⟩
      exact (hmemKer k.1).mp k.2
    have h2 : Nat.card ↥θK.range ∣ Nat.card ↥F := Subgroup.card_dvd_of_le hrange
    let j : ↥θK.ker →* G := R.subtype.comp (ψ.ker.subtype.comp θK.ker.subtype)
    have hjinj : Function.Injective j := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.ext hab))
    have hjQ : j.range ≤ Q := by
      rintro _ ⟨a, rfl⟩
      have h3 : θ (a.1.1) = 1 := a.2
      exact (hθ a.1.1).mp h3
    have h4 : Nat.card ↥θK.ker = Nat.card ↥j.range :=
      Nat.card_congr (MonoidHom.ofInjective hjinj).toEquiv
    have h5 : Nat.card ↥θK.ker ∣ Nat.card ↥Q := h4 ▸ Subgroup.card_dvd_of_le hjQ
    rw [hcardK', ← h1, ← hFord]
    exact Nat.mul_dvd_mul h5 h2
  have hN2' := hN2
  exact step86_core hQZ0 hZ0N hNR hQK hR hKn hNn' hZn' hirr hN2' hf he hQcard hNcard hZ0card
    hRcard ho₁ hKdvd ho₂ hme

end CFSG.RankThree.GF2n.Stroth80
