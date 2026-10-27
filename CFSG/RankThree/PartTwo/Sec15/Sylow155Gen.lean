module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftSylow
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155G

open CFSG.Semidihedral.Principal
open scoped Pointwise

section Coprime

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_mul_inv_mem {p : ℕ} [Fact p.Prime] {A V L : Subgroup G}
    (hA : IsPGroup p A) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hcop : ¬ p ∣ Nat.card ↥(V ⊓ L))
    {v : G} (hv : v ∈ V) (hfix : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ L) :
    ∃ c ∈ V, (∀ a ∈ A, a * c * a⁻¹ = c) ∧ c * v⁻¹ ∈ L := by
  let α : ↥A →* MulAut G := MulAut.conj.comp A.subtype
  obtain ⟨c, hc, hcfix⟩ := (coprime_invariant_coset_fixed p hA α (V ⊓ L) hcop v).1 (by
    intro a x hx
    change (a : G) * x * (a : G)⁻¹ * v⁻¹ ∈ V ⊓ L
    have h1 : (a : G) * (x * v⁻¹) * (a : G)⁻¹ ∈ V ⊓ L :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp (hAL a.2) _).mp hx.2⟩
    have h2 : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ V ⊓ L :=
      ⟨V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp hv) (V.inv_mem hv),
        hfix a a.2⟩
    have e : (a : G) * x * (a : G)⁻¹ * v⁻¹ =
        ((a : G) * (x * v⁻¹) * (a : G)⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by group
    rw [e]
    exact (V ⊓ L).mul_mem h1 h2)
  refine ⟨c, ?_, fun a ha => hcfix ⟨a, ha⟩, hc.2⟩
  have e : c = (c * v⁻¹) * v := by group
  rw [e]
  exact V.mul_mem hc.1 hv

omit [Finite G] in
theorem mem_of_mul_pow_two {U U₀ : Subgroup G} (hUU₀ : U ≤ Subgroup.normalizer (U₀ : Set G))
    {r c : G} (hr : r ∈ U) (hc : c ∈ U)
    (hrc : r * c * r⁻¹ * c⁻¹ ∈ U₀) (hr2 : ∃ m : ℕ, r ^ 2 ^ m = 1)
    (hc3 : ∃ k : ℕ, c ^ 3 ^ k ∈ U₀) (hrc2 : ∃ m : ℕ, (r * c) ^ 2 ^ m = 1) : c ∈ U₀ := by
  obtain ⟨m, hm⟩ := hr2
  obtain ⟨k, hk⟩ := hc3
  obtain ⟨m', hm'⟩ := hrc2
  obtain ⟨ρ, rfl⟩ : ∃ ρ : ↥U, (ρ : G) = r := ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥U, (γ : G) = c := ⟨⟨c, hc⟩, rfl⟩
  haveI : (U₀.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUU₀
  let π : ↥U →* ↥U ⧸ U₀.subgroupOf U := QuotientGroup.mk' (U₀.subgroupOf U)
  have hπ : ∀ x : ↥U, π x = 1 ↔ (x : G) ∈ U₀ := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  have hcomm : π ρ * π γ = π γ * π ρ := by
    have h1 : π (ρ * γ * ρ⁻¹ * γ⁻¹) = 1 := (hπ _).mpr hrc
    simp only [map_mul, map_inv] at h1
    calc π ρ * π γ = (π ρ * π γ * (π ρ)⁻¹ * (π γ)⁻¹) * (π γ * π ρ) := by group
      _ = π γ * π ρ := by rw [h1, one_mul]
  have hρ2 : π ρ ^ 2 ^ m = 1 := by
    rw [← map_pow, hπ, Subgroup.coe_pow, hm]
    exact U₀.one_mem
  have hργ2 : (π ρ * π γ) ^ 2 ^ m' = 1 := by
    rw [← map_mul, ← map_pow, hπ, Subgroup.coe_pow, Subgroup.coe_mul, hm']
    exact U₀.one_mem
  have hγ3 : π γ ^ 3 ^ k = 1 := by
    rw [← map_pow, hπ, Subgroup.coe_pow]
    exact hk
  have h2 : orderOf (π γ) ∣ 2 ^ (m + m') :=
    (Commute.orderOf_dvd_lcm_mul hcomm).trans (Nat.lcm_dvd
      ((orderOf_dvd_of_pow_eq_one hρ2).trans (pow_dvd_pow 2 (Nat.le_add_right m m')))
      ((orderOf_dvd_of_pow_eq_one hργ2).trans (pow_dvd_pow 2 (Nat.le_add_left m' m))))
  have h3 : orderOf (π γ) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hγ3
  have hcop : Nat.Coprime (2 ^ (m + m')) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  exact (hπ γ).mp (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3))

end Coprime

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {A J N : Subgroup G}
    (hA : IsPGroup p A) (hN : ¬ p ∣ Nat.card N) (hNJ : N ≤ J)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (hJA : ∀ j ∈ J, ∀ a ∈ A, ∃ k ∈ N, ∃ a' ∈ A, j * a * j⁻¹ = k * a')
    {j : G} (hj : j ∈ J) : ∃ k ∈ N, k * j ∈ Subgroup.normalizer (A : Set G) := by
  have hS : ((N ⊔ A : Subgroup G) : Set G) = (N : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N A hAN
  have hconjN : ∀ g ∈ J, ∀ k ∈ N, g * k * g⁻¹ ∈ N := Subgroup.le_normalizer_iff.mp hJN
  have hconjA : ∀ a ∈ A, ∀ k ∈ N, a * k * a⁻¹ ∈ N := Subgroup.le_normalizer_iff.mp hAN
  have hmul : ∀ x ∈ N ⊔ A, ∃ k ∈ N, ∃ a ∈ A, x = k * a := by
    intro x hx
    have hx' : x ∈ (N : Set G) * (A : Set G) := by
      rw [← hS]
      exact hx
    obtain ⟨k, hk, a, ha, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨k, hk, a, ha, rfl⟩
  have hJS : ∀ g ∈ J, ∀ x ∈ N ⊔ A, g * x * g⁻¹ ∈ N ⊔ A := by
    intro g hg x hx
    obtain ⟨k, hk, a, ha, rfl⟩ := hmul x hx
    obtain ⟨k', hk', a', ha', h⟩ := hJA g hg a ha
    have e : g * (k * a) * g⁻¹ = (g * k * g⁻¹ * k') * a' := by
      calc g * (k * a) * g⁻¹ = (g * k * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * k * g⁻¹ * k') * a' := by rw [h]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.mul_mem (hconjN g hg k hk) hk'))
      (Subgroup.mem_sup_right ha')
  have hJAS : J ⊔ A ≤ Subgroup.normalizer ((N ⊔ A : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_normalizer_iff.mpr hJS)
      ((le_sup_right : A ≤ N ⊔ A).trans Subgroup.le_normalizer)
  have hAn : ∀ g ∈ J ⊔ A, ∀ x ∈ N ⊔ A, g * x * g⁻¹ ∈ N ⊔ A :=
    Subgroup.le_normalizer_iff.mp hJAS
  have hrel : ¬ p ∣ A.relIndex (N ⊔ A) := by
    have hcop : Nat.Coprime (Nat.card N) (Nat.card A) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN).symm
    have hdisj : Disjoint N A := Subgroup.disjoint_of_coprime_natCard hcop
    have hinj : Set.InjOn (QuotientGroup.mk : G → G ⧸ A) (N : Set G) := by
      intro x hx y hy hxy
      have h1 : x⁻¹ * y ∈ A := QuotientGroup.eq.mp hxy
      have h2 : x⁻¹ * y ∈ N := N.mul_mem (N.inv_mem hx) hy
      have h3 : x⁻¹ * y = 1 := Subgroup.mem_bot.mp (hdisj.le_bot ⟨h2, h1⟩)
      exact inv_mul_eq_one.mp h3
    have hcardS : Nat.card (N ⊔ A : Subgroup G) = Nat.card A * Nat.card N := by
      have h1 : Nat.card (N ⊔ A : Subgroup G) = Nat.card ((N : Set G) * (A : Set G) : Set G) := by
        rw [← hS]
        rfl
      rw [h1, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient A (N : Set G)]
      congr 1
      exact Nat.card_image_of_injOn hinj
    have h2 := Subgroup.relIndex_mul_card (H := A) (K := N ⊔ A)
    rw [inf_of_le_left (le_sup_right : A ≤ N ⊔ A), hcardS, mul_comm (Nat.card A)] at h2
    have h3 : A.relIndex (N ⊔ A) = Nat.card N := Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    rw [h3]
    exact hN
  obtain ⟨s, hs, hsn⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.frattini_argument_subgroup (J ⊔ A)
      (N ⊔ A) A p Fact.out (sup_le_sup_right hNJ A) hAn le_sup_right hA hrel j
      (Subgroup.mem_sup_left hj)
  obtain ⟨k, hk, a, ha, rfl⟩ := hmul s hs
  refine ⟨a⁻¹ * k * a, ?_, ?_⟩
  · simpa using hconjA a⁻¹ (A.inv_mem ha) k hk
  · have e : a⁻¹ * k * a * j = a⁻¹ * (k * a * j) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (H := A) (A.inv_mem ha)) hsn

end Frattini

end CFSG.RankThree.PartTwo.Sec15.Sylow155G
