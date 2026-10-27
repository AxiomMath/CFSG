module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rK
public import Mathlib.GroupTheory.Frattini
import CFSG.Assembly.OrderReductions.FrattiniElementary
import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

section Abstract

theorem uc22s21rm_isCyclic_of_quotient {X : Type*} [Group X] [Finite X]
    (h : IsCyclic (X ⧸ frattini X)) : IsCyclic X := by
  obtain ⟨g, hg⟩ := h.exists_generator
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini X) g
  have h1 : (zpowers a).map (QuotientGroup.mk' (frattini X)) = ⊤ := by
    rw [MonoidHom.map_zpowers, eq_top_iff]
    intro y _
    exact hg y
  have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini X)) (zpowers a)
  rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨a, frattini_nongenerating h2.symm⟩

theorem uc22s21rm_card_le {q : ℕ} (hq : q.Prime) {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v ^ q = 1) {V₁ V₂ : Subgroup V}
    (h₁ : IsCyclic V₁) (h₂ : IsCyclic V₂) (hsup : V₁ ⊔ V₂ = ⊤) : Nat.card V ≤ q ^ 2 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have hd : ∀ U : Subgroup V, IsCyclic U → Nat.card U ≤ q := by
    intro U hU
    have h1 : Monoid.exponent U ∣ q :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun u => Subtype.ext (hV u)
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hq.pos h1
  have hsurj : Function.Surjective (fun p : V₁ × V₂ => (p.1 : V) * p.2) := by
    intro v
    have hv : v ∈ V₁ ⊔ V₂ := by rw [hsup]; exact mem_top v
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  calc Nat.card V ≤ Nat.card (V₁ × V₂) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card V₁ * Nat.card V₂ := Nat.card_prod _ _
    _ ≤ q * q := Nat.mul_le_mul (hd V₁ h₁) (hd V₂ h₂)
    _ = q ^ 2 := (sq q).symm

theorem uc22s21rm_perfect_le_ker {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {V : Type*} [Group V]
    [Finite V] (hcomm : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v ^ q = 1)
    (hcard : Nat.card V = q ^ 2) {W : Type*} [Group W] [Finite W] (ρ : W →* MulAut V)
    (S : Sylow 2 W) {V₁ V₂ : Subgroup V} (h₁ : IsCyclic V₁) (h₂ : IsCyclic V₂)
    (hsup : V₁ ⊔ V₂ = ⊤) (hS₁ : ∀ s ∈ S, ∀ v ∈ V₁, ρ s v ∈ V₁)
    (hS₂ : ∀ s ∈ S, ∀ v ∈ V₂, ρ s v ∈ V₂) {K : Subgroup W} (hK : ⁅K, K⁆ = K) :
    K ≤ ρ.ker := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  exact uc22s21rk_perfect_le_ker_of_lines hq2 hV hcard ρ S h₁ h₂ hsup hS₁ hS₂ hK

end Abstract

section Action

variable {W : Type} [Group W] [Finite W]

theorem uc22s21rm_commutator_mem_frattini {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup W}
    [X.Normal] (hXexp : ∀ x ∈ X, x ^ q = 1) (hXnc : ¬ IsCyclic ↥X) {S : Subgroup W}
    (hS : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index) {X₁ X₂ : Subgroup W} (h₁ : IsCyclic ↥X₁)
    (h₂ : IsCyclic ↥X₂) (h₁X : X₁ ≤ X) (h₂X : X₂ ≤ X) (hsup : X₁ ⊔ X₂ = X)
    (hS₁ : S ≤ normalizer (X₁ : Set W)) (hS₂ : S ≤ normalizer (X₂ : Set W)) {K : Subgroup W}
    (hK : ⁅K, K⁆ = K) : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ (frattini ↥X).map X.subtype := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup q ↥X := fun x => ⟨1, Subtype.ext (by simpa using hXexp x x.2)⟩
  set f : ↥X →* ↥X ⧸ frattini ↥X := QuotientGroup.mk' (frattini ↥X) with hf
  have hcomm : ∀ a b : ↥X ⧸ frattini ↥X, a * b = b * a :=
    isMulCommutative_iff.1
      (CFSG.OrderReductions.FrattiniElementary.frattini_quotient_isMulCommutative q hXp)
  have hVexp : ∀ v : ↥X ⧸ frattini ↥X, v ^ q = 1 :=
    CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent q hXp
  letI : MulDistribMulAction W ↥X := MulDistribMulAction.compHom ↥X (MulAut.conjNormal (H := X))
  letI : MulDistribMulAction W (↥X ⧸ frattini ↥X) :=
    CFSG.PreuniquenessRankFour.Helpers.characteristic_quotient_mulDistribMulAction (frattini ↥X)
  let ρ : W →* MulAut (↥X ⧸ frattini ↥X) :=
    MulDistribMulAction.toMulAut W (↥X ⧸ frattini ↥X)
  have hρ : ∀ (w : W) (y : ↥X), ρ w (f y) = f (MulAut.conjNormal (H := X) w y) := by
    intro w y
    letI : MulAction.QuotientAction W (frattini ↥X) :=
      CFSG.PreuniquenessRankFour.Helpers.characteristic_subgroup_quotientAction (frattini ↥X)
    exact MulAction.Quotient.smul_mk (frattini ↥X) w y
  have hline : ∀ Y : Subgroup W, Y ≤ X → IsCyclic ↥Y → IsCyclic ↥((Y.subgroupOf X).map f) := by
    intro Y hYX hY
    haveI : IsCyclic ↥(Y.subgroupOf X) :=
      (Subgroup.subgroupOfEquivOfLe hYX).isCyclic.mpr hY
    exact isCyclic_of_surjective (f.subgroupMap (Y.subgroupOf X))
      (f.subgroupMap_surjective (Y.subgroupOf X))
  have hinv : ∀ Y : Subgroup W, Y ≤ X → ∀ s ∈ normalizer (Y : Set W), ∀ v ∈ (Y.subgroupOf X).map f,
      ρ s v ∈ (Y.subgroupOf X).map f := by
    rintro Y hYX s hs _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal (H := X) s y, ?_, (hρ s y).symm⟩
    have hy' : (y : W) ∈ Y := hy
    have h1 := (Subgroup.mem_normalizer_iff.1 hs (y : W)).1 hy'
    show ((MulAut.conjNormal (H := X) s y : ↥X) : W) ∈ Y
    rw [MulAut.conjNormal_apply]
    exact h1
  have hsup' : (X₁.subgroupOf X).map f ⊔ (X₂.subgroupOf X).map f = ⊤ := by
    rw [← Subgroup.map_sup]
    have h1 : X₁.subgroupOf X ⊔ X₂.subgroupOf X = ⊤ := by
      have := Subgroup.comap_sup_eq_of_le_range X.subtype (by simpa using h₁X)
        (by simpa using h₂X)
      change X₁.subgroupOf X ⊔ X₂.subgroupOf X = (X₁ ⊔ X₂).subgroupOf X at this
      rw [hsup, Subgroup.subgroupOf_self] at this
      exact this
    rw [h1, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
  have hcard : Nat.card (↥X ⧸ frattini ↥X) = q ^ 2 := by
    have hle := uc22s21rm_card_le hq hcomm hVexp (hline X₁ h₁X h₁) (hline X₂ h₂X h₂) hsup'
    obtain ⟨n, hn⟩ := (hXp.to_quotient (frattini ↥X)).exists_card_eq
    have hn2 : n ≤ 2 := by
      rw [hn] at hle
      exact (Nat.pow_le_pow_iff_right hq.one_lt).1 hle
    have hnc : ¬ IsCyclic (↥X ⧸ frattini ↥X) := fun hc => hXnc (uc22s21rm_isCyclic_of_quotient hc)
    interval_cases n
    · haveI : Subsingleton (↥X ⧸ frattini ↥X) :=
        (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
      exact (hnc inferInstance).elim
    · exact absurd (isCyclic_of_prime_card (by simpa using hn)) hnc
    · exact hn
  have hker := uc22s21rm_perfect_le_ker hq2 hcomm hVexp hcard ρ (hS.toSylow hSi)
    (hline X₁ h₁X h₁) (hline X₂ h₂X h₂) hsup'
    (fun s hs => hinv X₁ h₁X s (hS₁ hs)) (fun s hs => hinv X₂ h₂X s (hS₂ hs)) hK
  intro k hk x hx
  have h1 : ρ k (f ⟨x, hx⟩) = f ⟨x, hx⟩ := by
    have := MonoidHom.mem_ker.1 (hker hk)
    rw [this]
    rfl
  rw [hρ] at h1
  have h2 : (MulAut.conjNormal (H := X) k ⟨x, hx⟩) * ⟨x, hx⟩⁻¹ ∈ frattini ↥X := by
    have := (QuotientGroup.eq_iff_div_mem).1 h1
    simpa [div_eq_mul_inv] using this
  exact Subgroup.mem_map.2 ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩

end Action

end CFSG.LocalAnalysis.UniquenessCase.UC22
