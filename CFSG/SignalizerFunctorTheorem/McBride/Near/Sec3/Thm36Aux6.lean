module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

variable {G : Type u} [Group G]

theorem card_le_mul_of_cyclicMod [Finite G] {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hA : IsElemAbelian p A) (hBA : B ≤ A) (h : CyclicMod A B) :
    Nat.card ↥A ≤ p * Nat.card ↥B := by
  have : IsMulCommutative ↥A := hA.1
  have hcyc : IsCyclic (↥A ⧸ B.subgroupOf A) := by
    obtain ⟨a, ha, hle⟩ := h
    have hBc : B ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      exact congrArg Subtype.val (mul_comm' (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)
    have hBn : B ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      hBc.trans (Subgroup.centralizer_le_normalizer _)
    refine ⟨QuotientGroup.mk (⟨a, ha⟩ : ↥A), fun q => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, c, hc, hbc⟩ := (Thm32.mem_sup_iff_mul' hBn).mp (hle y.2)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hy : y = ⟨b, hBA hb⟩ * ⟨a, ha⟩ ^ k := Subtype.ext (by simpa using hbc)
    have hb1 : (QuotientGroup.mk (⟨b, hBA hb⟩ : ↥A) : ↥A ⧸ B.subgroupOf A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hb)
    rw [hy, QuotientGroup.mk_mul, hb1, one_mul, QuotientGroup.mk_zpow]
  rcases (isCyclic_quotient_iff_of_isElemAbelian hp hA hBA).mp hcyc with h1 | ⟨-, hcard⟩
  · rw [h1]
    exact Nat.le_mul_of_pos_left _ hp.pos
  · exact hcard.le

theorem inf_ne_bot_of_cyclicMod [Finite G] {p : ℕ} (hp : p.Prime) {A B B₁ : Subgroup G}
    (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card ↥A) (hB : B ≤ A) (hB₁ : B₁ ≤ A)
    (hc : CyclicMod A B) (hc₁ : CyclicMod A B₁) : B ⊓ B₁ ≠ ⊥ := by
  intro hbot
  have h1 := card_le_mul_of_cyclicMod hp hA hB hc
  have h2 := card_le_mul_of_cyclicMod hp hA hB₁ hc₁
  have hrB : B.relIndex A * Nat.card ↥B = Nat.card ↥A := by
    have := Subgroup.relIndex_mul_card (H := B) (K := A)
    rwa [inf_eq_left.mpr hB] at this
  have hrB₁ : B₁.relIndex A * Nat.card ↥B₁ = Nat.card ↥A := by
    have := Subgroup.relIndex_mul_card (H := B₁) (K := A)
    rwa [inf_eq_left.mpr hB₁] at this
  have hr : (B ⊓ B₁).relIndex A * Nat.card ↥(B ⊓ B₁) = Nat.card ↥A := by
    have := Subgroup.relIndex_mul_card (H := B ⊓ B₁) (K := A)
    rwa [inf_eq_left.mpr (inf_le_left.trans hB)] at this
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hB₁pos : 0 < Nat.card ↥B₁ := Nat.card_pos
  have hlB : B.relIndex A ≤ p := by
    refine Nat.le_of_mul_le_mul_right ?_ hBpos
    calc B.relIndex A * Nat.card ↥B = Nat.card ↥A := hrB
      _ ≤ p * Nat.card ↥B := h1
  have hlB₁ : B₁.relIndex A ≤ p := by
    refine Nat.le_of_mul_le_mul_right ?_ hB₁pos
    calc B₁.relIndex A * Nat.card ↥B₁ = Nat.card ↥A := hrB₁
      _ ≤ p * Nat.card ↥B₁ := h2
  have hcardbot : Nat.card ↥(B ⊓ B₁) = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  rw [hcardbot, mul_one] at hr
  have hle : (B ⊓ B₁).relIndex A ≤ B.relIndex A * B₁.relIndex A := Subgroup.relIndex_inf_le
  have hp2 := hp.two_le
  have : Nat.card ↥A ≤ p * p := by
    calc Nat.card ↥A = (B ⊓ B₁).relIndex A := hr.symm
      _ ≤ B.relIndex A * B₁.relIndex A := hle
      _ ≤ p * p := Nat.mul_le_mul hlB hlB₁
  nlinarith [pow_succ p 2, Nat.mul_le_mul hp2 (le_refl (p * p))]

theorem cenIn_sup_eq {X₁ C B : Subgroup G} (hCn : C ≤ Subgroup.normalizer (X₁ : Set G))
    (hCB : C ≤ Subgroup.centralizer (B : Set G)) :
    cenIn (X₁ ⊔ C) (B : Set G) = cenIn X₁ (B : Set G) ⊔ C := by
  refine le_antisymm (fun g hg => ?_) (sup_le (inf_le_inf_right _ le_sup_left)
    (le_inf le_sup_right hCB))
  obtain ⟨hgS, hgC⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨x, hx, c, hc, rfl⟩ := (Thm32.mem_sup_iff_mul hCn).mp hgS
  have hxC : x ∈ Subgroup.centralizer (B : Set G) := by
    have : x = x * c * c⁻¹ := by group
    rw [this]
    exact mul_mem hgC (inv_mem (hCB hc))
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hx, hxC⟩) hc

theorem le_thetaOf {A X M E : Subgroup G} {θ : G → Subgroup G}
    (hX : ∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a) (hMX : M ≤ X) (hE : E ≤ A)
    (hMc : M ≤ Subgroup.centralizer (E : Set G)) : M ≤ thetaOf θ E := by
  refine le_iInf fun b => le_iInf fun hb => le_iInf fun hb1 => ?_
  intro m hm
  have hmC : m ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hMc hm) b hb).symm
  exact hX b (hE hb) hb1 ⟨hMX hm, hmC⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36
