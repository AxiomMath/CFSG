module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Khat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Count
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.HypA

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma_6_9_a
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    bC A θ B = A ⊓ Subgroup.centralizer (thetaOf θ B : Set G) ∧
      ∀ L ∈ lcal (thetaOf θ B), bC A θ B = A ⊓ Subgroup.centralizer (L : Set G) :=
  ⟨h.bC_eq_inf_centralizer hBA hB, fun _ hL => h.bC_eq_inf_centralizer_of_mem_lcal hBA hB hL⟩

theorem lemma_6_9_b
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    ∀ L ∈ lcal (thetaOf θ B), bN A θ B = A ⊓ Subgroup.normalizer (L : Set G) :=
  fun _ hL => h.bN_eq_inf_normalizer hBA hB hL

theorem lemma_6_9_c
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    Nat.card (lcal (thetaOf θ B)) * Nat.card (bN A θ B) = Nat.card A :=
  h.card_lcal_mul_card_bN hBA hB

theorem lemma_6_9_d
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    (∀ L ∈ lcal (thetaOf θ B), ∀ L' ∈ lcal (thetaOf θ B),
        ∃ a ∈ A, L' = L.map (MulAut.conj a).toMonoidHom) ∧
      ∀ a ∈ A, a ∉ bN A θ B → ∀ L ∈ lcal (thetaOf θ B),
        L.map (MulAut.conj a).toMonoidHom ≠ L := by
  refine ⟨fun L hL L' hL' => h.exists_conj_eq_of_mem_lcal hBA hB hL hL', ?_⟩
  intro a ha hanot L hL hLa
  refine hanot ?_
  rw [h.bN_eq_inf_normalizer hBA hB hL]
  exact Subgroup.mem_inf.mpr ⟨ha, L69.map_conj_eq_self_iff.mp hLa⟩

theorem lemma_6_9_e
    (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : ¬ F ≤ bN A θ E) (hEF : ¬ E ≤ bN A θ F) :
    Nat.card (lcal (thetaOf θ E)) = Nat.card (lcal (thetaOf θ F)) := by
  have h1 := h.card_lcal_thetaOf_sup hE hF
  have h2 := h.card_lcal_thetaOf_sup hF hE
  rw [sup_comm F E] at h2
  rw [h2, h1]
  simp [hFE, hEF]

theorem lemma_6_9_f
    (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : ¬ F ≤ bN A θ E) (hEF : E ≤ bN A θ F) :
    Nat.card (lcal (thetaOf θ E)) = p * Nat.card (lcal (thetaOf θ F)) := by
  have h1 := h.card_lcal_thetaOf_sup hE hF
  have h2 := h.card_lcal_thetaOf_sup hF hE
  rw [sup_comm F E] at h2
  rw [h2, h1]
  simp [hFE, hEF]

theorem lemma_6_9_g
    (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≤ bN A θ E) (hEF : E ≤ bN A θ F) :
    Nat.card (lcal (thetaOf θ E)) = Nat.card (lcal (thetaOf θ F)) := by
  have h1 := h.card_lcal_thetaOf_sup hE hF
  have h2 := h.card_lcal_thetaOf_sup hF hE
  rw [sup_comm F E] at h2
  rw [h2, h1]
  simp [hFE, hEF]

theorem lemma_6_9_h
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    ∃ x ∈ bN A θ B, ∀ y ∈ bN A θ B, ∃ k : ℤ, x ^ k * y⁻¹ ∈ bC A θ B := by
  obtain ⟨L, hL⟩ := h.lcal_thetaOf_nonempty hBA hB
  have hN := h.bN_eq_inf_normalizer hBA hB hL
  have hC := h.bC_eq_inf_centralizer_of_mem_lcal hBA hB hL
  have hBN : bN A θ B ≤ Subgroup.normalizer (L : Set G) := hN ▸ inf_le_right
  have hNA : bN A θ B ≤ A := hN ▸ inf_le_left
  let ρ : ↥(bN A θ B) →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hdvd : Nat.card ρ.range ∣ p :=
    card_range_conj_dvd h.prime h.elemAbelian (h.hypB_thetaOf hBA hB) hL hNA hBN
  have hcyc : IsCyclic ρ.range := by
    have : Fact p.Prime := ⟨h.prime⟩
    rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
    · have : Subsingleton ρ.range := (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · exact isCyclic_of_prime_card h1
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨x, hx⟩ := g.2
  refine ⟨x, x.2, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨ρ ⟨y, hy⟩, ⟨_, rfl⟩⟩)
  refine ⟨k, ?_⟩
  have hρy : ρ ⟨y, hy⟩ = ρ x ^ k := by
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h1
    rw [hx]
    exact h1.symm
  have hz : ρ (x ^ k * (⟨y, hy⟩ : bN A θ B)⁻¹) = 1 := by
    rw [map_mul, map_zpow, map_inv, hρy, mul_inv_cancel]
  rw [hC]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (zpow_mem (hNA x.2) k) (inv_mem (hNA hy)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : G)) hz
  have h3 : ((ρ (x ^ k * (⟨y, hy⟩ : bN A θ B)⁻¹)) ⟨l, hl⟩ : G) =
      (x : G) ^ k * y⁻¹ * l * ((x : G) ^ k * y⁻¹)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe L _ ⟨l, hl⟩
  simp only [h3] at h2
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
