module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

theorem cenB_cen_b (h : FF84Sec4 b L B K b₁ b₂) {σ : G} (hσB : σ ∈ CenS B) : σ ∈ Cen b :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hσB b (mem_b h)).symm

theorem theta_inv (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) : thG L θ σ = swap 6 7 := by
  have hσb := cenB_cen_b h hσB
  have hσN : σ ∈ Nor L := h.hyp.hLN hσb
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2
  have hc₁ : thG L θ σ * a8c = a8c * thG L θ σ := by
    rw [← hθ.c, ← thG_mul hσN hb₁N, ← thG_mul hb₁N hσN,
      (Subgroup.mem_centralizer_iff.1 hσB b₁ (mem_b₁ h)).symm]
  have hc₂ : thG L θ σ * a8d = a8d * thG L θ σ := by
    rw [← hθ.d, ← thG_mul hσN hb₂N, ← thG_mul hb₂N hσN,
      (Subgroup.mem_centralizer_iff.1 hσB b₂ (mem_b₂ h)).symm]
  have hsq : thG L θ σ * thG L θ σ = 1 := by
    rw [← thG_mul hσN hσN, hσ2, thG_one]
  rcases (cen_two _ hc₁ hc₂).2 hsq with h1 | h1
  · exfalso
    have hmem := Qθ h hZ hX hθ hσN hσb h1
    exact hσ1 (two_elt_zpowers h hmem (k := 1) (by rw [pow_one, pow_two]; exact hσ2))
  · exact h1

theorem V_le (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥)
    (hX : Opp 3 (Cen b) = ⊥) (hθ : ThM L b₁ b₂ θ) {σ : G} (hσB : σ ∈ CenS B)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) {V : Subgroup G} (hV : ∀ w ∈ V, ∃ k : ℕ, w ^ 2 ^ k = 1) (hVb : V ≤ Cen b)
    (hVσ : V ≤ Cen σ) (hVn : ∀ l ∈ L ⊓ Cen σ, ∀ v ∈ V, l * v * l⁻¹ ∈ V) :
    ∀ v ∈ V, v = 1 ∨ v = σ := by
  have hσb := cenB_cen_b h hσB
  have hσN : σ ∈ Nor L := h.hyp.hLN hσb
  have hστ := theta_inv h hZ hX hθ hσB hσ2 hσ1
  have hord : ∀ w ∈ V, (thG L θ w) ^ 8 = 1 := by
    intro w hw
    obtain ⟨k, hk'⟩ := hV w hw
    have := thG_pow (θ := θ) (h.hyp.hLN (hVb hw)) (2 ^ k)
    rw [hk', thG_one] at this
    exact two_pow_perm8 this.symm
  intro v hv
  have hvN : v ∈ Nor L := h.hyp.hLN (hVb hv)
  have hvσ : v * σ = σ * v := Subgroup.mem_centralizer_singleton_iff.1 (hVσ hv)
  have htc : thG L θ v * swap 6 7 = swap 6 7 * thG L θ v := by
    rw [← hστ, ← thG_mul hvN hσN, ← thG_mul hσN hvN, hvσ]
  have hρ : ∀ ρ : Perm (Fin 8), ρ ∈ alternatingGroup (Fin 8) → ρ * swap 6 7 = swap 6 7 * ρ →
      (thG L θ v * (ρ * thG L θ v * ρ⁻¹)) ^ 8 = 1 := by
    intro ρ hρA hρc
    obtain ⟨x, hxL, hxρ⟩ := hθ.surj ρ hρA
    have hxN : x ∈ Nor L := Subgroup.le_normalizer hxL
    have hxσ : x * σ = σ * x := cen_thG h hZ hθ hxL hσN (by rw [hxρ, hστ]; exact hρc)
    have hxV : x * v * x⁻¹ ∈ V := hVn x
      (Subgroup.mem_inf.2 ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2 hxσ⟩) v hv
    have hxvN : x * v * x⁻¹ ∈ Nor L := mul_mem (mul_mem hxN hvN) (inv_mem hxN)
    have := hord (v * (x * v * x⁻¹)) (mul_mem hv hxV)
    rwa [thG_mul hvN hxvN, thG_conj hxN hvN, hxρ] at this
  rcases cen_V (thG L θ v) htc (hord v hv)
    (hρ _ (mem_alternatingGroup.2 sign_c345) (by decide +kernel))
    (hρ _ (mem_alternatingGroup.2 sign_p12_67) (by decide +kernel))
    (hρ _ (mem_alternatingGroup.2 sign_p03_24) (by decide +kernel))
    (hρ _ (mem_alternatingGroup.2 sign_p14_23) (by decide +kernel)) with ht | ht
  · left
    have hmem := Qθ h hZ hX hθ hvN (hVb hv) ht
    obtain ⟨k, hk⟩ := hV v hv
    exact two_elt_zpowers h hmem (k := k) hk
  · right
    have hwN : v * σ ∈ Nor L := mul_mem hvN hσN
    have hw1 : thG L θ (v * σ) = 1 := by
      rw [thG_mul hvN hσN, ht, hστ, swap_mul_self]
    have hmem := Qθ h hZ hX hθ hwN (mul_mem (hVb hv) hσb) hw1
    obtain ⟨k, hk'⟩ := hV v hv
    have hσ2' : σ ^ 2 = 1 := by rw [pow_two]; exact hσ2
    have hvn : v ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
    have hσn : σ ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hσ2', one_pow]
    have hw2 : (v * σ) ^ 2 ^ (k + 1) = 1 := by
      rw [Commute.mul_pow (show Commute v σ from hvσ), hvn, hσn, one_mul]
    have hwe : v * σ = 1 := two_elt_zpowers h hmem hw2
    have h1 : v = σ⁻¹ := eq_inv_of_mul_eq_one_left hwe
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hσ2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
