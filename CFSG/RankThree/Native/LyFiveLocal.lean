module

public import CFSG.RankThree.Native.LyFiveCosets
public import CFSG.Sporadic.Ly.KeySpec

public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup
open scoped Matrix

namespace FiveMRel

variable {G : Type*} [Group G] {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 5} {a b : G}
  {Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)} {αc βc : Fin 4 → ZMod 5}
  (h : FiveMRel x v ω a b Ab Bb αc βc)
include h

theorem orderOf_a : orderOf a = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 : ¬a ^ 5 ^ 1 = 1 := by
    rw [pow_one, h.ax]
    exact h.q.x1
  have h2 : a ^ 5 ^ (1 + 1) = 1 := by norm_num [h.a25]
  have := orderOf_eq_prime_pow h1 h2
  norm_num at this
  exact this

theorem orderOf_b : orderOf b = 8 := by
  have h1 : ¬b ^ 2 ^ 2 = 1 := by norm_num [h.b4]
  have h2 : b ^ 2 ^ (2 + 1) = 1 := by norm_num [h.b8]
  have := orderOf_eq_prime_pow h1 h2
  norm_num at this
  exact this

theorem conj_b_x : b * x * b⁻¹ = x ^ 2 := by rw [h.bx, mul_inv_cancel_right]

theorem local_structure {n : ℕ} {par : ℕ → ℕ} {gen : ℕ → Bool} {t : ℕ → G}
    {tb : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 5)} {next : ℕ → Bool → ℕ}
    {qc : ℕ → Bool → ZMod 5 × (Fin 4 → ZMod 5)}
    (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    orderOf a = 25 ∧ orderOf b = 8 ∧ orderOf x = 5 ∧ b * x * b⁻¹ = x ^ 2 ∧
      fiveQ x v ≤ closure ({a, b} : Set G) ∧
      ((fiveQ x v).subgroupOf (closure ({a, b} : Set G))).Normal ∧
      Nat.card (fiveQ x v) = 3125 ∧ Monoid.exponent (fiveQ x v) = 5 ∧
      (center (fiveQ x v)).map (fiveQ x v).subtype = zpowers x ∧
      (∃ φ : fiveQ x v →* Multiplicative (Fin 4 → ZMod 5),
        (∀ (c : ZMod 5) (e : Fin 4 → ZMod 5) (q : fiveQ x v), (q : G) = fiveNF x v c e →
          φ q = Multiplicative.ofAdd e) ∧
        Function.Surjective φ ∧ φ.ker = (zpowers x).subgroupOf (fiveQ x v) ∧
        (∃ e : fiveQ x v ⧸ φ.ker ≃* Multiplicative (Fin 4 → ZMod 5),
          ∀ q : fiveQ x v, e q = φ q) ∧
        ∃ ρ : closure ({a, b} : Set G) →* GL (Fin 4) (ZMod 5),
          (∀ (g : closure ({a, b} : Set G)) (q q' : fiveQ x v), (q' : G) = g * q * (g : G)⁻¹ →
            φ q' = Multiplicative.ofAdd
              ((ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ Multiplicative.toAdd (φ q))) ∧
          (∀ g : closure ({a, b} : Set G), (g : G) = a →
            (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Ab) ∧
          (∀ g : closure ({a, b} : Set G), (g : G) = b →
            (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Bb) ∧
          ρ.ker = (fiveQ x v).subgroupOf (closure ({a, b} : Set G)) ∧ Nat.card ρ.range = n) ∧
      Nat.card (closure ({a, b} : Set G)) = n * 3125 ∧
      centralizer (fiveQ x v : Set G) ⊓ closure ({a, b} : Set G) = zpowers x ∧
      fiveU a b = centralizer {x} ⊓ closure ({a, b} : Set G) ∧
      ((fiveU a b).subgroupOf (closure ({a, b} : Set G))).Normal ∧
      ((fiveU a b).subgroupOf (closure ({a, b} : Set G))).index = 4 ∧
      Nat.card (closure ({a, b} : Set G)) = 4 * Nat.card (fiveU a b) ∧
      fiveQ x v ≤ fiveU a b ∧ ((fiveQ x v).subgroupOf (fiveU a b)).Normal ∧
      centralizer (fiveQ x v : Set G) ⊓ fiveU a b = zpowers x := by
  obtain ⟨hU, hcard⟩ := h.cert_fiveU hc
  have hUM := h.fiveU_le_M
  have hidx : ((fiveU a b).subgroupOf (closure ({a, b} : Set G))).index = 4 := by
    have h1 := ((fiveU a b).subgroupOf (closure ({a, b} : Set G))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card (fiveU a b) := by
      have := h.cert_finite_M hc
      have : Finite (fiveU a b) := Finite.of_injective _ (inclusion_injective hUM)
      exact Nat.card_pos
    rw [mul_comm 4] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  refine ⟨h.orderOf_a, h.orderOf_b, h.q.orderOf_x, h.conj_b_x, h.fiveQ_le_M, h.fiveQ_normal,
    h.q.card_fiveQ, h.q.exponent_fiveQ, h.q.center_map, ⟨h.q.coordHom, fun c e q hq => ?_,
    h.q.coordHom_surjective, h.q.coordHom_ker,
    ⟨QuotientGroup.quotientKerEquivOfSurjective _ h.q.coordHom_surjective, fun _ => rfl⟩,
    h.rho, fun g q q' hq' => ?_, fun g hg => ?_, fun g hg => ?_, h.cert_rho_ker hc,
    h.cert_card_rho_range hc⟩, h.cert_card_M hc, h.cert_centralizer_Q hc, hU, ?_, hidx, hcard,
    ?_, h.fiveQ_normal_of_le hUM, h.cert_centralizer_Q_fiveU hc⟩
  · have e1 : q = ⟨fiveNF x v c e, FiveQRel.nf_mem c e⟩ := Subtype.ext hq
    rw [e1]
    show Multiplicative.ofAdd (h.q.coord _) = _
    rw [h.q.coord_nf]
  · have e1 : q' = h.conjQ g q := Subtype.ext hq'
    rw [e1]
    show Multiplicative.ofAdd (h.q.coord _) = Multiplicative.ofAdd (_ *ᵥ h.q.coord q)
    rw [h.coord_conjQ, rho_val]
  · have e1 : g = ⟨a, a_mem⟩ := Subtype.ext hg
    rw [e1, rho_val, h.rhoMat_a]
  · have e1 : g = ⟨b, b_mem⟩ := Subtype.ext hg
    rw [e1, rho_val, h.rhoMat_b]
  · rw [hU]
    exact h.centralizer_x_normal
  · rw [hU]
    exact h.fiveQ_le_centralizer_x

end FiveMRel

end CFSG.RankThree.Native
