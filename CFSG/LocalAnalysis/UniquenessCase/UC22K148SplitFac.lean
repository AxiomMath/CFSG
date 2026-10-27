module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Step
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.LocalAnalysis.UniquenessCase.UC22K148S5Br
import CFSG.Quasithin.Background.E2SeventeenSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem secNatS5_sup_zpowers_of_inf_eq_bot [Finite G] {L : Subgroup G} {a r : G}
    (hLn : L.Normal) (ha2 : a * a = 1) (haL : a ∉ L)
    (hS5 : SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥)
    (hact : ∀ g : G, ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ L ⊤, ρ g u = ρ h u)
    (hr2 : r * r = 1) (hrL : r ∉ L)
    (hMK : (L ⊔ Subgroup.zpowers r) ⊓ cenOn ρ ⊤ (commOn ρ L ⊤) = ⊥) :
    SecNatS5 ρ (L ⊔ Subgroup.zpowers r) (commOn ρ L ⊤) ⊥ := by
  have hN : ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.2 hLn]
    exact Subgroup.mem_top x
  have hsq : ∀ x : G, x * x = 1 → x ^ 2 ∈ L := fun x hx => by
    rw [pow_two, hx]
    exact L.one_mem
  refine secNatS5_of_forall_exists_eq_apply hS5 (fun h hh hU => ?_) (fun h _ => hact h) ?_
  · have hk : h ∈ (L ⊔ Subgroup.zpowers r) ⊓ cenOn ρ ⊤ (commOn ρ L ⊤) :=
      ⟨hh, Subgroup.mem_top _, hU⟩
    rwa [hMK, Subgroup.mem_bot] at hk
  · exact ((CFSG.ComponentClassification.UnbalancedGS.AHelpers.card_sup_zpowers_eq_two_mul
      (hN a) haL (hsq a ha2)).trans
        (CFSG.ComponentClassification.UnbalancedGS.AHelpers.card_sup_zpowers_eq_two_mul
          (hN r) hrL (hsq r hr2)).symm).le

theorem nonempty_sup_zpowers_mulEquiv_perm_three [Finite G] {Q K : Subgroup G} {b r : G}
    (hQ3 : Nat.card ↥Q = 3) (hb : ∀ x ∈ Q, b * x * b⁻¹ = x⁻¹) (hb2 : b * b = 1)
    (hQK : ∀ x ∈ Q, ∀ k ∈ K, x * k = k * x) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrb : r * b ∈ K) :
    Nonempty (↥(Q ⊔ Subgroup.zpowers r) ≃* Equiv.Perm (Fin 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q).1 (isCyclic_of_prime_card hQ3)
  have hq3 : orderOf q = 3 := by rw [← Nat.card_zpowers, hq, hQ3]
  have hqQ : q ∈ Q := hq ▸ Subgroup.mem_zpowers q
  have hinv : r * q * r⁻¹ = q⁻¹ := by
    have e : r * q * r⁻¹ = (r * b) * (b * q * b⁻¹) * (r * b)⁻¹ := by
      calc r * q * r⁻¹ = r * (b * b) * q * (b * b)⁻¹ * r⁻¹ := by rw [hb2]; group
        _ = (r * b) * (b * q * b⁻¹) * (r * b)⁻¹ := by group
    rw [e, hb q hqQ, ← hQK q⁻¹ (Q.inv_mem hqQ) _ hrb, mul_inv_cancel_right]
  rw [← hq]
  exact CFSG.Quasithin.E2.nonempty_zpowers_sup_mulEquiv_perm_three hq3 hr2 hr1 hinv

theorem hasFactors148_of_split [Finite G] [Finite V] (hO : CFSG.pCore 2 G = ⊥)
    (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G)) {N : Subgroup G} {r : G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) (hcod : commOn ρ N ⊤ ⊔ fixSub ρ N = ⊤) (hr2 : r * r = 1)
    (hMn : (N ⊔ Subgroup.zpowers r).Normal)
    (hMK : (N ⊔ Subgroup.zpowers r) ⊓ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊥)
    (hMKsup : (N ⊔ Subgroup.zpowers r) ⊔ cenOn ρ ⊤ (commOn ρ N ⊤) = ⊤)
    (hMc : ∀ m ∈ N ⊔ Subgroup.zpowers r, ∀ k ∈ cenOn ρ ⊤ (commOn ρ N ⊤), m * k = k * m)
    (hfM : IsFactor148 (N ⊔ Subgroup.zpowers r)) : HasFactors148 G :=
  hasFactors148_of_prod hO hρ hshape hH IH hMn (cenOn_commOn_normal hN) hMK hMKsup hMc
    (fun h => hN1 (le_bot_iff.1 (h ▸ le_sup_left))) hfM (commOn_sup_zpowers_le hN hcod hr2)
    fun k hk x hx => hk.2 x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
