module

public import CFSG.Sporadic.HNOddCore.FusC
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Equiv Equiv.Perm

theorem t2J_sq :
    t2J ^ 2 = 1 := jR_injective (by rw [map_pow, t2_sqR, map_one])

theorem t2J_ne_one :
    t2J ≠ 1 := fun h => t2_ne_oneR (by rw [h, map_one])

theorem t4J_sq' :
    t4J ^ 2 = 1 := by rw [pow_two, t4J_sq]

theorem ctuc_hn_involution_fusion_and_local_stabilizers :
    (∀ y : RH, y ^ 2 = 1 → y ≠ 1 → IsConj t1R y ∨ IsConj (jR t2J) y ∨ IsConj (jR t4J) y) ∧
    ¬ IsConj t1R (jR t2J) ∧ ¬ IsConj t1R (jR t4J) ∧ ¬ IsConj (jR t2J) (jR t4J) ∧
    (∀ x y : RH, x ^ 2 = 1 → x ≠ 1 → IsConj x y → ∃ g : JH, jR g * x * (jR g)⁻¹ = y) ∧
    (thetaR t1V).cycleType = Multiset.replicate 1 2 ∧
    (thetaR t2V).cycleType = Multiset.replicate 2 2 ∧
    (thetaR t4V).cycleType = Multiset.replicate 4 2 ∧
    (thetaR t6V).cycleType = Multiset.replicate 6 2 ∧
    (∀ r : RV, (r : RH) ^ 2 = 1 → (IsConj t1R (r : RH) ↔
      ((thetaR r).cycleType = Multiset.replicate 1 2 ∨
        (thetaR r).cycleType = Multiset.replicate 3 2 ∨
        (thetaR r).cycleType = Multiset.replicate 5 2))) ∧
    (∀ r : RV, (r : RH) ^ 2 = 1 → (r : RH) ≠ 1 → (IsConj (jR t2J) (r : RH) ↔
      ((thetaR r).cycleType = Multiset.replicate 2 2 ∨
        (thetaR r).cycleType = Multiset.replicate 6 2))) ∧
    IsConj t2J t6J ∧ Nat.card (Subgroup.centralizer {t2J}) = 177408000 ∧
    (∀ r : RV, (r : RH) ^ 2 = 1 → (r : RH) ≠ 1 → (IsConj (jR t4J) (r : RH) ↔
      (thetaR r).cycleType = Multiset.replicate 4 2)) ∧
    ∀ p : X, t2J • p = p → ∃ (g : JH) (hx : g⁻¹ * t2J * g ∈ HJ), g • x0 = p ∧
      ((thetaJ ⟨g⁻¹ * t2J * g, hx⟩ : Perm (Fin 12)).cycleType = Multiset.replicate 2 2 ∨
        (thetaJ ⟨g⁻¹ * t2J * g, hx⟩ : Perm (Fin 12)).cycleType = Multiset.replicate 6 2) ∧
      (∀ c : JH, (c ∈ Subgroup.centralizer {t2J} ∧ c • p = p) ↔
        (g⁻¹ * c * g ∈ Subgroup.centralizer {g⁻¹ * t2J * g} ∧ g⁻¹ * c * g ∈ HJ)) ∧
      CFSG.oddCore (MulAction.stabilizer (Subgroup.centralizer {t2J}) p) = ⊥ :=
  ⟨fun _ h2 h1 => involution_cover_R h2 h1,
    not_isConj_c_jR t2J, not_isConj_c_jR t4J, not_isConj_t2_t4,
    fun _ _ h2 h1 hc => exists_J_conj h2 h1 hc,
    thetaR_t1V, thetaR_t2V, thetaR_t4V, thetaR_t6V,
    fun _ h2 => conj_c_iff h2, fun _ h2 h1 => conj_t2_iff h2 h1,
    isConj_t2_aJ, card_CJ_t2, fun _ h2 h1 => conj_t4_iff h2 h1,
    fun _ hp => stabilizer_t2 hp⟩

end CFSG.Sporadic.HNOddCore
