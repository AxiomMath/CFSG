module

public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue
public import CFSG.RankThree.GF2n.Parrott.SylowH
public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
public import CFSG.RankThree.GF2n.Parrott.SpinTraceData
public import CFSG.RankThree.GF2n.Parrott.Section5LocalKLower
public import CFSG.RankThree.GF2n.Parrott.Section5LocalKUpper

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup

private theorem vecToV_zero_eq_one (h : Tim79a.ParrottHyp z) (P : GL8) : vecToV h P 0 = 1 := by
  have h0 := vecToV_add h P 0 0
  rw [add_zero] at h0
  exact mul_eq_left.mp h0.symm

private theorem exists_conj_eq_vecToV (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {w₀ : V} (hw₀ : w₀ ≠ 0)
    (hq₀ : q w₀ = 0) :
    ∀ v : QuotientV.V z, v ≠ 1 → qVZMod h v = 0 → ∃ g : ↥(H z), conjV h g v = vecToV h P w₀ := by
  intro v hv hqv
  refine exists_conj_of_qVZMod_eq_zero D h P hP hv (fun h1 => hw₀ ?_) hqv ?_
  · exact vecToV_injective h P (h1.trans (vecToV_zero_eq_one h P).symm)
  · rw [qVZMod_vecToV_eq_q D h P hP]
    exact hq₀

private theorem qH_mem_gens_of_mem_lifts {y : ↥(H z)}
    (hy : y ∈ ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z))) :
    qH D y ∈ ({⟨u, u_mem_A⟩, ⟨v, v_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩, ⟨beta1, beta1_mem_A⟩,
      ⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set A45) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (qH_uH D)
  · exact Or.inr (Or.inl (qH_vH D))
  · exact Or.inr (Or.inr (Or.inl (qH_a1H D)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (qH_b1H D))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (qH_a2H D)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (qH_b2H D)))))

private theorem lift_trace_data_of_spin (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {w₀ : V}
    (hdata : ∀ g ∈ ({⟨u, u_mem_A⟩, ⟨v, v_mem_A⟩, ⟨alpha1, alpha1_mem_A⟩, ⟨beta1, beta1_mem_A⟩,
        ⟨alpha2, alpha2_mem_A⟩, ⟨beta2, beta2_mem_A⟩} : Set A45),
      ((rhoA g : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w₀ = w₀ ∧
        ∃ r : A45, r ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ∧ r ^ 3 = 1 ∧
          (g * r * g⁻¹ = r ∨ g * r * g⁻¹ = r⁻¹) ∧
          w₀ + ((rhoA r : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w₀ +
            ((rhoA r : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
              (((rhoA r : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w₀) = 0) :
    ∀ y ∈ ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z)),
      conjV h y (vecToV h P w₀) = vecToV h P w₀ ∧ ∃ x : ↥(H z), conjZ z x = 1 ∧
        qH D x ^ 3 = 1 ∧
        (qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
          qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹) ∧
        vecToV h P w₀ * conjV h x (vecToV h P w₀) * conjV h x (conjV h x (vecToV h P w₀)) =
          1 := by
  intro y hy
  obtain ⟨hfix, r, hrQ, hr3, hnorm, htr⟩ := hdata _ (qH_mem_gens_of_mem_lifts D hy)
  obtain ⟨x, rfl⟩ := qH_surjective D r
  refine ⟨?_, x, conjZ_eq_one_of_qH_mem_QP45 D h x (Subgroup.mem_subgroupOf.mp hrQ), hr3,
    hnorm, ?_⟩
  · rw [conjV_vecToV D h P hP y w₀, hfix]
  · rw [conjV_vecToV D h P hP x w₀, conjV_vecToV D h P hP x, ← vecToV_add, ← vecToV_add, htr,
      vecToV_zero_eq_one]

private theorem fixDimV_lt_seven_of_isConj_t (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (ht : fixCard ((rhoA (⟨t, t_mem_A⟩ : A45) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = 64) :
    ∀ k : ↥(H z), IsConj (qH D k) (⟨t, t_mem_A⟩ : A45) → fixDimV h k < 7 := by
  intro k hk
  obtain ⟨c, hc⟩ := isConj_iff.mp hk.symm
  have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP k
  rw [← hc, map_mul, map_mul, map_inv, fixCard_conj, ht,
    show (64 : ℕ) = 2 ^ 6 by norm_num] at h1
  have h6 : fixDimV h k = 6 := Nat.pow_right_injective le_rfl h1
  omega

theorem card_and_centerIn_isSylowOf_centralizer_of_spin (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∀ j ∈ J z, orderOf j = 2 → j ∉ centerIn (J z) →
      ∀ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) →
        Nat.card K = 2 ^ 16 ∧ centerIn K = Subgroup.closure {z, j} := by
  intro j hj hj2 hjZ K hK
  have hlo := two_pow_sixteen_le_card_of_isSylowOf_centralizer D h
    (exists_conj_eq_vecToV D h P hP spinW0_ne_zero q_spinW0)
    (lift_trace_data_of_spin D h P hP spinTraceData) hj hj2 hjZ hK
  have hcard := le_antisymm (card_isSylowOf_centralizer_le h hj hjZ hK) hlo
  exact ⟨hcard, centerIn_isSylowOf_centralizer_eq D h hZ hz₁ hz₁z hord
    (fixDimV_lt_seven_of_isConj_t D h P hP spinFixedCard_t) hj hj2 hjZ hK hcard⟩

end CFSG.RankThree.GF2n.Parrott
