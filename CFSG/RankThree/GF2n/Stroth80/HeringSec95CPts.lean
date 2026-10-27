module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVNe6Om4
public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData
public import CFSG.RankThree.GF2n.Stroth80.Sec91

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_points95 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)))
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (Fin 2 ⊕ Fin 2 → K))
      (u : Fin 2 ⊕ Fin 2 → K),
      Nat.card K = Nat.card Z ∧ φ.range = StatedOmega (StatedQuadPlus 2 K) ∧
      φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∧
      quadPlus 2 K u = 0 ∧ u ≠ 0 ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ x : Fin 2 ⊕ Fin 2 → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔
        polar (quadPlus 2 K) u x = 0) ∧
      polar (quadPlus 2 K) u ((φ ⟨r, hr.mem⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u)
        ≠ 0 ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u ∧
      ((conjSubgroup r (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        E.LomGL ((φ ⟨r, hr.mem⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) := by
  classical
  have hs5 := hs.toSec5
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  let E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K)) :=
    ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)
  obtain ⟨u, hQu, hu0, hBiff, hW, hLeq⟩ := hc.omega_points_flag h34 hs5 hnotQB hK E hQ h3
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hLA := sec7_conj_LomGL E φ hφ ⟨r, hrR⟩ hLeq
  obtain ⟨ĉ, hĉQ, hĉC, b', hb'B, hb'ne⟩ := hr.plane
  have hvV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t := (hc.conj_Rt_le_Vt hs5.mem hrR) hĉC
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs5 hnotQB ⁅ĉ, t⁆ hvV
  have hvnQ : ⁅ĉ, t⁆ ∉ QB B := fun hvQ =>
    hb'ne ((hperp.mp hvQ) b' hb'B ĉ hĉQ
      (by rw [show ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ = 1 by group]; exact Z.one_mem))
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hpolar : polar (quadPlus 2 K) u (secVec ψ ⟨⁅ĉ, t⁆, hvV⟩) ≠ 0 := by
    intro h0
    obtain ⟨w, hwVQ, hwv⟩ := (hW _).mpr h0
    apply hvnQ
    have hzw : (w : G)⁻¹ * ⁅ĉ, t⁆ ∈ Z := by
      have h1 : secVec ψ (w⁻¹ * ⟨⁅ĉ, t⁆, hvV⟩) = 0 := by
        rw [secVec_mul, secVec_inv, hwv]
        abel
      exact (secVec_eq_zero_iff ψ _).mp h1
    have e1 : ⁅ĉ, t⁆ = (w : G) * ((w : G)⁻¹ * ⁅ĉ, t⁆) := by group
    rw [e1]
    exact (QB B).mul_mem (Subgroup.mem_inf.mp hwVQ).2 (hZQB hzw)
  have hBN : conjSubgroup r B ≤ Subgroup.normalizer (Z : Set G) := by
    intro a ha
    have : a ∈ Q := by
      have hbB : r⁻¹ * a * r ∈ B := mem_conjSubgroup.mp ha
      have hb' : r⁻¹ * a * r ∈ Q := hc.le hbB
      have := (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hrR)).1 _ hb'
      simpa [mul_assoc] using this
    exact hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 this)
  obtain ⟨a, ha, ζ, hζ, hvaζ⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hĉC
  have hbB : r⁻¹ * a * r ∈ B := mem_conjSubgroup.mp ha
  have haV : a ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs5.mem hrR) (Subgroup.mem_sup_left ha)
  have hbV : r⁻¹ * a * r ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs5.mem hbB
  obtain ⟨c, hc'⟩ := (hBiff (secVec ψ ⟨r⁻¹ * a * r, hbV⟩)).mp ⟨⟨r⁻¹ * a * r, hbV⟩, hbB, rfl⟩
  have hsa : secVec ψ ⟨a, haV⟩ =
      (φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        secVec ψ ⟨r⁻¹ * a * r, hbV⟩ :=
    hψ ⟨r, hrR⟩ ⟨r⁻¹ * a * r, hbV⟩ ⟨a, haV⟩ (by simp [mul_assoc])
  have hsv : secVec ψ ⟨⁅ĉ, t⁆, hvV⟩ = secVec ψ ⟨a, haV⟩ := by
    have h1 : secVec ψ (⟨a, haV⟩⁻¹ * ⟨⁅ĉ, t⁆, hvV⟩) = 0 := by
      rw [secVec_eq_zero_iff ψ]
      have : a⁻¹ * ⁅ĉ, t⁆ = ζ := by rw [← hvaζ]; group
      show a⁻¹ * ⁅ĉ, t⁆ ∈ Z
      rw [this]
      exact hζ
    rw [secVec_mul, secVec_inv] at h1
    exact (neg_add_eq_zero.mp h1).symm
  have hpol2 : polar (quadPlus 2 K) u
      ((φ ⟨r, hrR⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ≠ 0 := by
    intro h0
    apply hpolar
    rw [hsv, hsa, hc', Matrix.mulVec_smul, polar_smul_right_eq, h0, mul_zero]
  exact ⟨K, fK, finK, ‹CharP K 2›, E, hn, φ, ψ, u, hK, hφ, hker, hψ, hQu, hu0, hBiff, hW, hpol2,
    hLeq, hLA⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80
