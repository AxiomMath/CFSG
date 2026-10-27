module

public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.ClassicalGroups.Orthogonal.RootInvolutionModels
import CFSG.ClassicalGroups.Orthogonal.RootInvolutionClass
import CFSG.RankThree.GF2n.Stroth80.Sec116Elt
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.GH74.Generic.GKFCover
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

abbrev IsOmegaLieModel (X : Type) [Group X] (m x : ℕ) : Prop :=
  CFSG.Blueprint.LieModel X .POmegaPlus m 2 x ∨ CFSG.Blueprint.LieModel X .POmegaMinus m 2 x ∨
    (m = 3 ∧ CFSG.Blueprint.LieModel X .PSU 4 2 x)

private theorem card_generic_prod_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
        CFSG.Blueprint.Multiplier.exceptional t n p f) =
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  have hcard : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    Nat.card_prod, hcard]

private theorem gcd_four_eq_one_of_odd {k : ℕ} (hk : Odd k) : Nat.gcd 4 k = 1 := by
  have h := (Nat.coprime_two_left.mpr hk).pow_left 2
  simpa using h


theorem isPerfect_and_card_griessHopfMultiplier_eq_one_omega {X : Type} [Group X] {m x : ℕ}
    (hx : 2 ≤ x) (hΩ : IsOmegaLieModel X m x) :
    commutator X = ⊤ ∧ Nat.card (griessHopfMultiplier X) = 1 := by
  have h2x : Even (2 ^ x) := (Nat.even_pow' (by omega)).2 even_two
  have h4 : 4 ≤ 2 ^ x := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
  rcases hΩ with h | h | ⟨rfl, h⟩
  · have hS := h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row hS
      (Or.inl (by omega))
    refine ⟨hX, ?_⟩
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus m 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.genericOrders
      simp [h2x]
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus m 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [Nat.card_congr e.toEquiv, card_generic_prod_exceptional, hg, hex]
    norm_num
  · have hS := h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    obtain ⟨hX, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row hS
    refine ⟨hX, ?_⟩
    have hm : 1 ≤ m := by have := h.admissible.2.2; omega
    have hodd : Odd ((2 ^ x) ^ m + 1) :=
      Even.add_one ((Nat.even_pow' (by omega)).2 h2x)
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus m 2 x = (1, 1) := by
      have : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus m 2 x =
          (Nat.gcd 4 ((2 ^ x) ^ m + 1), 1) := rfl
      rw [this, gcd_four_eq_one_of_odd hodd]
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus m 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [Nat.card_congr e.toEquiv, card_generic_prod_exceptional, hg, hex]
    norm_num
  · have hS := h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hS
      (by decide) (Or.inl h4)
    refine ⟨hX, ?_⟩
    have hodd : Odd (2 ^ x + 1) := h2x.add_one
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 x = (1, 1) := by
      have : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 x =
          (Nat.gcd 4 (2 ^ x + 1), 1) := rfl
      rw [this, gcd_four_eq_one_of_odd hodd]
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [Nat.card_congr e.toEquiv, card_generic_prod_exceptional, hg, hex]
    norm_num

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.center_Xbar_eq_bot_of_omega (hc : Ctx M Q Z B) {m x : ℕ} (hx : 2 ≤ x)
    (hΩ : IsOmegaLieModel (XbarMod M Q Z B) m x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  obtain ⟨hperf, hcard⟩ := isPerfect_and_card_griessHopfMultiplier_eq_one_omega hx hΩ
  have hcomm := hc.commutator_Xbar_eq_top_of_isPerfect_xbarMod (Group.isPerfect_def.2 hperf)
  have : Group.IsPerfect ↥(Xbar M Q Z B) := Group.isPerfect_def.2 hcomm
  have hker : (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))).ker =
      Subgroup.center ↥(Xbar M Q Z B) := QuotientGroup.ker_mk' _
  have h1 := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))) (QuotientGroup.mk'_surjective _)
    hker.le
  rw [hker, ← Nat.card_congr
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (XbarMod M Q Z B)).toEquiv,
    hcard] at h1
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)

theorem Ctx.exists_mulEquiv_isOrthA2_of_model (hc : Ctx M Q Z B)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) {K : Type} [Field K] [Finite K] [CharP K 2]
    {N : Type} [AddCommGroup N] [Module K N] [FiniteDimensional K N] {QN : QuadraticForm K N}
    (hQ : (polarBilin QN).Nondegenerate) {m : ℕ} (hdim : finrank K N = 2 * m) (hm3 : 3 ≤ m)
    (e : XbarMod M Q Z B ≃* ↥(elementaryGroup QN)) :
    ∃ ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN),
      ∀ t : ↥(Xbar M Q Z B), (t : Mbar M Q) ∈ Ebar M Q Z B →
        IsOrthA2 QN ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K] N) := by
  obtain ⟨hquot, hquot_mk⟩ : ∃ f : XbarMod M Q Z B ≃* Xbar M Q Z B,
      ∀ s : ↥(Xbar M Q Z B), f (QuotientGroup.mk s) = s :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot, fun s => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN),
      ∀ s : ↥(Xbar M Q Z B), ψ s = e (QuotientGroup.mk s) :=
    ⟨hquot.symm.trans e, fun s => by
      rw [MulEquiv.trans_apply, hquot.symm_apply_eq.2 (hquot_mk s).symm]⟩
  refine ⟨ψ, fun t ht => ?_⟩
  refine isOrthA2_of_forall_orderOf_mul_conj hQ hdim hm3 (ψ t).2 ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact Ctx.orderOf_eq_two_of_mem_Ebar ht
  · intro g hg
    set s : ↥(Xbar M Q Z B) := ψ.symm ⟨g, hg⟩ with hs
    have hgs : (ψ s : ↥(elementaryGroup QN)) = ⟨g, hg⟩ := ψ.apply_symm_apply _
    have h1 : ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K] N) *
        (g * ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K] N) * g⁻¹) =
        ((ψ (t * (s * t * s⁻¹)) : ↥(elementaryGroup QN)) : N ≃ₗ[K] N) := by
      rw [map_mul, map_mul, map_mul, map_inv, hgs]
      rfl
    have hmk : (QuotientGroup.mk (t * (s * t * s⁻¹)) : XbarMod M Q Z B) =
        (t : XbarMod M Q Z B) * ((s : XbarMod M Q Z B) * t * (s : XbarMod M Q Z B)⁻¹) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, Subgroup.orderOf_coe, hψ, MulEquiv.orderOf_eq, hmk]
    exact hc.orderOf_mul_conj_mk_of_mem_Ebar ht (QuotientGroup.mk s)

theorem Ctx.exists_omega_model (hc : Ctx M Q Z B) {m x : ℕ} (hx : 2 ≤ x)
    (hΩ : IsOmegaLieModel (XbarMod M Q Z B) m x) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2) (N : Type)
      (_ : AddCommGroup N) (_ : Module K' N) (_ : FiniteDimensional K' N)
      (QN : QuadraticForm K' N), Nat.card K' = 2 ^ x ∧ (polarBilin QN).Nondegenerate ∧
        finrank K' N = 2 * m ∧ 3 ≤ m ∧
        ∃ ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN),
          ∀ t : ↥(Xbar M Q Z B), (t : Mbar M Q) ∈ Ebar M Q Z B →
            IsOrthA2 QN ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N) := by
  obtain ⟨K, _, _, _, N, _, _, _, QN, hK, hQ, hdim, hm3, ⟨e⟩⟩ :=
    exists_quadraticSpace_of_rootInvolutionModel hΩ
  obtain ⟨ψ, hψ⟩ :=
    hc.exists_mulEquiv_isOrthA2_of_model (hc.center_Xbar_eq_bot_of_omega hx hΩ) hQ hdim hm3 e
  exact ⟨K, inferInstance, inferInstance, inferInstance, N, inferInstance, inferInstance,
    inferInstance, QN, hK, hQ, hdim, hm3, ψ, hψ⟩

end CFSG.RankThree.GF2n.Stroth80
