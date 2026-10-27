module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LieType.Universal.Catalog
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag

theorem exists_unitTBModel_of_su_centralImage {G : Type} [Group G] {f n : ℕ} (hf : 1 ≤ f)
    (hn : 4 ≤ n) {K : Subgroup G}
    (ψ : ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) →* G)
    (hker : ψ.ker ≤ Subgroup.center
      ↥(Unitary.SU (BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n))
    (hr : ψ.range = K) :
    ∃ φ : ↥(unitarySU 2 f (GaloisField 2 (2 * f)) n) →* ↥K, UnitTB.Model φ := by
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  let e := Unitary.equivStatedSU hF n
  have hmem : ∀ g, ψ (e.symm g) ∈ K := fun g => by
    rw [← hr]
    exact ⟨_, rfl⟩
  refine ⟨(ψ.comp e.symm.toMonoidHom).codRestrict K hmem,
    TableBU.unitaryFieldData_of_card hF hf, fun k => ?_, fun g hg => ?_⟩
  · obtain ⟨s, hs⟩ : (k : G) ∈ ψ.range := by
      rw [hr]
      exact k.2
    exact ⟨e s, Subtype.ext (by simpa using hs)⟩
  · have h1 : ψ (e.symm g) = 1 := congrArg Subtype.val hg
    have h2 := hker h1
    have h3 : g ∈ Subgroup.center ↥(unitarySU 2 f (GaloisField 2 (2 * f)) n) := by
      rw [Subgroup.mem_center_iff] at h2 ⊢
      intro h
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h2 (e.symm h)
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (center_statedSU_le_scalars hF hn h3)
    refine ⟨(c : GaloisField 2 (2 * f)), ?_⟩
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem GGSecFiveRouteCfg.pow_le_card_range_ggGamma_nbr {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hBB : B = Bs) {y : G} {K : Subgroup G}
    (hNy : GGNbr p B x D J y K) {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    p ^ (n - 1) ≤ Nat.card (ggGamma K hN).range := by
  have hp : p.Prime := (hR.1.1.tableB_facts).1
  have : Fact p.Prime := ⟨hp⟩
  have hcardBs : Nat.card ↥Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hN
  have hCK := hR.card_inf_centralizer_nbr_le hBB hNy
  rw [hcardBs] at hmul
  have hpos : 0 < Nat.card (ggGamma K hN).range := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, zero_mul] at hmul
    exact (pow_pos hp.pos n).ne hmul
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_sub, pow_zero]
    exact hpos
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have h1 : p ^ k * p ≤ Nat.card (ggGamma K hN).range * p := by
      rw [← pow_succ, ← hmul]
      exact Nat.mul_le_mul_left _ hCK
    exact Nat.le_of_mul_le_mul_right h1 hp.pos

end CFSG.StandardType

end
