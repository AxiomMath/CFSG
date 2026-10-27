module

public import CFSG.Quasithin.MS93.S33LamM
public import CFSG.Quasithin.MS93.S5ALift

public section

namespace CFSG.Quasithin.MS93.S59

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem omega5Act_of_mem_rad (g : ↥(StatedSp 2 F)) {y : Multiplicative (MSP.V4 F × F)}
    (hy : y ∈ omega5Rad F) : omega5Act F g y = y := by
  have hy1 : (Multiplicative.toAdd y).1 = 0 := hy
  apply Multiplicative.toAdd.injective
  rw [omega5Act, toAdd_ofAdd, hy1, Matrix.mulVec_zero]
  refine Prod.ext hy1.symm ?_
  simp [sp4Quad]

theorem exists_omega5_cover (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) :
    ∃ ψ : Multiplicative (MSP.V4 F × F) →* G, (∀ y, ψ y ∈ Uq M T L) ∧
      (∀ u ∈ Uq M T L, ∃ y, ψ y = u) ∧
      (∀ (m : ↥M) y, ψ (omega5Act F (a m) y) = (m : G) * ψ y * (m : G)⁻¹) ∧
      ∀ y, ψ y ∈ Subgroup.centralizer (L : Set G) ↔ y ∈ omega5Rad F := by
  have hlift := S5.sp4Lift G M T L h k F _ _ a hd
  obtain ⟨hk, hcard, ha, hnat⟩ := hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have := Sp4L.isMulCommutative_uq h
  have hAV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnat
  have hAβ := S33.isCoordAct_of_natSp hβα
  have hβker' : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L) := by
    rw [hβker, h.Uq_inf_Zq]
  obtain ⟨π, hπs, hπa⟩ := S33.exists_pi_of_ker hAV ha fun m hm =>
    S33.centralizer_of_eq_one h le_rfl hβ hβker' hAβ hm
  have hAY : M ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_centralizer h.le_normalizer)
  have hreal := S33.realizesVia_nat_of hAV ha hnat hAY hπs hπa
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) ≤
      fixV (autOn M (Uq M T L)) := by
    intro z hz x hx
    obtain ⟨g, hgA, rfl⟩ := Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply]
    have hzL : (z : G) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨z.2, Subgroup.mem_subgroupOf.1 hz⟩
    rw [hlift.2.1] at hzL
    rw [Subgroup.mem_centralizer_iff.1 hzL.2 g hgA, mul_inv_cancel_right]
  have hUA : ⁅Uq M T L, M⁆ = Uq M T L :=
    le_antisymm (commutator_le_left_of_le_normalizer hAV)
      (h.commutator_uq.symm.le.trans (Subgroup.commutator_mono le_rfl h.L_le))
  have hcomm := InternalSec.commV_autOn_eq_top hAV hUA
  have hW : ∀ w : ↥(Uq M T L), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using Sp4L.uq_sq h w.2)
  have hFn : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨ψ, hψs, hψe, hψZ⟩ := S33.exists_omega5_quotient hFn hk hW hZ hcomm hreal
  have hact : ∀ (m : ↥M) y, ψ (omega5Act F (a m) y) =
      (m : G) * (ψ y : G) * (m : G)⁻¹ := by
    intro m y
    rw [hψe, hπa]
    exact InternalSec.coe_conjAct_apply _ _
  refine ⟨(Uq M T L).subtype.comp ψ, fun y => (ψ y).2, fun u hu => ?_, fun m y => hact m y,
    fun y => ⟨fun hy => hψZ y (Subgroup.mem_subgroupOf.2 hy), fun hy => ?_⟩⟩
  · obtain ⟨y, hy⟩ := hψs ⟨u, hu⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlM : l ∈ M := h.L_le hl
    have key := hact ⟨l, hlM⟩ y
    rw [omega5Act_of_mem_rad _ hy] at key
    show l * (ψ y : G) = (ψ y : G) * l
    calc l * (ψ y : G) = (l * (ψ y : G) * l⁻¹) * l := by group
      _ = (ψ y : G) * l := by
        rw [show ((⟨l, hlM⟩ : ↥M) : G) = l from rfl] at key
        rw [← key]

end CFSG.Quasithin.MS93.S59
