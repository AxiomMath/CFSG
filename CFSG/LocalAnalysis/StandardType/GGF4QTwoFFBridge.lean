module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.Adapters.TauCetiExceptional.BridgeTransport
import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

theorem nonempty_mulEquiv_ggU_E6_one_of_label
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ x y : G, x * y ≠ y * x)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ (G ⧸ Subgroup.center G)) :
    Nonempty (G ≃* (ggU .E6 0 1).K) := by
  classical
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · obtain ⟨x, y, hxy⟩ := hna
      have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
      exact absurd (Subgroup.mem_center_iff.mp hx y).symm hxy
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hlab
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨ψ⟩ := centerQuot_chevGroup_equiv K .E6
  have hcenK : Subgroup.center (adjointGroup .E6 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcardF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK2, hcardF]
  let σ : K ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  have hcen1 : Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 1)) = ⊥ := by
    have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (GaloisField 2 1)).1
    rw [hcardF] at h
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h)
  have hinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcen1]
    exact CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
      (GaloisField 2 1)
  let ι : ↥(e6Data_valid.minGroup (GaloisField 2 1)) ≃* ↥(adjointGroup .E6 (GaloisField 2 1)) :=
    MulEquiv.ofBijective _
      ⟨hinj, CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective (GaloisField 2 1)⟩
  let p₀ : G ≃* G ⧸ Subgroup.center G :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let q₀ : CFSG.Blueprint.AdjointQuotient .E6 K ≃* ↥(adjointGroup .E6 K) :=
    (QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot
  exact ⟨((((p₀.trans φ).trans ψ).trans q₀).trans
    (CFSG.TauCetiBridge.adjointGroupCongr (τ := .E6) σ)).trans ι.symm⟩

end CFSG.StandardType

end
