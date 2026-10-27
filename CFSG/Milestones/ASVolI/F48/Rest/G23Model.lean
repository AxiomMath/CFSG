module

public import CFSG.Milestones.ASVolI.F48.Rest.G23ModelPrelude
public import Certificates.Certificate7761

public import CFSG.Milestones.ASVolI.F48.Rest.G23ModelBase

public import CFSG.Milestones.ASVolI.F48.Rest.G23Facts
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.Quasithin.H13.ModelsG2
public import Certificates.Certificate7760

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Matrix

section Iso

open scoped Pointwise in
open scoped Pointwise in
open scoped Pointwise in
theorem burnsideF48t_g23_ρ_injective : Function.Injective burnsideF48t_g23ρ := by
  haveI : Finite ↥burnsideF48t_g23R :=
    Nat.finite_of_card_ne_zero (by rw [burnsideF48t_g23_card_R]; norm_num)
  have hsurj : Function.Surjective burnsideF48t_g23ρ.rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hcard : Nat.card ↥burnsideF48t_g23R ≤ Nat.card ↥burnsideF48t_g23ρ.range := by
    rw [burnsideF48t_g23_ρ_range, burnsideF48t_g23_card_X, burnsideF48t_g23_card_R]
  have hbij := hsurj.bijective_of_nat_card_le hcard
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

@[expose] noncomputable def burnsideF48t_g23ρe : ↥burnsideF48t_g23R ≃* ↥burnsideF48t_g23X :=
  (MonoidHom.ofInjective burnsideF48t_g23_ρ_injective).trans
    (MulEquiv.subgroupCongr burnsideF48t_g23_ρ_range)

theorem burnsideF48t_g23_equiv_X {H : Type} [Group H] (h : ChF.IsGenLie H .G2 3 1) :
    Nonempty (↥burnsideF48t_g23X ≃* H) := by
  obtain ⟨-, -, K, fK, finK, hK, ⟨e⟩⟩ := h
  letI := fK
  haveI := finK
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let σ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e₁ : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  let e₂ : ↥(adjointGroup .G2 K) ≃* ↥burnsideF48t_g23R :=
    (Subgroup.equivMapOfInjective _ (glHom σ) (glHom_injective σ)).trans
      (MulEquiv.subgroupCongr (burnsideF48t_g23_map_adjointGroup σ))
  exact ⟨(burnsideF48t_g23ρe.symm.trans (e₂.symm.trans e₁.symm)).trans e.symm⟩

end Iso

end CFSG.ASVolI
