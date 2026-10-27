module

public import CFSG.Quasithin.Vol2.Ch11SecAKDg
public import CFSG.Quasithin.Vol2.Ch11SecAKDi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

namespace C10KH


theorem cover_g2 {W : Type} [CommGroup W] {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {H : Subgroup (MulAut W)}
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H ⊤ ⊥) :
    ∃ τ : MulAut ↥H, ∀ θ, θ ∈ indH H ∨ θ * τ⁻¹ ∈ indH H := by
  have : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
  obtain ⟨π, e, he⟩ := exists_model_action
    (FFModel.zornQ_isActionModel ⁅quasithinG2 K, quasithinG2 K⁆ (g2D_le K))
    (FFC.zornQ_faithful _ (g2D_le K)) hR
  refine cover_of_model (g2QA K) π e he ⟨1, fun θ => Or.inl ?_⟩
  rw [indM_g2_eq_top hn hK]
  exact Subgroup.mem_top θ

end C10KH

theorem factTwist_holds : FactTwist := by
  intro X W _ _ _ _ ρ n hn hreal α₁ α₂ h₁ h₂ hn₁ hn₂
  refine C10KH.twist_of_cover ρ ?_ α₁ α₂ h₁ h₂ hn₁ hn₂
  obtain ⟨K, _, _, hK, hR | hR | hR⟩ := hreal
  · obtain ⟨π, e, he⟩ := C10KH.exists_model_nat hR
    exact C10KH.cover_of_model _ π e he C10KH.cover_sl3
  · have : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
    obtain ⟨π, e, he⟩ := C10KH.exists_model_nat hR
    exact C10KH.cover_of_model _ π e he C10KH.cover_sp4
  · exact C10KH.cover_g2 hn hK hR

end CFSG.Quasithin.Vol2.Ch11.SecA
