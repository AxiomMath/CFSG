module

public import CFSG.Quasithin.AppendixH.H16.H165FourMain
public import CFSG.Quasithin.Background.RonanH163Main

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem main165_four {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(golayC ⊓ pairKer a b) ⧸
      (Subgroup.zpowers (G6.allOnes 24)).subgroupOf (golayC ⊓ pairKer a b)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ)
    (hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    (hΓ : Γ = M2ab a b) {z : P24} (hz : z ∈ Γ) (hz2 : orderOf z = 2)
    (hzc : ∃ S : Subgroup P24, IsSylowIn 2 S Γ ∧ ∀ s ∈ S, s * z = z * s) : Cen4 ρ z := by
  obtain ⟨c, -, -, -, -, -, hcΓ, φ, hφ, e, he⟩ :=
    exists_std_iso hab hO haO hbO hS hBS haB hbB hTO hTS hL hSyl hΓ hreal
  exact h165_four_main ρ c hcΓ φ hφ e he hz hz2 hzc

end CFSG.ASVolI.H16
