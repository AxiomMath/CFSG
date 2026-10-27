module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylAdjSylow

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

section Main


theorem sylowAutBoundAll_derivedCentralQuotient {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type} [Field K] [Finite K] (hK : ¬ 11 ∣ Nat.card K)
    {H : Subgroup (ModGL τ K)} (hH : H ≤ adjointGroup τ K) :
    SylowAutBoundAll 11 24 (DerivedCentralQuotient H) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hYH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hY : ⁅H, H⁆ ≤ adjointGroup τ K := hYH.trans hH
  have h0 : SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (adjointGroup τ K) :=
    sylowAutBoundAll_adjointGroup hτ hK
  have h1 : SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) ↥⁅H, H⁆ :=
    SylowAutBoundAll.of_injective (Subgroup.inclusion hY) (Subgroup.inclusion_injective hY) h0
  have h2 : SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (DerivedCentralQuotient H) :=
    SylowAutBoundAll.of_surjective (QuotientGroup.mk' (Subgroup.center ↥⁅H, H⁆))
      (QuotientGroup.mk'_surjective _) h1
  exact h2.mono (by split_ifs <;> norm_num)

end Main

end CFSG.Quasithin.KGC31
