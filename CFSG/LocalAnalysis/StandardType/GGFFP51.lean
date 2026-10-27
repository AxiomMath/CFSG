module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
import CFSG.LocalAnalysis.StandardType.GGFFTen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.StandardType.GGFF.Setting

open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.RankThree.PartTwo.Sec21.FF81.P51T
  CFSG.RankThree.PartTwo.Sec21.FF81.P51 in
theorem autOrder_cases (h : Setting b K z) :
    autOrder (Bt b z) = 384 ∨ autOrder (Bt b z) = 1152 ∨ autOrder (Bt b z) = 1440 := by
  have hH0 := h.hasH0
  have : CFSG.IsElementaryAbelian 3 (Bt b z) := hH0.1.1
  obtain ⟨β, hβ⟩ := exists_basis (B := Bt b z) hH0.1.2 hH0.2.1
  have hyp := P51T.hyp_of hH0 h.stab h.meetB β hβ
  have h5 := ne_mC_mE hyp (h.fiveInv β hβ)
  set Γ := (ρU β).range with hΓdef
  have hcard := card_eq hyp
  have haut : autOrder (Bt b z) = Nat.card Γ := autOrder_eq β
  have hOm : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      Om Γ = ↑((nonzeroL.filter fun v => m (tab v).1).toFinset) := by
    intro m hm
    ext v
    rw [om_iff hyp, hm]
    simp
  have hautm : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) →
      (cfgOf Γ).1 = m → autOrder (Bt b z) = 96 * lineCount m := by
    intro m hm hcm
    rw [haut, hcard, hOm m hcm, Set.ncard_coe_finset, vecCount m hm]
    ring
  rcases cfgOf_good hyp with hA | ⟨hB, -⟩ | ⟨hC, -⟩ | hD | hE
  · exact Or.inl (by rw [hautm mA (Or.inl rfl) hA, lineCount_mA])
  · exact Or.inr (Or.inl (by rw [hautm mB (by simp) hB, lineCount_mB]))
  · exact absurd hC h5.1
  · exact Or.inr (Or.inr (by rw [hautm mD (by simp) hD, lineCount_mD]))
  · exact absurd hE h5.2

end CFSG.StandardType.GGFF.Setting

end
