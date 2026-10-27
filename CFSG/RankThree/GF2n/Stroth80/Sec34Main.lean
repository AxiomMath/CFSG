module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc
public import CFSG.RankThree.GF2n.Stroth80.Sec34Fibre
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Sec34TailGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Spure_le_Q_of_orthLe (hT75 : TimmesfeldTransitivityTI) (hHKS : HKSStatement)
    (hSL2 : SL2ModuleDimStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) (hO : OrthLe M B) : hc.Spure ≤ Q := by
  by_contra hSQ
  have horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z := fun m hm hcomm => hc.conj_le_sup_Z_of_orthLe hO hm hcomm
  have hTI := hc.isTIMod_LB hw hn hno horth
  have hWC : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
      conjSubgroup m (LB M Q B) = LB M Q B := fun m hm hmN =>
    hc.weaklyClosed_of_3_1 hw hn hno hm hmN
  obtain ⟨hn3, hSL⟩ := stroth34_caseA_n3 hT75 hc hw hn hno hTI hWC hSQ
  subst hn3
  exact stroth34_caseA_false hHKS hSL2 hc hw hno hgen hSL horth

@[expose] def Stroth34CaseBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B → ¬ OrthLe M B → hc.Spure ≤ Q

theorem stroth34Statement_of_inputs (hT75 : TimmesfeldTransitivityTI) (hHKS : HKSStatement)
    (hSL2 : SL2ModuleDimStatement) (hB : Stroth34CaseBStatement) : Stroth34Statement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen
  rw [hc.conc34_iff_Spure_le_Q]
  by_cases hO : OrthLe M B
  · exact hc.Spure_le_Q_of_orthLe hT75 hHKS hSL2 hw hn hno hgen hO
  · exact hB G M Q Z B hc n hw hn hno hgen hO

end CFSG.RankThree.GF2n.Stroth80
