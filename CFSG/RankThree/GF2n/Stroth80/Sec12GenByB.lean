module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Mixed
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.false_of_not_genByB (hT75 : TimmesfeldTransitivityTI) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hng : ¬ GenByB M Q B) :
    False := by
  obtain ⟨hO, hSQ⟩ := hc.orthLe_and_not_Spure_le_Q_of_not_genByB hw hn hno hng
  have horth : ∀ m ∈ M, (∀ x ∈ conjSubgroup m B, ∀ y ∈ B, x * y = y * x) →
      conjSubgroup m B ≤ B ⊔ Z := fun m hm hcomm => hc.conj_le_sup_Z_of_orthLe hO hm hcomm
  have hTI := hc.isTIMod_LB hw hn hno horth
  have hWC : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
      conjSubgroup m (LB M Q B) = LB M Q B := fun m hm hmN =>
    hc.weaklyClosed_of_3_1 hw hn hno hm hmN
  obtain ⟨hn3, hSL⟩ := stroth34_caseA_n3 hT75 hc hw hn hno hTI hWC hSQ
  subst hn3
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have hS : Nat.card hc.Spure = Nat.card Q * Nat.card Z ^ 2 := by
    rw [hSL]
    exact (hc.card_of_3_3 hw (by omega) hno (stroth_3_3 hc hw (by omega))).1
  obtain ⟨X, hX, x, hxX, hxW⟩ := hc.exists_mixed_root h hng
  exact hc.false_of_mixed h hno hng hw hS hb0 hbs hB hcent hX hxX hxW

theorem strothGenByB_of_T75 (hT75 : TimmesfeldTransitivityTI) : StrothGenByBStatement := by
  intro G _ _ M Q Z B hc n hw hn hno
  by_contra hng
  exact hc.false_of_not_genByB hT75 hw hn hno hng

end CFSG.RankThree.GF2n.Stroth80
