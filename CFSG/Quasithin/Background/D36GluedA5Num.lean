module

public import CFSG.Quasithin.Background.F918Z4bL2
public import CFSG.Quasithin.Background.F918Z4c1PSL
public import CFSG.Quasithin.Background.D36GluedNDBase

public section

namespace CFSG.Quasithin

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem numerics (hL : IsPSL 2 2 2 ↥L₀) :
    rk ↥(A ⊓ stabSub U) = 2 ∧ 4 ≤ rk ↥U - rk ↥(U ⊓ U') ∧ rk ↥U - rk ↥(U ⊓ U') ≤ 5 ∧
      1 ≤ rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ∧
      rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ 2 ∧
      (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) + (rk ↥U - rk ↥(U ⊓ U')) ≤ 6 := by
  have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  obtain ⟨ρ, hρ⟩ := S.exists_gl
  have h4 := two_mul_le_of_psl2_two (by norm_num) (by norm_num) hL hF2 ρ hρ
  have hk := S.rk_le (autRankLe_psl2_two (by norm_num) hL)
  obtain ⟨hs1, -, hB⟩ := S.swap.shape_B S.exp
  refine ⟨by omega, by omega, by omega, hs1, by omega, by omega⟩

theorem not_le_fixV : ¬ U ≤ fixV L₀ := by
  intro h
  obtain ⟨a, b, hab⟩ := S.nonab
  apply hab
  have h1 : ∀ l : ↥L₀, (l : MulAut Y) = 1 := by
    intro l
    refine mulAut_eq_of_eqOn_sup S.swap.pair.sup_eq (fun u hu => ?_) (fun u hu => ?_)
    · exact h hu l l.2
    · exact S.cent l l.2 u hu
  have ha : a = 1 := Subtype.ext (h1 a)
  have hb : b = 1 := Subtype.ext (h1 b)
  rw [ha, hb]

end NDSetup

end CFSG.Quasithin
