module

public import CFSG.Quasithin.Background.SmithB45ExcDouble
public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeWrap
public import Certificates.Certificate260382
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement


theorem he_inv_check : (opsP 7 50).cubicCheck heInvData = true :=
  Certificates.certificate260382

theorem He_inv_witness :
    ∃ x y t : NativeSporadic.He,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.He)) = 7 ^ 3 ∧
      t * x * t⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      t * y * t⁻¹ = x ^ 6 * y ^ 6 * ⁅x, y⁆ ^ 3 ∧
      t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆ ^ 6 :=
  (specP 7 50).cubic_of_check heInvData he_inv_check

theorem he_dim42 (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (σ : NativeSporadic.Carrier .He →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 42 ≤ Nat.card V := by
  obtain ⟨x, y, t, hx, -, hz, hzx, hzy, -, htx, -, htz⟩ := He_inv_witness
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have htx' : t * x * t⁻¹ = x := by rw [htx]; simp
  have hf : Odd (orderOf (2 : ZMod 7)) := by rw [orderOf_two_zmod_7]; decide
  have h := two_pow_le_card_of_extraspecial_inv (S := NativeSporadic.Carrier .He) (p := 7)
    (by norm_num) hf hx hz hzx hzy htx' htz hV σ hσ
  rw [orderOf_two_zmod_7] at h
  exact h

theorem sporadicExclusion2F_He
 :
    SporadicExclusion2F .He := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel
  have : Nontrivial (NativeSporadic.Carrier .He) := he_nontrivial
  exact weight2_lt_of_three_conj hW hq.1 hirr hE hEne hEel e (r := 6) (k := 3) (ρ := 42)
    (by norm_num) (fun E _ _ _ π hπ hC hodd => he_cover E π hπ hC hodd) heTwoRankProp
    heThreeConjProp (fun V _ _ hV σ hσ => he_dim42 V hV σ hσ)

end CFSG.Quasithin.B45Exc
