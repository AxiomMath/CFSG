module

public import CFSG.RankThree.GF2n.Stroth80.Sec118FieldEqNotTWire
import CFSG.RankThree.GF2n.Stroth80.Sec118FieldEq
import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Final

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem stroth118_of_cmSpStructure (hSp : CMSpStructure)
    (hI4 : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal],
      Ctx M Q Z B → ∀ n m x : ℕ, Width Q Z n → 2 < n →
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x →
      ∀ (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)),
        ¬ CMSpTransvAt M Q Z B m x a h →
        2 ^ x = Nat.card Z →
        m = 3 → Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 →
        (∀ W : Subgroup G, Z ≤ W → W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ →
          (∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) →
        (∃ y : ↥M, (QuotientGroup.mk y : Mbar M Q) ∈ Xbar M Q Z B ∧
          Odd (orderOf (QuotientGroup.mk y : Mbar M Q)) ∧
          ∀ v ∈ Z ⊔ ⁅Q, XbarPre M Q Z B⁆, ⁅(y : G), v⁆ ∈ Z → v ∈ Z) →
        False) :
    Stroth118Statement := by
  classical
  intro G _ _ M Q Z B _ hc n hw hn ha2 hSpc
  obtain ⟨m, x, hLie⟩ := hSpc
  obtain ⟨a, haL, haA⟩ := ha2
  have haM : a ∈ M := hc.LB_le_M haL
  have h : ((⟨a, haM⟩ : ↥M) : G) ∈ LB M Q B ∧ IsA2 Q Z ((⟨a, haM⟩ : ↥M) : G) := ⟨haL, haA⟩
  obtain ⟨hr, hcase⟩ := hSp G M Q Z B hc n m x hw hn ⟨a, haL, haA⟩ hLie
  by_cases hspt : CMSpTransvAt M Q Z B m x ⟨a, haM⟩ h
  · have hq : 2 ^ x = Nat.card Z :=
      le_antisymm hr (hc.card_Z_le_two_pow_of_transvAt hw hn hspt)
    obtain ⟨hT, -⟩ := hcase hq ⟨a, haM⟩ h
    obtain ⟨hcard, hmod⟩ := hT hspt
    obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
    obtain ⟨φ, hφπ, W₁, W₂, h12, hsup, hW₁, hW₂, hs₁, hs₂, b, ρ, hρr, hρk, hbas⟩ :=
      hmod K γ M₀ hD
    exact stroth118_RT1_refutation G M Q Z B hc n m x hw hn hLie hq ⟨a, haM⟩ h hspt hcard K γ M₀
      hD φ hφπ W₁ W₂ h12 hsup hW₁ hW₂ hs₁ hs₂ b ρ hρr hρk hbas
  · have hq : 2 ^ x = Nat.card Z :=
      le_antisymm hr (hc.card_Z_le_two_pow_of_not_cmSpTransvAt hw hn hLie hspt)
    obtain ⟨-, hN⟩ := hcase hq ⟨a, haM⟩ h
    obtain ⟨hm3, hcard, hM1, hM2⟩ := hN hspt
    exact hI4 G M Q Z B hc n m x hw hn hLie ⟨a, haM⟩ h hspt hq hm3 hcard hM1 hM2

end CFSG.RankThree.GF2n.Stroth80
