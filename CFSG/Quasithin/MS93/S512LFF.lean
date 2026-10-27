module

public import CFSG.Quasithin.MS93.S512NFF

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

namespace S512L

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_coord_ff (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k)
    {S₀ : Type} [CommGroup S₀] [Finite S₀] {ρ : ↥M →* MulAut S₀} (hρ : S38E.IsIrrRep L ρ)
    (hFF : IsFFModule ρ.range) (hL : ρ.range ≤ S38E.IsIrrRep.imL L ρ) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F') (φ : ↥ρ.range →* MSP.Sp4 F')
      (θ : S₀ ≃* Multiplicative (MSP.V4 F')), Fintype.card F' = 2 ^ k ∧ Function.Surjective φ ∧
      ∀ (x : ↥ρ.range) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
        MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s) := by
  have hS2 := hρ.sq
  have hH := hρ.ffHyp h hSQ hFF
  obtain ⟨-, -, hcases, -⟩ := h14 S₀ hS2 _ _ hH
  have hBC : Nat.card (S32.Lstar L) = ordBC 2 (2 ^ k) := by
    rcases S512N.card_lstar_of_data h hd with ⟨hk1, -⟩ | ⟨-, hBC⟩
    · omega
    · exact hBC
  rcases hcases with hSL | hhat | hsp | hG2
  ·
    exfalso
    obtain ⟨n, hn, hc⟩ := S38E.card_lstar_of_ffCaseSL3 hρ h hSL
    exact S36E.ordA_two_ne_ordBC_two hk2 (hc.symm.trans hBC)
  ·
    exfalso
    have hc := S38E.card_lstar_of_ffCaseHatA6 hρ h hhat
    exact (S32.ordBC_two_ne (by omega)).2.1 (hBC.symm.trans hc)
  · rcases hsp with ⟨n, hn2, F', iF, fF, hcard, π, hπ⟩ | ⟨π, hπ⟩
    ·
      have hc := S38E.card_lstar_of_sp4Nat hρ h hn2 ⟨F', iF, fF, hcard, π, hπ⟩
      have hnk : n = k := S36E.eq_of_ordBC_two_eq (by omega) (by omega) (hc.symm.trans hBC)
      subst hnk
      have : Fintype F' := Fintype.ofFinite F'
      obtain ⟨φK, θ, hθ⟩ := S36E.coord_of_natSp4 hπ
      have hXK : ρ.range = S38E.IsIrrRep.imL L ρ := le_antisymm hL S38E.IsIrrRep.imL_le
      set e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
      have hφKi : Function.Injective φK := S512N.injective_of_coord hθ
      have hφKs : Function.Surjective φK := by
        have : Finite ↥(StatedSp 2 F') := Finite.of_equiv _ e.symm.toEquiv
        exact (Finite.injective_iff_surjective_of_equiv e.symm.toEquiv).1 hφKi
      refine ⟨F', iF, this, φK.comp (Subgroup.inclusion hXK.le), θ, ?_, ?_, fun x s => ?_⟩
      · rw [Fintype.card_eq_nat_card, hcard]
      · intro g
        obtain ⟨y, rfl⟩ := hφKs g
        exact ⟨Subgroup.inclusion hXK.ge y, rfl⟩
      · exact hθ (Subgroup.inclusion hXK.le x) s
    ·
      exfalso
      have hc := S38E.card_lstar_of_altNat hρ h ⟨π, hπ⟩
      exact (S32.ordBC_two_ne (by omega)).2.1 (hBC.symm.trans hc)
  ·
    exfalso
    rcases S38E.card_lstar_of_ffCaseG2 hρ h hT hG2 with ⟨n, hn2, hc⟩ | hc
    · exact S36E.ordG2_ne_ordBC_two (by omega) (by omega) (hc.symm.trans hBC)
    · exact (S32.ordBC_two_ne (by omega)).2.2 (hBC.symm.trans hc)

end S512L

end CFSG.Quasithin.MS93
