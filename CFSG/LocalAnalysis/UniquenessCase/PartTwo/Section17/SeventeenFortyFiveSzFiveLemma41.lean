module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineAxB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineBasic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_kerM_eq_bot_of_mem_uniqueSet (D : Data G) {U H : Subgroup G} {p : ℕ}
    (hU : U ∈ uniqueSet D.M) (hp : p.Prime) (hUcard : Nat.card U = p)
    (hUH : U ≤ H) (hHM : ¬ H ≤ D.M) :
    U ⊓ kerM D.M H = ⊥ := by
  have hstar : ∀ g : G, (∀ b ∈ U, g⁻¹ * b * g ∈ D.M) → g ∈ D.M := by
    intro g hg
    have hUg : U ≤ D.M.map (MulAut.conj g).toMonoidHom := by
      intro u hu
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * u * g, hg u hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hMmap : D.M.map (MulAut.conj g).toMonoidHom = D.M := hU.2 g hUg
    have hgN : g ∈ Subgroup.normalizer (D.M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
    rwa [maxTwoLocal_self_normalizing D.M D.maxLocal] at hgN
  exact inf_kerM_eq_bot hp hUcard hU.1 hUH hstar hHM

theorem conjSubgroup_inf_kerM_eq_bot (D : Data G) {A A₁ A₂ B H : Subgroup G}
    (hA₁U : A₁ ∈ uniqueSet D.M) (hA₂U : A₂ ∈ uniqueSet D.M)
    (hA₁card : Nat.card A₁ = 31) (hA₂card : Nat.card A₂ = 31)
    (hsup : A₁ ⊔ A₂ = A)
    (hAdvd : Nat.card A ∣ 31 ^ 2)
    (hBH : B ≤ H) (hBnormA : B ≤ Subgroup.normalizer (A : Set G))
    (hlines : ∀ D' : Subgroup G, D' ≤ A → Nat.card D' = 31 →
      B ≤ Subgroup.normalizer (D' : Set G) → D' = A₁ ∨ D' = A₂)
    (hAH : A ≤ H) (hHM : ¬ H ≤ D.M) :
    ∀ q ∈ H, conjSubgroup A q ⊓ kerM D.M H = ⊥ := by
  classical
  let Y : Subgroup G := kerM D.M H
  change ∀ q ∈ H, conjSubgroup A q ⊓ Y = ⊥
  have hYH : Y ≤ H := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left D.M H
  have hYn : H ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_kerM D.M H
  have hA₁A : A₁ ≤ A := hsup ▸ le_sup_left
  have hA₂A : A₂ ≤ A := hsup ▸ le_sup_right
  have hp31 : Nat.Prime 31 := by norm_num
  have hBnormY : B ≤ Subgroup.normalizer (Y : Set G) := hBH.trans hYn
  have hBnormZ : B ≤ Subgroup.normalizer ((A ⊓ Y : Subgroup G) : Set G) :=
    (le_inf hBnormA hBnormY).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := Y))
  have hcontra : ∀ U : Subgroup G, (U = A₁ ∨ U = A₂) → U ≤ Y → False := by
    intro U hUA hUY
    have hUinf : U ⊓ Y = ⊥ := by
      rcases hUA with rfl | rfl
      · exact inf_kerM_eq_bot_of_mem_uniqueSet D hA₁U hp31 hA₁card (hA₁A.trans hAH) hHM
      · exact inf_kerM_eq_bot_of_mem_uniqueSet D hA₂U hp31 hA₂card (hA₂A.trans hAH) hHM
    have hle : U ≤ U ⊓ Y := le_inf le_rfl hUY
    have hle' : U ≤ ⊥ := by simpa [hUinf] using hle
    have hUbot : U = ⊥ := le_bot_iff.mp hle'
    have hcard1 : Nat.card U = 1 := by rw [hUbot, Subgroup.card_bot]
    rcases hUA with rfl | rfl <;> omega
  have hYbot : A ⊓ Y = ⊥ := by
    have hZdvd : Nat.card (A ⊓ Y : Subgroup G) ∣ 31 ^ 2 :=
      (Subgroup.card_dvd_of_le (inf_le_left : A ⊓ Y ≤ A)).trans hAdvd
    obtain ⟨k, hk, hkZ⟩ := (Nat.dvd_prime_pow hp31).mp hZdvd
    have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk012 with rfl | rfl | rfl
    · norm_num at hkZ
      exact (Subgroup.card_eq_one).mp hkZ
    · norm_num at hkZ
      exfalso
      exact hcontra (A ⊓ Y) (hlines (A ⊓ Y) inf_le_left hkZ hBnormZ) inf_le_right
    · have hZeqA : (A ⊓ Y : Subgroup G) = A := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hkZ]
        exact Nat.le_of_dvd (by norm_num) hAdvd
      exfalso
      exact hcontra A₁ (Or.inl rfl)
        (hA₁A.trans (hZeqA ▸ (inf_le_right : A ⊓ Y ≤ Y)))
  intro q hq
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxY : x ∈ Y := hx.2
  have hqAx : q * x * q⁻¹ ∈ A :=
    (CFSG.Quasithin.mem_conjSubgroup_iff).mp hx.1
  have hqY : q * x * q⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hYn hq) x).mp hxY
  have hqAY : q * x * q⁻¹ ∈ A ⊓ Y := ⟨hqAx, hqY⟩
  rw [hYbot] at hqAY
  have hx1 : x = 1 := by
    have h1 : q * x * q⁻¹ = 1 := Subgroup.mem_bot.mp hqAY
    have := congrArg (fun z : G => q⁻¹ * z * q) h1
    simpa [mul_assoc] using this
  simpa [hx1]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
