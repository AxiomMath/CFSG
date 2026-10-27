module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineSolv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineAxB
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_kerM_of_minimal (D : Data G) (h107 : UC2_10_7w G) {s p : ℕ}
    {B : Subgroup G} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hB : B ≤ D.M ⊓ normalizer (D.T : Set G)) (hBp : Nat.card B = p) (hU : UC6.InU D.M B)
    {N D₀ H : Subgroup G} (hN : N ∈ calMOf (B ⊔ D.T)) (hD₀ : B ⊔ D.T ≤ D₀)
    (hD₀M : D₀ ≤ D.M) (hD₀H : D₀ ≤ H) (hHN : H ≤ N) (hHM : ¬ H ≤ D.M)
    (hmin : ∀ H' : Subgroup G, D₀ ≤ H' → H' ≤ H → ¬ H' ≤ D.M → H' = H) :
    ⁅D.T, B⁆ ≤ kerM D.M H := by
  have hBM : B ≤ D.M := hB.trans inf_le_left
  have hBT : B ≤ normalizer (D.T : Set G) := hB.trans inf_le_right
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hstar := hstar_of_inU D hU
  have hp7 : 7 ≤ p := PartTwo.s13_seven_le_of_dvd hs hp hdvd
  have hp2 : p ≠ 2 := by omega
  have hd := CFSG.not_exists_orderOf_two_eq_two_pow_of_odd hs hp hdvd
  have hTH : D.T ≤ H := le_sup_right.trans (hD₀.trans hD₀H)
  have hBH : B ≤ H := le_sup_left.trans (hD₀.trans hD₀H)
  have hHtop : H ≠ ⊤ := by
    have := D.standing.simple
    intro h
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1
      (top_le_iff.1 (h ▸ hHN))
  have hYH : kerM D.M H ≤ H := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left D.M H
  have hYM : kerM D.M H ≤ D.M := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right D.M H
  have hYn : H ≤ normalizer (kerM D.M H : Set G) := le_normalizer_kerM D.M H
  have hYlt : kerM D.M H < H := lt_of_le_of_ne hYH fun h => hHM (h ▸ hYM)
  obtain ⟨X, hYX, hXH, hXn, hXmin⟩ := exists_minimal_normal_above hYlt
  have hXM : ¬ X ≤ D.M := fun h => (not_le_of_gt hYX) (le_kerM_of_normal hXH hXn h)
  have hHMX : H ≤ (H ⊓ D.M) ⊔ X := by
    have hD₀X : D₀ ⊔ X = H :=
      hmin _ le_sup_left (sup_le hD₀H hXH) fun h => hXM (le_sup_right.trans h)
    calc H = D₀ ⊔ X := hD₀X.symm
      _ ≤ (H ⊓ D.M) ⊔ X := sup_le_sup_right (le_inf hD₀H hD₀M) X
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hTH le_top
  have hkey : ∀ c ∈ ⁅D.T, B⁆, ∀ x ∈ X, ⁅x, c⁆ ∈ kerM D.M H := by
    by_cases hab : ⁅X, X⁆ ≤ kerM D.M H
    · obtain ⟨ℓ, hℓ, hchief⟩ := exists_isChiefFactorUnder_of_minimal hYX hXH hYn hXn hXmin hab
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hXMY : X ⊓ D.M ≤ kerM D.M H := by
        have hXn' : X ≤ normalizer ((X ⊓ D.M : Subgroup G) : Set G) := by
          intro x hx
          rw [mem_normalizer_iff]
          intro w
          constructor
          · intro hw
            have hw' := Subgroup.mem_inf.1 hw
            have hc : ⁅x, w⁆ ∈ kerM D.M H := hab (commutator_mem_commutator hx hw'.1)
            have e : x * w * x⁻¹ = ⁅x, w⁆ * w := by rw [commutatorElement_def]; group
            rw [e]
            exact Subgroup.mem_inf.2 ⟨X.mul_mem (hYX.le hc) hw'.1, D.M.mul_mem (hYM hc) hw'.2⟩
          · intro hw
            have hw' := Subgroup.mem_inf.1 hw
            have hc : ⁅x⁻¹, x * w * x⁻¹⁆ ∈ kerM D.M H :=
              hab (commutator_mem_commutator (X.inv_mem hx) hw'.1)
            have e : w = ⁅x⁻¹, x * w * x⁻¹⁆ * (x * w * x⁻¹) := by
              rw [commutatorElement_def]; group
            rw [e]
            exact Subgroup.mem_inf.2 ⟨X.mul_mem (hYX.le hc) hw'.1, D.M.mul_mem (hYM hc) hw'.2⟩
        have hHn : H ≤ normalizer ((X ⊓ D.M : Subgroup G) : Set G) := by
          refine hHMX.trans (sup_le ?_ hXn')
          exact (le_inf (inf_le_left.trans hXn) (inf_le_right.trans le_normalizer)).trans
            inf_normalizer_le_normalizer_inf
        rcases hXmin _ (le_inf hYX.le hYM) inf_le_left hHn with h | h
        · exact h.le
        · exact absurd (inf_eq_left.1 h) hXM
      have hfix : ∀ x ∈ X, (∀ b ∈ B, ⁅x, b⁆ ∈ kerM D.M H) → x ∈ kerM D.M H := by
        intro x hx hxb
        refine hXMY ⟨hx, ?_⟩
        have hxinv : x⁻¹ ∈ D.M := hstar x⁻¹ fun b hb => by
          have e : x⁻¹⁻¹ * b * x⁻¹ = ⁅x, b⁆ * b := by rw [commutatorElement_def]; group
          rw [e]
          exact D.M.mul_mem (hYM (hxb b hb)) (hBM hb)
        simpa using D.M.inv_mem hxinv
      have hℓ2 : ℓ ≠ 2 := by
        rintro rfl
        have hS := hTsyl.inf_of_le_normalizer hXH hXn
        have h1 := le_sup_of_isSylowOf_of_pow_mem hYX.le (hXH.trans hYn) hS
          hchief.2.2.2.2.2.1
        exact hXM (h1.trans (sup_le (inf_le_left.trans hTM) hYM))
      exact commutator_mem_of_isChiefFactorUnder hp hp2 hℓ2 hd hchief D.sylowM.isPGroup hTH hBH
        hBT hBp hfix
    · exact h107 D.standing.kProper s p H D.M D.T B X (kerM D.M H) hs hp hdvd hHtop hTsyl hBH
        hBT hBp hTM hBM hYM (fun K hKH hKn hKM => le_kerM_of_normal hKH hKn hKM)
        (fun g _ => hstar g) hYX.le hXH hYn hXn hXM hHMX hXmin hab
  have hTBT : ⁅D.T, B⁆ ≤ D.T := Subgroup.le_normalizer_iff_commutator_le_left.1 hBT
  intro c hc
  exact mem_kerM_of_forall_commutator_mem hXn hHMX (hTH (hTBT hc)) (hTM (hTBT hc))
    (hkey c hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo UCTenNine
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem uc2_10_9_of_inputs (D : Data G) (h640 : UC6.R6_40_2 D) (h107 : UC2_10_7w G) :
    UC2_10_9 D := by
  intro s p B hs hp hdvd hB hBp hU
  have hBM : B ≤ D.M := hB.trans inf_le_left
  have hBT : B ≤ normalizer (D.T : Set G) := hB.trans inf_le_right
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hp7 : 7 ≤ p := PartTwo.s13_seven_le_of_dvd hs hp hdvd
  have hp2 : p ≠ 2 := by omega
  have hstar := hstar_of_inU D hU
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBp
    omega
  have h1 := exists_calMOf_ne_of_r6_40_2 D h640 hBT
  have hNM : ∀ N, N ∈ calMOf (B ⊔ D.T) → N ≠ D.M → ¬ N ≤ D.M := fun N hN hne hle =>
    hne (hN.1.2 D.M D.maxLocal.1 hle).symm
  have h2 : ∀ N : Subgroup G, N ∈ calMOf (B ⊔ D.T) → N ≠ D.M →
      ¬ UC22.F05.InvertedIn (D.M ⊓ N) B := by
    rintro N hN hne ⟨g, hg, hginv⟩
    obtain ⟨m, a, -, hgB⟩ :=
      RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne.exists_two_element_inverting hginv
    have hgm : g ^ m ∈ D.M ⊓ N := pow_mem hg m
    have hD₀ : B ⊔ D.T ⊔ zpowers (g ^ m) ≤ D.M ⊓ N :=
      sup_le (sup_le (le_inf hBM (le_sup_left.trans hN.2))
        (le_inf hTM (le_sup_right.trans hN.2))) ((zpowers_le (G := G)).2 hgm)
    obtain ⟨H, hD₀H, hHN, hHM, hmin⟩ :=
      exists_minimal_between (hD₀.trans inf_le_right) (hNM N hN hne)
    have hcore := commutator_le_kerM_of_minimal D h107 hs hp hdvd hB hBp hU hN le_sup_left
      (hD₀.trans inf_le_left) hD₀H hHN hHM hmin
    have hBH : B ≤ H := le_sup_left.trans (le_sup_left.trans hD₀H)
    have hTH : D.T ≤ H := le_sup_right.trans (le_sup_left.trans hD₀H)
    have hBY := inf_kerM_eq_bot hp hBp hBM hBH hstar hHM
    exact not_invertedIn_of_commutator_le hp hp2 (D.sylowG.of_le hTH le_top) hBH hBp
      (le_normalizer_kerM D.M H) hBY hcore
      ⟨g ^ m, hD₀H (Subgroup.mem_sup_right (mem_zpowers _)), hgB⟩
  have h3 : B ≤ centralizer (D.Z : Set G) → ¬ centralizer (D.Z : Set G) ≤ D.M := by
    intro hBZ hCM
    obtain ⟨N, hN, hne⟩ := h1
    obtain ⟨H, hD₀H, hHN, hHM, hmin⟩ := exists_minimal_between hN.2 (hNM N hN hne)
    have hcore := commutator_le_kerM_of_minimal D h107 hs hp hdvd hB hBp hU hN le_rfl
      (sup_le hBM hTM) hD₀H hHN hHM hmin
    have hBH : B ≤ H := le_sup_left.trans hD₀H
    have hTH : D.T ≤ H := le_sup_right.trans hD₀H
    have hYH := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left D.M H
    have hYM := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right D.M H
    have hYn := le_normalizer_kerM D.M H
    have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hTH le_top
    have hTY := hTsyl.inf_of_le_normalizer hYH hYn
    have hfr := UC6.frattini_of_isSylowOf hYH hYn hTY
    have hNHM : ¬ H ⊓ normalizer ((D.T ⊓ kerM D.M H : Subgroup G) : Set G) ≤ D.M := by
      intro h
      apply hHM
      rw [hfr]
      exact sup_le hYM h
    have hD₀N : B ⊔ D.T ≤ H ⊓ normalizer ((D.T ⊓ kerM D.M H : Subgroup G) : Set G) := by
      refine le_inf hD₀H ((sup_le (le_inf hBT (hBH.trans hYn))
        (le_inf le_normalizer (hTH.trans hYn))).trans inf_normalizer_le_normalizer_inf)
    have hHeq := hmin _ hD₀N inf_le_left hNHM
    have hWH : H ≤ normalizer ((D.T ⊓ kerM D.M H : Subgroup G) : Set G) :=
      hHeq.ge.trans inf_le_right
    have hTBW : ⁅D.T, B⁆ ≤ D.T ⊓ kerM D.M H :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hBT) hcore
    have hTN : CFSG.ABGLocalTools.IsSylowOf 2 D.T N := D.sylowG.of_le (hTH.trans hHN) le_top
    have hBV := le_centralizer_conjClosure_of_commutator_le hp hp2
      (D.standing.charTwo N hN.1.1) hTN hHN hTH hBH hBp inf_le_left hWH hTBW hBZ
    have hZV : D.Z ≤ UC22.conjClosure H D.Z :=
      uc22s217u3a_le_conjClosure ⟨1, one_mem H, by ext; simp⟩
    have hCV : H ⊓ centralizer (UC22.conjClosure H D.Z : Set G) ≤ kerM D.M H := by
      refine le_kerM_of_normal inf_le_left ?_
        ((inf_le_right.trans (centralizer_le hZV)).trans hCM)
      exact (le_inf le_normalizer fun h hh => UC22.P22so.mem_normalizer_centralizer_of
        (uc22p22v_le_normalizer_conjClosure H D.Z hh)).trans inf_normalizer_le_normalizer_inf
    have hBY : B ≤ kerM D.M H := (le_inf hBH hBV).trans hCV
    exact hB1 (by
      rw [← inf_kerM_eq_bot hp hBp hBM hBH hstar hHM]
      exact (inf_eq_left.2 hBY).symm)
  have h4 : UniqueMax D.M (UC22.conjClosure D.M B ⊔ D.T) →
      ⁅D.Z, UC22.conjClosure D.M B⁆ ≠ ⊥ := by
    intro hUM hbot
    have hcl : UC22.conjClosure D.M B ≤ centralizer (D.Z : Set G) := by
      rw [commutator_comm] at hbot
      exact commutator_eq_bot_iff_le_centralizer.1 hbot
    have hBcl : B ≤ UC22.conjClosure D.M B :=
      uc22s217u3a_le_conjClosure ⟨1, one_mem D.M, by ext; simp⟩
    apply h3 (hBcl.trans hcl)
    have hloc : CFSG.Open.IsTwoLocal (normalizer (D.Z : Set G)) :=
      ⟨D.Z, uc22main1_Z_ne_bot D, D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D), rfl⟩
    exact (centralizer_le_normalizer _).trans (uc22p22p_le_of_uniqueMax hUM hloc
      (sup_le (hcl.trans (centralizer_le_normalizer _))
        ((uc22main1_T_le_centralizer D).trans (centralizer_le_normalizer _))))
  exact ⟨h1, h2, h3, h4⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
