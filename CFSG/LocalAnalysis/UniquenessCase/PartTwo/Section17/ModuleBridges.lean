module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct
public import CFSG.Quasithin.Background.SmithB45J2Dim
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.QuasithinUnique.Setup

theorem X1_isIrrOn_of_isIrrOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : IsIrrOn L ⊤ ⊥) : X1.IsIrrOn L := by
  refine ⟨?_, ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    exact (ne_of_lt h.1) (Subgroup.ext (fun x => by simp [Subsingleton.elim x 1]))
  · intro U hU
    exact h.2.2.2 U hU bot_le le_top

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22


theorem ne_bot_of_isIrrOn_of_two_lt_card {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L ⊤ ⊥) (hcard : 2 < Nat.card W) : L ≠ ⊥ := by
  intro hbot
  have hn : Nat.card W = 2 ^ CFSG.Quasithin.rk (⊤ : Subgroup W) := by
    rw [← Subgroup.card_top (G := W)]
    exact CFSG.Quasithin.card_eq_two_pow hW (⊤ : Subgroup W)
  have h2dvd : 2 ∣ Nat.card W := by
    rw [hn]
    have hr0 : CFSG.Quasithin.rk (⊤ : Subgroup W) ≠ 0 := by
      intro h0
      rw [hn, h0] at hcard
      norm_num at hcard
    exact dvd_pow_self 2 hr0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2dvd
  have hx2 : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, hx]
  have hproper : Subgroup.zpowers x ≠ ⊤ := by
    intro htop
    have hW2 : Nat.card W = 2 := by
      rw [← hx2, htop, Subgroup.card_top]
    omega
  have hstable : StableUnder L (Subgroup.zpowers x) := by
    rw [hbot]
    intro l hl u hu
    rw [Subgroup.mem_bot] at hl
    subst hl
    simpa using hu
  have hcases := hirr.2.2.2 (Subgroup.zpowers x) hstable bot_le le_top
  rcases hcases with h | h
  · rw [h, Subgroup.card_bot] at hx2
    omega
  · exact hproper h
theorem isSpor_barSub_of_isSpor_bar2_of_pcore
    {G : Type} [Group G] [Finite G] {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : L ≤ stabTil V₀ V)
    (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub V₀ V hV L ≠ ⊥)
    (hSpor : IsSpor (Bar2 L) .J2) :
    IsSpor (barSub V₀ V hV L) .J2 := by
  obtain ⟨e⟩ := hSpor
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  obtain ⟨eψ⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV hL h2 hL1
    (MulEquiv.isSimpleGroup e)
  exact ⟨eψ.symm.trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_four_of_J2
    {D : Data G} {V₀ V L A : Subgroup G} (hV : Hyp125 D V₀ V)
    (c : Ctx17_17 D V₀ V L) (h17_25 : R17_25At D V₀ V)
    (h17_23 : R17_23At D V₀ V) (hV0 : V₀ = ⊥)
    (hMN : D.M ≤ Subgroup.normalizer (L : Set G))
    (hA : A ∈ F12.Gam 2 D.T V) (hAel : IsElemAbelian 2 A) :
    E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≤ 4 := by
  classical
  let W := Vtil V₀ V hV.isElemAbelian
  have hWpow : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hW : ∀ w : W, w * w = 1 := fun w => by simpa [pow_two] using hWpow w
  have hcardW : Nat.card W = 2 ^ CFSG.Quasithin.rk (⊤ : Subgroup W) := by
    rw [← Subgroup.card_top (G := W)]
    exact CFSG.Quasithin.card_eq_two_pow hWpow (⊤ : Subgroup W)
  have h12 : CFSG.Quasithin.rk (⊤ : Subgroup W) = 12 := by
    rw [CFSG.Quasithin.rk_top]
    exact (h17_25 L c).2.1
  have hcard2 : 2 < Nat.card W := by
    rw [hcardW, h12]
    norm_num
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
    ne_bot_of_isIrrOn_of_two_lt_card hWpow (h17_25 L c).1 hcard2
  have h2M : barSub V₀ V hV.isElemAbelian (pCoreOf 2 D.M) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.barSub_pCoreOf_eq_bot_of_hyp125 hV
  have hLsub : IsSubnormal L D.M := c.mem_calC.1
  have h2 : barSub V₀ V hV.isElemAbelian (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hLsub h2M
  have hLs : L ≤ stabTil V₀ V :=
    hLsub.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hSpor : IsSpor (barSub V₀ V hV.isElemAbelian L) .J2 :=
    isSpor_barSub_of_isSpor_bar2_of_pcore hV.isElemAbelian hLs h2 hL1 (h17_23 L c)
  obtain ⟨e⟩ := hSpor
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup ↥(barSub V₀ V hV.isElemAbelian L) := MulEquiv.isSimpleGroup e
  have hcardL : Nat.card ↥(barSub V₀ V hV.isElemAbelian L) = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have hZ : Subgroup.center ↥(barSub V₀ V hV.isElemAbelian L) = ⊥ :=
    CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime (by rw [hcardL]; norm_num)
  have hLq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV.isElemAbelian L) :=
    TwelveTwentyThree.isQuasisimple_barSub hV.isElemAbelian hLs c.mem_calC.2.2 h2 hL1
  have hperf : Group.IsPerfect ↥(barSub V₀ V hV.isElemAbelian L) := ⟨hLq.1⟩
  have hE : barSub V₀ V hV.isElemAbelian A ≤
      Subgroup.normalizer (barSub V₀ V hV.isElemAbelian L :
        Set (MulAut (Vtil V₀ V hV.isElemAbelian))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact TwelveEighteen.conj_mem_barSub hV.isElemAbelian hMN x
        ((barSub_mono V₀ V hV.isElemAbelian (hA.1.trans D.sylowM.le)) hx) y hy
    · intro hy
      have hxi : x⁻¹ ∈ Mbar D.M V₀ V hV.isElemAbelian :=
        (Mbar D.M V₀ V hV.isElemAbelian).inv_mem ((barSub_mono V₀ V hV.isElemAbelian
          (hA.1.trans D.sylowM.le)) hx)
      have h := TwelveEighteen.conj_mem_barSub hV.isElemAbelian hMN x⁻¹ hxi
        (x * y * x⁻¹) hy
      simpa [mul_assoc] using h
  have hEel : IsElemAbelian2 (barSub V₀ V hV.isElemAbelian A) :=
    isElemAbelian2_barSub hV.isElemAbelian hAel
  have hcardE := J2Row.card_le_sixteen (V := W) (L := barSub V₀ V hV.isElemAbelian L)
    (E := barSub V₀ V hV.isElemAbelian A) hW hperf
    (X1_isIrrOn_of_isIrrOn (h17_25 L c).1) hZ e hE hEel
  have hA2 : IsPGroup 2 ↥A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hcardA : Nat.card ↥(barSub V₀ V hV.isElemAbelian A) =
      (A ⊓ F11.CTilde D.M V₀ V).relIndex A :=
    CFSG.LocalAnalysis.WeakClosure81.card_barSub_eq_relIndex hV.isElemAbelian
      hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀ (hA.1.trans D.sylowM.le)
  have hrel : (A ⊓ F11.CTilde D.M V₀ V).relIndex A =
      2 ^ E3.mQuot A (A ⊓ F11.CTilde D.M V₀ V) :=
    CFSG.Quasithin.E3.relIndex_eq_two_pow hA2 (A ⊓ F11.CTilde D.M V₀ V)
  have hCT : F11.CTilde D.M V₀ V =
      D.M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hV0]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_cTilde_bot D.M V
  have hAB : A ⊓ F11.CTilde D.M V₀ V =
      A ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hCT, ← inf_assoc, inf_eq_left.mpr (hA.1.trans D.sylowM.le)]
  have hpow : 2 ^ E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 ^ 4 := by
    rw [← hAB]
    rw [← hrel, ← hcardA]
    simpa using hcardE
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
