module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenKHolds
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShape
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem nonsingular_centralizer_le_case2On (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h142 : R18_14_2At D V₀ V p L h)
    {s f : ℕ} (hs : P18_13_2 D V₀ V p L h s) (hf2 : 2 ≤ f)
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f)
    {W' : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)}
    (hW' : StableUnder (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) W')
    (hN : NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) W' ⊥ 6 f)
    {F : Type} [Field F] [Finite F] {b c : F} (hF : Nat.card F = 2 ^ f)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaMinusOn
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) W' hW' F b c ε ψ)
    (x : IntMod V h.hyp125.isElemAbelian) (hx0 : x.val ∉ V₀)
    (hxW : tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem ∈ W')
    (hns : StatedQuadMinus 3 F b c
      (Multiplicative.toAdd (ψ ⟨tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem, hxW⟩))
        ≠ 0) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
    have hU4 : IsU4 ↥H f := isU4_of_isOmegaMinus hO
    exact (isU4_barSub_cong h h1742 hU4).2.2.2
  have hSp : IsSp4 (Bar2 (Opp p (centVec H
      (tilOf V₀ V hV x.val x.val_mem)))) f :=
    ((h142 ⟨s, hs⟩ f hf2 hO).2 W' hW' hN F b c hF hbc ε ψ hψ x.val x.val_mem hx0
      hxW).2 hns
  obtain ⟨E, hEH, hEp, hEc, hEfix⟩ :=
    k_K_Omega6Minus_nonsingPoint_holds H p f hf2 hO W' hW' hN h.p_prime hcong F b c hF hbc
      ε ψ hψ
      ⟨tilOf V₀ V hV x.val x.val_mem, hxW⟩ (by simpa using hns)
  have hHM : H ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.X_le_M
  have hEM : E ≤ Mbar D.M V₀ V hV := hEH.trans hHM
  have hV0lt : Nat.card V₀ < p := by
    have hle : Nat.card V₀ ≤ 2 := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    have hp2 : p ≠ 2 := h.p_ne_two
    have := h.p_prime.two_le
    omega
  have hEfix' : ∀ e ∈ E, e (mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) := by
    intro e he
    simpa [tilOf] using hEfix e he
  obtain ⟨Q, hQM, hQp, hQc⟩ :=
    C163.exists_noncyclic_le_centralizer hV h.p_prime hV0lt x.val_mem hEM hEp hEc hEfix'
  exact centralizer_le_of_noncyclic D h61 h.hp (hQM.trans inf_le_left) hQp hQc
    (fun h1 => hx0 (h1 ▸ V₀.one_mem))
    ⟨1, by simpa using hV.2 x.val x.val_mem⟩ (hQM.trans inf_le_right)

theorem nonsingular_centralizer_le_case2 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h142 : R18_14_2At D V₀ V p L h)
    {s f : ℕ} (hs : P18_13_2 D V₀ V p L h s) (hf2 : 2 ≤ f)
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f)
    (hN : NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 6 f)
    {F : Type} [Field F] [Finite F] {b c : F} (hF : Nat.card F = 2 ^ f)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaMinusOn
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ)
    (x : IntMod V h.hyp125.isElemAbelian) (hx0 : x.val ∉ V₀)
    (hns : StatedQuadMinus 3 F b c
      (Multiplicative.toAdd (ψ ⟨tilOf V₀ V h.hyp125.isElemAbelian x.val x.val_mem,
        Subgroup.mem_top _⟩)) ≠ 0) :
    centralizer ({x.val} : Set G) ≤ D.M :=
  nonsingular_centralizer_le_case2On D h61 h h1742 h142 hs hf2 hO
    (fun _ _ s _ => Subgroup.mem_top s) hN hF hbc ε ψ hψ x hx0 (Subgroup.mem_top _) hns

theorem rk_imgTil_le_case2_s1 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h142 : R18_14_2At D V₀ V p L h)
    (hKl : K_Omega6Minus_lineStab)
    (hs : P18_13_2 D V₀ V p L h 1) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V h.hyp125.isElemAbelian U) ≤ 2 * S17.nOf L - 1 + mSub V₀ := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hs1 := hs
  obtain ⟨-, -, f, hO, hsum⟩ := hs
  obtain ⟨hmem, -, -, hsup, hN⟩ := hsum
  have hI : hmem 0 = ⊤ := by
    rw [bot_sup_eq, iSup_unique] at hsup
    exact hsup
  have hNat : NatOmegaMinus H ⊤ ⊥ 6 f := hI ▸ hN 0
  obtain ⟨-, hnof, hf1, hcong⟩ := isU4_barSub_cong h h1742 (isU4_of_isOmegaMinus hO)
  have hf2 : 2 ≤ f := by omega
  obtain ⟨F, hF, hFfin, b, c, hFcard, hbc, ε, ψ, hψ⟩ := exists_natCoords_of_natOmegaMinus hNat
  have htil : ∀ x : IntMod V hV,
      tilOf V₀ V hV x.val x.val_mem = mkTil V₀ V hV x := by
    intro x
    change mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) = mkTil V₀ V hV x
    exact congrArg (mkTil V₀ V hV) (IntMod.val_injective rfl)
  have hSing : ∀ x : IntMod V hV, x.val ∈ U → x.val ∉ V₀ →
      StatedQuadMinus 3 F b c
        (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV x, Subgroup.mem_top _⟩)) = 0 := by
    intro x hxU hx0
    by_contra hns
    exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
      (nonsingular_centralizer_le_case2 D h61 h h1742 h142 hs1 hf2 hO hNat hFcard hbc
        ε ψ hψ x hx0 (by simpa [htil x] using hns)))
  have hWtSing : ∀ y ∈ imgTil V₀ V hV U,
      StatedQuadMinus 3 F b c
        (Multiplicative.toAdd (ψ ⟨y, Subgroup.mem_top _⟩)) = 0 := by
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U y).1 hy
    by_cases hx0 : x.val ∈ V₀
    · have h1 : mkTil V₀ V hV x = 1 :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx0
      have h2 : (⟨(1 : Vtil V₀ V hV), Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 1 := Subtype.ext rfl
      rw [h1, h2, map_one, toAdd_one]
      simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
    · exact hSing x hxU hx0
  have hrk : rk ↥(imgTil V₀ V hV U) ≤ 2 * f := by
    have hWt2 : ∀ y ∈ imgTil V₀ V hV U, y * y = 1 :=
      fun y _ => by simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV y
    have hWtSing' : ∀ y ∈ imgTil V₀ V hV U, LieType.Universal.Spin.quadMinus 3 F b c
        (Multiplicative.toAdd (ψ ⟨y, Subgroup.mem_top _⟩)) = 0 := by
      intro y hy
      simpa only [CFSG.LieType.Universal.Spin.coe_quadMinus] using hWtSing y hy
    exact rk_le_two_mul_of_singularOn hFcard hbc ψ _ (fun _ _ => Subgroup.mem_top _) hWt2
      hWtSing'
  rw [hnof]
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    have h0 : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk_bot]
    rw [h0, Nat.add_zero]
    by_cases hlt : rk ↥(imgTil ⊥ V hV U) ≤ 2 * f - 1
    · omega
    · exfalso
      have hrk2 : rk ↥(imgTil ⊥ V hV U) = 2 * f := by omega
      obtain ⟨P, hPH, hPp, hPc⟩ :=
        hKl H f p hFcard hbc h.p_prime h.p_ne_two hcong ⊤
          (fun _ _ s _ => Subgroup.mem_top s) hNat ε ψ hψ _ (fun _ _ => Subgroup.mem_top _)
          hrk2 hWtSing
      have hPM : P ≤ Mbar D.M ⊥ V hV := (hPH.trans inf_le_left).trans (barSub_mono ⊥ V hV h.X_le_M)
      have hPstab : P ≤ stabSub (imgTil ⊥ V hV U) := hPH.trans inf_le_right
      obtain ⟨Q, hQN, hQM, hQp, hQc⟩ :=
        exists_noncyclic_le_normalizer_of_stab hV hUV rfl h.p_prime hPM hPp hPc hPstab
      exact hQc (isCyclic_of_le_normalizer_of_not_centralizer_le D h61 h hUV le_rfl
        (by
          intro hbot
          rw [hbot, TwelveSeventeen.imgTil_bot] at hrk2
          have hzb : rk (⊥ : Subgroup (Vtil ⊥ V hV)) = 0 := rk_bot
          rw [hzb] at hrk2
          omega) hU hQN hQM hQp)
  · have hm1 : mSub V₀ = 1 := by
      have hle := h.small
      have hne : mSub V₀ ≠ 0 := by
        intro h0
        apply hV0
        have hcard : Nat.card V₀ = 1 := by
          rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup, h0]
          norm_num
        exact (Subgroup.card_eq_one).1 hcard
      omega
    omega

theorem eighteen_sixteen_two_s1 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (h1742 : S17.R17_42At D V₀ V)
    (h142 : R18_14_2At D V₀ V p L h)
    (hKl : K_Omega6Minus_lineStab)
    (hs : P18_13_2 D V₀ V p L h 1) :
    ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hs1 := hs
  obtain ⟨-, -, f, hO, hsum⟩ := hs
  obtain ⟨hmem, -, -, hsup, hN⟩ := hsum
  have hI : hmem 0 = ⊤ := by
    rw [bot_sup_eq, iSup_unique] at hsup
    exact hsup
  have hNat : NatOmegaMinus
      (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 6 f := hI ▸ hN 0
  obtain ⟨-, hnof, -, -⟩ := isU4_barSub_cong h h1742 (isU4_of_isOmegaMinus hO)
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) = 6 * S17.nOf L := by
    rw [hnof]
    exact rk_eq_six_mul_of_natOmegaMinus hNat
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_rMV_of_forall_rk_imgTil_le D h.hyp125
    (b := 2 * S17.nOf L - 1 + mSub V₀) (c := 4 * S17.nOf L + 1) ?_ ?_
  · have h6 := le_mSub_of_rk_top_le D h.hyp125 (N := 6 * S17.nOf L) (le_of_eq hrk.symm)
    have hsub := rk_top_vtil_add_mSub V₀ V h.hyp125.isElemAbelian h.hyp125.pairFacts.le
    have hn2 : 2 ≤ S17.nOf L := by rw [hnof]; exact (isU4_barSub_cong h h1742
      (isU4_of_isOmegaMinus hO)).2.2.1
    omega
  · intro U hUV hUC
    exact rk_imgTil_le_case2_s1 D h61 h h1742 h142 hKl hs1 hUV hUC

theorem rk_imgTil_le_case2_s2 (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h142 : R18_14_2At D V₀ V p L h)
    (hKl : K_Omega6Minus_lineStab)
    (hs : P18_13_2 D V₀ V p L h 2) {U : Subgroup G} (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V h.hyp125.isElemAbelian U) ≤
      6 * S17.nOf L * 2 - (4 * S17.nOf L + 1) + mSub V₀ := by
  classical
  have hV := h.hyp125.isElemAbelian
  let H : Subgroup (MulAut (Vtil V₀ V hV)) :=
    barSub V₀ V hV (UC22.conjClosure D.M L)
  have hs2 := hs
  obtain ⟨-, -, f, hO, hsum⟩ := hs
  obtain ⟨-, hnof, hf2, hcong⟩ := isU4_barSub_cong h h1742 (isU4_of_isOmegaMinus hO)
  obtain ⟨J0, J1, hN0, hN1, hdisj, hsup⟩ := s16c167_sumOfNat_two hsum
  have hW0 : StableUnder H J0 := stableUnder_of_natOmegaMinus hN0
  have hJ0 : rk ↥J0 = 6 * f := rk_eq_six_mul_of_natOmegaMinus hN0
  have hJ1 : rk ↥J1 = 6 * f := rk_eq_six_mul_of_natOmegaMinus hN1
  have hrkTop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 12 * f := by
    have h1 := rk_sup_add_rk_inf J0 J1
    rw [hdisj, rk_bot, hJ0, hJ1] at h1
    have h2 : (⊤ : Subgroup (Vtil V₀ V hV)) = J0 ⊔ J1 := hsup.symm
    rw [h2]
    omega
  obtain ⟨F, hF, hFfin, b, c, hFcard, hbc, ε, ψ, hψ⟩ :=
    exists_natCoords_of_natOmegaMinusOn hW0 hN0
  let W : Subgroup (Vtil V₀ V hV) := imgTil V₀ V hV U
  have hdec : rk ↥W ≤ 6 * f + rk ↥(W ⊓ J0) := by
    have h1 := rk_sup_add_rk_inf W J0
    have h2 : rk ↥(W ⊔ J0) ≤ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) := rk_mono le_top
    have h3 : rk ↥J0 = 6 * f := hJ0
    omega
  have htil : ∀ x : IntMod V hV,
      tilOf V₀ V hV x.val x.val_mem = mkTil V₀ V hV x := by
    intro x
    change mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) = mkTil V₀ V hV x
    exact congrArg (mkTil V₀ V hV) (IntMod.val_injective rfl)
  have hSing : ∀ y (hy : y ∈ W ⊓ J0),
      StatedQuadMinus 3 F b c
        (Multiplicative.toAdd (ψ ⟨y, hy.2⟩)) = 0 := by
    intro y hy
    by_contra hns
    obtain ⟨x, hxU, hxy⟩ := (mem_imgTil V₀ V hV U y).1 hy.1
    have hyeq : tilOf V₀ V hV x.val x.val_mem = y := (htil x).symm.trans hxy
    by_cases hy1 : y = 1
    · have hq1 : StatedQuadMinus 3 F b c
          (Multiplicative.toAdd (ψ ⟨y, hy.2⟩)) = 0 := by
        rw [show (⟨y, hy.2⟩ : J0) = ⟨1, J0.one_mem⟩ from Subtype.ext hy1,
          show (⟨(1 : Vtil V₀ V hV), J0.one_mem⟩ : J0) = 1 from rfl, map_one, toAdd_one]
        simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
      exact hns hq1
    · have hx0 : x.val ∉ V₀ := by
        intro hxV0
        have h1 : mkTil V₀ V hV x = 1 :=
          (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hxV0
        exact hy1 (by rw [← hxy, h1])
      have hxJ0 : tilOf V₀ V hV x.val x.val_mem ∈ J0 := by
        rw [hyeq]; exact hy.2
      have harg : (⟨tilOf V₀ V hV x.val x.val_mem, hxJ0⟩ : J0) =
          ⟨y, hy.2⟩ := Subtype.ext hyeq
      have hns' : StatedQuadMinus 3 F b c
          (Multiplicative.toAdd (ψ ⟨tilOf V₀ V hV x.val x.val_mem, hxJ0⟩)) ≠ 0 := by
        simpa only [harg] using hns
      exact hU ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
        (nonsingular_centralizer_le_case2On D h61 h h1742 h142 hs2 hf2 hO
          hW0 hN0 hFcard hbc ε ψ hψ x hx0 hxJ0 hns'))
  have hSing' : ∀ y (hy : y ∈ W ⊓ J0), quadMinus 3 F b c
      (Multiplicative.toAdd (ψ ⟨y, hy.2⟩)) = 0 := by
    intro y hy
    simpa only [CFSG.LieType.Universal.Spin.coe_quadMinus] using hSing y hy
  have hE2 : ∀ y ∈ W ⊓ J0, y * y = 1 :=
    fun y _ => by simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV y
  have hE : rk ↥(W ⊓ J0) ≤ 2 * f :=
    rk_le_two_mul_of_singularOn hFcard hbc ψ (W ⊓ J0) (fun _ hy => hy.2) hE2 hSing'
  rw [hnof]
  have hrkW : rk ↥(imgTil V₀ V hV U) ≤ 8 * f := by
    have hdec' : rk ↥(imgTil V₀ V hV U) ≤
        6 * f + rk ↥(imgTil V₀ V hV U ⊓ J0) := hdec
    have hE' : rk ↥(imgTil V₀ V hV U ⊓ J0) ≤ 2 * f := hE
    omega
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    have h0 : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk_bot]
    rw [h0, Nat.add_zero]
    by_cases hlt : rk ↥(W ⊓ J0) ≤ 2 * f - 1
    · have hlt' : rk ↥(imgTil ⊥ V hV U ⊓ J0) ≤ 2 * f - 1 := hlt
      have hdec' : rk ↥(imgTil ⊥ V hV U) ≤
          6 * f + rk ↥(imgTil ⊥ V hV U ⊓ J0) := hdec
      omega
    · exfalso
      have hrkE : rk ↥(W ⊓ J0) = 2 * f := by omega
      obtain ⟨P, hPH, hPp, hPc⟩ :=
        hKl H f p hFcard hbc h.p_prime h.p_ne_two hcong J0 hW0 hN0 ε ψ hψ
          (W ⊓ J0) (fun _ hy => hy.2) hrkE hSing
      have hPM : P ≤ Mbar D.M ⊥ V hV :=
        (hPH.trans inf_le_left).trans (barSub_mono ⊥ V hV h.X_le_M)
      have hPstab : P ≤ stabSub (W ⊓ J0) := hPH.trans inf_le_right
      let X : Subgroup G := preTil ⊥ V hV (W ⊓ J0)
      have hXU : X ≤ U := by
        rw [← CFSG.LocalAnalysis.WeakClosure81.preTil_imgTil_of_le hV hUV
          (bot_le : (⊥ : Subgroup G) ≤ U)]
        exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
      have hXV : X ≤ V := hXU.trans hUV
      have hXne : X ≠ ⊥ := by
        change preTil ⊥ V hV (W ⊓ J0) ≠ ⊥
        intro hbot
        have hc := s16c167_rk_preTil (V₀ := (⊥ : Subgroup G)) hV rfl (W ⊓ J0)
        rw [hbot, rk_bot] at hc
        omega
      obtain ⟨Q, hQN, hQM, hQp, hQc⟩ :=
        exists_noncyclic_le_normalizer_of_stab hV hXV (imgTil_preTil ⊥ V hV (W ⊓ J0))
          h.p_prime hPM hPp hPc hPstab
      exact hQc (isCyclic_of_le_normalizer_of_not_centralizer_le D h61 h hXV hXU hXne hU
        hQN hQM hQp)
  · have hm1 : mSub V₀ = 1 := by
      have hle := h.small
      have hne : mSub V₀ ≠ 0 := by
        intro h0
        apply hV0
        have hcard : Nat.card V₀ = 1 := by
          rw [card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup, h0]
          norm_num
        exact (Subgroup.card_eq_one).1 hcard
      omega
    have h8 : rk ↥(imgTil V₀ V hV U) ≤ 8 * f := hrkW
    omega

theorem eighteen_sixteen_two_s2 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (h1742 : S17.R17_42At D V₀ V)
    (h142 : R18_14_2At D V₀ V p L h)
    (hKl : K_Omega6Minus_lineStab)
    (hs : P18_13_2 D V₀ V p L h 2) :
    ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hV := h.hyp125.isElemAbelian
  have hs2 := hs
  obtain ⟨-, -, f, hO, hsum⟩ := hs
  obtain ⟨-, hnof, hf2, -⟩ := isU4_barSub_cong h h1742 (isU4_of_isOmegaMinus hO)
  obtain ⟨J0, J1, hN0, hN1, hdisj, hsup⟩ := s16c167_sumOfNat_two hsum
  have hJ0 : rk ↥J0 = 6 * f := rk_eq_six_mul_of_natOmegaMinus hN0
  have hJ1 : rk ↥J1 = 6 * f := rk_eq_six_mul_of_natOmegaMinus hN1
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 12 * S17.nOf L := by
    rw [hnof]
    have h1 := rk_sup_add_rk_inf J0 J1
    rw [hdisj, rk_bot, hJ0, hJ1] at h1
    have h2 : (⊤ : Subgroup (Vtil V₀ V hV)) = J0 ⊔ J1 := hsup.symm
    rw [h2]
    omega
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_rMV_of_forall_rk_imgTil_le D h.hyp125
    (b := 6 * S17.nOf L * 2 - (4 * S17.nOf L + 1) + mSub V₀) (c := 4 * S17.nOf L + 1)
    ?_ ?_
  · have hsub := rk_top_vtil_add_mSub V₀ V hV h.hyp125.pairFacts.le
    rw [hrk] at hsub
    have h4 : 4 * S17.nOf L + 1 ≤ 6 * S17.nOf L * 2 := by omega
    omega
  · intro U hUV hUC
    exact rk_imgTil_le_case2_s2 D h61 h h1742 h142 hKl hs2 hUV hUC

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
