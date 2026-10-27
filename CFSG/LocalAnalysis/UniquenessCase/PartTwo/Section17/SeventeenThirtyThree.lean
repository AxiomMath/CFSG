module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.Quasithin.Background.HTransport
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem data_of_ctx17_33 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h17_35 : R17_35At D V₀ V) (h17_39 : R17_39At D V₀ V) :
    n = 2 ∧ D.k = 2 ∧ mBar D.M V₀ V c.hyp125.isElemAbelian = 4 ∧
      L = UC22.conjClosure D.M L := by
  have hV₀ : V₀ = ⊥ := h17_39 L n c
  obtain ⟨h1, h2⟩ := h17_35
  obtain ⟨_, h35m⟩ := h1 L n c
  obtain ⟨-, hk, hm4, hL⟩ := h2 L n c hV₀
  refine ⟨?_, hk, hm4, hL⟩
  have h2n : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := h35m
  omega

theorem barSub_bot_iff_le_centralizer {D : Data G} {V A : Subgroup G} (h : Hyp125 D ⊥ V)
    (hAM : A ≤ D.M) :
    barSub ⊥ V h.isElemAbelian A = ⊥ ↔ A ≤ Subgroup.centralizer (V : Set G) := by
  have hM0 : D.M ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  rw [CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff h.isElemAbelian
    h.pairFacts.le_normalizer hM0 hAM]
  rw [show F11.CTilde D.M ⊥ V = D.M ⊓ Subgroup.centralizer (V : Set G) from
    UC22.cTilde_bot D.M V]
  constructor
  · intro hA
    exact fun a ha => (Subgroup.mem_inf.1 (hA ha)).2
  · intro hA
    exact fun a ha => Subgroup.mem_inf.2 ⟨hAM ha, hA ha⟩

theorem exists_gammaTwo_barSub_ne_bot {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hC : ¬ Subgroup.centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M) :
    ∃ A ∈ E3.gammaSet V 2 D.T, barSub ⊥ V h.isElemAbelian A ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  have hW : E3.wClos V 2 D.T ≤ Subgroup.centralizer (V : Set G) :=
    E3.wClos_le_of_forall fun A hA =>
      (barSub_bot_iff_le_centralizer h (hA.1.trans D.sylowM.le)).1 (hcon A hA)
  have hVT : V ≤ D.T := UC22.uc22p22p_le_T_of_inCalV D h.inCalV
  have hVc : V ≤ E3.cClos V 2 D.T :=
    le_inf hVT (Subgroup.le_centralizer_iff.1 hW)
  exact hC ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVc)).trans
    (centralizer_le_of_inCalV D h.inCalV))

theorem not_le_conjSubgroup_of_mem_gammaTwo {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hW0 : E3.wClos V 0 D.T ≤ Subgroup.centralizer (V : Set G))
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 2 D.T)
    (hAne : ¬ A ≤ Subgroup.centralizer (V : Set G)) {g : G}
    (hAg : A ≤ conjSubgroup V g) :
    ¬ V ≤ conjSubgroup D.M g := by
  classical
  intro hVMg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVginvM : conjSubgroup V g⁻¹ ≤ D.M :=
    (E3.conjSubgroup_le_iff_le_inv (A := V) (B := D.M) g⁻¹).2
      (by simpa using hVMg)
  have hV2 : IsPGroup 2 V := h.isElemAbelian.isPGroup
  have hsyl : IsSylowIn 2 D.T D.M := by
    refine ⟨D.sylowM.le, D.sylowM.isPGroup, ?_⟩
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.2
  obtain ⟨m, hmM, hmle⟩ :=
    E3.exists_le_conj_of_isSylowIn hsyl hVginvM (E3.isPGroup_conjSubgroup hV2 g⁻¹)
  have hconj : conjSubgroup V (g⁻¹ * m⁻¹) ≤ D.T := by
    have hle := E3.conjSubgroup_mono_left m⁻¹ hmle
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup,
      E3.conjSubgroup_conj_inv] at hle
  have hmem : conjSubgroup V (g⁻¹ * m⁻¹) ∈ E3.gammaSet V 0 D.T := by
    refine ⟨hconj, g⁻¹ * m⁻¹, le_rfl, ?_⟩
    exact E3.mQuot_self _
  have hWle : conjSubgroup V (g⁻¹ * m⁻¹) ≤ E3.wClos V 0 D.T :=
    E3.le_wClos hmem
  have hleC : conjSubgroup V (g⁻¹ * m⁻¹) ≤ Subgroup.centralizer (V : Set G) :=
    hWle.trans hW0
  have hMnormC : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (V : Set G) : Set G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer h.pairFacts.le_normalizer
  have hCinv : conjSubgroup V g⁻¹ ≤ Subgroup.centralizer (V : Set G) := by
    have h1 := E3.conjSubgroup_mono_left m hleC
    have hCm : conjSubgroup (Subgroup.centralizer (V : Set G)) m =
        Subgroup.centralizer (V : Set G) :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.2 (hMnormC hmM)
    rw [hCm] at h1
    have heq : (g⁻¹ * m⁻¹) * m = g⁻¹ := by group
    simpa [CFSG.Quasithin.conjSubgroup_conjSubgroup, heq] using h1
  have hVleC : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    have hle := E3.conjSubgroup_mono_left g hCinv
    simpa only [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, E3.conjSubgroup_centralizer] using hle
  refine hAne (hAg.trans ?_)
  intro a ha
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro v hv
  exact (Subgroup.mem_centralizer_iff.1 (hVleC hv) a ha).symm

theorem le_conjSubgroup_of_mem_gammaTwo {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (h41_3 : (8 : ℕ∞) ≤ rMV D.M V)
    (hpR : CFSG.Open.pRank 2 (Mbar D.M ⊥ V h.isElemAbelian) ≤ 3)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 2 D.T)
    (hAne : barSub ⊥ V h.isElemAbelian A ≠ ⊥) {g : G}
    (hmA : E3.mQuot (conjSubgroup V g) A = 2)
    (hAg : A ≤ conjSubgroup V g) :
    V ≤ conjSubgroup D.M g := by
  classical
  have hAM : A ≤ D.M := hA.1.trans D.sylowM.le
  have hM0 : D.M ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hAst : A ≤ stabTil ⊥ V :=
    hAM.trans (le_stabTil h.pairFacts.le_normalizer hM0)
  set B : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBV : B ≤ conjSubgroup V g := hBA.trans hAg
  have hAel : IsElemAbelian 2 A :=
    IsElemAbelian.mono (E3.isElemAbelian_conjSubgroup h.isElemAbelian g) hAg
  have hbarA_el : IsElemAbelian 2 (barSub ⊥ V h.isElemAbelian A) :=
    IsElemAbelian.map (IsElemAbelian.comap hAel (stabTil ⊥ V).subtype_injective)
      (actTil ⊥ V h.isElemAbelian)
  have hbarA_pg : IsPGroup 2 (barSub ⊥ V h.isElemAbelian A) :=
    hbarA_el.isPGroup
  have hbarA_le : barSub ⊥ V h.isElemAbelian A ≤ Mbar D.M ⊥ V h.isElemAbelian :=
    barSub_mono ⊥ V h.isElemAbelian hAM
  have hcardA : Nat.card (barSub ⊥ V h.isElemAbelian A) =
      2 ^ rk ↥(barSub ⊥ V h.isElemAbelian A) :=
    card_eq_two_pow_mSub hbarA_pg
  have hrk_le : rk ↥(barSub ⊥ V h.isElemAbelian A) ≤
      CFSG.Open.pRank 2 (Mbar D.M ⊥ V h.isElemAbelian) :=
    CFSG.SectionRank.le_pRank (by norm_num) hbarA_le hbarA_el hcardA
  have hMA : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans h.pairFacts.le_normalizer
  have hpre : preBarSub A ⊥ V h.isElemAbelian ⊥ = B := by
    rw [← cTilde_eq_preBarSub_bot (M := A) h.isElemAbelian hMA]
    rw [show F11.CTilde A ⊥ V = A ⊓ Subgroup.centralizer (V : Set G) from
      UC22.cTilde_bot A V]
  have hmB_eq : E3.mQuot A B = rk ↥(barSub ⊥ V h.isElemAbelian A) := by
    rw [← CFSG.Quasithin.H.mQuot_bot_eq_rk (barSub ⊥ V h.isElemAbelian A), ← hpre]
    exact (CFSG.LocalAnalysis.WeakClosure81.mQuot_barSub_preBarSub_gen
      h.isElemAbelian hAst (C := ⊥) bot_le).symm
  have hmB : E3.mQuot A B ≤ 3 := by
    rw [hmB_eq]; exact hrk_le.trans hpR
  have hmVgB : E3.mQuot (conjSubgroup V g) B ≤ 5 := by
    have hadd := E3.mQuot_add (V := conjSubgroup V g) (U := B) (U' := A) hBA hAg
    rw [hmA] at hadd
    omega
  have hCB : Subgroup.centralizer (B : Set G) ≤ conjSubgroup D.M g := by
    by_contra hnot
    set U : Subgroup G := conjSubgroup V g ⊓
      Subgroup.centralizer (Subgroup.centralizer (B : Set G) : Set G) with hUdef
    have hBU : B ≤ U := by
      refine le_inf hBV ?_
      exact Subgroup.le_centralizer_iff.2 le_rfl
    have hUVg : U ≤ conjSubgroup V g := inf_le_left
    have hmVgU : E3.mQuot (conjSubgroup V g) U ≤ E3.mQuot (conjSubgroup V g) B :=
      E3.mQuot_mono hBU
    have h8 : (8 : ℕ∞) ≤ rMV D.M V := h41_3
    have hr : rMV (conjSubgroup D.M g) (conjSubgroup V g) = rMV D.M V := by
      rw [rMV_eq_rParam (M := conjSubgroup D.M g) (V := conjSubgroup V g) ?_,
        rMV_eq_rParam (M := D.M) (V := V) (normalizer_eq_of_inCalV D h.inCalV),
        E3.rParam_conj]
      rw [← E3.conjSubgroup_normalizer, normalizer_eq_of_inCalV D h.inCalV]
    have hUCY : U ≤ Subgroup.centralizer
        (Subgroup.centralizer (B : Set G) : Set G) := inf_le_right
    have hYU : Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer (U : Set G) :=
      Subgroup.le_centralizer_iff.1 hUCY
    have hnotU : ¬ Subgroup.centralizer (U : Set G) ≤ conjSubgroup D.M g :=
      fun hle => hnot (hYU.trans hle)
    have hle : rMV (conjSubgroup D.M g) (conjSubgroup V g) ≤
        (E3.mQuot (conjSubgroup V g) U : ℕ∞) := by
      unfold rMV
      exact iInf₂_le U ⟨hUVg, hnotU⟩
    have h8' : 8 ≤ E3.mQuot (conjSubgroup V g) U := Nat.cast_le.mp (h8.trans (hr ▸ hle))
    omega
  have hVleCB : V ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 v hv).symm
  exact hVleCB.trans hCB


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
