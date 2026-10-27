module

public import CFSG.LocalAnalysis.WeakClosure81.PGLTwoPrimePrintedRelativeGeneration
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.RonanE114HeLat
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.RonanE114.HeOver CFSG.Quasithin.ModH
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

theorem inF_one_top_of_mulEquiv_pgl2_prime
    {Q F : Type} [Group Q] [Finite Q] [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 5 < p)
    (e : Q ≃* CFSG.GorensteinWalter.PGL2 F) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF 1 (⊤ : Subgroup Q) := by
  classical
  intro T hT Ω hΩ hne hbot
  have hTin : CFSG.Quasithin.IsSylowIn 2 T (⊤ : Subgroup Q) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  obtain ⟨A, hAΩ, hAT⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_mem_le_of_isSylowOf hT hΩ hne
  have hAel : CFSG.Open.IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
  have hAne : A ≠ ⊥ := hbot A hAΩ
  let π : ↥(⊤ : Subgroup Q) →* CFSG.GorensteinWalter.PGL2 F :=
    e.toMonoidHom.comp (Subgroup.topEquiv (G := Q)).toMonoidHom
  have hπ : Function.Surjective π :=
    e.surjective.comp (Subgroup.topEquiv (G := Q)).surjective
  have hker : IsPGroup 2 π.ker := by
    have hbot : π.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      intro x y hxy
      exact (Subgroup.topEquiv (G := Q)).injective (e.injective hxy)
    rw [hbot]
    exact IsPGroup.of_bot
  have hneπ : (A.subgroupOf (⊤ : Subgroup Q)).map π ≠ ⊥ := by
    intro h
    apply hAne
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have ha' : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup Q)) ∈ A.subgroupOf ⊤ := ha
    have h1 : π ⟨a, Subgroup.mem_top a⟩ = 1 := by
      rw [Subgroup.eq_bot_iff_forall] at h
      exact h _ (Subgroup.mem_map_of_mem π ha')
    have h2 : e a = 1 := by simpa [π] using h1
    exact e.injective (by simpa using h2)
  have hgen := relative_generation_printed_of_pgl2_prime hF hp hTin hAT hAel
    (by rw [inf_top_eq]; exact CFSG.Quasithin.E1.tauOf_le (⊤ : Subgroup Q) T A)
    (by simpa using hTin) π hπ hker hneπ
  have hle : (⨆ J ∈ {J : Subgroup Q | CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J},
      J) ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω := by
    refine iSup₂_le fun J hJ => ?_
    exact le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT (le_iSup₂_of_le J
      (isEP_of_inCalEi hAT hAel hJ) le_rfl))
  have hsup : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω ⊔ T = ⊤ := by
    rw [sup_comm]
    exact top_le_iff.mp (hgen.trans (sup_le_sup le_rfl hle))
  have hnorm : T ≤ Subgroup.normalizer
      (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω : Set Q) :=
    le_normalizer_eGenP 1 hΩ
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left
    (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω) T hnorm,
    hsup, Subgroup.coe_top]

theorem inF_one_top_of_isPGL2_seven
    {Q : Type} [Group Q] [Finite Q]
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 Q) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF 1 (⊤ : Subgroup Q) := by
  obtain ⟨F, hF, hFfin, hFcard, ⟨eQ⟩⟩ := hPGL
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  let e : Q ≃* CFSG.GorensteinWalter.PGL2 F :=
    eQ.trans (QuotientGroup.quotientMulEquivOfEq hcs).symm
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact inF_one_top_of_mulEquiv_pgl2_prime hFcard (by norm_num) e

theorem he_isL2Odd_bar2_Y7 {Γ : Type} [Group Γ] [Finite Γ] (hl : CFSG.Quasithin.ModH.HeLat Γ)
    (h128 : Nat.card (CFSG.pCore 2 ↥(hl.Y 7)) = 128) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2Odd
      (Bar2 (hl.Y 7)) 7 := by
  classical
  obtain ⟨f, hf, hker⟩ := heY7_levi hl h128
  have hcardY7 : Nat.card ↥(hl.Y 7) = 21504 := card_Y7 hl
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two
      CFSG.Quasithin.RonanE114.P7.isPSL_sl3_two
  have hrange : Nat.card ↥f.range = 168 := by
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, hcardSL]
  have hcardker : Nat.card ↥f.ker = 128 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hcardY7, hrange] at h1
    omega
  have hkerle : f.ker ≤ CFSG.pCore 2 ↥(hl.Y 7) :=
    CFSG.LieType.BorelTits.le_pCore 2 f.normal_ker hker
  have hkereq : f.ker = CFSG.pCore 2 ↥(hl.Y 7) :=
    Subgroup.eq_of_le_of_card_ge hkerle (by rw [h128, hcardker])
  have : f.ker.Normal := f.normal_ker
  let e : Bar2 (hl.Y 7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hkereq).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hpsl : CFSG.Quasithin.IsPSL 3 2 1 (Bar2 (hl.Y 7)) :=
    CFSG.Quasithin.IsPSL.of_mulEquiv e.symm CFSG.Quasithin.RonanE114.P7.isPSL_sl3_two
  have h7 : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 (hl.Y 7)) .PSL 2 7 1 :=
    CFSG.QuasithinUnique.Vol2Native.statedClassicalModel_psl_two_seven_of_three_two
      hpsl
  exact Or.inl ⟨by decide, h7⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
