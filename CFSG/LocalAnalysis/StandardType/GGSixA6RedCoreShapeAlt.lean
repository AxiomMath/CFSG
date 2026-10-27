module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAlt
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

private theorem ggA6CharTwoLie_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {n e : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ e) (h4 : 4 ≤ Nat.card K) :
    GGA6CharTwoLie (StatedSp n K) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hne : (n, 2 ^ e) ≠ (2, 2) := by
    rintro h
    have h2 : 2 ^ e = 2 := congrArg Prod.snd h
    rw [hK, h2] at h4
    omega
  have hadm : StatedLieAdmissible .PSp n 2 e := ⟨Nat.prime_two, he, hn, hne⟩
  exact ⟨.PSp, n, e, Or.inl ⟨by decide,
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient n K hadm hK⟩⟩

private theorem ggA6CharTwoLie_statedSp_one {K : Type} [Field K] [Finite K] [CharP K 2] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (h4 : 4 ≤ Nat.card K) :
    GGA6CharTwoLie (StatedSp 1 K) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hne2 : (2, 2 ^ e) ≠ (2, 2) := by
    rintro h
    have h2 : 2 ^ e = 2 := congrArg Prod.snd h
    rw [hK, h2] at h4
    omega
  have hne3 : (2, 2 ^ e) ≠ (2, 3) := by
    rintro h
    have h2 : 2 ^ e = 3 := congrArg Prod.snd h
    have hdvd : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    rw [h2] at hdvd
    norm_num at hdvd
  have hadm : StatedLieAdmissible .PSL 2 2 e := ⟨Nat.prime_two, he, le_rfl, hne2, hne3⟩
  have hmodel :=
    CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 K hadm hK
  have hcenter : Subgroup.center (StatedSL 2 K) =
      (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) :=
    (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 2 K)).symm.trans
      (map_center_eq_statedScalars 2 K)
  let e2 : StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hmodelSL : StatedClassicalModel
      (StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K)) .PSL 2 2 e :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e2.symm hmodel
  have hshapeSL : GGA6CharTwoLie (StatedSL 2 K) :=
    ⟨.PSL, 2, e, Or.inl ⟨by decide, hmodelSL⟩⟩
  exact GGA6CharTwoLie.of_mulEquiv
    (CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two K).some.symm hshapeSL

theorem altCoreInputLie_holds : AltCoreInputLie := by
  intro D _ _ _ d T hT hscal hy h4
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    have hU : matUnitary hT = ⊥ := le_antisymm
      (fun x _ => Subgroup.mem_bot.mpr (Subsingleton.elim x 1)) bot_le
    refine ⟨⊥, bot_le, fun u _ s hs => ?_, ⟨0, ?_⟩, Or.inl rfl⟩
    · rw [Subgroup.mem_bot.mp hs, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [LayerFacts.ggDer_zero, hU]
  have hdz : NeZero d := ⟨hd.ne'⟩
  obtain ⟨H, hH⟩ := hT.exists_gram_id hscal
  have hsym := transpose_gram_eq hT H hH
  obtain ⟨y, hy⟩ := hy
  have hHy := gram_eq_add_transpose H hH hsym hy
  have hB : (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)).IsAlt := by
    have h2 := isAlt_toBilin'_add_transpose ((H : Matrix (Fin d) (Fin d) D) * y)
    rwa [← hHy] at h2
  have hn := nondegenerate_toBilin'_gram H
  have hmap := map_toLin_matUnitary H hH (hT := hT)
  let e : matUnitary hT ≃* sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)) :=
    ((matUnitary hT).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  obtain ⟨s, hs, ⟨E⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs
  let : Fintype D := Fintype.ofFinite D
  obtain ⟨e0, _, he0⟩ := FiniteField.card D 2
  have hD2pow : Nat.card D = 2 ^ (e0 : ℕ) := by rw [Nat.card_eq_fintype_card, he0]
  have hfin2 : 2 ≤ Module.finrank D (Fin d → D) := by rw [hfr]; omega
  have hq : CFSG.IsQuasisimple
      (sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D))) :=
    CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn hfin2
      (Or.inl h4)
  have hshapeU : GGA6CharTwoLie ↥(matUnitary hT) := by
    by_cases hs2 : 2 ≤ s
    · have hshapeSp : GGA6CharTwoLie (StatedSp s D) := ggA6CharTwoLie_statedSp hs2 hD2pow h4
      exact GGA6CharTwoLie.of_mulEquiv (e.trans E).symm hshapeSp
    · have hs_eq1 : s = 1 := by omega
      subst hs_eq1
      have hshapeSp1 : GGA6CharTwoLie (StatedSp 1 D) := ggA6CharTwoLie_statedSp_one hD2pow h4
      exact GGA6CharTwoLie.of_mulEquiv (e.trans E).symm hshapeSp1
  refine ⟨matUnitary hT, le_rfl, (fun u hu s hs =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hs) (Subgroup.inv_mem _ hu)), ⟨0, le_rfl⟩,
    Or.inr ⟨?_, ?_, hshapeU⟩⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  · intro z hz hzc hz2
    obtain ⟨c, hc⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_smul_of_commute_sesqUnitaryGroup_alt hB hn _
        fun g hg => by
          rw [← hmap] at hg
          obtain ⟨u, hu, rfl⟩ := hg
          have h2 : Matrix.GeneralLinearGroup.toLin z * Matrix.GeneralLinearGroup.toLin u =
              Matrix.GeneralLinearGroup.toLin u * Matrix.GeneralLinearGroup.toLin z := by
            rw [← map_mul, ← map_mul, hzc u hu]
          exact congrArg Units.val h2
    exact eq_one_of_smul_one (eq_smul_one_of_toLin hc) hz2

end CFSG.StandardType.A6Red.CoreShape

end
