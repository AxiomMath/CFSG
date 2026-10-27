module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Size
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniTorusDiag
import CFSG.RankThree.PartOne.S15K.NormAct
import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section UnitaryRank

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

private theorem uniNCRank_isHermIsometry_iff_stdHermForm {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem uniNCRank_isHermIsometry_mem_guSet {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {g : GL (Fin n) K}
    (hg : IsHermIsometry (2 ^ f) (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ LargeEvenGUSet (Fin n) K (2 ^ f) := by
  have hstd : ∀ x y, stdHermForm h n
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      stdHermForm h n x y := (uniNCRank_isHermIsometry_iff_stdHermForm h).mp hg
  have hmat := CFSG.StandardType.SUTB.map_bar_transpose_mul_of_isometry h hstd
  refine ⟨1, one_ne_zero, by simp, ?_⟩
  have hbar : ((g : Matrix (Fin n) (Fin n) K).map (· ^ (2 ^ f))) =
      (g : Matrix (Fin n) (Fin n) K).map h.bar := by
    ext i j
    simp only [Matrix.map_apply, h.bar_apply]
  rw [hbar, hmat]
  simp

private theorem uniNCRank_isConjBy_eq {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q, g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) (h' : IsConjBy g a') : a = a' := by
  ext y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K q)) y
  subst hx
  let x' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g * (x : GL (Fin n) K) * g⁻¹, hnorm x x.2⟩
  have hx' : (x' : GL (Fin n) K) = g * (x : GL (Fin n) K) * g⁻¹ := rfl
  rw [h x x' hx', h' x x' hx']

private theorem uniNCRank_isConjBy_projConj {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {d : GL (Fin 6) K}
    (hdGU : d ∈ LargeEvenGUSet (Fin 6) K (2 ^ f)) :
    IsConjBy d (TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ f))
      ⟨d, TableBUE.gu_subset_normalizer (d := 6) h hdGU⟩) := by
  intro x x' hx
  change TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ f))
      ⟨d, TableBUE.gu_subset_normalizer (d := 6) h hdGU⟩ ((x : LargeEvenProj
        (LargeEvenSUGroup (Fin 6) K (2 ^ f)))) =
    ((x' : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ f))))
  rw [TableB.projConj_mk]
  have hcoe : (((LargeEvenSUGroup (Fin 6) K (2 ^ f)).normalizerMonoidHom
      ⟨d, TableBUE.gu_subset_normalizer (d := 6) h hdGU⟩ x :
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ f))) : GL (Fin 6) K) =
      d * (x : GL (Fin 6) K) * d⁻¹ :=
    CFSG.RankThree.PartOne.S15K.coe_normalizerMonoidHom_apply _ x
  have hx' : (LargeEvenSUGroup (Fin 6) K (2 ^ f)).normalizerMonoidHom
      ⟨d, TableBUE.gu_subset_normalizer (d := 6) h hdGU⟩ x = x' :=
    Subtype.ext (hcoe.trans hx.symm)
  rw [hx']

private theorem uniNCRank_eq_projConj_of_isConjBy {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {d : GL (Fin 6) K}
    (hdGU : d ∈ LargeEvenGUSet (Fin 6) K (2 ^ f))
    {δ' : MulAut (PSUg 6 K (2 ^ f))} (hδ : IsConjBy d δ') :
    δ' = TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ f))
      ⟨d, TableBUE.gu_subset_normalizer (d := 6) h hdGU⟩ :=
  uniNCRank_isConjBy_eq (n := 6) (q := 2 ^ f)
    (fun k hk => (Subgroup.mem_normalizer_iff.mp
      (TableBUE.gu_subset_normalizer (d := 6) h hdGU) k).mp hk) hδ
    (uniNCRank_isConjBy_projConj h hdGU)

theorem uniR_noncube_rank {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) {Ā : Subgroup (MulAut (PSUg 6 K q))} {δ' : MulAut (PSUg 6 K q)}
    {J' : Subgroup (PSUg 6 K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin 6) K)}
    (hL : UniLift 6 q K Ā Ahat) {d : GL (Fin 6) K} (hdA : d ∈ Ahat) {c : Kˣ}
    (hdc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) (hc : c ^ (q + 1) = 1)
    (hnc : ∀ s : Kˣ, s ^ (q + 1) = 1 → s ^ 3 ≠ c) (hδ : IsConjBy d δ') :
    Nat.card Ā ≤ 3 ^ 3 := by
  classical
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnc' : ∀ s : Kˣ, s ^ 3 ≠ c := by
    intro s hs
    have hs3 : (s : K) ^ 3 = (c : K) := by
      have h' := congrArg (fun u : Kˣ => (u : K)) hs
      simpa only [Units.val_pow_eq_pow_val] using h'
    have hcK : (c : K) ^ (2 ^ f + 1) = 1 := by
      have h' := congrArg (fun u : Kˣ => (u : K)) hc
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h'
    have hcbar : h.bar (c : K) * (c : K) = 1 := by
      rw [h.bar_apply, ← pow_succ, hcK]
    have hsbar : h.bar (s : K) * (s : K) = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.CanonU3.norm_eq_one_of_pow_three_eq h hq3 hs3 hcbar
    have hsU : s ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      rw [h.bar_apply, ← pow_succ] at hsbar
      exact hsbar
    exact hnc s hsU hs
  have hmem : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 f K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ f)) := by
    intro a ha
    obtain ⟨g, hgA, hgconj⟩ := hL.onto a ha
    exact ⟨g, uniNCRank_isHermIsometry_mem_guSet h (hL.iso g hgA), hgconj⟩
  have hfield : ∃ a ∈ Ā, CFSG.LocalAnalysis.GLTheoremA.T171Sh.FieldType h a := by
    refine ⟨δ', hR.mem, d, uniNCRank_isHermIsometry_mem_guSet h (hL.iso d hdA), c, hdc, hnc', ?_⟩
    exact uniNCRank_eq_projConj_of_isConjBy h (uniNCRank_isHermIsometry_mem_guSet h (hL.iso d hdA)) hδ
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.u6SizeModel_holds f K h hq3 Ā hR.elem hmem hfield

end UnitaryRank

end CFSG.StandardType.TablePThreeKG

end
