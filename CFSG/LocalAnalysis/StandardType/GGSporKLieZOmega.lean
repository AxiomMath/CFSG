module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZBlockO2
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZQuot
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDict
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockDeg
import CFSG.LocalAnalysis.StandardType.TableC.GramBlockDegree
import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
import CFSG.LinearAlgebra.OrthogonalIdempotentsFinrank
public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
import CFSG.RankThree.GF2n.Smith81.EStmt
import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
import CFSG.RankThree.GF2n.Smith81.TiLane
import CFSG.RankThree.GF2n.Smith81.TiLemmaC
import CFSG.RankThree.GF2n.Stroth80.Consumers
import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec310Main
import CFSG.RankThree.GF2n.Stroth80.Sec45
import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
import Certificates.Certificate9530

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open Matrix
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks

private lemma l937z_om_gram {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    Matrix.transpose (b : Matrix ι ι K) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (b : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  have hg : ∀ v : ι → K, Φ ((b : Matrix ι ι K) *ᵥ v) = Φ v :=
    fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
      (f := ⇑Φ) hb v
  have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
  simpa [CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h

private lemma l937z_om_hSU {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) *
        LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (s : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs]
  simpa [Matrix.map_id] using l937z_om_gram Φ hb

private lemma l937z_om_hS {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (b : GL ι K) :
    ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
  intro s hs s' hs'
  rw [Set.mem_singleton_iff] at hs hs'
  rw [hs, hs']

private lemma l937z_om_cent_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x : ↥(StatedOmega ⇑Φ)) :
    Subgroup.centralizer ({x} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer ({(x : GL ι K)} : Set (GL ι K))).comap
        (StatedOmega ⇑Φ).subtype := by
  ext u
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact congrArg Subtype.val (h x (by simp))
  · intro h v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact Subtype.ext (h (x : GL ι K) (by simp))

private lemma l937z_om_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {x y : Matrix ι ι K}
    (hx : x ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
    (hy : y ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) :
    x * y = y * x := by
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hcommP : (Units.val '' ({b} : Set (GL ι K)) : Set (Matrix ι ι K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs; subst ht
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  have h := mul_comm (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)
  exact congrArg Subtype.val h

private lemma l937z_om_prim_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') : e * e' = 0 := by
  have hA : ∀ x ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))),
      ∀ y ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))), x * y = y * x :=
    fun x hx y hy => l937z_om_commute b hx hy
  have hfA : e * e' ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
    Subalgebra.mul_mem _ he.1 he'.1
  have hfid : IsIdempotentElem (e * e') := by
    rw [isIdempotentElem_iff]
    calc (e * e') * (e * e') = e * (e' * (e * e')) := by rw [mul_assoc]
      _ = e * ((e' * e) * e') := by rw [mul_assoc]
      _ = e * ((e * e') * e') := by rw [hA e' he'.1 e he.1]
      _ = e * (e * (e' * e')) := by rw [mul_assoc]
      _ = (e * e) * (e' * e') := by rw [mul_assoc]
      _ = e * e' := by rw [he.2.1.eq, he'.2.1.eq]
  have hfe : (e * e') * e = e * e' := by
    rw [mul_assoc, hA e' he'.1 e he.1, ← mul_assoc, he.2.1.eq]
  have hfe' : (e * e') * e' = e * e' := by
    rw [mul_assoc, he'.2.1.eq]
  rcases he.2.2.2 (e * e') hfA hfid hfe with h0 | hee
  · exact h0
  · rcases he'.2.2.2 (e * e') hfA hfid hfe' with h0 | hee'
    · exact h0
    · exact absurd (hee.symm.trans hee') hne

private lemma l937z_om_finrank_range_ne_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {e : Matrix ι ι K} (he : e ≠ 0) :
    Module.finrank K (LinearMap.range (Matrix.toLin' e)) ≠ 0 := by
  intro h
  have hbot : LinearMap.range (Matrix.toLin' e) = ⊥ := (Submodule.finrank_eq_zero).mp h
  have hzero : Matrix.toLin' e = 0 := (LinearMap.range_eq_bot).mp hbot
  exact he (Matrix.toLin'.injective (by simpa using hzero))

private lemma l937z_om_rank_sum {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {P : Finset (Matrix ι ι K)} (hidem : ∀ ε ∈ P, IsIdempotentElem ε)
    (horth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hsum : ∑ ε ∈ P, ε = 1) :
    ∑ ε ∈ P, Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = Fintype.card ι := by
  classical
  let e : {ε // ε ∈ P} → Module.End K (ι → K) := fun ε => Matrix.toLin' (ε : Matrix ι ι K)
  have hidem' : ∀ i, IsIdempotentElem (e i) := by
    intro i
    change IsIdempotentElem (Matrix.toLin' (i : Matrix ι ι K))
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, (hidem i i.2).eq]
  have horth' : Pairwise (e · * e · = 0) := by
    intro i j hij
    change Matrix.toLin' (i : Matrix ι ι K) * Matrix.toLin' (j : Matrix ι ι K) = 0
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      horth i i.2 j j.2 (fun h => hij (Subtype.ext h)), map_zero]
  have hOrth : OrthogonalIdempotents e := ⟨hidem', horth'⟩
  have hInd : iSupIndep fun i => LinearMap.range (e i) := by
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨u, rfl⟩ := hv
    have hle : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (e j)) ≤ LinearMap.ker (e i) :=
      iSup₂_le fun j hj => by
        rintro _ ⟨w, rfl⟩
        rw [LinearMap.mem_ker, ← Module.End.mul_apply, hOrth.ortho (Ne.symm hj),
          LinearMap.zero_apply]
    have h1 := hle hv'
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, (hOrth.idem i).eq] at h1
    exact h1
  have hsum_matrix : (∑ i : {ε // ε ∈ P}, (i : Matrix ι ι K)) = 1 := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach P (fun x : Matrix ι ι K => x), hsum]
  have hsup : (⨆ i, LinearMap.range (e i)) = ⊤ := by
    apply le_antisymm le_top
    intro v hv
    have hv' : v = ∑ i : {ε // ε ∈ P}, (i : Matrix ι ι K) *ᵥ v := by
      rw [← Matrix.sum_mulVec Finset.univ (fun i : {ε // ε ∈ P} => (i : Matrix ι ι K)) v,
        hsum_matrix, Matrix.one_mulVec]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
      ⟨v, Matrix.toLin'_apply (i : Matrix ι ι K) v⟩
  have hfin := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hInd
  rw [hsup, finrank_top] at hfin
  have hfin' : (∑ i : {ε // ε ∈ P}, Module.finrank K
      (LinearMap.range (Matrix.toLin' (i : Matrix ι ι K)))) = Fintype.card ι := by
    have h := hfin
    rw [Module.finrank_fintype_fun_eq_card] at h
    simpa [e] using h.symm
  rwa [Finset.univ_eq_attach, Finset.sum_attach P
    (fun x : Matrix ι ι K => Module.finrank K (LinearMap.range (Matrix.toLin' x)))] at hfin'

private lemma l937z_om_exists_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) {b : GL ι K}
    (hb : b ∈ StatedOmega ⇑Φ) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧
        formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠ e ∧
        ε = e + formAdj (RingHom.id K)
          (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e)) := by
  refine CFSG.StandardType.ClassicalPosition.exists_isPrimIdemIn_of_isPrimAdjIdemIn
    (RingHom.id K) (fun _ => rfl) ?_ ?_ (l937z_om_hS b) (l937z_om_hSU Φ hb) hε
  · simpa [Matrix.map_id] using TableC.polarGram_isUnit_det Φ hΦ
  · simpa [Matrix.map_id] using TableC.polarGram_transpose Φ

private lemma l937z_om_unique_one_block {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) {b : GL ι K}
    (hb : b ∈ StatedOmega ⇑Φ) (hb7 : orderOf b = 7)
    {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    {ε ε' : Matrix ι ι K} (hε : ε ∈ P) (hε' : ε' ∈ P)
    (h1 : (b : Matrix ι ι K) * ε = ε) (h1' : (b : Matrix ι ι K) * ε' = ε') :
    ε = ε' := by
  classical
  have hodd : Odd (orderOf b) := by rw [hb7]; norm_num
  by_contra hne
  obtain ⟨e, he, heε, _⟩ := l937z_om_exists_prim Φ hΦ hb (hP ε hε)
  obtain ⟨e', he', he'ε', _⟩ := l937z_om_exists_prim Φ hΦ hb (hP ε' hε')
  have hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
    Algebra.subset_adjoin (by simp)
  have he1 : (b : Matrix ι ι K) * e = e := by
    calc (b : Matrix ι ι K) * e = (b : Matrix ι ι K) * (e * ε) := by rw [heε]
      _ = ((b : Matrix ι ι K) * e) * ε := by rw [mul_assoc]
      _ = (e * (b : Matrix ι ι K)) * ε := by rw [l937z_om_commute b hbA he.1]
      _ = e * ((b : Matrix ι ι K) * ε) := by rw [mul_assoc]
      _ = e * ε := by rw [h1]
      _ = e := heε
  have he1' : (b : Matrix ι ι K) * e' = e' := by
    calc (b : Matrix ι ι K) * e' = (b : Matrix ι ι K) * (e' * ε') := by rw [he'ε']
      _ = ((b : Matrix ι ι K) * e') * ε' := by rw [mul_assoc]
      _ = (e' * (b : Matrix ι ι K)) * ε' := by rw [l937z_om_commute b hbA he'.1]
      _ = e' * ((b : Matrix ι ι K) * ε') := by rw [mul_assoc]
      _ = e' * ε' := by rw [h1']
      _ = e' := he'ε'
  have hee' : e ≠ e' := by
    intro heq
    have heε' : e * ε' = e := by rw [heq, he'ε']
    have h0 : e = 0 := by
      calc e = e * ε := heε.symm
        _ = (e * ε') * ε := by rw [heε']
        _ = e * (ε' * ε) := by rw [mul_assoc]
        _ = e * 0 := by rw [hPorth ε' hε' ε hε (Ne.symm hne)]
        _ = 0 := mul_zero e
    exact he.2.2.1 h0
  have horth : e * e' = 0 := l937z_om_prim_orthogonal b he he' hee'
  have hpos : eigDimOn (b : Matrix ι ι K) e 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 he1]
    exact l937z_om_finrank_range_ne_zero he.2.2.1
  have hpos' : eigDimOn (b : Matrix ι ι K) e' 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he').1 he1']
    exact l937z_om_finrank_range_ne_zero he'.2.2.1
  rcases eigDimOn_eq_zero_or_of_mul_eq_zero he he' horth 1 with h0 | h0
  · exact hpos h0
  · exact hpos' h0

private lemma l937z_om_nontrivial_block_data {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hK : Fintype.card K = 2) (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hb7 : orderOf b = 7)
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E),
      Fintype.card E = Fintype.card K ^ 3 ∧
      6 * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E) := by
  have hodd : Odd (orderOf b) := by rw [hb7]; norm_num
  obtain ⟨e, he, heε, hcase⟩ := l937z_om_exists_prim Φ hΦ hb hε
  have hsp : ∀ s ∈ ({b} : Set (GL ι K)), s ^ 7 = 1 := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs, ← hb7]
    exact pow_orderOf_eq_one b
  have hdich := TableC.blockDegree_trivial_or_eq_orderOf_gram K (by norm_num : Nat.Prime 7)
    (by norm_num : (7 : ℕ) ≠ 2) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
    (TableC.polarGram_transpose Φ) (TableC.polarGram_isUnit_det Φ hΦ)
    (l937z_om_hSU Φ hb) (l937z_om_hS b) hsp he
  have horder : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 3)]
    refine ⟨by decide, ?_⟩
    intro m hm hm3
    have hm2 : m = 1 ∨ m = 2 := by omega
    rcases hm2 with rfl | rfl <;> decide
  have hK' : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
  rcases hcase with heq | ⟨hne, hneadj, hεeq⟩
  · exfalso
    have hfe : formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e = e := by
      rw [heq]; exact hε.2.2.2.1
    rcases hdich with ⟨hfix, -, hadj⟩ | ⟨-, -, hadjiff⟩
    · exact h1 (heq ▸ hfix b (by simp))
    · have hEven : Even (orderOf ((Nat.card K : ℕ) : ZMod 7)) := hadjiff.mp hfe
      rw [hK', horder] at hEven
      exact (by decide : ¬ Even 3) hEven
  · have he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))))
        (formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) :=
      TableC.isPrimIdemIn_formAdj_gram K (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (TableC.polarGram_transpose Φ) (TableC.polarGram_isUnit_det Φ hΦ)
        (l937z_om_hSU Φ hb) (l937z_om_hS b) he
    have hne' : e ≠ formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := fun h => hneadj h.symm
    obtain ⟨d, m, E, hEfield, hEfin, h1d, hcardE, hdim, hdeg, hEiso⟩ :=
      blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd hε he he' hne' hεeq
    have hd3 : d = 3 := by
      rcases hdich with ⟨hfix, -, hadj⟩ | ⟨-, hdegmoved, -⟩
      · exact absurd hadj hneadj
      · rw [← hdeg, hdegmoved, hK', horder]
    refine ⟨m, E, hEfield, hEfin, ?_, ?_, hEiso⟩
    · rw [hcardE, hd3]
    · rw [← hdim, hd3]

private lemma l937z_om_one_block_rank {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hK : Fintype.card K = 2) (hι : Fintype.card ι = 12) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hb7 : orderOf b = 7)
    {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hPsum : ∑ ε ∈ P, ε = 1)
    {ε : Matrix ι ι K} (hε : ε ∈ P) (h1 : (b : Matrix ι ι K) * ε = ε) :
    Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 0 ∨
      6 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
  classical
  have hrank := l937z_om_rank_sum (fun ε hε => (hP ε hε).2.1) hPorth hPsum
  have hsplit : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) +
      ∑ ε' ∈ P.erase ε, Module.finrank K (LinearMap.range (Matrix.toLin' ε')) = 12 := by
    rw [add_comm, Finset.sum_erase_add P (fun ε' => Module.finrank K
        (LinearMap.range (Matrix.toLin' ε'))) hε, hrank, hι]
  have hdvd : 6 ∣ ∑ ε' ∈ P.erase ε,
      Module.finrank K (LinearMap.range (Matrix.toLin' ε')) := by
    apply Finset.dvd_sum
    intro ε' hε'
    rw [Finset.mem_erase] at hε'
    obtain ⟨hne, hε'P⟩ := hε'
    have h1' : (b : Matrix ι ι K) * ε' ≠ ε' := by
      intro h
      exact hne (l937z_om_unique_one_block Φ hΦ hb hb7 hP hPorth hε'P hε h h1)
    obtain ⟨m, E, hEfield, hEfin, hcardE, hmul, -⟩ :=
      l937z_om_nontrivial_block_data Φ hΦ h8 hK b hb hb7 (hP ε' hε'P) h1'
    exact ⟨m, hmul.symm⟩
  obtain ⟨k, hk⟩ := hdvd
  have hle : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ≤ 12 := by
    calc Module.finrank K (LinearMap.range (Matrix.toLin' ε))
        ≤ Module.finrank K (ι → K) := Submodule.finrank_le _
      _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
      _ = 12 := hι
  rw [hk] at hsplit
  omega

private lemma l937z_om_pCoreOf_eq_bot_iff {G : Type} [Group G] (H : Subgroup G) :
    pCoreOf 2 H = ⊥ ↔ pCore 2 ↥H = ⊥ := by
  have hinj := Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [pCoreOf, ← Subgroup.map_bot (f := H.subtype), hinj.eq_iff]

private lemma l937z_om_block_O2 {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (hK : Fintype.card K = 2) (hι : Fintype.card ι = 12) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hb7 : orderOf b = 7)
    {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hPsum : ∑ ε ∈ P, ε = 1)
    {ε : Matrix ι ι K} (hε : ε ∈ P) :
    pCoreOf 2 (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) = ⊥ := by
  have hodd : Odd (orderOf b) := by rw [hb7]; norm_num
  by_cases h1 : (b : Matrix ι ι K) * ε = ε
  · obtain ⟨ι₁, hFintype₁, hDecEq₁, Q₁, hcardι₁, hform, hdisj⟩ :=
      blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd (hP ε hε) h1
    have hrank := l937z_om_one_block_rank Φ hΦ h8 hK hι b hb hb7 hP hPorth hPsum hε h1
    have hd : Fintype.card ι₁ = 0 ∨ 6 ≤ Fintype.card ι₁ := by
      rw [hcardι₁]; exact hrank
    obtain ⟨Φ₁, hΦ₁eq, hΦ₁nd⟩ := hform
    have hfirst : Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(StatedOmega Q₁)) := by
      rcases hdisj with h | hexc
      · exact h.1
      · exfalso
        obtain ⟨-, hcard4, -, -⟩ := hexc
        rw [hcardι₁] at hcard4
        rcases hrank with h0 | h6 <;> omega
    obtain ⟨eiso⟩ := hfirst
    have hpcore : pCore 2 ↥(StatedOmega Q₁) = ⊥ := by
      rw [← hΦ₁eq]
      exact pCore_two_StatedOmega_eq_bot Φ₁ hΦ₁nd hd
    have : pCore 2 ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) = ⊥ :=
      pCore_trivial_of_mulEquiv eiso.symm hpcore
    exact (l937z_om_pCoreOf_eq_bot_iff _).mpr this
  · obtain ⟨m, E, hEfield, hEfin, hcardE, hmul, hEiso⟩ :=
      l937z_om_nontrivial_block_data Φ hΦ h8 hK b hb hb7 (hP ε hε) h1
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    have hcharE : CharP E 2 := by
      refine charP_of_card_eq_prime_pow (p := 2) (f := 3) ?_
      rw [hcardE, hK]
    obtain ⟨eiso⟩ := hEiso
    have hpcore : pCore 2 (GL (Fin m) E) = ⊥ := pCore_two_GL_eq_bot m
    have : pCore 2 ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) = ⊥ :=
      pCore_trivial_of_mulEquiv eiso.symm hpcore
    exact (l937z_om_pCoreOf_eq_bot_iff _).mpr this

theorem pCoreSevenTrivial_StatedOmega_twelve {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (hK : Fintype.card K = 2) (hι : Fintype.card ι = 12)
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    PCoreSevenTrivial ↥(StatedOmega ⇑Φ) := by
  intro x hx
  have h8 : 8 ≤ Fintype.card ι := by rw [hι]; norm_num
  set b : GL ι K := (x : GL ι K) with hbdef
  have hb : b ∈ StatedOmega ⇑Φ := x.2
  have hb7 : orderOf b = 7 := by rw [hbdef, Subgroup.orderOf_coe, hx]
  have hodd : Odd (orderOf b) := by rw [hb7]; norm_num
  obtain ⟨P, hPprim, hPorth, hPsum, hPcomm, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hcent : Subgroup.centralizer ({x} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype := by
    rw [hbdef]
    exact l937z_om_cent_eq Φ x
  have hle : ∀ ε ∈ P, glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε ≤
      (Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype := by
    intro ε hε
    rw [← hPsup]
    exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
  have hO2 : ∀ ε ∈ P,
      pCoreOf 2 (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) = ⊥ :=
    fun ε hε => l937z_om_block_O2 Φ hΦ h8 hK hι b hb hb7 hPprim hPorth hPsum hε
  have hbot := pCore_trivial_of_commutingProduct
    ((Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype)
    P (fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)
    hle hPcomm hPsup hPcard hO2
  rw [hcent]
  exact hbot

private lemma l937z_om_scalars_coprime {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.Coprime 14 (Nat.card ↥((StatedScalars (Fin 6 ⊕ Fin 6) K).subgroupOf
      (StatedOmega (StatedQuadPlus 6 K)))) := by
  have hdvd := card_statedScalars_subgroupOf_dvd (K := K) (StatedOmega (StatedQuadPlus 6 K))
  rw [hK] at hdvd
  have h1 : Nat.card ↥((StatedScalars (Fin 6 ⊕ Fin 6) K).subgroupOf
      (StatedOmega (StatedQuadPlus 6 K))) = 1 := Nat.dvd_one.mp hdvd
  rw [h1]
  norm_num

theorem lieZRow_POmegaPlus_twelve {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    LieZRow (StatedProj (StatedOmega (StatedQuadPlus 6 K))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hKfin : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 1) (by rw [hKfin]; norm_num)
  have hΩeq : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadPlus 6 K) =
      StatedOmega (StatedQuadPlus 6 K) := by
    rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
  have hpcore_quad : PCoreSevenTrivial
      ↥(StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadPlus 6 K)) :=
    pCoreSevenTrivial_StatedOmega_twelve (ι := Fin 6 ⊕ Fin 6) hKfin (by simp)
      (CFSG.LieType.Universal.Spin.quadPlus 6 K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 K)
  have hpcore : PCoreSevenTrivial ↥(StatedOmega (StatedQuadPlus 6 K)) :=
    pCoreSevenTrivial_of_mulEquiv (MulEquiv.subgroupCongr hΩeq) hpcore_quad
  have hrow : LieZRow ↥(StatedOmega (StatedQuadPlus 6 K)) :=
    lieZRow_of_pCoreSevenTrivial hpcore
  exact lieZRow_statedProj (StatedOmega (StatedQuadPlus 6 K)) (l937z_om_scalars_coprime hK) hrow

end CFSG.StandardType.SporadicShape
