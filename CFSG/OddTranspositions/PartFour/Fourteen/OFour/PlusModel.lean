module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.PlusTau
import CFSG.GroupTheory.CommutatorIndexTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open CFSG.LieType.BorelTits Matrix CFSG.Open

variable {F : Type} [Field F]

@[expose] noncomputable def plusN : Subgroup ↥(CFSG.PGLModel.orthogonalPlus 2 F) :=
  (jProd (F := F)).range.subgroupOf (CFSG.PGLModel.orthogonalPlus 2 F)

theorem mem_plusN_iff {g : ↥(CFSG.PGLModel.orthogonalPlus 2 F)} :
    g ∈ plusN ↔ ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F,
      j1 a * j2 b = (g : GL (Fin 2 ⊕ Fin 2) F) := by
  rw [plusN, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    exact ⟨a, b, by rw [← hab, jProd_apply]⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨(a, b), by rw [jProd_apply, hab]⟩

theorem index_plusN [Finite F] [CharP F 2] : (plusN (F := F)).index = 2 :=
  relIndex_jProd_range (F := F)

theorem plusN_normal [Finite F] [CharP F 2] : (plusN (F := F)).Normal :=
  Subgroup.normal_of_index_eq_two (index_plusN (F := F))

theorem jProd_range_le_orthogonalPlus :
    (jProd (F := F)).range ≤ CFSG.PGLModel.orthogonalPlus 2 F := by
  rintro _ ⟨x, rfl⟩
  exact jProd_mem_orthGroup x

@[expose] noncomputable def plusNEquiv [CharP F 2] :
    (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) ≃*
      ↥(plusN (F := F)) :=
  (MonoidHom.ofInjective (jProd_injective (F := F))).trans
    (Subgroup.subgroupOfEquivOfLe (jProd_range_le_orthogonalPlus (F := F))).symm

theorem commutator_plusN_eq_top [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    commutator ↥(plusN (F := F)) = ⊤ := by
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
    Group.isPerfect_def.1 (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4).1
  have hSL' : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), ⊤⁆ = ⊤ := hSL
  have hprod : commutator (Matrix.SpecialLinearGroup (Fin 2) F ×
      Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ := by
    rw [commutator_def, ← Subgroup.top_prod_top
      (G := Matrix.SpecialLinearGroup (Fin 2) F)
      (N := Matrix.SpecialLinearGroup (Fin 2) F),
      Subgroup.commutator_prod_prod, hSL']
  have hmap : (commutator (Matrix.SpecialLinearGroup (Fin 2) F ×
      Matrix.SpecialLinearGroup (Fin 2) F)).map (plusNEquiv (F := F)) =
      commutator ↥(plusN (F := F)) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_equiv_top]
    rfl
  rw [← hmap, hprod, Subgroup.map_equiv_top]

theorem commutator_orthogonalPlus_two [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    commutator ↥(CFSG.PGLModel.orthogonalPlus 2 F) = plusN (F := F) :=
  CFSG.GroupTheory.commutator_eq_of_index_two_of_commutator_eq_top (index_plusN (F := F))
    (commutator_plusN_eq_top h4)

@[expose] noncomputable def tauO : ↥(CFSG.PGLModel.orthogonalPlus 2 F) :=
  ⟨tauMat, tauMat_mem_orthGroup⟩

theorem tauO_not_mem_plusN [CharP F 2] : tauO (F := F) ∉ plusN := by
  intro h
  rw [mem_plusN_iff] at h
  obtain ⟨a, b, hab⟩ := h
  exact tauMat_not_mem_range (F := F) ⟨(a, b), by rw [jProd_apply, hab]; rfl⟩

theorem tauMat_mul_j2 (b : Matrix.SpecialLinearGroup (Fin 2) F) :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) * j2 b = j1 b * tauMat := by
  rw [← tau_conj_j2 b, mul_assoc, tauMat_mul_self, mul_one]

local notation "x[" c "]" =>
  Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c

@[expose] noncomputable def tauC (c : F) : ↥(CFSG.PGLModel.orthogonalPlus 2 F) :=
  ⟨j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹,
    mul_mem (mul_mem (j1_mem_orthGroup _) tauMat_mem_orthGroup)
      (inv_mem (j1_mem_orthGroup _))⟩

@[expose] noncomputable def j12 (c : F) : ↥(CFSG.PGLModel.orthogonalPlus 2 F) :=
  ⟨j1 (x[c]) * j2 (x[c]),
    mul_mem (j1_mem_orthGroup _) (j2_mem_orthGroup _)⟩

theorem tauC_mul_GL [CharP F 2] (c d : F) :
    (j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹) * (j1 (x[d]) * tauMat * (j1 (x[d]))⁻¹) =
      j1 (x[c + d]) * j2 (x[c + d]) := by
  have hneg : (x[(c : F)])⁻¹ = x[c] := by
    rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  have hnegd : (x[(d : F)])⁻¹ = x[d] := by
    rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  have hcd : (j1 (x[c]))⁻¹ * j1 (x[d]) = j1 (x[c + d]) := by
    rw [← map_inv, hneg, ← map_mul, ← Matrix.SpecialLinearGroup.transvection_add]
  have hd : (j1 (x[d]))⁻¹ = j1 (x[d]) := by rw [← map_inv, hnegd]
  have hcomm : Commute (j2 (x[c + d])) ((j1 (x[d]))⁻¹) := by
    rw [hd]
    exact (j1_j2_commute (x[d]) (x[c + d])).symm
  calc (j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹) *
        (j1 (x[d]) * tauMat * (j1 (x[d]))⁻¹)
      = j1 (x[c]) * tauMat * ((j1 (x[c]))⁻¹ * j1 (x[d])) * tauMat *
          (j1 (x[d]))⁻¹ := by simp only [mul_assoc]
    _ = j1 (x[c]) * tauMat * j1 (x[c + d]) * tauMat * (j1 (x[d]))⁻¹ := by rw [hcd]
    _ = j1 (x[c]) * (tauMat * j1 (x[c + d]) * tauMat) * (j1 (x[d]))⁻¹ := by
          simp only [mul_assoc]
    _ = j1 (x[c]) * j2 (x[c + d]) * (j1 (x[d]))⁻¹ := by rw [tau_conj_j1]
    _ = j1 (x[c]) * (j1 (x[d]))⁻¹ * j2 (x[c + d]) := by
          rw [mul_assoc, hcomm.eq, ← mul_assoc]
    _ = j1 (x[c] * (x[d])⁻¹) * j2 (x[c + d]) := by rw [map_mul, map_inv]
    _ = j1 (x[c] * x[d]) * j2 (x[c + d]) := by rw [hnegd]
    _ = j1 (x[c + d]) * j2 (x[c + d]) := by
          rw [← Matrix.SpecialLinearGroup.transvection_add]

theorem tauC_zero : tauC (F := F) 0 = tauO := by
  have h0 : x[(0 : F)] = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.transvection_coe]
    simp
  refine Subtype.ext ?_
  show j1 (x[0]) * tauMat * (j1 (x[0]))⁻¹ = tauMat
  rw [h0, map_one, inv_one, one_mul, mul_one]

theorem tauC_mul [CharP F 2] (c d : F) : tauC c * tauC d = j12 (c + d) := by
  refine Subtype.ext ?_
  exact tauC_mul_GL c d

theorem j12_mul_tauC [CharP F 2] (c : F) : j12 c * tauC c = tauO := by
  have hxx : x[(c : F)] * x[c] = 1 := by
    have h := Matrix.SpecialLinearGroup.transvection_mul_neg
      (zero_ne_one : (0 : Fin 2) ≠ 1) c
    rwa [CharTwo.neg_eq] at h
  have haa : j1 (x[c]) * j1 (x[c]) = 1 := by
    rw [← map_mul, hxx, map_one]
  have hbt : j2 (x[c]) * tauMat = tauMat * j1 (x[c]) :=
    (tauMat_mul_j1 (x[c])).symm
  have hab : j1 (x[c]) * j2 (x[c]) = j2 (x[c]) * j1 (x[c]) :=
    (j1_j2_commute _ _).eq
  refine Subtype.ext ?_
  show j1 (x[c]) * j2 (x[c]) * (j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹) = tauMat
  have hx : (j1 (x[c]))⁻¹ = j1 (x[c]) := by
    rw [← map_inv, Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  rw [hx]
  calc j1 (x[c]) * j2 (x[c]) * (j1 (x[c]) * tauMat * j1 (x[c]))
      = (j1 (x[c]) * j2 (x[c])) * (j1 (x[c]) * tauMat * j1 (x[c])) := rfl
    _ = (j2 (x[c]) * j1 (x[c])) * (j1 (x[c]) * tauMat * j1 (x[c])) := by rw [hab]
    _ = j2 (x[c]) * (j1 (x[c]) * j1 (x[c])) * tauMat * j1 (x[c]) := by group
    _ = j2 (x[c]) * tauMat * j1 (x[c]) := by rw [haa, mul_one]
    _ = tauMat * j1 (x[c]) * j1 (x[c]) := by rw [hbt]
    _ = tauMat := by rw [mul_assoc, haa, mul_one]

theorem tauC_commute [CharP F 2] (c d : F) : Commute (tauC c) (tauC d) := by
  show tauC c * tauC d = tauC d * tauC c
  rw [tauC_mul, tauC_mul, add_comm]

theorem isConj_tauC [CharP F 2] (c : F) : IsConj (tauO (F := F)) (tauC c) := by
  let g : ↥(CFSG.PGLModel.orthogonalPlus 2 F) := ⟨j1 (x[c]), j1_mem_orthGroup _⟩
  refine isConj_iff.mpr ⟨g, ?_⟩
  refine Subtype.ext ?_
  rfl

theorem tauC_ne_tauO [CharP F 2] {c : F} (hc : c ≠ 0) : tauC (F := F) c ≠ tauO := by
  intro h
  have h' : j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹ = tauMat := congrArg Subtype.val h
  have h3 : j1 (x[c]) * tauMat = tauMat * j1 (x[c]) := by
    calc j1 (x[c]) * tauMat
        = j1 (x[c]) * tauMat * (j1 (x[c]))⁻¹ * j1 (x[c]) := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = tauMat * j1 (x[c]) := by rw [h']
  rw [tauMat_mul_j1] at h3
  have h2 : j1 (x[c]) = j2 (x[c]) := mul_right_cancel h3
  have hx : x[c] = 1 := (eq_one_of_j1_eq_j2 h2).1
  have hc0 : c = 0 := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) hx
    rw [Matrix.SpecialLinearGroup.transvection_coe] at h
    simpa using h
  exact hc hc0

theorem j1_mul_j2_mul_tau_sq (a b : Matrix.SpecialLinearGroup (Fin 2) F) :
    (j1 a * j2 b * tauMat) * (j1 a * j2 b * tauMat) = j1 (a * b) * j2 (b * a) := by
  have hA : tauMat * j1 a = j2 a * tauMat := tauMat_mul_j1 a
  have hB : tauMat * j2 b = j1 b * tauMat := tauMat_mul_j2 b
  have hAB : j2 b * j2 a = j2 (b * a) := (map_mul j2 b a).symm
  have hcomm : j2 (b * a) * j1 b = j1 b * j2 (b * a) :=
    (j1_j2_commute b (b * a)).symm.eq
  calc (j1 a * j2 b * tauMat) * (j1 a * j2 b * tauMat)
      = j1 a * j2 b * (tauMat * j1 a) * j2 b * tauMat := by group
    _ = j1 a * j2 b * (j2 a * tauMat) * j2 b * tauMat := by rw [hA]
    _ = j1 a * (j2 b * j2 a) * (tauMat * j2 b) * tauMat := by group
    _ = j1 a * (j2 b * j2 a) * (j1 b * tauMat) * tauMat := by rw [hB]
    _ = j1 a * j2 (b * a) * j1 b * (tauMat * tauMat) := by rw [hAB]; group
    _ = j1 a * j2 (b * a) * j1 b := by rw [tauMat_mul_self, mul_one]
    _ = j1 a * (j2 (b * a) * j1 b) := by group
    _ = j1 a * (j1 b * j2 (b * a)) := by rw [hcomm]
    _ = (j1 a * j1 b) * j2 (b * a) := by group
    _ = j1 (a * b) * j2 (b * a) := by rw [← map_mul]

theorem exists_j1_conj_tauMat_of_mul_self_eq_one [Finite F] [CharP F 2]
    {t : ↥(CFSG.PGLModel.orthogonalPlus 2 F)} (ht : t * t = 1) (htN : t ∉ plusN) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) F,
      (t : GL (Fin 2 ⊕ Fin 2) F) = j1 a * tauMat * (j1 a)⁻¹ := by
  have hτN : tauO (F := F) ∉ plusN := tauO_not_mem_plusN
  have hmul : t * tauO ∈ plusN := by
    refine (Subgroup.mul_mem_iff_of_index_two (index_plusN (F := F))).2 ?_
    exact ⟨fun h => absurd h htN, fun h => absurd h hτN⟩
  obtain ⟨a, b, hab⟩ := mem_plusN_iff.1 hmul
  have ht1 : (t : GL (Fin 2 ⊕ Fin 2) F) * tauMat = j1 a * j2 b := by
    rw [hab]
    rfl
  have ht_eq : (t : GL (Fin 2 ⊕ Fin 2) F) = j1 a * j2 b * tauMat := by
    calc (t : GL (Fin 2 ⊕ Fin 2) F)
        = (t : GL (Fin 2 ⊕ Fin 2) F) * tauMat * tauMat := by
            rw [mul_assoc, tauMat_mul_self, mul_one]
      _ = j1 a * j2 b * tauMat := by rw [ht1]
  have htt : (t : GL (Fin 2 ⊕ Fin 2) F) * (t : GL (Fin 2 ⊕ Fin 2) F) = 1 := by
    simpa using congrArg Subtype.val ht
  have hprod : j1 (a * b) * j2 (b * a) = 1 := by
    rw [← j1_mul_j2_mul_tau_sq a b, ← ht_eq]
    exact htt
  have hJ : j1 (a * b) = j2 ((b * a)⁻¹) := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hprod
  obtain ⟨hab1, -⟩ := eq_one_of_j1_eq_j2 hJ
  have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab1
  refine ⟨a, ?_⟩
  rw [ht_eq, hb, show (j1 a)⁻¹ = j1 (a⁻¹) from (map_inv j1 a).symm]
  calc j1 a * j2 a⁻¹ * tauMat
      = j1 a * (j2 a⁻¹ * tauMat) := mul_assoc (j1 a) (j2 a⁻¹) tauMat
    _ = j1 a * (tauMat * j1 (a⁻¹)) := by rw [← tauMat_mul_j1]
    _ = j1 a * tauMat * j1 (a⁻¹) := (mul_assoc (j1 a) tauMat (j1 (a⁻¹))).symm

theorem isConj_tauO_of_mul_self_eq_one [Finite F] [CharP F 2]
    {t : ↥(CFSG.PGLModel.orthogonalPlus 2 F)} (ht : t * t = 1) (htN : t ∉ plusN) :
    IsConj tauO t := by
  obtain ⟨a, ha⟩ := exists_j1_conj_tauMat_of_mul_self_eq_one ht htN
  let g : ↥(CFSG.PGLModel.orthogonalPlus 2 F) := ⟨j1 a, j1_mem_orthGroup a⟩
  refine isConj_iff.mpr ⟨g, ?_⟩
  refine Subtype.ext ?_
  show (g : GL (Fin 2 ⊕ Fin 2) F) * tauMat * (g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) =
    (t : GL (Fin 2 ⊕ Fin 2) F)
  rw [ha]

theorem exists_triple_tauO [CharP F 2] {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    ∃ Λ : Set ↥(CFSG.PGLModel.orthogonalPlus 2 F),
      Λ ⊆ {y | IsConj tauO y} ∧
        (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧
          ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v}) := by
  have h1ω : 1 + ω ≠ 0 := by
    intro h
    apply hω1
    have h' : ω = -1 := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h'
  have hprod : tauC 1 * tauC ω * tauC (1 + ω) = tauC (0 : F) := by
    rw [tauC_mul, j12_mul_tauC]
    exact tauC_zero.symm
  have hmem1 : tauC (F := F) 1 ∈
      ({tauC 0, tauC 1, tauC ω, tauC (1 + ω)} : Set ↥(CFSG.PGLModel.orthogonalPlus 2 F)) \
        {tauC (0 : F)} := by
    refine ⟨by simp, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun h => tauC_ne_tauO one_ne_zero (h.trans tauC_zero)
  have hmemω : tauC (F := F) ω ∈
      ({tauC 0, tauC 1, tauC ω, tauC (1 + ω)} : Set ↥(CFSG.PGLModel.orthogonalPlus 2 F)) \
        {tauC (0 : F)} := by
    refine ⟨by simp, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun h => tauC_ne_tauO hω0 (h.trans tauC_zero)
  have hmem1ω : tauC (F := F) (1 + ω) ∈
      ({tauC 0, tauC 1, tauC ω, tauC (1 + ω)} : Set ↥(CFSG.PGLModel.orthogonalPlus 2 F)) \
        {tauC (0 : F)} := by
    refine ⟨by simp, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun h => tauC_ne_tauO h1ω (h.trans tauC_zero)
  refine ⟨{tauC 0, tauC 1, tauC ω, tauC (1 + ω)}, ?_, ?_, tauC 0, by simp, ?_⟩
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact isConj_tauC 0
    · exact isConj_tauC 1
    · exact isConj_tauC ω
    · exact isConj_tauC (1 + ω)
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      exact tauC_commute _ _
  · have hx : tauC 1 * tauC ω * tauC (1 + ω) ∈
        Subgroup.closure ({tauC 0, tauC 1, tauC ω, tauC (1 + ω)} \
          {tauC (0 : F)}) :=
      mul_mem (mul_mem (Subgroup.subset_closure hmem1) (Subgroup.subset_closure hmemω))
        (Subgroup.subset_closure hmem1ω)
    rwa [hprod] at hx

end CFSG.OddTranspositions.PartFour
