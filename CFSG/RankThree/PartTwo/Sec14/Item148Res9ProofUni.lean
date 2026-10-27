module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def suToSL3 (h : UnitaryFieldData p f K) :
    unitarySU p f K 3 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ((mem_unitarySU_iff h).1 g.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_suToSL3 (h : UnitaryFieldData p f K) (g : unitarySU p f K 3) :
    ((suToSL3 h g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem unitaryScalars_le_comap (h : UnitaryFieldData p f K) :
    unitaryScalars h 3 ≤ (scalars 3 K).comap (suToSL3 h) := by
  rintro g ⟨c, -, hc3, hgc⟩
  refine ⟨c, hc3, ?_⟩
  rw [coe_suToSL3, hgc, GeneralLinearGroup.coe_scalar]

@[expose] noncomputable def psuToPSL3 (h : UnitaryFieldData p f K) :
    unitaryPSU h 3 →* projectiveSL 3 K :=
  QuotientGroup.map _ _ (suToSL3 h) (unitaryScalars_le_comap h)

theorem psuToPSL3_mk (h : UnitaryFieldData p f K) (g : unitarySU p f K 3) :
    psuToPSL3 h (g : unitaryPSU h 3) = proj 3 K (suToSL3 h g) :=
  rfl

theorem psuToPSL3_injective (h : UnitaryFieldData p f K) :
    Function.Injective (psuToPSL3 h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psuToPSL3_mk, proj_eq_one_iff] at hx
  obtain ⟨c, -, hgc⟩ := hx
  rw [QuotientGroup.eq_one_iff, unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf]
  refine ⟨c, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, ← hgc, coe_suToSL3]

theorem psuToPSL3_psuConj (h : UnitaryFieldData p f K) (A : unitaryIsom3 h)
    (x : unitaryPSU h 3) :
    psuToPSL3 h (psuConj h A x) = conjAut 3 K (A : GL (Fin 3) K) (psuToPSL3 h x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psuConj_mk, psuToPSL3_mk, psuToPSL3_mk, conjAut_proj]
  congr 1
  apply Subtype.ext
  change ((suToSL3 h (suConj h A g) : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_slConjugation, coe_suToSL3, coe_suToSL3, coe_suConj, Units.val_mul, Units.val_mul]
  rfl

theorem psuConj_eq_one_of_fixes (h : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0)
    (B : unitaryIsom3 h) {n : ℕ} (hn : (n : K) ≠ 0) (hBn : psuConj h B ^ n = 1)
    (R : Subgroup (unitaryPSU h 3)) (hR : IsPGroup p R)
    (hfix : ∀ r ∈ R, psuConj h B r = r) {u v : unitaryPSU h 3} (hu : u ∈ R) (hv : v ∈ R)
    (huv : u * v ≠ v * u) : psuConj h B = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have := h.charP
  have hBn' : conjAut 3 K (B : GL (Fin 3) K) ^ n = 1 := by
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one (B ^ n) 1
      (by rw [map_one, mul_one, map_pow, hBn])
    rw [← map_pow, ← Subgroup.coe_pow, hc, conjAut_scalar]
  have hinj := psuToPSL3_injective h
  have h1 := conjAut_eq_one_of_fixes p h3 (B : GL (Fin 3) K) hn hBn' (R.map (psuToPSL3 h))
    (hR.map _) (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← psuToPSL3_psuConj, hfix r hr]) (Subgroup.mem_map_of_mem _ hu)
    (Subgroup.mem_map_of_mem _ hv) (by
      rw [← map_mul, ← map_mul]
      exact fun h' => huv (hinj h'))
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (B : GL (Fin 3) K) 1
    (by rw [map_one, mul_one, h1])
  have hcB : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := hc ▸ B.2
  have hB : B = ⟨_, hcB⟩ := Subtype.ext hc.symm
  rw [hB, psuConj_scalar]

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
