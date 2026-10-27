module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveCharpoly
public import CFSG.LieType.SeitzGeneration.ExcTorusUntw
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice Polynomial
open scoped Matrix

namespace NoOffE8Five

section LangTorusOrder

variable {L : Type} [Field L]

theorem natCard_twistedTorus_E8W [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hℓq : ℓ ∣ q) :
    Nat.card (twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr) =
      (q * q + 1) ^ 4 := by
  classical
  set M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
    wordMat Tag.E8 NoOffRest.wordE8W with hM
  have hw : ∀ u : Fin Tag.E8.rank → ℤ, NoOffRest.weylE8W • u = M *ᵥ u := by
    intro u
    rw [hM]
    exact wordProd_smul_eq_wordMat_mulVec Tag.E8 NoOffRest.wordE8W u
  have hT0 : twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr =
      (fixedCharTuples M Fr).map (rootDiagUnitHom Tag.E8 L) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  have hcharpoly : M.charpoly = cyclotomic 4 ℤ ^ 4 := by
    rw [hM, e8W_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  have hcyc : (cyclotomic 4 ℤ).eval (q : ℤ) = (q : ℤ) ^ 2 + 1 := by
    rw [CFSG.LieType.SeitzGeneration.cyclotomic_four_eq]
    simp
  have hev : M.charpoly.eval (q : ℤ) ≠ 0 := by
    rw [hcharpoly, Polynomial.eval_pow, hcyc]
    exact pow_ne_zero 4 (ne_of_gt (by positivity : (0 : ℤ) < (q : ℤ) ^ 2 + 1))
  have hdetB : (M - (q : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)).det.natAbs =
      (M.charpoly.eval (q : ℤ)).natAbs :=
    (CFSG.LieType.SeitzGeneration.natAbs_eval_charpoly M (q : ℤ)).symm
  have hBne : (M - (q : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)).det ≠ 0 :=
    fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := CFSG.LieType.SeitzGeneration.not_dvd_natAbs_det_sub (Fact.out : ℓ.Prime) hℓq M
    (n := 4) (by norm_num) (by rw [hM]; exact e8W_pow)
  have hcard : Nat.card (twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W)
      Fr) = (M.charpoly.eval (q : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      CFSG.LieType.SeitzGeneration.natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  rw [hcard]
  have hval : M.charpoly.eval (q : ℤ) = ((q * q + 1 : ℕ) : ℤ) ^ 4 := by
    rw [hcharpoly, Polynomial.eval_pow, CFSG.LieType.SeitzGeneration.cyclotomic_four_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    push_cast
    ring
  rw [hval, Int.natAbs_pow, Int.natAbs_natCast]

theorem conj_mem_adjEmb_range_of_mem_twistedTorus {K : Type} [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (hℓK : ℓ ∣ Nat.card K)
    {g₀ : ModGL Tag.E8 L} (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) {x : ModGL Tag.E8 L}
    (hx : x ∈ twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr) :
    g₀ * x * g₀⁻¹ ∈ (adjEmb Tag.E8 K L).range := by
  classical
  set n : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W with hn
  have hx' : x ∈ twistedTorus n Fr := by rw [hn]; exact hx
  have hg₀' : Units.map (entrywiseHom Fr) g₀ = g₀ * n := by rw [hn]; exact hg₀
  set X : Subgroup (ModGL Tag.E8 L) :=
    (twistedTorus n Fr).map (MulAut.conj g₀).toMonoidHom with hX
  have hcardT : Nat.card (twistedTorus n Fr) = (Nat.card K * Nat.card K + 1) ^ 4 := by
    rw [hn]
    exact natCard_twistedTorus_E8W (L := L) (ℓ := ℓ) (Fr := Fr) (q := Nat.card K) hFr hℓK
  haveI hTfin : Finite (twistedTorus n Fr) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero _ (Nat.succ_ne_zero _))
  haveI hXfin : Finite X :=
    Finite.of_surjective ((MulAut.conj g₀).toMonoidHom.subgroupMap (twistedTorus n Fr))
      ((MulAut.conj g₀).toMonoidHom.subgroupMap_surjective (twistedTorus n Fr))
  have hXC : X ≤ adjointGroup Tag.E8 L := by
    rw [hX]
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg₀C
      (twistedTorusOf_le_adjointGroup n (Units.map (entrywiseHom Fr)) hy)) (inv_mem hg₀C)
  have hXF : ∀ y ∈ X, Units.map (entrywiseHom Fr) y = y := by
    intro y hy
    rw [hX] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzfix := (mem_twistedTorus.1 hz).2
    change Units.map (entrywiseHom Fr) (g₀ * z * g₀⁻¹) = g₀ * z * g₀⁻¹
    rw [map_mul, map_mul, map_inv, hg₀']
    calc g₀ * n * Units.map (entrywiseHom Fr) z * (g₀ * n)⁻¹
        = g₀ * (n * Units.map (entrywiseHom Fr) z * n⁻¹) * g₀⁻¹ := by group
      _ = g₀ * z * g₀⁻¹ := by rw [hzfix]
  have hrel :=
    (finite_fixed_subgroup_rational 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1
  have hle : X ≤ (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← Subgroup.relIndex_eq_one]
    exact Nat.dvd_one.1 hrel
  rw [adjEmb_range]
  exact hle (by rw [hX]; exact Subgroup.mem_map.2 ⟨x, hx', rfl⟩)

end LangTorusOrder

end NoOffE8Five

end CFSG.StandardType
