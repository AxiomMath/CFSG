module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinFieldsB
import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinL5
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofUniExt
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofLinear
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Item211Res6Proof
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

@[expose] def modelEquiv : unitaryPSU h 3 ≃* primeFormP h 𝟙 :=
  (QuotientGroup.quotientMulEquivOfEq (proj_isCover h).ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (proj_surjective h))

theorem modelEquiv_mk (g : unitarySU p f F 3) : modelEquiv h (g : unitaryPSU h 3) = proj h g :=
  rfl

@[expose] def linExtend [Finite F] (h5 : 5 ≤ p ^ f) :
    MulAut (primeFormP h 𝟙) →* MulAut (projectiveSL 3 F) :=
  (extAut h (by omega)).comp (MulAut.congr (modelEquiv h).symm).toMonoidHom

theorem linExtend_injective [Finite F] (h5 : 5 ≤ p ^ f) : Function.Injective (linExtend h h5) :=
  (extAut_injective (h := h) (by omega)).comp (MulAut.congr (modelEquiv h).symm).injective

theorem linExtend_conj [Finite F] (h5 : 5 ≤ p ^ f) (g : unitarySU p f F 3) :
    linExtend h h5 (MulAut.conj (proj h g)) = MulAut.conj
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F (suToSL h g)) := by
  rw [linExtend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, ← modelEquiv_mk,
    MulEquiv.symm_apply_apply, extAut_conj, psuToPSL_mk]

theorem modelEquiv_conjHom (A : primeFormUnitary h 𝟙) :
    MulAut.congr (modelEquiv h).symm (primeFormConjHom h 𝟙 A) =
      CFSG.RankThree.PartTwo.KFacts.psuConj h
        ⟨A, by
          rw [CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3]
          simpa only [mem_primeFormUnitary, Units.val_one, Matrix.mul_one] using A.2⟩ := by
  ext x
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  apply (modelEquiv h).injective
  change modelEquiv h ((modelEquiv h).symm
    (primeFormConjHom h 𝟙 A (modelEquiv h (unitaryProj h 3 g)))) = _
  rw [MulEquiv.apply_symm_apply]
  change primeFormConjHom h 𝟙 A (modelEquiv h (g : unitaryPSU h 3)) =
    modelEquiv h (CFSG.RankThree.PartTwo.KFacts.psuConj h _ (g : unitaryPSU h 3))
  rw [modelEquiv_mk, CFSG.RankThree.PartTwo.KFacts.psuConj_mk, modelEquiv_mk]
  change primeFormConjHom h 𝟙 A ((suEquiv h g : gramSU h 𝟙) : primeFormP h 𝟙) = _
  rw [primeFormConjHom_mk]
  congr 1

theorem linExtend_conjHom [Finite F] (h5 : 5 ≤ p ^ f) (A : primeFormUnitary h 𝟙) :
    linExtend h h5 (primeFormConjHom h 𝟙 A) = conjAut 3 F (A : GL (Fin 3) F) := by
  rw [linExtend, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, modelEquiv_conjHom]
  rw [extAut_eq (by omega) (A := ⟨A, by
    rw [CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3]
    simpa only [mem_primeFormUnitary, Units.val_one, Matrix.mul_one] using A.2⟩) (σ := 1)
    (by rw [map_one, mul_one]), map_one, mul_one]

theorem linExtend_e [Finite F] (h5 : 5 ≤ p ^ f) : linExtend h h5 (e h) = L3Lin.eA F := by
  rw [e, ← primeFormConjHom_eq_conj, linExtend_conjHom, L3Lin.eA, ← L3Lin.conjAut_toGL_eq]
  rfl

theorem linExtend_r [Finite F] (h5 : 5 ≤ p ^ f) : linExtend h h5 (r h) = L3Lin.rA F := by
  rw [r, ← primeFormConjHom_eq_conj, linExtend_conjHom, L3Lin.rA, ← L3Lin.conjAut_toGL_eq]
  rfl

theorem linExtend_mem_P [Finite F] (h5 : 5 ≤ p ^ f) {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ P h) :
    linExtend h h5 x ∈ (conjAut 3 F).range := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨A, (linExtend_conjHom h h5 A).symm⟩

theorem linExtend_mem_KS [Finite F] (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Kb h hq) : linExtend h h5 x ∈ L3Lin.KS F := by
  obtain ⟨y, ⟨B, hB⟩, hxy⟩ := hx
  change proj h (Uni.levU hq.pos B) = y at hB
  rw [← hxy, ← hB, linExtend_conj]
  let Bsl : SL(2, F) := ⟨((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
    ((mem_unitarySU_iff h).1 B.2).1⟩
  have hsl : suToSL h (Uni.levU hq.pos B) = CFSG.GH74.KGroups.L3Eps.bSL Bsl := by
    apply Subtype.ext
    rfl
  rw [hsl]
  exact ⟨CFSG.GH74.KGroups.L3Eps.blockEmb Bsl, ⟨Bsl, rfl⟩, rfl⟩

theorem linExtend_blockC [Finite F] (h5 : 5 ≤ p ^ f)
    (B : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F)) :
    linExtend h h5 (blockC h B : MulAut (primeFormP h 𝟙)) = conjAut 3 F (L3Lin.bG (B : GL (Fin 2) F)) := by
  change linExtend h h5 (primeFormConjHom h 𝟙 (blockU h B)) = _
  rw [linExtend_conjHom]
  congr 1

theorem linExtend_mem_ZS [Finite F] (h5 : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0)
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Zb h) : linExtend h h5 x ∈ L3Lin.ZS F := by
  let xc : ↥(C h) := ⟨x, ((mem_Zb h x).1 hx).1⟩
  have hρ := (rho_eq_one h h2 h5 xc).2 hx
  rw [rho_eq_mk_psi, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hρ
  obtain ⟨a, ha⟩ := hρ
  let B : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) := ⟨psi h h2 xc, psi_unitary h h2 xc⟩
  have hb : blockC h B = xc := psi_injective h h2 (psi_blockC h h2 B)
  rw [show x = (blockC h B : MulAut (primeFormP h 𝟙)) from congrArg Subtype.val hb.symm,
    linExtend_blockC]
  have hBA : (B : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) a := ha.symm
  rw [hBA, L3Lin.mem_ZS_iff]
  have hg : L3Lin.bG (GeneralLinearGroup.scalar (Fin 2) a) ∈ L3Lin.CenG F :=
    L3Lin.bG_mem_CenG _
  refine ⟨L3Lin.conjAut_mem_CS hg, ?_⟩
  intro y hy
  obtain ⟨Y, hY⟩ := L3Lin.piC_surjective (⟨y, hy⟩ : ↥(L3Lin.CS F))
  have hye : y = conjAut 3 F (Y : GL (Fin 3) F) := (congrArg Subtype.val hY).symm
  rw [hye, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, L3Lin.coe_bG_scalar]
  obtain ⟨h02, h12, h20, h21⟩ := L3Lin.entries_of_mem_CenG h2 Y.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21] <;> ring

theorem comm_of_comm_Kb [Finite F] (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Kb h hq) (hx1 : x ≠ 1)
    (hxc : Nat.Coprime (orderOf x) (6 * p)) {g : MulAut (primeFormP h 𝟙)} (hg : g ∈ P h)
    (hcomm : g * x = x * g) : g * e h ^ 2 = e h ^ 2 * g := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  apply linExtend_injective h h5
  rw [map_mul, map_mul, map_pow, linExtend_e]
  exact L3Lin.comm_of_comm_KS (linExtend_mem_KS h h5 hq hx)
    ((map_ne_one_iff _ (linExtend_injective h h5)).2 hx1)
    (by rwa [orderOf_injective _ (linExtend_injective h h5)])
    (linExtend_mem_P h h5 hg) (by rw [← map_mul, ← map_mul, hcomm])

theorem comm_of_comm_Zb [Finite F] (h5 : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0)
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Zb h) (hx1 : x ≠ 1)
    {g : MulAut (primeFormP h 𝟙)} (hg : g ∈ P h) (hcomm : g * x = x * g) :
    g * e h ^ 2 = e h ^ 2 * g := by
  apply linExtend_injective h h5
  rw [map_mul, map_mul, map_pow, linExtend_e]
  exact L3Lin.comm_of_comm_ZS h2 (linExtend_mem_ZS h h5 h2 hx)
    ((map_ne_one_iff _ (linExtend_injective h h5)).2 hx1)
    (linExtend_mem_P h h5 hg) (by rw [← map_mul, ← map_mul, hcomm])

theorem not_inv_Zb [Finite F] (h5 : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0)
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Zb h) (hx1 : x ≠ 1) (hodd : Odd (orderOf x))
    {g : MulAut (primeFormP h 𝟙)} (hg : g ∈ P h) : g * x * g⁻¹ ≠ x⁻¹ := by
  intro hInv
  exact L3Lin.not_inv_ZS h2 (linExtend_mem_ZS h h5 h2 hx)
    ((map_ne_one_iff _ (linExtend_injective h h5)).2 hx1)
    (by rwa [orderOf_injective _ (linExtend_injective h h5)])
    (linExtend_mem_P h h5 hg) (by rw [← map_inv, ← map_mul, ← map_mul, hInv, map_inv])

theorem comm_of_abelian [Finite F] (h5 : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (hp3 : p ≠ 3)
    {A B : Subgroup (MulAut (primeFormP h 𝟙))} (hAB : A ≤ B) (hBP : B ≤ P h)
    (hBab : IsMulCommutative ↥B) (h3B : 3 ∣ Nat.card B) (h6 : Nat.Coprime (Nat.card A) 6)
    (he : e h ∈ normalizer (A : Set (MulAut (primeFormP h 𝟙))))
    (hr : r h ∈ normalizer (A : Set (MulAut (primeFormP h 𝟙)))) :
    ∀ a ∈ A, a * e h ^ 2 = e h ^ 2 * a := by
  have : CharP F p := h.charP
  let Φ := linExtend h h5
  have hinj : Function.Injective Φ := linExtend_injective h h5
  let A' := A.map Φ
  let B' := B.map Φ
  have hB'ab : IsMulCommutative ↥B' := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨x₀, hx₀, hxe⟩ := x.2
    obtain ⟨y₀, hy₀, hye⟩ := y.2
    have he := congrArg Subtype.val (hBab.is_comm.comm (⟨x₀, hx₀⟩ : ↥B) ⟨y₀, hy₀⟩)
    change x₀ * y₀ = y₀ * x₀ at he
    change (x : MulAut (projectiveSL 3 F)) * y = (y : MulAut (projectiveSL 3 F)) * x
    rw [← hxe, ← hye, ← map_mul, ← map_mul, he]
  have hB'P : B' ≤ (conjAut 3 F).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact linExtend_mem_P h h5 (hBP hx)
  have heN : L3Lin.eA F ∈ normalizer (A' : Set (MulAut (projectiveSL 3 F))) := by
    rw [← linExtend_e h h5]
    exact A.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ he)
  have hrN : L3Lin.rA F ∈ normalizer (A' : Set (MulAut (projectiveSL 3 F))) := by
    rw [← linExtend_r h h5]
    exact A.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ hr)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three hp3
  have hcomm := L3Lin.comm_of_abelian_lin h2 h3 (Subgroup.map_mono hAB) hB'P hB'ab
    (by rwa [Subgroup.card_map_of_injective hinj]) (by rwa [Subgroup.card_map_of_injective hinj]) heN hrN
  intro a ha
  apply hinj
  rw [map_mul, map_mul, map_pow, linExtend_e]
  exact hcomm (Φ a) (Subgroup.mem_map_of_mem Φ ha)

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
