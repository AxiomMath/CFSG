module

public import CFSG.Quasithin.H13.GoldschmidtU43ModDef
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
public import CFSG.Foundations
public import CFSG.LieType.Multipliers.U43Bridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.H13.GoldschmidtU43CQ8
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Recognition.F4Local
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.U43

theorem rels4Codes_eq : rels4Codes =
    [[(1, true), (1, true), (1, true)],
     [(1, false), (0, true), (1, true), (1, false), (0, true), (1, true), (0, false), (0, false)],
     [(3, false), (0, true), (3, true), (0, true)],
     [(1, false), (1, false), (0, true), (1, true), (1, true), (1, false), (0, false), (1, true),
       (0, false)],
     [(2, false), (0, true), (2, true), (2, false), (0, true), (2, true), (0, false), (0, false)],
     [(3, false), (2, false), (0, true), (2, true), (3, true), (2, false), (0, true), (2, true)],
     [(3, false), (2, false), (1, true), (2, true), (3, true), (2, false), (1, true), (2, true)],
     [(0, false), (2, false), (0, false), (2, true), (0, true), (2, false), (0, true), (2, true)],
     [(0, false), (2, false), (1, false), (2, true), (0, true), (2, false), (1, true), (2, true)],
     [(1, false), (2, false), (1, false), (2, true), (1, true), (2, false), (1, true), (2, true)],
     [(3, true), (3, true), (0, false), (0, false)],
     [(2, true), (2, true)],
     [(2, false), (3, true), (2, true), (3, true)]] := by
  decide +kernel

theorem rels5Codes_eq : rels5Codes =
    [[(1, true), (1, true), (1, true)],
     [(1, false), (0, true), (1, true), (1, false), (0, true), (1, true), (0, false), (0, false)],
     [(3, false), (0, true), (3, true), (0, true)],
     [(1, false), (1, false), (0, true), (1, true), (1, true), (1, false), (0, false), (1, true),
       (0, false)],
     [(2, false), (0, true), (2, true), (2, false), (0, true), (2, true), (0, false), (0, false)],
     [(3, false), (2, false), (0, true), (2, true), (3, true), (2, false), (0, true), (2, true)],
     [(3, false), (2, false), (1, true), (2, true), (3, true), (2, false), (1, true), (2, true)],
     [(0, false), (2, false), (0, false), (2, true), (0, true), (2, false), (0, true), (2, true)],
     [(0, false), (2, false), (1, false), (2, true), (0, true), (2, false), (1, true), (2, true)],
     [(1, false), (2, false), (1, false), (2, true), (1, true), (2, false), (1, true), (2, true)],
     [(3, true), (3, true), (0, false), (0, false)],
     [(2, true), (2, true)],
     [(2, false), (3, true), (2, true), (3, true)],
     [(0, false), (0, false), (4, true), (0, true), (0, true), (4, true)],
     [(2, false), (4, true), (2, true), (4, false)],
     [(2, false), (1, false), (2, true), (2, false), (0, false), (2, true), (4, true), (2, false),
       (0, true), (2, true), (2, false), (1, true), (2, true), (1, false), (2, false), (0, false),
       (2, true), (4, false), (2, false), (0, true), (2, true), (4, true)],
     [(2, false), (0, false), (2, true), (4, false), (2, false), (0, true), (2, true), (4, true),
       (2, false), (0, false), (2, true), (4, true), (2, false), (0, true), (2, true), (1, true),
       (4, false)],
     [(4, false), (2, false), (0, false), (2, true), (3, false), (4, false), (3, true), (2, false),
       (0, true), (2, true), (4, true), (2, false), (0, false), (2, true), (3, false), (4, true),
       (3, true), (2, false), (0, true), (2, true)],
     [(2, true), (0, true), (0, true), (2, false), (0, false), (2, true), (4, true), (2, false),
       (0, true), (2, true), (2, true), (0, true), (0, true), (2, false), (0, false), (2, true),
       (4, true), (2, false), (0, true), (2, true), (2, true), (0, true), (0, true), (2, false),
       (0, false), (2, true), (4, true), (2, false), (0, true), (2, true)],
     [(2, true), (3, true), (2, false), (0, false), (2, true), (4, false), (2, false), (0, true),
       (2, true), (2, false), (0, false), (2, true), (3, false), (4, true), (3, true), (2, false),
       (0, true), (2, true), (2, true), (3, true), (2, false), (0, false), (2, true), (4, false),
       (2, false), (0, true), (2, true), (2, false), (0, false), (2, true), (3, false), (4, true),
       (3, true), (2, false), (0, true), (2, true), (2, true), (3, true), (2, false), (0, false),
       (2, true), (4, false), (2, false), (0, true), (2, true), (2, false), (0, false), (2, true),
       (3, false), (4, true), (3, true), (2, false), (0, true), (2, true)]] := by
  decide +kernel

private theorem flat_of_eq {K : Type*} [Group K] {x y P : K} (h : x = y) (hP : P = x * y⁻¹) :
    P = 1 := by
  rw [hP, h, mul_inv_cancel]

private theorem eq_of_flat {K : Type*} [Group K] {x y P : K} (h : P = 1) (hP : P = x * y⁻¹) :
    x = y :=
  mul_inv_eq_one.1 (hP.symm.trans h)

local macro "grp" : tactic =>
  `(tactic| (simp only [evalG, letterVal, gen5, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ,
    jwA₂, jwS₂, jwP₂, jwP₃, jwP₄, pow_succ, pow_zero, one_mul, mul_one]; group))

local macro "fromRel " h:term:max : term => `(flat_of_eq $h (by grp))
local macro "toRel " h:term:max : term => `(eq_of_flat $h (by grp))

theorem JW20.eval_rels {K : Type} [Group K] {a s u v φ : K} (h : JW20 a s u v φ) :
    ∀ r ∈ rels5Codes, evalG (gen5 a s u v φ) r = 1 := by
  rw [rels5Codes_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, implies_true, and_true, IsEmpty.forall_iff]
  exact ⟨fromRel h.r1, fromRel h.r2, fromRel h.r3, fromRel h.r4, fromRel h.r5, fromRel h.r6,
    fromRel h.r7, fromRel h.r8, fromRel h.r9, fromRel h.r10, fromRel h.r11, fromRel h.r12,
    fromRel h.r13, fromRel h.r14, fromRel h.r15, fromRel h.r16, fromRel h.r17, fromRel h.r18,
    fromRel h.r19, fromRel h.r20⟩

theorem JW20.of_eval_rels {K : Type} [Group K] {a s u v φ : K}
    (h : ∀ r ∈ rels5Codes, evalG (gen5 a s u v φ) r = 1) : JW20 a s u v φ := by
  rw [rels5Codes_eq] at h
  simp only [List.forall_mem_cons, List.not_mem_nil, implies_true, and_true,
    IsEmpty.forall_iff] at h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
    k20⟩ := h
  exact ⟨⟨toRel k1, toRel k2, toRel k3, toRel k4, toRel k5, toRel k6, toRel k7, toRel k8,
    toRel k9, toRel k10, toRel k11, toRel k12, toRel k13⟩, toRel k14, toRel k15, toRel k16,
    toRel k17, toRel k18, toRel k19, toRel k20⟩

theorem JW13.of_eval_rels4 {K : Type} [Group K] {a s u v : K}
    (h : ∀ r ∈ rels4Codes, evalG (gen5 a s u v 1) r = 1) : JW13 a s u v := by
  rw [rels4Codes_eq] at h
  simp only [List.forall_mem_cons, List.not_mem_nil, implies_true, and_true,
    IsEmpty.forall_iff] at h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13⟩ := h
  exact ⟨toRel k1, toRel k2, toRel k3, toRel k4, toRel k5, toRel k6, toRel k7, toRel k8,
    toRel k9, toRel k10, toRel k11, toRel k12, toRel k13⟩

end CFSG.Quasithin.H13.U43
