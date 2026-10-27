module

public import CFSG.RankThree.PartOne.KF4.B2Surj
public import CFSG.RankThree.PartOne.KF4.MinNativeTorus
public import CFSG.RankThree.PartOne.KF4.MinNativeBase

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open scoped Pointwise

section Weights

variable {K : Type} [Field K]

@[expose] def f4B2Chars (b : Fin Tag.F4.rank → Kˣ) : Fin 4 → Kˣ :=
  ![b (f4Index 1) * b (f4Index 2) ^ 2 * b (f4Index 3),
    b (f4Index 1) * b (f4Index 2) * b (f4Index 3), b (f4Index 2) * b (f4Index 3), b (f4Index 3)]

theorem f4B2_rootChar_weight (b : Fin Tag.F4.rank → Kˣ) (k : Fin 4) :
    rootChar b (f4B2Weight k) = f4B2Chars b k := by
  change ∏ i : Fin 4, b i ^ f4B2Weight k i = _
  fin_cases k <;> simp [f4B2Weight, f4B2Chars, f4Index, Fin.prod_univ_four]

end Weights

section Frame

variable
  {K L : Type} [Field K] [Field L]

theorem f4B2_Mat_conj_rootDiagUnit (b : Fin Tag.F4.rank → Kˣ) {g : ModGL Tag.F4 K}
    (hg : g ∈ subsystemGroup Tag.F4 K f4B2Support) :
    f4B2_data.Mat (rootDiagUnit Tag.F4 b * g * (rootDiagUnit Tag.F4 b)⁻¹) =
      Matrix.diagonal (fun k => ((f4B2Chars b k : Kˣ) : K)) * f4B2_data.Mat g *
      Matrix.diagonal (fun k => (((f4B2Chars b k)⁻¹ : Kˣ) : K)) := by
  rw [f4B2_data.Mat_conj_rootDiagUnit b hg]
  simp only [f4B2_rootChar_weight]

theorem f4B2Equiv_baseChangeGL (f : K →+* L) (g : subsystemGroup Tag.F4 K f4B2Support) :
    ((f4B2Equiv L ⟨baseChangeGL f (g : ModGL Tag.F4 K),
        baseChangeGL_mem_subsystemGroup f g.2⟩ : f4SpGroup L) : GL (Fin 4) L).val =
      ((f4B2Equiv K g : f4SpGroup K) : GL (Fin 4) K).val.map f := by
  rw [show ((f4B2Equiv L ⟨baseChangeGL f (g : ModGL Tag.F4 K),
        baseChangeGL_mem_subsystemGroup f g.2⟩ : f4SpGroup L) : GL (Fin 4) L).val =
      f4B2_data.Mat (baseChangeGL f (g : ModGL Tag.F4 K)) from rfl,
    f4B2_data.Mat_baseChangeGL]
  rfl

end Frame

end CFSG.RankThree.PartOne.KF4
