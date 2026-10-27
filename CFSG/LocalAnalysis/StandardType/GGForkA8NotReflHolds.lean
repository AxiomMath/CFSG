module

public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGA8NRDetChar
public import CFSG.LocalAnalysis.StandardType.GGA8NRRetraction
public import CFSG.LocalAnalysis.StandardType.GGA8NRSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGA8NRActHom
public import CFSG.LocalAnalysis.StandardType.GGA8NRShiftInduced

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggForkA8NotReflInput_of_mp
    (hMp : GGInnerDiagMpInput) : GGForkA8NotReflInput := by
  intro G _ _ B Bs x L D J hcfg hinn y K hnb hlab
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 :=
    statedClassicalModel_of_hasLabel_typeA (n := 8) (f := 1)
      ⟨by norm_num, by norm_num, fun h => by simp at h⟩ hlab
  haveI : IsMulCommutative ↥Bs := hcfg.2.1.2.1.1
  have hab : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative Bs ha hb
  have hpow : ∀ b ∈ Bs, b ^ 7 = 1 := fun b hb => hcfg.2.1.2.1.2 b hb
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨ρ₀, hdec⟩ := ggA8NR_retraction hMp hab hpow hSC (hinn.2 y K hnb) hKm
  obtain ⟨ρ, hρ⟩ := ggA8NR_sylowTorus ρ₀ hab hpow hSC hdec
  obtain ⟨act, hact⟩ := ggA8NR_actHom ρ hρ
  obtain ⟨φ₀, hφ₀, n₀, hρn₀, hn₀⟩ := ggA8NR_shiftInduced ρ hρ hdec
  obtain ⟨χ₀, hχ₀⟩ := ggA8NR_detChar
  have hs : act ⟨φ₀, hφ₀⟩ = ggSL9ShiftCoord := by
    ext f : 1
    apply ggSL9TorusCoord_injective
    rw [← hact ⟨φ₀, hφ₀⟩ n₀ hn₀ f, ← ggSL9Shift_conj_torusCoord, ← hρn₀]
    simp
  refine ⟨χ₀.comp act, fun h => hχ₀ ?_⟩
  have h1 := DFunLike.congr_fun h ⟨φ₀, hφ₀⟩
  rw [MonoidHom.comp_apply, hs] at h1
  simpa using h1

end CFSG.StandardType

end
