module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolution
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSU
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSpinPlus
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestF4

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section

theorem ggRootSylowCentralTag_PSU : GGRootSylowCentralTag .PSU := by
  intro n f hadm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : ggU .PSU n f =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  exact GGRootSU.ggRootSylowCentral_unitary (card_galoisField_two_mul 2 f hf) (by omega)

theorem ggRootSylowCentralTag_POmegaPlus : GGRootSylowCentralTag .POmegaPlus := by
  intro n f hadm
  have hn : 3 ≤ n := by
    have := hadm.2.2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)), Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
    simp only [ggU, lieUniversal, hn, ↓reduceDIte]
  rw [e]
  exact GGRootSpinPlus.ggRootSylowCentral_spinPlus hn .POmegaPlus

theorem ggRootSylowCentralTag_F4 : GGRootSylowCentralTag .F4 := fun _ f _ =>
  GGRootF4.ggRootSylowCentral_f4 (k := GaloisField 2 f) .F4

theorem ggRootInvolutionCentralInput_holds : GGRootInvolutionCentralInput :=
  ggRootInvolutionCentralInput_of_remaining' ggRootSylowCentralTag_PSU
    ggRootSylowCentralTag_POmegaPlus ggRootSylowCentralTag_F4

end

end CFSG.StandardType
