module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3GammaWords
import Certificates.Kernel.J3Gamma.Act
public import Certificates.Kernel.J3Gamma.ActData
import Certificates.Kernel.CoverCenter.J3Cov
import CFSG.Certificates.Kernel.Misc.Coset.ActRegular

public section

namespace CertificateChecks.Batch12621

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.SectionRank.Native
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Certificates.CosetEnumeration

theorem codesR : codes j3GammaWords = CFSG.KAct.J3Gamma.R := by decide +kernel

theorem codesEQ : codes eqWords = CFSG.KAct.J3Gamma.EQ := by decide +kernel

theorem codesMV : codes moveWords = CFSG.KAct.J3Gamma.MV := by decide +kernel

theorem hpt : ∀ x < 5832, Act.pointOK CFSG.KAct.J3Gamma.A 6 5832 CFSG.KAct.J3Gamma.R x = true :=
  fun x hx => Act.allR_spec CFSG.KAct.J3Gamma.all x (Nat.zero_le _) (by omega)

theorem hdown : ∀ x, 0 < x → x < 5832 →
    Act.downAt CFSG.KAct.J3Gamma.A (Nat.add 6 6) (Nat.add 6 6) x = true :=
  fun x h0 hx => Act.allR_spec CFSG.KAct.J3Gamma.down x h0 (by omega)

theorem eq_one {u : List (Fin 6 × Bool)} (hu : u ∈ eqWords) :
    PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ j3GammaWords.map FreeGroup.mk}
      (FreeGroup.mk u) = 1 := by
  have hm : u.map letterCode ∈ CFSG.KAct.J3Gamma.EQ := by
    rw [← codesEQ]
    exact List.mem_map.2 ⟨_, hu, rfl⟩
  exact Act.eq_one_of_walk_zero (N := 5832) j3GammaWords codesR (by norm_num) hpt hdown
    (by simpa using KernelCover.J3Cov.gamma_card) (Act.fixAll_spec CFSG.KAct.J3Gamma.eq _ hm)

theorem ne_one {u : List (Fin 6 × Bool)} (hu : u ∈ moveWords) :
    PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ j3GammaWords.map FreeGroup.mk}
      (FreeGroup.mk u) ≠ 1 := by
  obtain ⟨E, _, ψ, -, hψ⟩ := Act.movesOK_sound j3GammaWords [] (by rw [codesR]; rfl)
    (N := 5832) (by norm_num) hpt moveWords (by rw [codesMV]; exact CFSG.KAct.J3Gamma.mv)
  intro h1
  exact hψ u hu (by rw [h1, map_one])

end CertificateChecks.Batch12621

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem certificate12621 :
    (∀ u ∈ eqWords,
        PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ CFSG.SectionRank.Native.j3GammaWords.map
          FreeGroup.mk} (FreeGroup.mk u) = 1) ∧
      ∀ u ∈ moveWords,
        PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ CFSG.SectionRank.Native.j3GammaWords.map
          FreeGroup.mk} (FreeGroup.mk u) ≠ 1 :=
  ⟨fun _ hu => CertificateChecks.Batch12621.eq_one hu, fun _ hu => CertificateChecks.Batch12621.ne_one hu⟩

end Certificates
