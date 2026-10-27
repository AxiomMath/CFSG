module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
import CFSG.LocalAnalysis.StandardType.GGStdPosDToral
import CFSG.LocalAnalysis.StandardType.GGStdPosIsogCore
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin

namespace StdPosD

theorem exists_stdPos_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) {G : Type} [Group G] [Finite G] {ψ : spinGroup (quadPlus n F) →* G} {p : ℕ}
    {Bs : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n F))) (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (plusDatum n F hn) ψ b)
    (hc : p ^ n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : spinGroup (quadPlus n F),
      GGKGPosStdPos (plusDatum n F hn) (ψ.comp (MulAut.conj s).toMonoidHom) Bs :=
  StdPosExc.exists_stdPos_of_toral_isog (ι := MonoidHom.id _) (fun x => ⟨x, rfl⟩)
    (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn)
    (MonoidHom.ker_id.trans_le bot_le) (Subgroup.comap_id (ggTorus (plusDatum n F hn))).le hker
    (fun _ hE hEn => exists_conj_le_ggTorus hn hp hp2 hpF hE hEn) hBs
    (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hinn b hb)) hc

end StdPosD

theorem ggKGPosStdPosD :
    GGKGPosStdPosCase .POmegaPlus (fun _ _ => True) := by
  rintro G _ _ p Bs X n f ψ h -
  obtain ⟨⟨hp, hp2, hadm, -⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, -, -⟩, hinn, hc, -⟩ := h
  obtain ⟨-, hf, hn4⟩ := hadm
  have hn : 3 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hcn := hc (by rintro (⟨h', -⟩ | ⟨h', -⟩) <;> cases h')
  subst hX
  clear hc
  revert ψ
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
      plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  intro ψ hker hinn hcn
  exact StdPosD.exists_stdPos_spinPlus hn hp hp2 hpF hker hBs hinn hcn

end CFSG.StandardType

end
