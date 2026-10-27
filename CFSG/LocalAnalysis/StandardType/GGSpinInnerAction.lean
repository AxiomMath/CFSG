module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LieType.Universal.Catalog
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal

variable {G : Type} [Group G] [Finite G]

theorem ggSpinPlusInnerAction_of_mp (hMp : GGInnerDiagMpInput) {Bs X : Subgroup G} {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hmark : GGInnerDiagOn Bs X)
    (φ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = X) :
    ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹ := by
  intro b hb
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .POmegaPlus n 2 f := by
    simp only [StatedLieAdmissible]
    exact ⟨Nat.prime_two, hf, hn⟩
  have hggU : ggU .POmegaPlus n f =
      ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := dite_eq_left hn3
  have key : 2 ≤ (ggU .POmegaPlus n f).D.rank →
      ∀ ψ : (ggU .POmegaPlus n f).K →* G, ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K →
        ψ.range = X → ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ b := by
    intro hrk ψ hker hrange b hb
    have hmk := hMp G .POmegaPlus n f ψ hadm hrk hker X hrange _ hmark
    exact largeEvenMarking_elim_const
      (Q := GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ b)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2 b (h.1.1 hb) (h.1.2 b hb)) hmk)
  rw [hggU] at key
  have hrk : 2 ≤ (Spin.plusDatum n (GaloisField 2 f) hn3).rank := by
    show 2 ≤ n
    omega
  have hker : φ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))) := by
    have h0 : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).2 hinj
    rw [h0]
    exact bot_le
  obtain ⟨g, hg, hbg⟩ :=
    PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 f) hn3 φ hker
      (key hrk φ hker hrange b hb)
  have hgX : g ∈ X := by
    rw [← hrange]
    exact hg
  have hbgC : b * g ∈ Subgroup.centralizer (X : Set G) := by
    rw [← hrange]
    exact hbg
  refine ⟨g⁻¹, X.inv_mem hgX, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hgX) hk) hgX
  have hcomm : (g⁻¹ * k * g) * (b * g) = (b * g) * (g⁻¹ * k * g) :=
    Subgroup.mem_centralizer_iff.mp hbgC _ hk'
  calc b * k * b⁻¹ = (b * g) * (g⁻¹ * k * g) * (b * g)⁻¹ := by group
    _ = g⁻¹ * k * g := by rw [← hcomm]; group
    _ = g⁻¹ * k * g⁻¹⁻¹ := by group

theorem ggSpinMinusInnerAction_of_mp (hMp : GGInnerDiagMpInput) {Bs X : Subgroup G} {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hmark : GGInnerDiagOn Bs X)
    (φ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
      →* G) (hinj : Function.Injective φ) (hrange : φ.range = X) :
    ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹ := by
  intro b hb
  let ψ : (ggU .POmegaMinus n f).K →* G := φ
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f := by
    simp only [StatedLieAdmissible]
    exact ⟨Nat.prime_two, hf, hn⟩
  have hrk : 2 ≤ (ggU .POmegaMinus n f).D.rank := by
    show 2 ≤ n - 1
    omega
  have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K := by
    have h0 : ψ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).2 hinj
    rw [h0]
    exact bot_le
  have hQ : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ b := by
    have hmk := hMp G .POmegaMinus n f ψ hadm hrk hker X hrange _ hmark
    exact largeEvenMarking_elim_const
      (Q := ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ b)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h b hb => h.2 b (h.1.1 hb) (h.1.2 b hb)) hmk)
  obtain ⟨g, hg, hbg⟩ :=
    PsiDiag.SpinM.exists_mem_centralizer (K := GaloisField 2 f) (minusCoeffs_irr 2 f) hn ψ
      hker (hQ b hb)
  have hgX : g ∈ X := by
    rw [← hrange]
    exact hg
  have hbgC : b * g ∈ Subgroup.centralizer (X : Set G) := by
    rw [← hrange]
    exact hbg
  refine ⟨g⁻¹, X.inv_mem hgX, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hgX) hk) hgX
  have hcomm : (g⁻¹ * k * g) * (b * g) = (b * g) * (g⁻¹ * k * g) :=
    Subgroup.mem_centralizer_iff.mp hbgC _ hk'
  calc b * k * b⁻¹ = (b * g) * (g⁻¹ * k * g) * (b * g)⁻¹ := by group
    _ = g⁻¹ * k * g := by rw [← hcomm]; group
    _ = g⁻¹ * k * g⁻¹⁻¹ := by group

end CFSG.StandardType

end
