module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Open

section Inner

variable {G : Type} [Group G] [Finite G]

theorem ggSpInnerAction_of_mp (hMp : GGInnerDiagMpInput) {Bs X : Subgroup G} {m f : ℕ}
    (hm : 1 ≤ m) (hadm : StatedLieAdmissible .PSp (m + 1) 2 f) (hmark : GGInnerDiagOn Bs X)
    (φ : StatedSp (m + 1) (GaloisField 2 f) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = X) :
    ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹ := by
  intro b hb
  let ψ : (ggU .PSp (m + 1) f).K →* G := φ
  have hrk : 2 ≤ (ggU .PSp (m + 1) f).D.rank := by
    show 2 ≤ m + 1
    omega
  have hker : ψ.ker ≤ Subgroup.center (ggU .PSp (m + 1) f).K := by
    have h0 : ψ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).2 hinj
    rw [h0]
    exact bot_le
  have hQ : ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSp (m + 1) f).D ψ b := by
    have hmk := hMp G .PSp (m + 1) f ψ hadm hrk hker X hrange _ hmark
    exact largeEvenMarking_elim_const
      (Q := ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSp (m + 1) f).D ψ b)
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h b hb => h.2 b (h.1.1 hb) (h.1.2 b hb)) hmk)
  obtain ⟨g, hg, hbg⟩ :=
    PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) (by omega : 2 ≤ m + 1) ψ hker
      (hQ b hb)
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

end Inner

end CFSG.StandardType
