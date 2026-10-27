module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSp
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic

namespace RestSp

variable {n : ℕ} {F : Type} [Field F]

theorem coe_equiv_diagonal (t : Fin n → Fˣ) :
    ((equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) : StatedSp n F) :
      GL (Fin n ⊕ Fin n) F) = TauCeti.diagGL (TableBSymp.pairedUnits t) := by
  apply Units.ext
  have h := SpExtras.mat_equiv_diagonal (F := F) t
  rw [SpExtras.mat_apply] at h
  rw [h, TauCeti.diagGL_coe]
  congr 1
  funext x
  rcases x with i | i <;> rfl

end RestSp

section Core

theorem spFrame_core {G : Type} [Group G] [Finite G] {n f p : ℕ} (hf : 1 ≤ f) (hrk : 2 ≤ n)
    (ψ : StatedSp n (GaloisField 2 f) →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hpp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hp : p ∣ 2 ^ f - 1) :
    ∃ A₀ : StatedSp n (GaloisField 2 f), ∀ b ∈ Bs, ∃ t : Fin n → (GaloisField 2 f)ˣ,
      b = ψ (RestSp.frameDiag A₀ t) := by
  have : Fact p.Prime := ⟨hpp⟩
  have hmem : ∀ b ∈ Bs, b ∈ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker
      (hdiag b hb)
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hcomap : IsElemAbelian p (Bs.comap ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      apply hinj
      change ψ ((a : StatedSp n (GaloisField 2 f)) * b) =
        ψ ((b : StatedSp n (GaloisField 2 f)) * a)
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs a.2 b.2
    · apply hinj
      rw [map_pow, map_one]
      exact hBs.2 _ ha
  set E : Subgroup (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    (Bs.comap ψ).map (StatedSp n (GaloisField 2 f)).subtype with hE
  have hESp : E ≤ LargeEvenSpGroup (GaloisField 2 f) n := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hEel : IsElemAbelian p E := TableB.isElemAbelian_map hcomap _
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) (p := p)
    (by rw [GaloisField.card 2 f (by omega)]; exact hp)
  obtain ⟨P, hPSp, u, hu⟩ := TableBSymp.exists_symplectic_weight_basis_GL
    (TableBSymp.natCast_ne_zero_of_charTwo hpp hp2) hζ hESp hEel
  have hPSp' : P ∈ StatedSp n (GaloisField 2 f) := hPSp
  refine ⟨⟨P, hPSp'⟩, fun b hb => ?_⟩
  obtain ⟨â, rfl⟩ := hmem b hb
  have hâE : ((â : StatedSp n (GaloisField 2 f)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ E :=
    ⟨â, hb, rfl⟩
  refine ⟨fun i => u i ⟨_, hâE⟩, ?_⟩
  suffices h : â = RestSp.frameDiag ⟨P, hPSp'⟩ (fun i => u i ⟨_, hâE⟩) from congrArg ψ h
  apply Subtype.ext
  have h1 := hu ⟨_, hâE⟩
  simp only [RestSp.frameDiag, Subgroup.coe_mul, Subgroup.coe_inv, RestSp.coe_equiv_diagonal]
  calc ((â : StatedSp n (GaloisField 2 f)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (â : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * P * P⁻¹ := by group
    _ = P * TauCeti.diagGL (TableBSymp.pairedUnits fun i => u i ⟨_, hâE⟩) * P⁻¹ := by
        rw [show ((â : StatedSp n (GaloisField 2 f)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          P = P * TauCeti.diagGL (TableBSymp.pairedUnits fun i => u i ⟨_, hâE⟩) from h1]

end Core

section Inputs

theorem ggSpBstarFrameInput_holds : GGSpBstarFrameInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.2.2.2.2.1.1]
    exact s1.1
  exact spFrame_core hctx.2.2.2.1.1.2.1 hctx.2.2.2.1.2 ψ hctx.2.2.2.2.1.2 hC hctx.prime
    hctx.ne_two hctx.bstar.2.1 (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb) hp

theorem ggRootPlaneInputOn_PSpSplit : GGRootPlaneInputOn GGPSpSplit :=
  ggRootPlaneInputOn_PSpSplit_of_frame ggSpBstarFrameInput_holds

theorem ggRootPlaneAt_PSp_of_nonsplit (h₂ : GGRootPlaneInputOn GGPSpNonsplit) :
    GGRootPlaneAt .PSp :=
  ggRootPlaneAt_PSp_of_frame ggSpBstarFrameInput_holds h₂

end Inputs

end CFSG.StandardType
