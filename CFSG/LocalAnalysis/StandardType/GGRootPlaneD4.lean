module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneD4Core
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section D4

theorem ggRootPlaneD4Input_holds : GGRootPlaneD4Input := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, rfl, -⟩ := hP
  have hn : 3 ≤ 4 := by norm_num
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hctx s1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
  have hcardB : p ^ 4 ≤ Nat.card B := by
    rw [hctx.1.2.2.2.2.2.2.1.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hctx.1.2.2.2.2.2.1.2.2.2
  have hJJ : ⁅J, J⁆ = J := RootPlaneA.commutator_eq_of_isQuasisimple hctx.j_comp.2.2
  have hJψ : J ≤ ψ.range := hrange ▸ hctx.le_ggG0
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 (GaloisField 2 f) hn
  obtain ⟨γ, hγ, -⟩ := exists_maxHeight (D := plusDatum 4 (GaloisField 2 f) hn)
    (show 0 < 4 by norm_num)
  obtain ⟨i, j, hij, s, t, -, hγX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  obtain ⟨u, hcent, hord⟩ := RootPlaneD4.exists_rootPlane_spin_d4 (plusIndexEquiv 4)
    (AutOm.range_spinMatrix_plus hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hnd hT (by norm_num)
    (plusFrame 4 (GaloisField 2 f) hn) hij s t hψinj hp hp2 hctx.2.1.2.1 hctx.2.1.2.2.2
    hctx.2.1.1 hcardB hctx.card_d hctx.stdSub.1.2.2.2.2.2.2 hJJ hBψ hJψ
  have hX : (plusDatum 4 (GaloisField 2 f) hn).rootGroup γ =
      ((plusFrame 4 (GaloisField 2 f) hn).longRoot hij s t).range := hγX
  refine ⟨D, γ, u, ψ (u * (plusFrame 4 (GaloisField 2 f) hn).longRoot hij s t (.ofAdd 1) * u⁻¹),
    hctx.d_le_bstar, hctx.d_elem, hctx.card_d, ⟨hγ, fun h => ?_⟩, ?_, ?_, hord,
    fun e he _ => Or.inl he⟩
  · rcases h with h | h | h <;> exact absurd h (by decide)
  · change D ≤ Subgroup.centralizer (((((plusDatum 4 (GaloisField 2 f) hn).rootGroup γ).map
      (MulAut.conj u).toMonoidHom).map ψ : Subgroup G) : Set G)
    rw [hX]
    exact hcent
  · change _ ∈ (((plusDatum 4 (GaloisField 2 f) hn).rootGroup γ).map
      (MulAut.conj u).toMonoidHom).map ψ
    rw [hX]
    exact ⟨_, ⟨_, ⟨.ofAdd 1, rfl⟩, rfl⟩, rfl⟩

theorem ggRootPlaneAt_POmegaPlus : GGRootPlaneAt .POmegaPlus :=
  ggRootPlaneAt_POmegaPlus_of_d4 ggRootPlaneD4Input_holds

theorem ggRootPlaneRestD4Exc_of_exc (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneRestD4Exc :=
  ⟨ggRootPlaneD4Input_holds, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggRootPlaneRestOmegaExc_of_exc (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneRestOmegaExc :=
  ggRootPlaneRestOmegaExc_of_d4Exc (ggRootPlaneRestD4Exc_of_exc hF4 hE6 hE7 hE8 hTwE6)

theorem ggRootPlaneInput_of_exc (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneInput :=
  ggRootPlaneInput_of_d4Exc (ggRootPlaneRestD4Exc_of_exc hF4 hE6 hE7 hE8 hTwE6)

end D4

end CFSG.StandardType
