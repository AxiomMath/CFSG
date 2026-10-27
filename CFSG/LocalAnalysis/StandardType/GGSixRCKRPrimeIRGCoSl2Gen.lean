module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGA1Sl2
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgC1_good
    {g : ℕ} {β : Fin 1 → ℤ}
    (hβ : β = Pi.single 0 1 ∨ β = -Pi.single 0 1) : IRGGoodRoot .PSL 2 g β := by
  have h0 : (Pi.single (0 : Fin 1) 1 : Fin 1 → ℤ) ∈
      (SpecialLinear.rootDatum 1 (GaloisField 2 g)).roots :=
    CFSG.ClassicalInvolution.RouteD.single_mem_roots (SpecialLinear.rootDatum 1 (GaloisField 2 g))
      (0 : Fin 1)
  have hroot : β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 g)).roots := by
    rcases hβ with rfl | rfl
    · exact h0
    · exact CFSG.LieType.Steinberg.OfCartan.neg_mem_roots
        (SpecialLinear.rootDatum 1 (GaloisField 2 g)).isFiniteType h0
  have hlong : GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 g)) β :=
    ggLongRoot_of_symmetric
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A (by norm_num : 0 < 1))
      (fun i j => CFSG.ClassicalInvolution.ModelFacts.cartanA_symm 1 i j) rfl hroot
  exact ⟨hroot, Or.inl hlong⟩

theorem irg_isoCompat_of_sl2
    {t' : StatedLieTag} {m g' g : ℕ} (hg : 2 ≤ g) (e : (ggU t' m g').K ≃* (ggU .PSL 2 g).K)
    (hroot : ∀ β' : Fin (ggU t' m g').D.rank → ℤ, β' ∈ (ggU t' m g').D.roots →
      GGLongRoot (ggU t' m g').D β' →
      Nat.card ((ggU t' m g').D.rootGroup β') = 2 ^ g ∧
      Nat.card ((ggU t' m g').D.rootGroup (-β')) = 2 ^ g ∧
      (ggU t' m g').D.rootGroup β' ⊓ (ggU t' m g').D.rootGroup (-β') = ⊥) :
    IRGIsoCompat e := by
  unfold IRGIsoCompat
  intro β' hβ' hlong
  obtain ⟨hc1, hc2, hinf⟩ := hroot β' hβ' hlong
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
  have hF4 : 4 ≤ Nat.card (GaloisField 2 g) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hP : Nat.card (((ggU t' m g').D.rootGroup β').map e.toMonoidHom) =
      Nat.card (GaloisField 2 g) := by
    rw [Subgroup.card_map_of_injective hinj, hc1, hF]
  have hQ : Nat.card (((ggU t' m g').D.rootGroup (-β')).map e.toMonoidHom) =
      Nat.card (GaloisField 2 g) := by
    rw [Subgroup.card_map_of_injective hinj, hc2, hF]
  have hPQ : ((ggU t' m g').D.rootGroup β').map e.toMonoidHom ⊓
      ((ggU t' m g').D.rootGroup (-β')).map e.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ hinj, hinf, Subgroup.map_bot]
  obtain ⟨β, w, hβ, hPeq, hQeq⟩ := irg_sl2_pair (F := GaloisField 2 g) hF4
    (((ggU t' m g').D.rootGroup β').map e.toMonoidHom)
    (((ggU t' m g').D.rootGroup (-β')).map e.toMonoidHom) hP hQ hPQ
  exact ⟨β, irgC1_good hβ, w, hPeq, hQeq⟩

end CFSG.StandardType.RCKRP
