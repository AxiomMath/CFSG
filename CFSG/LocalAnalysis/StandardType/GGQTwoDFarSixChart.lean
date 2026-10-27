module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthSixChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSixAlign

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Orthogonal CFSG.StandardType.OrthTorus
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem qtwoFarSix_exists_chart_of_frameCore {Bs X : Subgroup G} (Φ : OrthFrameCore 3 Bs X)
    (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥X = ⊥) (β : Additive ↥Bs ≃+ DVec 6)
    {i₀ : Fin 6} {c : ZMod 3} (hc : c ≠ 0) {x : G} (hx : x ∈ Bs)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hxX : X ≤ Subgroup.centralizer ({x} : Set G))
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β)) :
    ∃ φ₀ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀)) →* G, Function.Injective φ₀ ∧
      φ₀.range = X ∧ ∀ i (hi : i ∈ Finset.univ.erase i₀),
        φ₀ ⟨SixPlane.rot 6 i, SixPlane.rot_mem_supp hi⟩ =
          ((Additive.toMul (β.symm (Pi.single i 1)) : ↥Bs) : G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, s, hs, hπ⟩ := qtwoFarSix_align_of_frameCore Φ hF hZ β hc hx hxc hxX hAe
  obtain ⟨φ, hφ, hrange, hrot⟩ := Φ.exists_sixPlane_chart hF π s hs
  refine ⟨φ, hφ, hrange, fun i hi => ?_⟩
  have hτ : Φ.Δ.τ (Pi.mulSingle (π ⟨i, hi⟩) (Multiplicative.ofAdd (s ⟨i, hi⟩))) ∈
      orthDerived Φ.Q := Φ.hA (le_of_eq Φ.Δ.τ_range ⟨_, rfl⟩)
  rw [hrot ⟨i, hi⟩ ⟨_, hτ⟩ rfl, hπ ⟨i, hi⟩ ⟨_, hτ⟩ rfl]

section Cfg


theorem qtwoFarSix_exists_chart {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    {i₀ : Fin 6} {c : ZMod 3} (hc : c ≠ 0) (hx : x ∈ Bs)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hAe : (ggAutomizer L Bs).map (ggLin (p := 3) β) = dEvenStab 6 (Pi.single i₀ 1))
    (Φ : OrthFrameCore 3 Bs L) (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥L = ⊥) :
    ∃ φ₀ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀)) →* G, Function.Injective φ₀ ∧
      φ₀.range = L ∧ ∀ i (hi : i ∈ Finset.univ.erase i₀),
        φ₀ ⟨SixPlane.rot 6 i, SixPlane.rot_mem_supp hi⟩ =
          ((Additive.toMul (β.symm (Pi.single i 1)) : ↥Bs) : G) := by
  exact qtwoFarSix_exists_chart_of_frameCore Φ hF hZ β hc hx hxc
    (hcfg.1.1.1.1.2.2.2.2.2.2.1 : CFSG.Assembly.LargeEvenSStar 3 B x L).2.2.2.1.1 hAe.ge

end Cfg

end CFSG.StandardType.QTwo
