module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ClassicalInvolution.ModelFacts
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private lemma irgNF_ggRootSub_transport {K Q : Type*} [Group K] [Group Q]
    (D : UniversalRootDatum K) (φ : K →* Q) (θ : MulAut Q) (α : MulAut K) (x0 u x : K)
    (hcomm : θ.toMonoidHom.comp φ = φ.comp α.toMonoidHom)
    {r r' s : Fin D.rank → ℤ}
    (hxr : (D.rootGroup r).map (MulAut.conj x).toMonoidHom = D.rootGroup r')
    (hαr : (D.rootGroup r).map α.toMonoidHom =
        (D.rootGroup s).map (MulAut.conj x0).toMonoidHom) :
    (ggRootSub D φ r' u).map θ.toMonoidHom = ggRootSub D φ s (α (u * x) * x0) := by
  calc (ggRootSub D φ r' u).map θ.toMonoidHom
      = ((D.rootGroup r').map (MulAut.conj u).toMonoidHom).map (θ.toMonoidHom.comp φ) := by
          rw [ggRootSub, Subgroup.map_map]
    _ = ((D.rootGroup r').map (MulAut.conj u).toMonoidHom).map (φ.comp α.toMonoidHom) := by
          rw [hcomm]
    _ = (((D.rootGroup r').map (MulAut.conj u).toMonoidHom).map α.toMonoidHom).map φ := by
          rw [← Subgroup.map_map]
    _ = ((((D.rootGroup r).map (MulAut.conj x).toMonoidHom).map
            (MulAut.conj u).toMonoidHom).map α.toMonoidHom).map φ := by
          rw [← hxr]
    _ = (((D.rootGroup r).map (MulAut.conj (u * x)).toMonoidHom).map α.toMonoidHom).map φ := by
          rw [Subgroup.map_conj_map_conj]
    _ = (((D.rootGroup r).map α.toMonoidHom).map
            (MulAut.conj (α (u * x))).toMonoidHom).map φ := by
          rw [Subgroup.map_map_conj]
          rfl
    _ = ((((D.rootGroup s).map (MulAut.conj x0).toMonoidHom).map
            (MulAut.conj (α (u * x))).toMonoidHom)).map φ := by
          rw [hαr]
    _ = ((D.rootGroup s).map (MulAut.conj (α (u * x) * x0)).toMonoidHom).map φ := by
          rw [Subgroup.map_conj_map_conj]
    _ = ggRootSub D φ s (α (u * x) * x0) := by
          rw [ggRootSub]

theorem irg_weyl_conj
    {t : StatedLieTag} {n g : ℕ} (hB : HasBruhatDatum (ggU t n g).D)
    (w : (coxeterMatrix (ggU t n g).D.isFiniteType).Group) :
    ∃ x : (ggU t n g).K, ∀ γ ∈ (ggU t n g).D.roots,
      ((ggU t n g).D.rootGroup γ).map (MulAut.conj x).toMonoidHom =
        (ggU t n g).D.rootGroup (weylAction (ggU t n g).D.isFiniteType w γ) := by
  obtain ⟨nw, H, hct, -⟩ := hB
  exact exists_map_conj_rootGroup hct w

theorem irg_pair_aut_of_simple_nf
    {t : StatedLieTag} {n g : ℕ} (hB : HasBruhatDatum (ggU t n g).D)
    (hdiv : (ggU t n g).D.divisible = ∅)
    (hNF : ∀ θ : MulAut (IRGQuot t n g), ∃ (α : MulAut (ggU t n g).K) (x0 : (ggU t n g).K)
        (π : Fin (ggU t n g).D.rank → Fin (ggU t n g).D.rank),
        (∀ y, QuotientGroup.mk' (Subgroup.center (ggU t n g).K) (α y) =
            θ (QuotientGroup.mk' (Subgroup.center (ggU t n g).K) y)) ∧
        (∀ i, ((ggU t n g).D.rootGroup (Pi.single i 1)).map α.toMonoidHom =
              ((ggU t n g).D.rootGroup (Pi.single (π i) 1)).map (MulAut.conj x0).toMonoidHom ∧
            ((ggU t n g).D.rootGroup (-Pi.single i 1)).map α.toMonoidHom =
              ((ggU t n g).D.rootGroup (-Pi.single (π i) 1)).map (MulAut.conj x0).toMonoidHom) ∧
        (∀ i, GGLongRoot (ggU t n g).D (Pi.single i 1) →
          IRGGoodRoot t n g (Pi.single (π i) 1))) :
    IRGRootPairAut t n g := by
  unfold IRGRootPairAut
  intro θ β' hβ'mem hβ'long u'
  obtain ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩ := hβ'mem
  · have hlong_i : GGLongRoot (ggU t n g).D (Pi.single i 1) :=
      (CFSG.StandardType.LieKnownR2.Short.ggLongRoot_weylAction_iff (ggU t n g).D w
        (Pi.single i 1)).mp hβ'long
    obtain ⟨α, x0, π, hcomm, hsimp, hgood⟩ := hNF θ
    obtain ⟨x, hx⟩ := irg_weyl_conj hB w
    have hsi : Pi.single i 1 ∈ (ggU t n g).D.roots :=
      Or.inl ⟨1, i, by simp⟩
    have hnegi : -Pi.single i 1 ∈ (ggU t n g).D.roots := by
      have h := CFSG.LieType.CurtisTits.weylAction_mem_roots (D := (ggU t n g).D) hsi
        ((coxeterMatrix (ggU t n g).D.isFiniteType).toCoxeterSystem.simple i)
      rwa [weylAction_simple_single] at h
    have hcomp : θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) =
        (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)).comp α.toMonoidHom := by
      ext y
      exact (hcomm y).symm
    refine ⟨Pi.single (π i) 1, hgood i hlong_i, α (u' * x) * x0, ?_, ?_⟩
    · exact irgNF_ggRootSub_transport (ggU t n g).D _ θ α x0 u' x hcomp
        (hx (Pi.single i 1) hsi) (hsimp i).1
    · have hneg : -(weylAction (ggU t n g).D.isFiniteType w (Pi.single i 1)) =
          weylAction (ggU t n g).D.isFiniteType w (-Pi.single i 1) := by
        rw [map_neg]
      rw [hneg]
      exact irgNF_ggRootSub_transport (ggU t n g).D _ θ α x0 u' x hcomp
        (hx (-Pi.single i 1) hnegi) (hsimp i).2
  · rw [hdiv] at hi
    exact absurd hi (by simp)

end CFSG.StandardType.RCKRP
