module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTransferGen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irg_transfer
    {t : StatedLieTag} {n g : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 g)
    (hM : IRGRootPairAut t n g) {G : Type} [Group G] (φ φ' : (ggU t n g).K →* G)
    (hr : φ'.range = φ.range) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K)
    (hk' : φ'.ker ≤ Subgroup.center (ggU t n g).K)
    {β' : Fin (ggU t n g).D.rank → ℤ} (hβ' : β' ∈ (ggU t n g).D.roots)
    (hl : GGLongRoot (ggU t n g).D β') (u' : (ggU t n g).K) :
    IRGPairClass t n g φ (ggRootSub (ggU t n g).D φ' β' u')
      (ggRootSub (ggU t n g).D φ' (-β') u') := by
  have htD : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨
      t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 := by simpa only [GGPosTag] using ht
  have hmod : CFSG.ClassicalInvolution.ModelFacts.modelUniv t n 2 g Nat.prime_two = ggU t n g := by
    rcases htD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    rcases htD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have hfin : Finite (ggU t n g).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU htD hadm
  haveI := hfin
  have hodd : Odd (Nat.card (Subgroup.center (ggU t n g).K)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU htD hadm
  have hperf : commutator (ggU t n g).K = ⊤ := by
    have hq : commutator (CFSG.ClassicalInvolution.ModelFacts.modelUniv t n 2 g
        Nat.prime_two).K = ⊤ :=
      (CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv t n 2 g Nat.prime_two
        hfund hadm).1
    rwa [hmod] at hq
  have hroot : ∀ γ ∈ (ggU t n g).D.roots, IsPGroup 2 ((ggU t n g).D.rootGroup γ) := by
    have h := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t n 2 g Nat.prime_two
      hfund hadm
    rwa [hmod] at h
  have hneg : ∀ γ ∈ (ggU t n g).D.roots, -γ ∈ (ggU t n g).D.roots := fun γ hγ =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (ggU t n g).D.isFiniteType hγ
  have hP2 : ∀ β, (β ∈ (ggU t n g).D.roots ∧ GGLongRoot (ggU t n g).D β) →
      IsPGroup 2 ((ggU t n g).D.rootGroup β) ∧
        IsPGroup 2 ((ggU t n g).D.rootGroup (-β)) := by
    intro β hβ
    exact ⟨hroot β hβ.1, hroot (-β) (hneg β hβ.1)⟩
  have hQ2 : ∀ β, IRGGoodRoot t n g β →
      IsPGroup 2 ((ggU t n g).D.rootGroup β) ∧
        IsPGroup 2 ((ggU t n g).D.rootGroup (-β)) := by
    intro β hβ
    exact ⟨hroot β hβ.1, hroot (-β) (hneg β hβ.1)⟩
  have hMgen : ∀ θ : MulAut ((ggU t n g).K ⧸ Subgroup.center (ggU t n g).K),
      ∀ β' : Fin (ggU t n g).D.rank → ℤ,
        (β' ∈ (ggU t n g).D.roots ∧ GGLongRoot (ggU t n g).D β') → ∀ u' : (ggU t n g).K,
        ∃ β, IRGGoodRoot t n g β ∧ ∃ u : (ggU t n g).K,
          (ggRootSub (ggU t n g).D
              (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) β' u').map θ.toMonoidHom =
            ggRootSub (ggU t n g).D
              (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) β u ∧
          (ggRootSub (ggU t n g).D
              (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) (-β') u').map θ.toMonoidHom =
            ggRootSub (ggU t n g).D
              (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) (-β) u := by
    intro θ β' hβ' u'
    exact hM θ β' hβ'.1 hβ'.2 u'
  unfold IRGPairClass
  exact irg_transfer_gen (D := (ggU t n g).D)
    hperf hodd (P := fun β => β ∈ (ggU t n g).D.roots ∧ GGLongRoot (ggU t n g).D β)
    (Q := fun β => IRGGoodRoot t n g β) hP2 hQ2 hMgen φ φ' hr hk hk' ⟨hβ', hl⟩ u'

end CFSG.StandardType.RCKRP
