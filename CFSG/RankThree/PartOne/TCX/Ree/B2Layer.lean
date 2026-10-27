module

public import CFSG.RankThree.PartOne.KEXC.B2Key

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.RF4
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

theorem b2_level (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    Nonempty (suzukiGroup a K ≃* ↥(rootSpan ReeTag.F4.tag L
        (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓ twistedFixed D.F n')) ∧
      (1 ≤ a → ∀ y ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support),
        (∀ u ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
          twistedFixed D.F n', y * u = u * y) → y = 1) := by
  classical
  obtain ⟨Ξ, -, hΞ⟩ := b2_exists_struct D hK hperm hstab
  have hspan : rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) = B2Q L :=
    B2Q_eq_rootSpan.symm
  let ρ₂ : suzukiGroup a K →* ModGL ReeTag.F4.tag L :=
    (B2Q L).subtype.comp (Ξ.symm.toMonoidHom.comp (szEmbed hK (algebraMap K L)))
  have hinj : Function.Injective ρ₂ := by
    intro s t hst
    have h1 : Ξ.symm (szEmbed hK (algebraMap K L) s) = Ξ.symm (szEmbed hK (algebraMap K L) t) :=
      Subtype.ext hst
    exact szEmbed_injective hK (algebraMap K L) (Ξ.symm.injective h1)
  have hrange : ρ₂.range = rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
      twistedFixed D.F n' := by
    ext g
    rw [hspan]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨(Ξ.symm (szEmbed hK (algebraMap K L) s)).2, ?_⟩
      exact (hΞ (Ξ.symm (szEmbed hK (algebraMap K L) s))).2 ⟨s, by simp⟩
    · rintro ⟨hgQ, hgT⟩
      have h1 := (hΞ ⟨g, hgQ⟩).1 hgT
      obtain ⟨s, hs⟩ := h1
      refine ⟨s, ?_⟩
      show ((Ξ.symm (szEmbed hK (algebraMap K L) s) : B2Q L) : ModGL ReeTag.F4.tag L) = g
      rw [hs]
      simp
  refine ⟨⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩, ?_⟩
  intro ha y hy hcomm
  rw [hspan] at hy
  have hY : ∀ s : suzukiGroup a K,
      Ξ ⟨y, hy⟩ * szEmbed hK (algebraMap K L) s = szEmbed hK (algebraMap K L) s * Ξ ⟨y, hy⟩ := by
    intro s
    have hu : ρ₂ s ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
        twistedFixed D.F n' := by
      rw [← hrange]
      exact ⟨s, rfl⟩
    have hc := hcomm _ hu
    have hc' : (⟨y, hy⟩ : B2Q L) * Ξ.symm (szEmbed hK (algebraMap K L) s) =
        Ξ.symm (szEmbed hK (algebraMap K L) s) * ⟨y, hy⟩ := Subtype.ext hc
    have := congrArg Ξ hc'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  have h1 := szEmbed_centralizer_trivial ha hK (algebraMap K L) _ hY
  have h2 : (⟨y, hy⟩ : B2Q L) = 1 := Ξ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end CFSG.RankThree.PartOne.TCX.Ree
