module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A5
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Hyp11Bridge
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.1: the maximal involution centralizer has two involution classes

This acyclic owner module extracts the proof formerly trapped in
`GorensteinWalter.Section2.Basic`.  It combines the two Section 2 preamble
facts with Bender--Glauberman Theorem B.  If `Ĥ` had only one class of
involutions, Theorem B would identify `G / O_{2'}(G)` with `A₅`; minimality
has `O_{2'}(G) = 1`, so `G` would be a `D`-group, a contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Lemma 2.1 (Bender, p. 219): `Ĥ` has at least two conjugacy classes of
involutions. -/
public theorem lemma_2_1
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    HasAtLeastTwoInvolutionClasses c.Hhat := by
  classical
  by_contra hclasses
  have honeG := fact_2_preamble_involutions_conjugate_proved hmin
  have hHSU := fact_2_preamble_H_eq_SU_proved hmin c
  rcases exists_benderGlaubermanHyp11_of_centralizerSetup c honeG hHSU with
    ⟨bg, hbgH⟩
  have honeHhat : ∀ x y : G, IsInvolution x → IsInvolution y →
      x ∈ c.Hhat → y ∈ c.Hhat →
        ∃ g : G, g ∈ c.Hhat ∧ g * x * g⁻¹ = y := by
    intro x y hx hy hxH hyH
    by_contra hxy
    apply hclasses
    refine ⟨⟨x, hxH⟩, ⟨y, hyH⟩, ?_, ?_, ?_⟩
    · simpa [IsInvolution] using hx
    · simpa [IsInvolution] using hy
    · intro hconj
      apply hxy
      rcases hconj with ⟨g, hg⟩
      refine ⟨g, g.property, ?_⟩
      simpa using congrArg Subtype.val hg
  have hA5Q := BenderGlauberman.theorem_B bg c.Hhat
    c.Hhat_maximal.ne_top (by rw [hbgH]; exact c.H_le_Hhat) honeHhat
  have hO : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  have qG : G ⧸ pPrimeCore 2 G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq (G := G) hO).trans
      (QuotientGroup.quotientBot (G := G))
  have hDG : IsDGroup G :=
    isDGroup_of_mulEquiv_aFive ⟨qG.symm.trans hA5Q.some⟩
  exact hmin.2.1 hDG

end CFSG.GorensteinWalter
