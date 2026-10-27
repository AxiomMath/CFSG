module

public import CFSG.RankThree.PartOne.KEXC.A1Key

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

theorem a1_level (h : A1Pair i j) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    Nonempty (SL2 K ≃* ↥(rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n')) ∧
      ∀ y ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))),
        (∀ u ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
          twistedFixed D.F n', y * u = u * y) → y = 1 := by
  classical
  obtain ⟨f, hfinj, hfA, hXmem, hPdesc, hCtriv⟩ := a1_exists_struct D h hK hn' hperm hstab
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hABle : rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) ⊔
      rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hadjA : ∀ x ∈ rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1),
      x ∈ adjointGroup ReeTag.F4.tag L := fun x hx => hABle (Subgroup.mem_sup_left hx)
  have hφ1 : twistMap D.F n' (1 : ModGL ReeTag.F4.tag L) = 1 := by
    unfold twistMap
    rw [Fext_one]
    group
  let ρ₁ : SL2 K →* ModGL ReeTag.F4.tag L :=
    { toFun := fun B => f B * twistMap D.F n' (f B)
      map_one' := by rw [map_one, hφ1, mul_one]
      map_mul' := fun B B' => by
        have hB := hfA B
        have hB' := hfA B'
        have hc := hAB _ hB' _ (hφA _ hB)
        rw [map_mul, twistMap_mul n' (hadjA _ hB) (hadjA _ hB')]
        calc f B * f B' * (twistMap D.F n' (f B) * twistMap D.F n' (f B'))
            = f B * (f B' * twistMap D.F n' (f B)) * twistMap D.F n' (f B') := by group
          _ = f B * (twistMap D.F n' (f B) * f B') * twistMap D.F n' (f B') := by rw [hc]
          _ = f B * twistMap D.F n' (f B) * (f B' * twistMap D.F n' (f B')) := by group }
  have hρ₁ : ∀ B, ρ₁ B = f B * twistMap D.F n' (f B) := fun B => rfl
  have hinj : Function.Injective ρ₁ := by
    intro B B' hBB
    rw [hρ₁, hρ₁] at hBB
    have hB := hfA B
    have hB' := hfA B'
    obtain ⟨h1, -⟩ := mul_inj_of_disjoint hdisj hB hB' (hφA _ hB) (hφA _ hB') hBB
    exact hfinj h1
  have hrange : ρ₁.range = rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      twistedFixed D.F n' := by
    ext g
    rw [hPdesc g]
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨B, rfl⟩
  refine ⟨⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩, ?_⟩
  intro y hy hcomm
  exact a1_centralizer_trivial D h hK hn' hperm hstab hy hcomm

end CFSG.RankThree.PartOne.TCX.Ree
