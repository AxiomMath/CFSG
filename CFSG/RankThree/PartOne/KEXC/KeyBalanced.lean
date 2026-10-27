module

public import CFSG.RankThree.PartOne.KEXC.B2Key
public import CFSG.RankThree.PartOne.KEXC.A1Key

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Balanced

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

omit [CharP L 2] [IsAlgClosed L] [Algebra K L] [CharP K ReeTag.F4.prime] [Finite K] in
theorem rootChar_eq_one_of_support {J : Finset (Fin ReeTag.F4.tag.rank)}
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hb : ∀ k ∈ J, b k = 1)
    {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank))) :
    rootChar b α = 1 := by
  unfold rootChar
  refine Finset.prod_eq_one fun k _ => ?_
  by_cases hk : k ∈ J
  · rw [hb k hk, one_zpow]
  · rw [hα.2 k (by simpa using hk), zpow_zero]

theorem key_balanced (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} (hn' : n' ∈ adjointGroup ReeTag.F4.tag L)
    {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {R : Subgroup (ModGL ReeTag.F4.tag L)} (hR0 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRP : R ≤ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n')
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hbp : ∀ k, b k ^ p = 1)
    (hbfix : rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n')
    (hbN : rootDiagUnit ReeTag.F4.tag b ∈ Subgroup.normalizer (R : Set (ModGL ReeTag.F4.tag L))) :
    ∀ k ∈ J, b k = 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨k₀, hk₀, hk₀1⟩ := hno
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · exact absurd hk₀ (Finset.notMem_empty _)
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    refine a1_key D a1Pair_zero_two hK hn' hperm hstab hp hp2 hpq hR0 hR2 hRP hbp hbfix hbN ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀
    rcases hk₀ with rfl | rfl
    · exact Or.inl hk₀1
    · exact Or.inr hk₀1
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    refine a1_key D a1Pair_zero_three hK hn' hperm hstab hp hp2 hpq hR0 hR2 hRP hbp hbfix hbN ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀
    rcases hk₀ with rfl | rfl
    · exact Or.inl hk₀1
    · exact Or.inr hk₀1
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    refine a1_key D a1Pair_one_three hK hn' hperm hstab hp hp2 hpq hR0 hR2 hRP hbp hbfix hbN ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀
    rcases hk₀ with rfl | rfl
    · exact Or.inl hk₀1
    · exact Or.inr hk₀1
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hstab hRP
    rw [← B2Q_eq_rootSpan] at hRP
    have hk₀' : k₀ ∈ f4B2Support := by
      rw [← hJs]
      exact hk₀
    refine b2_key D ha hK hperm hstab hp hp2 hpq hR0 hR2 hRP hbp hbfix hbN ?_
    rcases (mem_f4B2Support k₀).1 hk₀' with rfl | rfl
    · exact Or.inl hk₀1
    · exact Or.inr hk₀1

end Balanced

end CFSG.RankThree.PartOne.KEXC
