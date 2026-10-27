module

public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinNodes
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
  CFSG.StandardType.RankOneXfer

theorem ggLongRoot_minusDatum_single {m : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Fin (m - 1)} (hk : k.val + 1 < m - 1) :
    GGLongRoot (minusDatum m hirr) (Pi.single k 1) := by
  have hm1 : 0 < m - 1 := by omega
  have hirrB : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible (cartanB (m - 1)) :=
    CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanB hm1
  have hdiv : (minusDatum m hirr).divisible = ∅ := rfl
  obtain ⟨r, hr⟩ := CFSG.LieType.HighestRoot.exists_isHighestRoot
    (D := minusDatum m hirr) hirrB hdiv hm1
  have hrL : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot (minusDatum m hirr) r :=
    ⟨hr.mem_roots, hr.longest⟩
  have hkL : CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot (minusDatum m hirr)
      (Pi.single k 1) :=
    CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanB (m := m - 1) hm1 rfl
      (minusDatum m hirr).isFiniteType hk
  obtain ⟨w, hw⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_of_isLongest
    (A := cartanB (m - 1)) (hA := isFiniteType_cartanB (m - 1))
    (D := (minusDatum m hirr).divisible) hirrB
    (fun i hi => by rw [hdiv] at hi; exact absurd hi (Set.notMem_empty i)) hrL hkL
  exact ⟨w, r, hr.mem_roots, hr.height_le, hw.symm⟩


theorem exists_selectedSL2Model_POmegaMinus_long {n : ℕ} (hn : 4 ≤ n) :
    ∃ δ : Fin (ggU .POmegaMinus n 1).D.rank → ℤ, δ ∈ (ggU .POmegaMinus n 1).D.roots ∧
      GGLongRoot (ggU .POmegaMinus n 1).D δ ∧
      Nonempty (SelectedSL2Model (ggU .POmegaMinus n 1).D (GaloisField 2 1) δ) := by
  have hirr := minusCoeffs_irr 2 1
  let k : Fin (n - 1) := ⟨0, by omega⟩
  have hk : k.val + 1 < n - 1 := by
    change 0 + 1 < n - 1
    omega
  have hroot : (Pi.single k 1 : Fin (n - 1) → ℤ) ∈ (minusDatum n hirr).roots :=
    (isCTRootSystem (minusDatum n hirr).isFiniteType (minusDatum n hirr).divisible).single_mem k
  have hupper : (sl2UpperUniSub (GaloisField 2 1)).map
      (rLong n (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 hk) =
        (minusDatum n hirr).rootGroup (Pi.single k 1) := by
    ext g
    constructor
    · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
      rw [← LevisExtras.tv01_eq_sl2Upper]
      exact rLong_upper hirr hk c
    · intro hg
      obtain ⟨c, rfl⟩ := rLong_param_upper hirr hk g hg
      exact ⟨tv 0 1 c, ⟨c, (LevisExtras.tv01_eq_sl2Upper c).symm⟩, rfl⟩
  exact ⟨Pi.single k 1, hroot, ggLongRoot_minusDatum_single hirr hk,
    ⟨SelectedSL2Model.ofGF2Upper (minusDatum n hirr) (Pi.single k 1) hroot _
      (rLong_injective hk) hupper⟩⟩

end CFSG.StandardType.SelectedRoot

end
