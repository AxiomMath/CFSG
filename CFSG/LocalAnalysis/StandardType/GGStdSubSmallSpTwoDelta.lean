module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem isInner_of_induces {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (a : MulAut L') {φ : MulAut R}
    (hφ : φ ∈ Set.range (MulAut.conj : R →* MulAut R)) (hind : ∀ l, φ (ψ l) = ψ (a l)) :
    ∃ g : L', a = MulAut.conj g := by
  obtain ⟨r, rfl⟩ := hφ
  obtain ⟨g, rfl⟩ := hψ r
  refine ⟨g, ?_⟩
  have key : ∀ l, ψ (a l) = ψ g * ψ l * (ψ g)⁻¹ := fun l => by
    rw [← hind l]
    rfl
  ext l
  rw [MulAut.conj_apply]
  exact TableBSymp.eq_conj_of_induces hker hperf a g key l

namespace SpTwo

theorem ggOutdiagOdd_spTwo {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) :
    GGOutdiagOdd 3 (LargeEvenProj (LargeEvenSpGroup K m)) I :=
  ggOutdiagOdd_of_prime fun φ _ _ => TwoThree.mem_range_conj_sp hK hm φ

theorem ggStdSubTwoTorusDeltaSmall_spTwo
    {K : Type} [Field K] [Finite K]
    [CharP K 2] {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m) (r : ℕ)
    (I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) :
    GGStdSubTwoTorusDeltaSmall 3 r (LargeEvenProj (LargeEvenSpGroup K m)) I := by
  intro L' _ _ ψ hψ hker hperf A _ hAI _ _ hδ
  exfalso
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨-, hδ2⟩ := hδ
  rcases hδ2 with ⟨⟨a', ha', hna⟩, -⟩ | ⟨hdvd, -, -⟩
  · obtain ⟨φ, -, hφ⟩ := hAI a' ha'
    obtain ⟨g, hg⟩ := isInner_of_induces hψ hker hperf a'
      (TwoThree.mem_range_conj_sp hK hm φ) hφ
    exact hna ⟨g, hg.symm⟩
  · exact ggCenterPrime_sp (K := K) (m := m) (p := 3) Nat.prime_three (by norm_num) L' ψ hψ
      hker hperf hdvd

end SpTwo

end CFSG.StandardType

end
