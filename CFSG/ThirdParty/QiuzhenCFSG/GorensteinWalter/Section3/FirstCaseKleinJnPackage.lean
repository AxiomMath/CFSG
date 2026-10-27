module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
namespace CFSG.GorensteinWalter
universe u

public theorem firstCase_klein_Jn_package {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) :
    ∃ b0 b1 b2 b3 b4 : ℕ, ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n := by
  let b0 := cosetInvolution_b c.Hhat 0
  let b1 := cosetInvolution_b c.Hhat 1
  let b2 := cosetInvolution_b c.Hhat 2
  let b3 := cosetInvolution_b c.Hhat 3
  let b4 := cosetInvolution_b c.Hhat 4
  refine ⟨b0, b1, b2, b3, b4, ?_⟩
  intro n hn
  have hJn := firstCase_J_n_card c n
  interval_cases n
  · change Nat.card {x : G // x ∈ firstCaseJ c 0} =
      0 * cosetInvolution_b c.Hhat 0
    simpa using hJn
  · change Nat.card {x : G // x ∈ firstCaseJ c 1} =
      1 * cosetInvolution_b c.Hhat 1
    simpa using hJn
  · change Nat.card {x : G // x ∈ firstCaseJ c 2} =
      2 * cosetInvolution_b c.Hhat 2
    simpa using hJn
  · change Nat.card {x : G // x ∈ firstCaseJ c 3} =
      3 * cosetInvolution_b c.Hhat 3
    simpa using hJn
  · change Nat.card {x : G // x ∈ firstCaseJ c 4} =
      4 * cosetInvolution_b c.Hhat 4
    simpa using hJn

end CFSG.GorensteinWalter
