module

public import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck
public import Certificates.Data.Kernel.RankElim

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

@[expose] def CoverElim : Prop :=
  ∃ (par dep : ℕ → ℕ) (rk ap bp : ℕ → ℕ → ℕ),
    CFSG.KC.RankElim.ok 8991 nbrC par dep rk ap bp (triC nbrC) = true

end CFSG.Sporadic.SuzRecog.LevelTwoCover
