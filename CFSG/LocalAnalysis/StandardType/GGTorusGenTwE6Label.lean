module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusGen
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_torusGenTableB_twE6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBTwE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨hn, -⟩ := hlab
  obtain ⟨ht, hp5, hpq⟩ := hrow
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  refine TwE6Delta.labelAll ht (Q := fun R _ I => GGTorusGenTableB p R I) ?_
  intro K _ _ hK
  have hI : ∀ φ ∈ TwE6Delta.RecipeI K lab.n, φ ^ p = 1 →
      φ ∈ Set.range (MulAut.conj :
        TwE6Delta.RecipeR K lab.n →* MulAut (TwE6Delta.RecipeR K lab.n)) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hZ : Subgroup.center (TwE6Delta.RecipeR K lab.n) = ⊥ :=
    TwE6Delta.center_recipeR_eq_bot hn hK
  have hcp : GGCenterPrime p (TwE6Delta.RecipeR K lab.n) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  have hgen5 : GGTorusGenR p 5 (TwE6Delta.RecipeR K lab.n) :=
    fun E hE hcard hcent x hx hx1 J hJ c hc hcpow =>
      ggTorusGenR_twE6 hp5 hn hK hpq E hE
        (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 5)) hcard) hcent
        x hx hx1 J hJ c hc hcpow
  have hRk : GGTorusGenTableBRk p (TwE6Delta.RecipeR K lab.n)
      (TwE6Delta.RecipeI K lab.n) (5 + 1) :=
    ggTorusGenTableBRk_of_torusGenR (r := 5) hp hI hZ hcp hgen5
  have hL : GGTorusLift p 5 (TwE6Delta.RecipeR K lab.n) := by
    have h := ggTorusLift_twE6Add_holds hn hK hp hpq
    rwa [TwE6Delta.liftRank_of_ne hp3] at h
  exact ggTorusGenTableB_of_rk (r := 6) hp (by norm_num) (by simpa using hL) hRk

end CFSG.StandardType
