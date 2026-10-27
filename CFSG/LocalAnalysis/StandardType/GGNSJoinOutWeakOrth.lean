module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutOfWeak
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameConcl
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

namespace NSJoin

section Orth


theorem nsWeakNonUnitaryInputOf_of_orthPos {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hTAD : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → NSTypeAD M)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRig : GGLabelRigidInput) (hD : PhanDInput2) (hPumpNbr : NSPumpNbrInput)
    (hM2 : OrthTorus.OrthRankOneModelInput) (hM4 : OrthTorus.OrthPairModelInput)
    (hM5 : OrthTorus.OrthGenModelInput) (hPos : NSWeakOrthPosInputOf T) :
    NSWeakNonUnitaryInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard K hw hnsK hNU
  obtain ⟨Φ, hΦ⟩ := hPos G p B Bs x L D J 𝒦 hcfg hns hguard K hw hnsK hNU
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨y, hK⟩, hKA⟩ := hw
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT3 hT
  have hguardAD : NSJoinGuard p L Bs 𝒦 := ⟨ι, M, e, hpres, hTAD hT, hbig⟩
  obtain ⟨hPumpWe, -⟩ := hPumpNbr G p B Bs x L D J 𝒦 ⟨hcfg, hns, hguardAD⟩ y K hK
  obtain ⟨ιK, MK, hMKweyl, f, hfrefl⟩ := hPumpWe
  have hpresK : GGCoxeterPres p (ggAutomizer K Bs) MK f := ⟨hMKweyl, hfrefl⟩
  have hriC : ∀ i : ιK, ((f (MK.simple i) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) ∈
      ggCoxRefl M e :=
    fun i => ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (hKA (f (MK.simple i)).2) (hfrefl i)
  have h3MK : ∀ i j : ιK, i ≠ j → MK.M i j ≤ 3 := by
    intro i j _hij
    have hf := ggCoxRefl_mul_orderOf_le_three hpres.1 h3 (hriC i) (hriC j)
    have hs : (MK.simple i * MK.simple j) ^ 2 = 1 ∨ (MK.simple i * MK.simple j) ^ 3 = 1 := by
      rcases hf with h2 | h3
      · left
        refine f.injective ?_
        apply Subtype.val_injective
        simpa [map_pow, map_mul, Subgroup.coe_mul, Subgroup.coe_pow] using h2
      · right
        refine f.injective ?_
        apply Subtype.val_injective
        simpa [map_pow, map_mul, Subgroup.coe_mul, Subgroup.coe_pow] using h3
    rcases hs with h2 | h3
    · have hdvd : MK.M i j ∣ 2 := by
        rw [← MK.toCoxeterSystem.orderOf_simple_mul_simple i j]
        exact orderOf_dvd_of_pow_eq_one h2
      exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
    · have hdvd : MK.M i j ∣ 3 := by
        rw [← MK.toCoxeterSystem.orderOf_simple_mul_simple i j]
        exact orderOf_dvd_of_pow_eq_one h3
      exact Nat.le_of_dvd (by norm_num) hdvd
  have hconnK : GGSimplyLacedConnected MK := ggSimplyLacedConnected_of_weyl hMKweyl h3MK
  have hr0 : (⟨0, by have := Φ.hr; omega⟩ : Fin Φ.r) ≠ ⟨1, by have := Φ.hr; omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  obtain ⟨a₀, ha₀A, ha₀R, ha₀Rk1⟩ := Φ.rk1_swap hRig hM2 hp2 hΦ hnsK hr0
  refine ⟨?_, Φ.le_iSup_rankOne hp2 hD hM2 hM4 hM5 hΦ⟩
  intro r hrA hrR
  have hrC : r ∈ ggCoxRefl MK f :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top K Bs) hpresK h3MK hrA hrR
  have ha₀C : a₀ ∈ ggCoxRefl MK f :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top K Bs) hpresK h3MK ha₀A ha₀R
  obtain ⟨c, hcA, hc⟩ := ggCoxRefl_conj_of_connected f hconnK ha₀C hrC
  rw [hc]
  exact ggRk1Concl_conj ha₀Rk1 hcA

end Orth

end NSJoin

end CFSG.StandardType

end
