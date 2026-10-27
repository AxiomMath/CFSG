module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSU6SmallInput_of_frame

    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) : GGSecFiveNSU6SmallInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA hrow
  obtain ⟨n, e', hn, hM⟩ := hA
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hP⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨⟨⟨hlabs, hpd⟩, hn1, hr5⟩, -⟩ := hP
  have htag : lab.tag = .twA := by
    rcases hlabs with ⟨ht, -⟩ | ⟨-, hr3⟩
    · exact ht
    · omega
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg
  have hp3 : p = 3 := by
    rw [hn1] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpd)
  haveI : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hconf, hcfg.1.2.1, hcfg.1.2.2.1, hcfg.1.2.2.2.1, hN, hcfg.2.1 y K hN, Or.inr hcfg.2.1⟩
  have hdvd3 : 3 ∣ 2 ^ lab.n + 1 := by
    rw [hn1]
    norm_num
  obtain ⟨-, -, ⟨iso⟩⟩ := ggTwA5Three_frame ggLabelRigidInput_holds hLB hPJ hH
    (Or.inl ⟨rfl, rfl⟩) hp3 hΛ hhas ⟨htag, hr5, hdvd3⟩
  have h6 : (6 : ℕ).factorial = 720 := by decide
  have hAL : Nat.card ↥(ggAutomizer L Bs) = 720 := by
    rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      h6]
  have hJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = (n + 1).factorial := by
    rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, l05nK3a_card_coxeterA]
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have hle : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) :=
    Subgroup.card_le_of_le (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
  have h120 : (n + 1).factorial ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
  rw [hAL, hJoin] at hle
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

end CFSG.StandardType

end
