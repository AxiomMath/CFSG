module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanDData
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggSecFiveData_res_of_dataRes
    (hLevi : GGSecFiveLeviData) (hA : GGSecFiveDataResAt (fun M => GGIsWeylMatrixA M))
    (hB : GGSecFiveDataResAt (fun M => GGIsWeylMatrixB M))
    (hD : GGSecFiveDataResAt (fun M => GGIsWeylMatrixD M))
    (hE : GGSecFiveDataResAt (fun M => GGIsWeylMatrixE M))
    (hF : GGSecFiveDataResAt (fun M => GGIsWeylMatrixF4 M))
    (hG : GGSecFiveDataResAt (fun M => GGIsWeylMatrixG2 M))
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hNotReg : ¬ GGSecFiveTier1Region p B Bs x L D J) : GGSecFiveData p B x L D J := by
  by_cases hLev : GGSecFiveLeviCase p B Bs x L D J
  · exact hLevi G p B Bs x L D J hR hW hLev
  obtain ⟨𝒦, hMax⟩ := exists_ggMaximalJoin hR hW
  have hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := ⟨hR, hW, hLev, hMax⟩
  obtain ⟨ι, M, hWM, e, hrefl⟩ := hMax.2.1
  have hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := ⟨hWM, hrefl⟩
  rcases hWM with ⟨n, e', hn, hM | ⟨hn2, hM⟩ | ⟨hn4, hM⟩⟩ | hE6 | hE7 | hE8 | hF4 | hG2
  · exact hA G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn, hM⟩
  · exact hB G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn2, hM⟩
  · exact hD G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres ⟨n, e', hn4, hM⟩
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inl hE6)
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inr (Or.inl hE7))
  · exact hE G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres (Or.inr (Or.inr hE8))
  · exact hF G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hF4
  · exact hG G p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hG2

theorem ggSecFiveDataResAt_G2_of_tbfix
    (hT : GGTBFixInput) : GGSecFiveDataResAt (fun M => GGIsWeylMatrixG2 M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres hG2
  exfalso
  obtain ⟨e', -⟩ := hG2
  have hR := hcfg.1
  have hWC := hcfg.2.1
  obtain ⟨hp, hBs, hxBs, h4⟩ := ggConfig_bstar_facts hR.1
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hR.1.1.2.2.2.2.2.2.2 hR.1.2.2
  have hfix := hT G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr
    (hWC y K hnbr) (Or.inr hWC)
  haveI : Fintype ι := Fintype.ofEquiv (Fin 2) e'
  let F₀ : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
  have hWT : GGWeylOfType p M (ggAutomizerJoin L Bs 𝒦) := ⟨e, hpres.2⟩
  have hAL : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have h1 : Nat.card Bs ≤ p ^ Fintype.card ι * Nat.card F₀ :=
    card_le_pow_mul_card_of_weylOfType hWT F₀
      (fun b hb => hfix b (fun φ hφ => hb φ (hAL hφ)))
  have hι : Fintype.card ι = 2 := by
    rw [Fintype.card_congr e'.symm, Fintype.card_fin]
  have h2 : Nat.card F₀ ≤ p := by
    refine card_le_of_le_zpowers hp hBs hxBs F₀ (fun b hb => ?_)
    exact Subgroup.mem_subgroupOf.mp hb
  have h3 : Nat.card Bs ≤ p ^ 3 := by
    calc Nat.card Bs ≤ p ^ 2 * Nat.card F₀ := by rw [← hι]; exact h1
      _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ h2
      _ = p ^ 3 := by ring
  exact absurd (h4.trans h3)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 3 < 4)))

end CFSG.StandardType

end
