module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFive
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

theorem pCoreOf_five_centralizer_eq_bot (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hBM : ¬ Subgroup.centralizer (B : Set G) ≤ D.M) :
    CFSG.Open.pCoreOf 5 (Subgroup.centralizer (B : Set G)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := Subgroup.centralizer (B : Set G)
  have hBL : B ≤ c.L := hBA.trans (F.A_le.trans F.P_le_L)
  have hBpg : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB3]; norm_num)
  have h5dvd : 5 ∣ Nat.card (C ⊓ D.M : Subgroup G) :=
    five_dvd_card_centralizer_inf F (fun x hx h => (a10Hom_eq_one_iff F hx).mp h)
      (three_le_pRank_five F) hBL hBpg
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(C ⊓ D.M : Subgroup G)) 5 h5dvd
  have hxordG : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hxord
  have hxne : (x : G) ≠ 1 := fun h1 => by simp [h1] at hxordG
  let R : Subgroup G := Subgroup.zpowers (x : G)
  have hR5 : IsPGroup 5 R := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card ↥(Subgroup.zpowers (x : G)) = 5 ^ 1
    rw [Nat.card_zpowers, hxordG]
    norm_num
  have hRne : R ≠ ⊥ := fun hbot => hxne (Subgroup.zpowers_eq_bot.mp hbot)
  have hRle : R ≤ C ⊓ D.M := by
    change Subgroup.zpowers (x : G) ≤ C ⊓ D.M
    exact Subgroup.zpowers_le.mpr x.2
  have hX5 : IsPGroup 5 (CFSG.Open.pCoreOf 5 C) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 5 C
  have hCX : C ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 5 C : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 5 C
  have hRnorm : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 5 C : Set G) :=
    (hRle.trans inf_le_left).trans hCX
  have hT5 : IsPGroup 5 ↥(R ⊔ CFSG.Open.pCoreOf 5 C) :=
    IsPGroup.to_sup_of_normal_right' hR5 hX5 hRnorm
  have hRM : R ≤ D.M := hRle.trans inf_le_right
  have hSne : (R ⊔ CFSG.Open.pCoreOf 5 C) ⊓ D.M ≠ ⊥ := by
    intro hbot
    have hle : R ≤ (R ⊔ CFSG.Open.pCoreOf 5 C) ⊓ D.M := le_inf le_sup_left hRM
    rw [hbot] at hle
    exact hRne (le_bot_iff.mp hle)
  have hTM : R ⊔ CFSG.Open.pCoreOf 5 C ≤ D.M :=
    (c.isStronglyPEmbedded_of_mem_sigma (by rw [F.sig]; simp)).le_of_isPGroup_inf hT5 hSne
  have hXM : CFSG.Open.pCoreOf 5 C ≤ D.M := le_sup_right.trans hTM
  by_contra hXne
  exact hBM (hCX.trans (F.normalizer_le_of_isPGroup_five hX5 hXne hXM))

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
