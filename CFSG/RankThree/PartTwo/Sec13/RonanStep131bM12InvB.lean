module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvTools
import CFSG.RankThree.PartTwo.Sec13.Item137ProofM12

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open M12Inv in
theorem invPartB_of (hK18 : KFacts.KS18M12) : InvPartB := by
  intro G _ _ A c L E F a b R Y hY hMθ hbY hF9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Sec13Data G F b Y := hY.hD
  have hEe := hY.hCfg.hEe
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hD.isElemAbelian
  have hF27 : Nat.card F = 27 := hD.card_eq
  have hbE := hY.hbE
  have hbF : b ∈ F := hD.mem_A
  have hb3 : b ^ 3 = 1 := hEe.2 b hbE
  have hb1 : b ≠ 1 := hD.ne_one
  have hc3 : c ^ 3 = 1 := hEe.2 c hY.hcE
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hKe : Y ≤ Subgroup.centralizer ({b} : Set G) := hD.le_centralizer
  have hbc : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKe hy)
  obtain ⟨-, hZ, hinn, -⟩ := hK18 (Y ⧸ aschbacherSolvableCore 3 Y) hMθ
  have hinner : ∀ σ : MulAut (Y ⧸ aschbacherSolvableCore 3 Y), σ ^ 3 = 1 →
      σ ∈ (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →* _).range := by
    intro σ hσ
    obtain ⟨y, hy⟩ := hinn σ ⟨1, by rw [pow_one]; exact hσ⟩
    exact ⟨y, hy.symm⟩
  have hFdec : F = Subgroup.zpowers b ⊔ (F ⊓ Y) := by
    have hle : Subgroup.zpowers b ⊔ (F ⊓ Y) ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr hbF) inf_le_left
    have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ (F ⊓ Y : Subgroup G), x * y = y * x := by
      intro x hx y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hbc y hy.2).symm j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hinf : Subgroup.zpowers b ⊓ (F ⊓ Y) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (zpowers_inf_eq_bot' hb3 hbY).le)
    have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
    have h27 : Nat.card (Subgroup.zpowers b ⊔ (F ⊓ Y) : Subgroup G) = 27 := by
      rw [hinf, Subgroup.card_bot, mul_one, hcardb, hF9] at hcard
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF27, h27])).symm
  have hPexp : ∀ x ∈ E ⊔ F, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ ((F ⊔ E : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right F E hY.hFE] at hx'
    obtain ⟨f, hf, e, he, rfl⟩ := hx'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hY.hcomm f hf e he)
    refine pow_three_mul_of_central (u := c ^ (-k)) (hFe.2 f hf) (hEe.2 e he) ?_
      (zpow_pow_three_eq_one hc3 _) ?_ ?_
    · rw [zpow_neg, hk]
      group
    · exact (Commute.zpow_left (hFc c hY.hcF f hf) (-k)).eq
    · exact (Commute.zpow_left (hEc c hY.hcE e he) (-k)).eq
  have hP3 : IsPGroup 3 (E ⊔ F : Subgroup G) :=
    fun x => ⟨1, Subtype.ext (by simpa using hPexp x x.2)⟩
  have hPN : E ⊔ F ≤ Subgroup.normalizer (Y : Set G) := sup_le hY.hEY hD.le_normalizer
  have hPe : ∀ x ∈ E ⊔ F, x * b = b * x := by
    have : E ⊔ F ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hEc e he b hbE))
        (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr (hFc f hf b hbF))
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  exact le_zpowers_sup_of_inner hZ hinner hFe hD.mem_partTwoF.2.1 hFdec hKe le_sup_right hP3 hPexp
    hPN hPe

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
