module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Suz
public import CFSG.Sporadic.SuzOddCore.SylowFusion
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import Certificates.Certificate8163

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem suzNC2_check :
    ∃ (t g x : NativeSporadic.Suz) (S : Subgroup NativeSporadic.Suz),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
      7 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.Suz)) :=
  Certificates.certificate8163

open CFSG.Sporadic.SuzOddCore in
theorem card_centralizer_Suz_of_seven_dvd
    {u : NativeSporadic.Suz} (hu : orderOf u = 2)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz))) :
    Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz)) = 161280 := by
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.Suz)) =
      Nat.card ↥(suzM ⊓ Subgroup.centralizer
        ({((suzEquivM u : suzM) : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782)))) := by
    rw [@card_centralizer_mulEquiv NativeSporadic.Suz suzM Units.instGroup (Subgroup.toGroup _)
      suzEquivM u, card_centralizer_subgroup]
  have hg : orderOf ((suzEquivM u : suzM) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, @MulEquiv.orderOf_eq NativeSporadic.Suz Units.instMonoid suzM _
      suzEquivM u, hu]
  have hcM : ∀ i < 4, Nat.card ↥(suzM ⊓ Subgroup.centralizer
      ({suzInv i} : Set (Equiv.Perm (Fin 1782)))) = invInnerOrders.getD i 0 := fun i hi => by
    rw [inf_comm, ← card_invE hi, invE_eq_centM hi]
    rfl
  obtain ⟨c, hc, h | h⟩ := suzM_involution_class (suzEquivM u).2 hg
  all_goals
    rw [← h, card_inf_centralizer_conj suzM (fun m hm => suzT_conj_mem_suzM hc hm)
      (fun m hm => by simpa only [inv_inv] using suzT_conj_mem_suzM (suzT.inv_mem hc) hm)] at hcard
  · rw [hcard, hcM 0 (by norm_num)]
    rfl
  · rw [hcard, hcM 1 (by norm_num)] at h7
    exact absurd h7 (by decide)

theorem not_isCharTwoType_Suz
    [Finite NativeSporadic.Suz] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.Suz :=
  not_isCharTwoType_of_nc2Facts' suzNC2_check fun u hu hq => by
    rw [card_centralizer_Suz_of_seven_dvd hu hq,
      factorization_two_of_eq (show 161280 = 2 ^ 9 * 315 by norm_num) (by norm_num)]

theorem excluded433_Suz :
    Excluded433 (.sporadic .Suz) :=
  excluded433_sporadic_of_not_isCharTwoType (T := NativeSporadic.Carrier .Suz)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Suz) not_isCharTwoType_Suz

end CFSG.RankThree.PartTwo.Census
