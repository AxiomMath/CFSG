module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12Mixed
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def CfgEA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Cfg G A c L E → Nat.card (E ⊓ A : Subgroup G) = 9

theorem ycfgMixed_of_EA9 (h : CfgEA9) : YCfgMixed := by
  intro G _ _ A c L E F a b R Y hY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCfg := hY.hCfg
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hCfg
  have hEA9 : Nat.card (E ⊓ A : Subgroup G) = 9 := h G A c L E hY.hCfg
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hD.isElemAbelian
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := hY.hD.isElemAbelian
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haA : a ∈ A := hY.haA
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  obtain ⟨hbF, -, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hY.hD.zpowers_mem_omegaA
  have hF27 : Nat.card F = 27 := hY.hD.mem_partTwoE.2.1
  have hFmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → F ≤ B → B = F :=
    hY.hD.mem_partTwoF.2.1
  set C : Subgroup G := E ⊓ Subgroup.centralizer ({a} : Set G) with hCdef
  have hEAC : E ⊓ A ≤ C := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (hAc a haA x hx.2).symm⟩
  have hEFC : E ⊓ F ≤ C := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr (hFc a hY.haF x hx.2).symm⟩
  have hCne : C ≠ E := by
    intro hCE
    have hEa : E ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [← hCE]; exact inf_le_right
    have hsup := Sec5.isElemAbelian_sup_zpowers hEe hY.haE ha3 (fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hEa hx))
    have hFle : F ≤ E ⊔ Subgroup.zpowers a := by
      rw [hY.hFgen]
      exact sup_le (le_sup_right) (inf_le_left.trans le_sup_left)
    have hEq := hFmax _ hsup.1 hFle
    have h81 := hsup.2
    rw [hEq, hF27, hE27] at h81
    omega
  have hC9 : Nat.card C ≤ 9 := by
    have hdvd : Nat.card C ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · calc Nat.card C = 3 ^ i := hn
        _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 := by norm_num
    · exfalso
      have hi3 : i = 3 := by omega
      apply hCne
      exact Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ E) (by rw [hn, hi3, hE27]; norm_num)
  have hEAeq : E ⊓ A = C :=
    Subgroup.eq_of_le_of_card_ge hEAC (by rw [hEA9]; exact hC9)
  have hEFeq : E ⊓ F = C :=
    Subgroup.eq_of_le_of_card_ge hEFC (by rw [hY.hFEcard]; exact hC9)
  have hbA : b ∈ A := by
    have hb : b ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨hY.hbE, hbF⟩
    rw [hEFeq, ← hEAeq] at hb
    exact hb.2
  have hAC : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
    Item131bProof.inf_thetaQuotCentralizer_eq hD
  have hAL : A ⊓ L ≤ Subgroup.zpowers c := Res2Proof.inf_le_zpowers_of_isSLThreePiTwo hD hSL2
  refine ⟨fun hb => hY.hcb ?_, fun hb => hY.hcb ?_⟩
  · have : b ∈ A ⊓ Sec4.thetaQuotCentralizer L := ⟨hbA, hb.2⟩
    rwa [hAC] at this
  · exact hAL ⟨hbA, hb.2⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
