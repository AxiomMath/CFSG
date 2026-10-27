module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourZK
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8A
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Vol2.Ch10.SecB.C11AmS
open scoped IsMulCommutative

theorem factA7FF_of (h51 : AsB51) : FactA7FF := by
  intro G _ _ K Q W hK ⟨e⟩ hQS hQK hSQ hred hKW hJW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have := hWe.1
  have hYK : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hQK
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hY2 : ∀ y ∈ K ⊔ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K := InternalSec.two_of_sup hQS.2.1 hQK
  have hSQK : SQTKGroup ↥K := K8.sqtkGroup_of_le hSQ le_sup_left
  obtain ⟨hB, hN⟩ := K8.b51Hyp_A7 hQS le_sup_left hYK hY2 hWe hred (Or.inl ⟨e⟩) hSQK hKW hJW
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨hP1, hP2, -⟩ := h51 ↥W hV2 _ _ hB
  have hshape := K8.part1_shape hP1 hN
  have hcard : Nat.card ↥(autOn K W) = 2520 := hshape.elim K8.card_of_alt7 K8.card_of_a7Four
  have hdir := K8.part2_direct hP2 hcard
  have hUW : ⁅W, K⁆ ≤ W := A7ZK.commutator_le_left_of_le_normalizer hKN
  have hcomm : commV (autOn K W) = (⁅W, K⁆).subgroupOf W := commV_autOn_eq1527d hKN
  have hfix : fixV (autOn K W) = (Subgroup.centralizer (K : Set G)).subgroupOf W := by
    ext v
    rw [mem_fixV, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      have hmem : A4.actionOn W K hKN ⟨k, hk⟩ ∈ autOn K W :=
        (A4.mem_autOn_iff hKN).mpr ⟨⟨k, hk⟩, rfl⟩
      have h1 := congrArg Subtype.val (h _ hmem)
      rw [A4.actionOn_apply_coe] at h1
      calc k * (v : G) = k * (v : G) * k⁻¹ * k := by group
        _ = (v : G) * k := by rw [h1]
    · intro h a ha
      obtain ⟨⟨k, hk⟩, rfl⟩ := (A4.mem_autOn_iff hKN).mp ha
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      simp only
      rw [h k hk]
      group
  have hirrp : commV (autOn K W) ∈ IrrPlus (autOn K W) ⊤ := by
    obtain ⟨-, hc⟩ := hP1
    rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
    · exact hi.1
    · exfalso
      obtain ⟨-, n, F, hF, hFin, hFc, I, π, -, -, hreal, -⟩ := hii
      have hc := card_eq_of_nat_realizes1527d (hreal 0)
      rw [card_statedSL_three1527d, hFc] at hc
      exact K8.sl3_ne hN hc.symm
    · exfalso
      obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
      exact K8.not_surj_sl hn hN π hr1.1
    · exfalso
      obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
      exact K8.not_surj_sl hn hN π (hreal ⟨0, hk1⟩).1
  have hfixed : XMod.fixed ↥(autOn K W) (commV (autOn K W)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ commV (autOn K W) ⊓ fixV (autOn K W) :=
      ⟨hx.1, mem_fixV.mpr fun a ha => hx.2 ⟨a, ha⟩⟩
    rw [hdir.2] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have h1 := congrArg (Subgroup.map W.subtype) hdir.1
    rw [Subgroup.map_sup, hcomm, hfix, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      inf_of_le_left hUW, inf_comm] at h1
    exact h1
  ·
    rw [eq_bot_iff]
    rintro x ⟨hx, hxc⟩
    have h1 : (⟨x, hUW hx⟩ : ↥W) ∈ commV (autOn K W) ⊓ fixV (autOn K W) := by
      rw [hcomm, hfix]
      exact ⟨hx, hxc⟩
    rw [hdir.2, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  ·
    intro J hJU hKJ
    have hJW : J ≤ W := hJU.trans hUW
    have hinv : XMod.IsInv ↥(autOn K W) (J.subgroupOf W) := by
      intro a x hx
      obtain ⟨⟨k, hk⟩, hka⟩ := (A4.mem_autOn_iff hKN).mp a.2
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      show (((a : MulAut ↥W) x : ↥W) : G) ∈ J
      rw [← hka, A4.actionOn_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hKJ hk) _).mp hx
    have hle : J.subgroupOf W ≤ commV (autOn K W) := by
      rw [hcomm]
      exact fun x hx => hJU hx
    rcases hirrp.2.2.2.2 (J.subgroupOf W) hinv (by rw [hfixed]; exact bot_le) hle with h | h
    · left
      rw [hfixed] at h
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hJW hx⟩ : ↥W) ∈ J.subgroupOf W := hx
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    · right
      rw [hcomm, Subgroup.subgroupOf_inj, inf_of_le_left hJW, inf_of_le_left hUW] at h
      exact h
  ·
    have hZ0 : fixV (autOn K W) ⊓ commV (autOn K W) = ⊥ := by
      rw [inf_comm]
      exact hdir.2
    rw [hZ0] at hshape
    have hcU : Nat.card ↥⁅W, K⁆ = Nat.card ↥(commV (autOn K W)) := by
      rw [hcomm]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv).symm
    rcases hshape with h7 | h4
    · right
      obtain ⟨π, hπ⟩ := h7
      rw [hcU, FFC.card_eq_of_realizes (D := FFModel.altDn 7) K8.dnZ_seven hπ,
        Subgroup.card_bot, one_mul]
      exact Explicit.card_coreMod (n := 7) (by norm_num)
    · left
      rw [hcU, K8.card_of_a7Four_bot h4]
      norm_num

end CFSG.Quasithin.H13
