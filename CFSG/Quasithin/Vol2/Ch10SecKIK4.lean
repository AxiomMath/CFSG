module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4p
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Vol2.Ch10SecKIK4d
public import CFSG.Quasithin.Vol2.Ch10SecKIK4e
public import CFSG.Quasithin.Vol2.Ch3Sec3UniqueMax

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

namespace C10KH

variable {G : Type} [Group G]

theorem not_le_centralizer_comm_of_le {J L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hLJ : L ≤ J) (hperf : ⁅L, L⁆ = L)
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    ¬ L ≤ Subgroup.centralizer ((⁅V, J⁆ : Subgroup G) : Set G) := by
  have : IsMulCommutative ↥V := hV.1
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLJ.trans hJN
  have hpA : commutator ↥(autOn L V) = ⊤ := by
    have hpL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
    exact (Group.IsPerfect.ofSurjective (f := InternalSec.autOnHom hLN)
      (InternalSec.autOnHom_surjective hLN)).commutator_eq_top
  intro h
  apply not_le_centralizer_commutator hV hLN hpA hLV
  exact h.trans (Subgroup.centralizer_le (Subgroup.commutator_mono le_rfl hLJ))

end C10KH

open C10KH

theorem factK4_of (h51 : AsB51) (h42 : AsB42) : FactK4 := by
  intro Γ _ _ H R J L V hV hc hA hblock
  obtain ⟨hSQH, -, hRsyl, hJcomp, hHJ, hJR, -, hred, hVJ, hJq, hJRV, hLfam, hLJ, hRL, hLsimple,
    hLV, -⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJH : J ≤ H := le_of_mem_cComp hJcomp
  obtain ⟨hshort, hblk⟩ := shape_of_block hA hblock
  obtain ⟨α, hαs, hαk⟩ := exists_alpha hblk
  have hJN : J ≤ Subgroup.normalizer (V : Set Γ) := hJH.trans hred.2.1
  have hJV : ¬ J ≤ Subgroup.centralizer (V : Set Γ) := fun h => hLV (hLJ.trans h)
  have hCJ := inf_centralizer_eq_pCoreOf hred hJH hHJ hJN hJV α hαs hαk
  refine ⟨hCJ, ?_⟩
  have hRJ : R ≤ Subgroup.normalizer (J : Set Γ) := hRsyl.1.trans hHJ
  have h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J := by
    rw [← hJR]
    exact InternalSec.two_of_sup hRsyl.2.1 hRJ
  have hSQ : SQTKGroup ↥J := B5.sqtk_of_le hSQH hJH
  have hJperf : ⁅J, J⁆ = J := perfect_of_mem_cComp hJcomp
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLfam
  have hJsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
    exact (quotEquiv α hαs hαk).isSimpleGroup
  have hJq' : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotEquiv α hαs hαk).symm isQuasisimple_alt7
  have hZ := center_autI_eq_bot hV hJN hCJ α hαs hαk
  have hO := pCoreOf_le_centralizer hred hJH hHJ
  have hJthom := commutator_thompsonJ_eq hV hred hRsyl.1 hHJ h2 hZ hO hJperf hJsimple hJRV
  have : IsMulCommutative ↥V := hV.1
  have hperfV : commutator ↥(autOn J V) = ⊤ := hJq.1
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Γ, W = ⁅V, J⁆ := ⟨_, rfl⟩
  have hWV : W ≤ V := hW ▸ commutator_le_left hJN
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_le hWV hV
  have : IsMulCommutative ↥W := hWe.1
  have hJW : ¬ J ≤ Subgroup.centralizer (W : Set Γ) := hW ▸ not_le_centralizer_commutator hV hJN
    hperfV hJV
  have hredW : IsTwoReducedIn H W := hW ▸ isTwoReducedIn_commutator hV hred hJH hHJ h2 hZ hO α
    hαs hαk hJperf (hW ▸ hJW)
  have hcommW : ⁅W, J⁆ = W := by rw [hW]; exact commutator_commutator_eq hV hJN hperfV
  have hJNW : J ≤ Subgroup.normalizer (W : Set Γ) := hJH.trans hredW.2.1
  have hCJW := inf_centralizer_eq_pCoreOf hredW hJH hHJ hJNW hJW α hαs hαk
  obtain ⟨eW⟩ := nonempty_autI_equiv hWe hJNW hCJW α hαs hαk
  have eW' : ↥(autOn J W) ≃* ↥(alternatingGroup (Fin 7)) := eW
  have hXW : Nat.card ↥(autOn J W) = 2520 := (Nat.card_congr eW'.toEquiv).trans card_alt7
  have hfixW := fixV_autOn_eq_bot h51 hRsyl hJH hHJ h2 hWe hredW hJq' hJsimple hSQ hJW hJthom
    hXW hcommW
  have hVp : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hVQ : V ≤ pCoreOf 2 J := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVJ hJN hVp
  have hWU : W ≤ blockU J := le_blockU (hWV.trans hVQ) hcommW
  have hinfW : W ⊓ blockZ J = ⊥ := inf_blockZ_eq_bot hfixW
  have hsupW : W ⊔ blockZ J = blockU J := sup_blockZ_eq hshort hWU hJNW hJW
  have hcardW : Nat.card ↥W = ((blockZ J).subgroupOf (blockU J)).index :=
    card_eq_index hshort hWU hinfW hsupW
  have hirrW : ∀ X : Subgroup Γ, X ≤ W → J ≤ Subgroup.normalizer (X : Set Γ) → X = ⊥ ∨ X = W :=
    fun X hXW hJX => eq_bot_or_eq_of_le hshort hWU hinfW hsupW hXW hJX
  have hLW : ¬ L ≤ Subgroup.centralizer (W : Set Γ) :=
    hW ▸ not_le_centralizer_comm_of_le hV hJN hLJ hLperf hLV
  have hLNW : L ≤ Subgroup.normalizer (W : Set Γ) := hLJ.trans hJNW
  have hLdvd : Nat.card ↥(autOn L W) ∣ 2520 := hXW ▸ Subgroup.card_dvd_of_le (A4.autOn_mono hLJ)
  refine ⟨fun ⟨eL⟩ => ?_, fun ⟨eL⟩ hVJc => ?_⟩
  ·
    rcases hblk with hAlt | hExc
    · exfalso
      have hcard6 : Nat.card ↥W = 2 ^ 6 := hcardW.trans (index_of_altType hAlt)
      have hL168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
        (Nat.card_congr eL.toEquiv).trans SecA.card_SL_three_zmod_two
      obtain ⟨k, hk⟩ := C10KH.card_autOn_eq hLNW hLperf hLsimple hLW
      rw [hL168] at hk
      have hk0 : k = 0 := by
        by_contra h0
        have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 h0
        have : 336 ∣ 2520 := (mul_dvd_mul_left 168 h2k).trans (hk ▸ hLdvd)
        norm_num at this
      subst hk0
      exact false_of_l32 h42 hWe hredW hRsyl hJH hHJ h2 hSQ hCJW α hαs hαk hJthom hJW hirrW
        hcard6 hLJ hRL (by rw [hk]; norm_num) (by rw [hk]; norm_num) (by rw [hk]; norm_num)
    · exact hExc
  ·
    have hWVeq : W = V := hW.trans hVJc
    have hL60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
      rw [Nat.card_congr eL.toEquiv, SecA.card_alt 5 (by norm_num)]
      decide
    rcases hblk with hAlt | hExc
    ·
      right
      have hcard6 : Nat.card ↥W = 2 ^ 6 := hcardW.trans (index_of_altType hAlt)
      obtain ⟨π, hR, hinj, hJF, -⟩ := exists_swap h42 hWe hredW hRsyl hJH hHJ h2 hSQ hCJW α hαs
        hαk hJthom hJW hirrW hcard6
      have hSJ : IsSylowTwoOf (R ⊓ J) J := Ch3Sec3.isSylowTwoOf_inf_of_normal hJH hHJ hRsyl
      obtain ⟨ha, hb⟩ := case_b2 π hR hinj hJF hXW hJNW hSJ hLJ hRL hLperf hLsimple hLW hL60
      refine ⟨fun v hv => ha v ?_, fun y hy hy3 => ?_⟩
      · rw [hWVeq]
        exact commutator_le_left (hLJ.trans hJN) hv
      · have := hb y hy hy3
        rwa [hWVeq] at this
    ·
      left
      have hcard4 : Nat.card ↥W = 2 ^ 4 := hcardW.trans hExc.2.2
      have h5 : 5 ∣ Nat.card ↥L :=
        (show (5 : ℕ) ∣ 60 by norm_num).trans (hL60 ▸ Subgroup.card_quotient_dvd_card _)
      have := irrG_of_card_sixteen hWe (by rw [hcard4]; norm_num) hLNW hLW hLperf hLsimple h5
      rwa [hWVeq] at this

end CFSG.Quasithin.Vol2.Ch10.SecC
