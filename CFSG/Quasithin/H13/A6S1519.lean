module

public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S1514

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pCoreOf_M_ne_bot : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨P, hP1, hP2, hPeq⟩, -⟩ := S.uniqueM.1.1
  intro h
  have := le_pCoreOf_normalizer 2 P hP2
  rw [← hPeq, h] at this
  exact hP1 (le_bot_iff.1 this)

theorem charTwo_M : CharTwo (Subgroup.normalizer (L : Set G)) :=
  S.charTwo_of_inH ⟨S.T_le_NL, S.pCoreOf_M_ne_bot⟩

theorem pCoreOf_M_le_T : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≤ T := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have := pCoreOf_two_le_sylow (Subgroup.normalizer (L : Set G)) P (hP ▸ S.T_le_NL)
  rwa [hP] at this

theorem V_le_pCoreOf_M
    : V ≤ pCoreOf 2 (Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hOLT : pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (S.pCoreOf_M_le_T.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer S.T_le_NL).trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) := hOLT.trans (S.cT ▸ inf_le_right)
  intro v hv
  have hvM : v ∈ M := S.NV_le_M (Subgroup.le_normalizer hv)
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hOC hq) v hv).symm
  exact S.charTwo_M ⟨hvM, hvC⟩

theorem V_le_pCoreOf_of_le_M {X : Subgroup G} (hVX : V ≤ X)
    (hXM : X ≤ Subgroup.normalizer (L : Set G)) : V ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ⊓ X ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (F7.le_normalizer_inf (hXM.trans (le_normalizer_pCoreOf 2 _)) Subgroup.le_normalizer)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact fun v hv => h1 ⟨S.V_le_pCoreOf_M hv, hVX hv⟩

theorem charTwo_L : CharTwo L :=
  A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful

theorem pCoreOf_l0_ne_bot (hhat : IsHatA6 L) : pCoreOf 2 (l0 L) ≠ ⊥ := by
  obtain ⟨c, hc, -, hcO, -⟩ := exists_l0_c hhat.2.1
  intro h
  apply hcO
  have hcL : c ∈ L := l0_le_L hc
  refine S.charTwo_L (Subgroup.mem_inf.2 ⟨hcL, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxL : x ∈ L := pCoreOf_le 2 L hx
  have hk0 : x * c * x⁻¹ * c⁻¹ ∈ l0 L :=
    (l0 L).mul_mem ((Subgroup.mem_normalizer_iff.mp (L_le_normalizer_l0 hxL) c).mp hc)
      ((l0 L).inv_mem hc)
  have hk2 : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 L := by
    have h1 : c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hcL) _).mp
        ((pCoreOf 2 L).inv_mem hx)
    have := (pCoreOf 2 L).mul_mem hx h1
    simpa [mul_assoc] using this
  have hk := mem_pCoreOf_l0 hk0 hk2
  rw [h, Subgroup.mem_bot] at hk
  calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
    _ = c * x := by rw [hk, one_mul]

theorem normalizer_l0_le_M (hhat : IsHatA6 L) :
    Subgroup.normalizer (l0 L : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (l0 L) : Set G)) :=
    ⟨_, S.pCoreOf_l0_ne_bot hhat, pCoreOf_isPGroup 2 _, rfl⟩
  have hN : Subgroup.normalizer (l0 L : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (l0 L) : Set G) := normalizer_le_normalizer_pCoreOf 2 _
  have hLT : L ⊔ T ≤ Subgroup.normalizer (l0 L : Set G) :=
    sup_le L_le_normalizer_l0 (S.frame.T_le.trans S.normalizer_le_l0)
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have := S.uniqueM.2 M' ⟨hM', (hLT.trans hN).trans hle⟩
  exact this ▸ hN.trans hle

theorem lemma13_5_19_two_l0
    (hhat : IsHatA6 L) {H : Subgroup G} (hVH : V ≤ H) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (l0 L : Set G)) :=
  S.V_le_pCoreOf_of_le_M (le_inf hVH (S.V_le_T.trans (S.frame.T_le.trans S.normalizer_le_l0)))
    (inf_le_right.trans (S.normalizer_l0_le_M hhat))

theorem normalizer_L1_mem_Hz {H : Subgroup G} (hH : H ∈ S.Hz)
    (hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    H ⊓ Subgroup.normalizer (S.L1 : Set G) ∈ S.Hz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1T : S.L1 ⊔ T ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf hH.1.1 (sup_le Subgroup.le_normalizer S.T_le_normalizer_L1)
  refine ⟨⟨hL1T, fun h => ?_⟩, inf_le_left.trans hH.2.1, hM⟩
  have hV1 : fsuV1 T V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (S.isPGroup_V.to_le
      ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V))
    · exact (((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V).trans S.V_le_T).trans
        (le_sup_right.trans hL1T)
    · intro x hx
      rw [S.normalizer_V1]
      exact hH.2.1 hx.1
  rw [h, le_bot_iff] at hV1
  have hc := S.card_V1
  rw [hV1] at hc
  simp at hc

theorem lemma13_5_19_two_L1
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two)
    (hcon : ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
  by_contra hV
  have hVH1 : V ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf (S.hypF91 hNS h13315 h1356two hH).V_le_H (S.V_le_T.trans S.T_le_normalizer_L1)
  have hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun h => hV (S.V_le_pCoreOf_of_le_M hVH1 h)
  have hH1 := S.normalizer_L1_mem_Hz hH hM
  have hF1 := S.hypF91 hNS h13315 h1356two hH1
  have hna : ¬ IsElemAbelian 2 (conjClosure S.V3 (H ⊓ Subgroup.normalizer (S.L1 : Set G))) := by
    intro hab
    refine hV (hF1.F94_2 ((Subgroup.commutator_mono le_rfl inf_le_left).trans
      (S.comm_centralizer_V3 h13315 _)) fun x hx y hy => ?_)
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact hcon _ hH1 hna inf_le_right

end Setting4

end CFSG.Quasithin.H13.A6
