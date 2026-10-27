module

public import CFSG.RankThree.GF2n.Tim78S4Basic
public import CFSG.GroupTheory.HuppertProduct.Mho
public import CFSG.RankThree.GF2n.Tim78S4Extra
import CFSG.RankThree.GF2n.Tim78S4Dual
import CFSG.RankThree.GF2n.Tim78Frattini

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_center_eq_inf (S : Subgroup G) :
    (Subgroup.center S).map S.subtype = S ⊓ Subgroup.centralizer (S : Set G) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (mem_center_iff_mem_inf s).mp hs
  · intro hx
    exact ⟨⟨x, hx.1⟩, (mem_center_iff_mem_inf ⟨x, hx.1⟩).mpr hx, rfl⟩

theorem comm_of_mul_self_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

theorem B_lt_P : B < P := by
  refine lt_of_le_of_ne H.B_le_P fun h => ?_
  obtain ⟨g, hgQ, hgne⟩ := H.notWC
  have hgP := H.conj_le_P hgQ
  rw [← h] at hgP
  exact hgne (Subgroup.eq_of_le_of_card_ge hgP (by rw [card_conjSubgroup]))
theorem comm_P_of_comm_gens {y : G}
    (h : ∀ g : G, conjSubgroup g B ≤ Q → ∀ a ∈ conjSubgroup g B, a * y = y * a) :
    ∀ p ∈ P, p * y = y * p := by
  have hP : P ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [H.hP]
    exact iSup₂_le fun g hg a ha => Subgroup.mem_centralizer_singleton_iff.mpr (h g hg a ha)
  intro p hp
  exact Subgroup.mem_centralizer_singleton_iff.mp (hP hp)
section Certified

theorem inf_centralizer_P : P ⊓ Subgroup.centralizer (P : Set G) = B := by
  have hle : B ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf H.B_le_P fun b hb => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (H.center_Q hb (H.P_le_Q hx)).symm
  refine (H.maxAb.eq_of_le ⟨inf_le_left.trans H.P_le_M, ?_, ?_⟩ hle).symm
  · exact fun m hm => mem_normalizer_inf (H.M_le_normalizer_P hm)
      (mem_normalizer_centralizer (H.M_le_normalizer_P hm))
  · exact ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩

theorem center_P : (Subgroup.center P).map P.subtype = B := by
  rw [map_center_eq_inf, H.inf_centralizer_P]

theorem inf_centralizer_eq_B {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) :
    N ⊓ Subgroup.centralizer (N : Set G) = B := by
  have hle : B ≤ N ⊓ Subgroup.centralizer (N : Set G) :=
    le_inf hBN fun b hb => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (H.center_Q hb (hNQ hx)).symm
  refine (H.maxAb.eq_of_le ⟨inf_le_left.trans (hNQ.trans H.Q_le_M), ?_, ?_⟩ hle).symm
  · exact fun m hm => mem_normalizer_inf (hMN hm) (mem_normalizer_centralizer (hMN hm))
  · exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩

theorem not_comm_of_ne {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hne : B ≠ N) :
    ¬ ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro h
  exact hne (H.maxAb.eq_of_le ⟨hNQ.trans H.Q_le_M, hMN,
    ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩⟩ hBN)

theorem frattini_eq_B_of_ne {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hne : B ≠ N) :
    inSubgroup frattini N = B := by
  have hN2 : IsPGroup 2 N := H.isPGroup_Q.to_le hNQ
  have hle : inSubgroup frattini N ≤ B := by
    have := inSubgroup_frattini_mono H.isPGroup_Q hNQ
    rwa [H.base_facts.1] at this
  refine H.eq_B_of_normalized hle ?_ fun m hm => mem_normalizer_inSubgroup_frattini (hMN hm)
  intro hbot
  refine H.not_comm_of_ne hBN hNQ hMN hne fun a ha b hb => ?_
  have := commutatorElement_mem_inSubgroup_frattini hN2 ha hb
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem mho_eq_B_of_ne {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hne : B ≠ N) :
    CFSG.GroupTheory.HuppertProduct.mho N 2 = B := by
  have hle : CFSG.GroupTheory.HuppertProduct.mho N 2 ≤ B :=
    CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun g hg => H.sq_mem (hNQ hg)
  refine H.eq_B_of_normalized hle ?_ fun m hm => ?_
  · intro hbot
    refine H.not_comm_of_ne hBN hNQ hMN hne fun a ha b hb => ?_
    have hsq : ∀ x ∈ N, x ^ 2 = 1 := fun x hx => by
      have := CFSG.GroupTheory.HuppertProduct.pow_mem_mho (n := 2) hx
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h1 : a * a = 1 := by rw [← sq]; exact hsq a ha
    have h2 : b * b = 1 := by rw [← sq]; exact hsq b hb
    have h3 : (a * b) * (a * b) = 1 := by rw [← sq]; exact hsq _ (N.mul_mem ha hb)
    exact comm_of_mul_self_eq_one h1 h2 h3
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact CFSG.GroupTheory.HuppertProduct.conj_mem_mho
      (fun s hs => (Subgroup.mem_normalizer_iff.mp (hMN hm) s).mp hs) hx

theorem commutator_eq_B_of_ne {N : Subgroup G} (hBN : B ≤ N) (hNQ : N ≤ Q)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hne : B ≠ N) : ⁅N, N⁆ = B := by
  have hle : ⁅N, N⁆ ≤ B := Subgroup.commutator_le.mpr fun a ha b hb =>
    H.commutator_mem (hNQ ha) (hNQ hb)
  refine H.eq_B_of_normalized hle ?_ fun m hm => ?_
  · intro hbot
    refine H.not_comm_of_ne hBN hNQ hMN hne fun a ha b hb => ?_
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · rw [← conjSubgroup_eq_self_iff, conjSubgroup, Subgroup.map_commutator]
    have : Subgroup.map (MulAut.conj m).toMonoidHom N = N := conjSubgroup_eq_self_iff.mpr (hMN hm)
    rw [this]

theorem commute_of_commutator_le_hyperplane {Hh : Subgroup G} (hHB : Hh ≤ B)
    (hH2 : Nat.card Hh * 2 = Nat.card B) {y : G} (hy : y ∈ Q) {g : G}
    (hg : conjSubgroup g B ≤ P) (hy' : ∀ a ∈ conjSubgroup g B, ⁅y, a⁆ ∈ Hh) :
    ∀ a ∈ conjSubgroup g B, ⁅y, a⁆ = 1 := by
  set A := conjSubgroup g B with hA
  have hAQ : A ≤ Q := hg.trans H.P_le_Q
  by_cases hAB : A = B
  · intro a ha
    rw [hAB] at ha
    have := H.center_Q ha hy
    rw [commutatorElement_def, show y * a * y⁻¹ * a⁻¹ = (y * a) * (a * y)⁻¹ by group,
      ← this]
    group
  have hAbot : A ⊓ B = ⊥ := by
    rw [inf_comm]
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAB
  by_cases hyN : y ∈ Subgroup.normalizer (A : Set G)
  · intro a ha
    have h1 : ⁅y, a⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN a).mp ha) (A.inv_mem ha)
    have h2 : ⁅y, a⁆ ∈ B := hHB (hy' a ha)
    have : ⁅y, a⁆ ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hAbot] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    have hAy : A ⊓ conjSubgroup y A = ⊥ :=
      inf_conjSubgroup_eq_bot_of_isTI (isTI_conjSubgroup H.ti g)
        (fun h => hyN (conjSubgroup_eq_self_iff.mp h))
    let φ : A → Hh := fun a => ⟨⁅y, (a : G)⁆, hy' a a.2⟩
    have hφ : Function.Injective φ := by
      intro a a' h
      have hc : ⁅y, (a : G)⁆ = ⁅y, (a' : G)⁆ := congrArg Subtype.val h
      set c := ⁅y, (a : G)⁆ with hcdef
      have hcB : c ∈ B := hHB (hy' a a.2)
      have e1 : y * a * y⁻¹ = c * a := by rw [hcdef, commutatorElement_def]; group
      have e2 : y * a' * y⁻¹ = c * a' := by rw [hc, commutatorElement_def]; group
      have hd : (a : G) * (a' : G)⁻¹ ∈ conjSubgroup y A := by
        rw [mem_conjSubgroup]
        have hc1 := H.center_Q hcB (hAQ (A.mul_mem a.2 (A.inv_mem a'.2)))
        have : y⁻¹ * ((a : G) * (a' : G)⁻¹) * y = (a : G) * (a' : G)⁻¹ := by
          have h3 : y * ((a : G) * (a' : G)⁻¹) * y⁻¹ = (a : G) * (a' : G)⁻¹ := by
            calc y * ((a : G) * (a' : G)⁻¹) * y⁻¹
                = (y * a * y⁻¹) * (y * a' * y⁻¹)⁻¹ := by group
              _ = (c * a) * (c * a')⁻¹ := by rw [e1, e2]
              _ = c * ((a : G) * (a' : G)⁻¹) * c⁻¹ := by group
              _ = (a : G) * (a' : G)⁻¹ := by rw [hc1]; group
          calc y⁻¹ * ((a : G) * (a' : G)⁻¹) * y
              = y⁻¹ * (y * ((a : G) * (a' : G)⁻¹) * y⁻¹) * y := by rw [h3]
            _ = (a : G) * (a' : G)⁻¹ := by group
        rw [this]
        exact A.mul_mem a.2 (A.inv_mem a'.2)
      have : (a : G) * (a' : G)⁻¹ ∈ A ⊓ conjSubgroup y A :=
        Subgroup.mem_inf.mpr ⟨A.mul_mem a.2 (A.inv_mem a'.2), hd⟩
      rw [hAy, Subgroup.mem_bot] at this
      exact Subtype.ext (mul_inv_eq_one.mp this)
    have hcard := Nat.card_le_card_of_injective φ hφ
    have hAcard : Nat.card A = Nat.card B := card_conjSubgroup g B
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega

theorem center_quotient {Hh : Subgroup G} (hHB : Hh ≤ B) (hH2 : Nat.card Hh * 2 = Nat.card B)
    {y : G} (hy : y ∈ P) (h : ∀ p ∈ P, ⁅y, p⁆ ∈ Hh) : y ∈ B := by
  have hcomm : ∀ p ∈ P, p * y = y * p := by
    refine H.comm_P_of_comm_gens fun g hg a ha => ?_
    have h1 := H.commute_of_commutator_le_hyperplane hHB hH2 (H.P_le_Q hy) (H.conj_le_P hg)
      (fun a ha => h a (H.conj_le_P hg ha)) a ha
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hmem : y ∈ P ⊓ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_iff.mpr fun p hp => hcomm p hp⟩
  rwa [H.inf_centralizer_P] at hmem

theorem exists_inner {Hh : Subgroup G} (hHB : Hh ≤ B) (hH2 : Nat.card Hh * 2 = Nat.card B)
    {y : G} (hy : y ∈ Q) : ∃ x ∈ P, ∀ p ∈ P, ⁅y * x, p⁆ ∈ Hh :=
  exists_inner_of_hyperplane H.P_le_Q (fun a ha b hb => H.commutator_mem ha hb)
    (fun b hb x hx => H.center_Q hb hx) hHB hH2
    (fun x hx h => H.center_quotient hHB hH2 hx h) hy

theorem Q_eq_sup : Q = P ⊔ T := by
  refine le_antisymm (fun y hy => ?_) (sup_le H.P_le_Q H.T_le_Q)
  obtain ⟨Hh, hHB, hH2⟩ := H.exists_hyperplane
  obtain ⟨x, hxP, hx⟩ := H.exists_inner hHB hH2 hy
  have hyxQ : y * x ∈ Q := Q.mul_mem hy (H.P_le_Q hxP)
  have hcomm := H.comm_P_of_comm_gens (y := y * x) fun g hg a ha => by
    have h1 := H.commute_of_commutator_le_hyperplane hHB hH2 hyxQ (H.conj_le_P hg)
      (fun a ha => hx a (H.conj_le_P hg ha)) a ha
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hyx : y * x ∈ T := by
    rw [H.hT]
    exact Subgroup.mem_inf.mpr ⟨hyxQ, Subgroup.mem_centralizer_iff.mpr fun p hp => hcomm p hp⟩
  have : y = (y * x) * x⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyx) (Subgroup.mem_sup_left (P.inv_mem hxP))

theorem B_ne_T : B ≠ T := by
  intro h
  apply H.PneQ
  rw [H.Q_eq_sup, ← h]
  exact (sup_eq_left.mpr H.B_le_P).symm

theorem P_inf_T : P ⊓ T = B := by
  refine le_antisymm (fun x hx => ?_) (le_inf H.B_le_P H.B_le_T)
  have hxC : x ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨hx.1, H.T_le_centralizer_P hx.2⟩
  rwa [H.inf_centralizer_P] at hxC

theorem center_T : (Subgroup.center T).map T.subtype = B := by
  rw [map_center_eq_inf]
  exact H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T

theorem P_le_centralizer_T : P ≤ Subgroup.centralizer (T : Set G) := fun p hp =>
  Subgroup.mem_centralizer_iff.mpr fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) p hp).symm

theorem inf_centralizer_T_eq_P : Q ⊓ Subgroup.centralizer (T : Set G) = P := by
  refine le_antisymm (fun x hx => ?_) (le_inf H.P_le_Q H.P_le_centralizer_T)
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := le_normalizer_of_comm fun t ht p hp =>
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) p hp).symm
  have hxQ := hx.1
  rw [H.Q_eq_sup] at hxQ
  obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hTP hxQ
  have htC : t ∈ Subgroup.centralizer (T : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (H.P_le_centralizer_T hp)) hx.2
    rwa [inv_mul_cancel_left] at this
  have htB : t ∈ B := by
    have : t ∈ T ⊓ Subgroup.centralizer (T : Set G) := ⟨ht, htC⟩
    rwa [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at this
  exact P.mul_mem hp (H.B_le_P htB)

theorem tim78_4_2 :
    (Subgroup.center P).map P.subtype = B ∧ inSubgroup frattini P = B ∧ B < P ∧
    (∀ Hh : Subgroup G, Hh ≤ B → Nat.card Hh * 2 = Nat.card B →
      ∃ _ : (Hh.subgroupOf P).Normal, IsExtraspecialPGroup 2 (↥P ⧸ Hh.subgroupOf P)) ∧
    Q = P ⊔ T ∧ Q ⊓ Subgroup.centralizer (T : Set G) = P ∧ P ⊓ T = B ∧
    (Subgroup.center T).map T.subtype = B ∧ inSubgroup frattini T = B ∧
    CFSG.GroupTheory.HuppertProduct.mho T 2 = B ∧
      CFSG.GroupTheory.HuppertProduct.mho P 2 = B := by
  have hPne : B ≠ P := H.B_lt_P.ne
  refine ⟨H.center_P, H.frattini_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P hPne,
    H.B_lt_P, fun Hh hHB hH2 => ?_, H.Q_eq_sup, H.inf_centralizer_T_eq_P, H.P_inf_T, H.center_T,
    H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T,
    H.mho_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T,
    H.mho_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P hPne⟩
  exact isExtraspecial_quotient_of_hyperplane H.isPGroup_P H.B_le_P
    (H.commutator_eq_B_of_ne H.B_le_P H.P_le_Q H.M_le_normalizer_P hPne)
    (fun b hb x hx => H.center_Q hb (H.P_le_Q hx)) (fun a ha => H.sq_mem (H.P_le_Q ha)) hHB hH2
    (fun x hx h => H.center_quotient hHB hH2 hx h)

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
