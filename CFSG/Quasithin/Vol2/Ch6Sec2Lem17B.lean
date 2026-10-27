module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem17A
public import CFSG.GH74.M12.HypGroup
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbs
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem gens_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    ∃ z ∈ zCh611 T, z ≠ 1 ∧ ∃ d ∈ lsCh617 T L V, d ^ 3 = 1 ∧
      d ∉ Subgroup.centralizer (ch6ZS T L V : Set G) ∧ d⁻¹ * z * d ∈ ch6ZS T L V ∧
      d⁻¹ * z * d ∉ zCh611 T ∧ ∃ t ∈ T, t ∉ Subgroup.centralizer (ch6ZS T L V : Set G) ∧
        t * z = z * t ∧ t * (d⁻¹ * z * d) * t⁻¹ = z * (d⁻¹ * z * d) := by
  have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ zCh611 T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨d, hdLS, hd3, hdN, hfix⟩ := h.exists_diag_ch617
  have hzV : z ∈ V := (hZZS.trans inf_le_left) hzZ
  have hdz : d * z * d⁻¹ ≠ z := fun he => hz1 (hfix z hzV he)
  have hdC : d ∉ Subgroup.centralizer (ch6ZS T L V : Set G) := fun hdC => hdz (by
    rw [← Subgroup.mem_centralizer_iff.mp hdC z (hZZS hzZ), mul_inv_cancel_right])
  set w := d⁻¹ * z * d with hw
  have hwZS : w ∈ ch6ZS T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) z).mp (hZZS hzZ)
    simpa [hw] using this
  have hzw : z = d * w * d⁻¹ := by rw [hw]; group
  have hwZ : w ∉ zCh611 T := by
    intro hwZ
    have hw1 : w ≠ 1 := fun h1 => hz1 (by rw [hzw, h1]; group)
    have hwz : w = z := SteinbergBS.eq_of_card_le_two hZ2.le hwZ hzZ hw1 hz1
    apply hdz
    calc d * z * d⁻¹ = d * w * d⁻¹ := by rw [hwz]
      _ = z := hzw.symm
  obtain ⟨t, ht, htC⟩ : ∃ t ∈ T, t ∉ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : ch6ZS T L V ≤ zCh611 T := fun x hx =>
      Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hx.1, Subgroup.mem_centralizer_iff.mpr
        fun y hy => (Subgroup.mem_centralizer_iff.mp (hcon y hy) x hx).symm⟩,
        h.toHyp611.isElemAbelian.2 x hx.1⟩
    have := Subgroup.card_le_of_le hle
    omega
  have htz : t * z = z * t := (Subgroup.mem_centralizer_iff.mp (hA.sylow_H.1 ht) z hzZ).symm
  have htw : t * w * t⁻¹ ∈ ch6ZS T L V :=
    (Subgroup.mem_normalizer_iff.mp (h.toHyp611Nat.T_le_normalizer_ZS ht) w).mp hwZS
  refine ⟨z, hzZ, hz1, d, hdLS, hd3, hdC, hwZS, hwZ, t, ht, htC, htz, ?_⟩
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS htw with e | e | e | e
  · exfalso
    have : w = 1 := by
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [e]; group
    exact hwZ (this ▸ (zCh611 T).one_mem)
  · exfalso
    have : w = z := by
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = t⁻¹ * (z * t) := by rw [e]; group
        _ = t⁻¹ * (t * z) := by rw [htz]
        _ = z := by group
    exact hwZ (this ▸ hzZ)
  · exfalso
    apply htC
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS hs with e' | e' | e' | e'
    · rw [e']; group
    · rw [e']; exact htz.symm
    · rw [e']
      have htw' : t * w = w * t := by
        calc t * w = (t * w * t⁻¹) * t := by group
          _ = w * t := by rw [e]
      exact htw'.symm
    · rw [e']
      have htw' : t * w = w * t := by
        calc t * w = (t * w * t⁻¹) * t := by group
          _ = w * t := by rw [e]
      calc z * w * t = z * (w * t) := by group
        _ = z * (t * w) := by rw [htw']
        _ = (z * t) * w := by group
        _ = (t * z) * w := by rw [htz]
        _ = t * (z * w) := by group
  · exact e

theorem normalizer_Z_eq_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    Subgroup.normalizer (zCh611 T : Set G) = hCh611 T :=
  le_antisymm (normalizer_le_centralizer_of_card_two (h.card_omega h331 h432 h512 h614 h615))
    (Subgroup.centralizer_le_normalizer _)

theorem mem_centralizer_of_fix_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) {z w q : G} (hzZ : z ∈ zCh611 T) (hz1 : z ≠ 1)
    (hwZS : w ∈ ch6ZS T L V) (hwZ : w ∉ zCh611 T) (hqz : q * z = z * q) (hqw : q * w = w * q) :
    q ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS hs with e | e | e | e
  · rw [e]; group
  · rw [e]; exact hqz.symm
  · rw [e]; exact hqw.symm
  · rw [e]
    calc z * w * q = z * (w * q) := by group
      _ = z * (q * w) := by rw [hqw]
      _ = (z * q) * w := by group
      _ = (q * z) * w := by rw [hqz]
      _ = q * (z * w) := by group

theorem sThree_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    Nonempty (OTwoQuot (lsCh617 T L V ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  classical
  set KT := lsCh617 T L V ⊔ T with hKT
  have hKTN : KT ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := h.sup_le_normalizer_ZS_ch617
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hV := h.toHyp611.isElemAbelian
  have : IsKleinFour ↥(ch6ZS T L V) :=
    isKleinFour_of_card_four_ch62 hZS4 fun x hx => hV.2 x hx.1
  obtain ⟨z, hzZ, hz1, d, hdLS, hd3, hdC, hwZS, hwZ, t, ht, htC, htz, htw⟩ :=
    h.gens_ch617 h331 h432 h512 h614 h615
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hz2 : z * z = 1 := by
    rw [← pow_two]; exact hV.2 z ((hZZS.trans inf_le_left) hzZ)
  have hdKT : d ∈ KT := Subgroup.mem_sup_left hdLS
  have htKT : t ∈ KT := Subgroup.mem_sup_right ht
  set α := conjAct (ch6ZS T L V) ⟨d, hKTN hdKT⟩ with hα
  set β := conjAct (ch6ZS T L V) ⟨t, hKTN htKT⟩ with hβ
  have hαA : α ∈ autOn KT (ch6ZS T L V) :=
    ⟨⟨d, hKTN hdKT⟩, Subgroup.mem_subgroupOf.mpr hdKT, rfl⟩
  have hβA : β ∈ autOn KT (ch6ZS T L V) :=
    ⟨⟨t, hKTN htKT⟩, Subgroup.mem_subgroupOf.mpr htKT, rfl⟩
  have hα1 : α ≠ 1 := fun h1 => hdC (conjAct_eq_one_iff_mem_centralizer.mp h1)
  have hβ1 : β ≠ 1 := fun h1 => htC (conjAct_eq_one_iff_mem_centralizer.mp h1)
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨d, hKTN hdKT⟩ : ↥(Subgroup.normalizer (ch6ZS T L V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have ht2C : t ^ 2 ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    refine h.mem_centralizer_of_fix_ch617 h331 h432 h512 h614 h615 hzZ hz1 hwZS hwZ ?_ ?_
    · rw [pow_two]
      calc t * t * z = t * (t * z) := by group
        _ = t * (z * t) := by rw [htz]
        _ = (t * z) * t := by group
        _ = (z * t) * t := by rw [htz]
        _ = z * (t * t) := by group
    · have h1 : t * t * (d⁻¹ * z * d) * (t * t)⁻¹ = d⁻¹ * z * d := by
        have htz' : t * z * t⁻¹ = z := by rw [htz, mul_inv_cancel_right]
        calc t * t * (d⁻¹ * z * d) * (t * t)⁻¹ = t * (t * (d⁻¹ * z * d) * t⁻¹) * t⁻¹ := by group
          _ = t * (z * (d⁻¹ * z * d)) * t⁻¹ := by rw [htw]
          _ = (t * z * t⁻¹) * (t * (d⁻¹ * z * d) * t⁻¹) := by group
          _ = z * (z * (d⁻¹ * z * d)) := by rw [htw, htz']
          _ = d⁻¹ * z * d := by rw [← mul_assoc, hz2, one_mul]
      rw [pow_two]
      calc t * t * (d⁻¹ * z * d) = (t * t * (d⁻¹ * z * d) * (t * t)⁻¹) * (t * t) := by group
        _ = d⁻¹ * z * d * (t * t) := by rw [h1]
  have hβ2 : β ^ 2 = 1 := by
    rw [hβ, ← map_pow]
    exact conjAct_eq_one_iff_mem_centralizer.mpr (by simpa using ht2C)
  have hcardA : Nat.card (autOn KT (ch6ZS T L V)) = 6 := by
    have hle : Nat.card (autOn KT (ch6ZS T L V)) ≤ 6 := by
      rw [← kleinFour_automorphism_card (E := ↥(ch6ZS T L V))]
      exact Subgroup.card_le_card_group _
    have h3 : orderOf α = 3 := orderOf_eq_prime hα3 hα1
    have h2 : orderOf β = 2 := orderOf_eq_prime hβ2 hβ1
    have hd3' : 3 ∣ Nat.card (autOn KT (ch6ZS T L V)) := by
      rw [← h3]
      exact Subgroup.orderOf_dvd_natCard _ hαA
    have hd2' : 2 ∣ Nat.card (autOn KT (ch6ZS T L V)) := by
      rw [← h2]
      exact Subgroup.orderOf_dvd_natCard _ hβA
    have hpos : 0 < Nat.card (autOn KT (ch6ZS T L V)) := Nat.card_pos
    obtain ⟨k, hk⟩ := hd3'
    obtain ⟨m, hm⟩ := hd2'
    omega
  have hcard : Nat.card (OTwoQuot KT) = 6 := by
    have h1 := card_autOn_eq_relIndex hKTN
    rw [hcardA, h.centralizer_eq_ch617 h331 h432 h512 h614 h615] at h1
    have hsub : (pCoreOf 2 KT).subgroupOf KT = CFSG.Open.pCore 2 ↥KT :=
      map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥KT)
    show (CFSG.Open.pCore 2 ↥KT).index = 6
    rw [← hsub]
    exact h1.symm
  let π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥KT)
  refine CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hcard
    (π ⟨d, hdKT⟩) (π ⟨t, htKT⟩) fun hc => ?_
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  have hcmem : (d * t)⁻¹ * (t * d) ∈ pCoreOf 2 KT := ⟨_, hc, rfl⟩
  have hcC := ((h.centralizer_eq_ch617 h331 h432 h512 h614 h615).ge hcmem).2
  have hcw : ((d * t)⁻¹ * (t * d)) * (d⁻¹ * z * d) = (d⁻¹ * z * d) * ((d * t)⁻¹ * (t * d)) :=
    (Subgroup.mem_centralizer_iff.mp hcC _ hwZS).symm
  have e1 : (t * d) * (d⁻¹ * z * d) * (t * d)⁻¹ = z := by
    calc (t * d) * (d⁻¹ * z * d) * (t * d)⁻¹ = t * z * t⁻¹ := by group
      _ = z := by rw [htz, mul_inv_cancel_right]
  have e2 : (t * d) * (d⁻¹ * z * d) * (t * d)⁻¹ = (d * z * d⁻¹) * z := by
    calc (t * d) * (d⁻¹ * z * d) * (t * d)⁻¹
        = (d * t) * (((d * t)⁻¹ * (t * d)) * (d⁻¹ * z * d)) * (t * d)⁻¹ := by group
      _ = (d * t) * ((d⁻¹ * z * d) * ((d * t)⁻¹ * (t * d))) * (t * d)⁻¹ := by rw [hcw]
      _ = d * (t * (d⁻¹ * z * d) * t⁻¹) * d⁻¹ := by group
      _ = d * (z * (d⁻¹ * z * d)) * d⁻¹ := by rw [htw]
      _ = (d * z * d⁻¹) * z := by group
  have h3 : (d * z * d⁻¹) * z = z := e2.symm.trans e1
  have h4 : d * z * d⁻¹ = 1 := by
    calc d * z * d⁻¹ = (d * z * d⁻¹) * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel z
  apply hz1
  calc z = d⁻¹ * (d * z * d⁻¹) * d := by group
    _ = 1 := by rw [h4]; group

theorem eq_conjClosure_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    ch6ZS T L V = conjClosure (zCh611 T) (lsCh617 T L V) := by
  obtain ⟨z, hzZ, hz1, d, hdLS, -, -, hwZS, hwZ, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  apply le_antisymm
  · intro s hs
    have hz' : z ∈ conjClosure (zCh611 T) (lsCh617 T L V) := le_conjClosure _ _ hzZ
    have hw' : d⁻¹ * z * d ∈ conjClosure (zCh611 T) (lsCh617 T L V) := by
      have := mem_conjClosure ((lsCh617 T L V).inv_mem hdLS) hzZ
      simpa using this
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hzZ hz1 hwZ hwZS hs with e | e | e | e
    · rw [e]; exact Subgroup.one_mem _
    · rw [e]; exact hz'
    · rw [e]; exact hw'
    · rw [e]; exact Subgroup.mul_mem _ hz' hw'
  · refine conjClosure_le fun l hl z' hz' => ?_
    exact (Subgroup.mem_normalizer_iff.mp ((ls_le_ch617 hl).2) z').mp (hZZS hz')

theorem natural_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    IsNaturalSL2Module 1 (lsCh617 T L V) (pCoreOf 2 (lsCh617 T L V ⊔ T)) (ch6ZS T L V)
      (zCh611 T) := by
  have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  obtain ⟨-, -, -, d, hdLS, -, hdC, -⟩ := h.gens_ch617 h331 h432 h512 h614 h615
  refine L128P.isNaturalSL2Module_one_of (fun x hx => (ls_le_ch617 hx).2) hA.elemAbelian hZS4
    (L128P.oTwoUpper_oTwoUpper _).symm (fun x hx => ?_) (fun hle => hdC (hle hdLS))
    (h.omega_le_ZS h331 h432 h512 h614 h615) (h.card_omega h331 h432 h512 h614 h615)
  rw [← h.centralizer_eq_ch617 h331 h432 h512 h614 h615]
  exact ⟨fun hc => ⟨Subgroup.mem_sup_left hx, hc⟩, fun hc => hc.2⟩

theorem setting_ch617 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    L128A.Setting (ch6ZS T L V) (zCh611 T) (lsCh617 T L V) T := by
  have hA := h.almostSpecialHyp_Gz h331 h432 h512 h614 h615
  have hNZ := h.normalizer_Z_eq_ch617 h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hTsyl : IsSylowTwoOf T (lsCh617 T L V ⊔ T) :=
    E6.isSylowIn_of_le (⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩)
      le_sup_right le_top
  have hVZU := h.inf_centerOf_eq_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hU : L128A.uA (ch6ZS T L V) (zCh611 T) = uCh611 T L V := by
    show conjClosure (ch6ZS T L V) (Subgroup.normalizer (zCh611 T : Set G)) = uCh611 T L V
    rw [hNZ]
  have hTN : T ≤ Subgroup.normalizer (zCh611 T : Set G) := hNZ ▸ hA.sylow_H.1
  have hbase : AlmostSpecialHyp (ch6ZS T L V) (zCh611 T) (lsCh617 T L V) T
      (Subgroup.normalizer (zCh611 T : Set G)) :=
    { elemAbelian := hA.elemAbelian
      ne_bot := hA.ne_bot
      le_V := hA.le_V
      oTwo_eq := (L128P.oTwoUpper_oTwoUpper _).symm
      V_le_T := hA.V_le_T
      T_le_normV₁ := hA.T_le_normV₁
      T_le_normV := hA.T_le_normV
      T_le_normL := h.T_le_normalizer_ls_ch617
      sylow_LT := hTsyl
      H_le := le_rfl
      lOne_sup_le := sup_le ((oTwoUpper_le _).trans inf_le_right) hTN
      sylow_H := hNZ ▸ hA.sylow_H
      charTwo := hNZ ▸ hA.charTwo
      irred := by
        refine ⟨hA.irred.1, sup_le ((oTwoUpper_le _).trans (inf_le_left.trans
          (fun x hx => (ls_le_ch617 hx).2))) hA.T_le_normV,
          sup_le ((oTwoUpper_le _).trans inf_le_right) hA.T_le_normV₁,
          fun W hZW hWZS hWN => hA.irred.2.2.2 W hZW hWZS ?_⟩
        have hlOne : lOne (⊥ : Subgroup G) (zCh611 T) = ⊥ :=
          eq_bot_iff.mpr ((oTwoUpper_le _).trans inf_le_left)
        rw [hlOne, bot_sup_eq]
        exact le_sup_right.trans hWN }
  refine
    { hyp :=
        { base := hbase
          n_pos := Nat.one_pos
          V_eq := h.eq_conjClosure_ch617 h331 h432 h512 h614 h615
          natural := h.natural_ch617 h331 h432 h512 h614 h615
          U_ne := fun hle => ?_ }
      card_V := hZS4
      card_V₁ := hZ2
      centralizer := h.centralizer_eq_ch617 h331 h432 h512 h614 h615
      sThree := h.sThree_ch617 h331 h432 h512 h614 h615
      inf_centerOf := ?_ }
  ·
    have hUC : uCh611 T L V ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
      have := hle.trans (h.pCoreOf_le_centralizer_ch617 h331 h432 h512 h614 h615)
      rwa [hNZ] at this
    have hle' : ch6ZS T L V ≤ V ⊓ centerOf (uCh611 T L V) := fun s hs =>
      ⟨hs.1, le_conjClosure _ _ hs, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (hUC hu) s hs).symm⟩
    rw [hVZU] at hle'
    have := Subgroup.card_le_of_le hle'
    omega
  · rw [hU]
    refine le_antisymm (fun s hs => ?_) (le_inf hZZS ?_)
    · rw [← hVZU]
      exact ⟨hs.1.1, hs.2⟩
    · rw [← hVZU]
      exact inf_le_right

end Hyp6Sec2

end CFSG.Quasithin.H13
