module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem20

variable {G : Type} [Group G]

theorem normalizer_le_of_hyp1223 [Finite G] (h1226 : Stmt12_2_6) {T L V : Subgroup G}
    (hH : Hyp1223 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h := (h1226 G T L V hH).2 V (Subgroup.normalizer (V : Set G)) hH.irrPlus.2.1 le_rfl le_rfl
  intro x hx
  have hx' : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (V : Set G) := ⟨hx, hx⟩
  rw [← h] at hx'
  exact hx'.2

theorem autOn_le_autOn_inf {U M V : Subgroup G} (hVM : Subgroup.normalizer (V : Set G) ≤ M) :
    autOn U V ≤ autOn (M ⊓ Subgroup.normalizer (V : Set G)) V := by
  unfold autOn
  refine Subgroup.map_mono fun x hx => ?_
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact ⟨hVM x.2, x.2⟩

theorem four_le_card_of_index_eq_two {V : Subgroup G} [Finite ↥V] (hV2 : IsPGroup 2 ↥V)
    (hV : ¬ Nat.card V ≤ 4) {A : Subgroup ↥V} (hA : A.index = 2) : 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card A * 2 = Nat.card V := by rw [← hA]; exact A.card_mul_index
  obtain ⟨k, hk⟩ := (hV2.to_subgroup A).exists_card_eq
  rw [hk] at hcard ⊢
  rcases k with _ | _ | k
  · exact absurd (by rw [← hcard]; norm_num) hV
  · exact absurd (by rw [← hcard]; norm_num) hV
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Lem20

open Lem20

theorem stmt12_2_20_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1219 : Stmt12_2_19) (hpick : Lem12220Pick) (htr : Lem12220Transv) : Stmt12_2_20 := by
  intro G _ _ T L V hH hNE
  obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hHs
  have hsolv := h1219 G T L V hH hNE H hHs
  obtain ⟨h, -, -, hidx, hcomm, htv⟩ := hpick G T L V H hH hNE hHs hsolv
  have hVM := normalizer_le_of_hyp1223 (stmt12_2_6_of h1222 h323) hH
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hV2 : IsPGroup 2 ↥V := hH.sylow.1.to_le hVT
  have hA4 := four_le_card_of_index_eq_two
    (A := (pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V) hV2
    (Lem18.not_card_le_four hH hred) hidx
  have hle : transvAxis ((pCoreOf 2 (V ⊔ CFSG.conjugate V h) ⊓ V).subgroupOf V) ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V := by
    rw [← htv]
    exact autOn_le_autOn_inf hVM
  obtain ⟨n, hn, hV, hLV, hnat, hT⟩ := htr G T L V hH hcomm _ hidx hA4 hle
  exact ⟨n, hn, hV, hLV, ⟨hcomm, hnat⟩, hT⟩

theorem stmt12_2_24_config_of (h331 : Stmt3_3_1) (h1219 : Stmt12_2_19) (h1220 : Stmt12_2_20)
    (h2123 : Lem12221_23) (h24 : Lem12224Block) : Stmt12_2_24_config := by
  intro G _ _ T L V hH hNE
  obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hHs
  have hsolv := h1219 G T L V hH hNE H hHs
  obtain ⟨n, hn, hV, hLV, hnat, hT⟩ := h1220 G T L V hH hNE
  obtain ⟨P, U, I, h, p, hC⟩ := h2123 G T L V H hH hNE hHs hsolv n hn hV hLV hnat hT
  have hB := h24 G T L V H P U I h n p hH hNE hC
  obtain ⟨hHs', hsolv', hn', hV', hT', -, -, hp, hp2, hP, hord, hhH, hhM, hI, hU, hUd, hUi, hUe,
    hD, hUP, hidx, htv, hUO, hUV, hK, hHU, hHI, hIP, hHIT, hIM, hQU⟩ := hC
  exact ⟨H, P, U, I, h, n, p, hHs', hsolv', hn', hV', hT', hB, hp, hp2, hP, hord, hhH, hhM, hI,
    hU, hUd, hUi, hUe, hD, hUP, hidx, htv, hUO, hUV, hK, hHU, hHI, hIP, hHIT, hIM, hQU⟩

theorem stmt12_2_13_of_inputs (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1219 : Stmt12_2_19) (hpick : Lem12220Pick) (htr : Lem12220Transv) (h2123 : Lem12221_23)
    (h24 : Lem12224Block) (h2526 : Stmt12_2_25_26_of_config) (h27 : Stmt12_2_27) :
    Stmt12_2_13 :=
  stmt12_2_13_of_config
    (stmt12_2_24_config_of h331 h1219 (stmt12_2_20_of h331 h1222 h323 h1219 hpick htr) h2123 h24)
    h2526 h27

end CFSG.Quasithin.H13
