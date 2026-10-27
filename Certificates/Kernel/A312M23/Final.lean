
module

public import Certificates.Kernel.A312M23.Bridge
public import CFSG.Quasithin.Background.HSporLatM23Sg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Lat
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Schreier.M23PinnedInputs
import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import CFSG.Quasithin.Background.HSporLatInputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import Certificates.Certificate4170Base

public section

namespace CFSG.KD.A312M23

open CFSG.KC.A312M23K

theorem y1_chk : m22Chk y1T AB Sg (gw 1) 23 y1Bl y1Bi y1WA y1WB y1GA y1GB = true := ch4170y1_0

theorem y8_chk : triChk y8T AB Sg (gw 8) 23 y8Bl y8Bi y8X = true := ch4170y8_0

theorem y2_chk : l34Chk y2T AB Sg (gw 2) 23 y2Xs y2Tq y2Ws y2Wcj y2Wu y2Wv y2Rel y2Wxs = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    interval_cases k
    · exact ch4170y2_0
    · exact ch4170y2_1
    · exact ch4170y2_2
    · exact ch4170y2_3

theorem y3_len : y3Xs.length = 3 := eq_of_beq (by quickRfl)
theorem y4_len : y4Xs.length = 2 := eq_of_beq (by quickRfl)
theorem y5_len : y5Xs.length = 2 := eq_of_beq (by quickRfl)
theorem y6_len : y6Xs.length = 2 := eq_of_beq (by quickRfl)
theorem y7_len : y7Xs.length = 3 := eq_of_beq (by quickRfl)
theorem y9_len : y9Xs.length = 3 := eq_of_beq (by quickRfl)

theorem y3_chk : e2Chk y3T AB Sg (gw 3) 23 y3Xs y3Tq y3Ws y3V y3Wit y3Ex y3Bl y3Bi 360 y3Sp false
    y3Cw false y3Wcj y3B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y3_len] at hk'
    interval_cases k
    · exact ch4170y3_0
    · exact ch4170y3_1
    · exact ch4170y3_2
    · exact ch4170y3_3
    · exact ch4170y3_4
    · exact ch4170y3_5
    · exact ch4170y3_6
    · exact ch4170y3_7
    · exact ch4170y3_8
    · exact ch4170y3_9
    · exact ch4170y3_10

theorem y4_chk : e2Chk y4T AB Sg (gw 4) 23 y4Xs y4Tq y4Ws y4V y4Wit y4Ex y4Bl y4Bi 168 y4Sp true
    y4Cw false y4Wcj y4B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y4_len] at hk'
    interval_cases k
    · exact ch4170y4_0
    · exact ch4170y4_1
    · exact ch4170y4_2
    · exact ch4170y4_3
    · exact ch4170y4_4
    · exact ch4170y4_5
    · exact ch4170y4_6
    · exact ch4170y4_7
    · exact ch4170y4_8

theorem y5_chk : e2Chk y5T AB Sg (gw 5) 23 y5Xs y5Tq y5Ws y5V y5Wit y5Ex y5Bl y5Bi 2520 y5Sp
    false y5Cw false y5Wcj y5B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y5_len] at hk'
    interval_cases k
    · exact ch4170y5_0
    · exact ch4170y5_1
    · exact ch4170y5_2
    · exact ch4170y5_3
    · exact ch4170y5_4
    · exact ch4170y5_5
    · exact ch4170y5_6
    · exact ch4170y5_7
    · exact ch4170y5_8

theorem y6_chk : e2Chk y6T AB Sg (gw 6) 23 y6Xs y6Tq y6Ws y6V y6Wit y6Ex y6Bl y6Bi 168 y6Sp true
    y6Cw true y6Wcj y6B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y6_len] at hk'
    interval_cases k
    · exact ch4170y6_0
    · exact ch4170y6_1
    · exact ch4170y6_2
    · exact ch4170y6_3
    · exact ch4170y6_4
    · exact ch4170y6_5
    · exact ch4170y6_6
    · exact ch4170y6_7
    · exact ch4170y6_8

theorem y7_chk : e2Chk y7T AB Sg (gw 7) 23 y7Xs y7Tq y7Ws y7V y7Wit y7Ex y7Bl y7Bi 60 y7Sp false
    y7Cw true y7Wcj y7B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y7_len] at hk'
    interval_cases k
    · exact ch4170y7_0
    · exact ch4170y7_1
    · exact ch4170y7_2
    · exact ch4170y7_3
    · exact ch4170y7_4
    · exact ch4170y7_5
    · exact ch4170y7_6
    · exact ch4170y7_7
    · exact ch4170y7_8
    · exact ch4170y7_9
    · exact ch4170y7_10

theorem y9_chk : e2Chk y9T AB Sg (gw 9) 23 y9Xs y9Tq y9Ws y9V y9Wit y9Ex y9Bl y9Bi 60 y9Sp false
    y9Cw true y9Wcj y9B = true :=
  List.all_eq_true.mpr fun k hk => by
    have hk' := List.mem_range.mp hk
    rw [y9_len] at hk'
    interval_cases k
    · exact ch4170y9_0
    · exact ch4170y9_1
    · exact ch4170y9_2
    · exact ch4170y9_3
    · exact ch4170y9_4
    · exact ch4170y9_5
    · exact ch4170y9_6
    · exact ch4170y9_7
    · exact ch4170y9_8
    · exact ch4170y9_9
    · exact ch4170y9_10

section Facts

open CFSG.Quasithin.A312M23 CFSG.Quasithin.A312Words CFSG.Quasithin.H.MathieuLat
open CFSG.QuasithinUnique.K1.SporadicPerm
open scoped Pointwise

theorem card_mul_two_le {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    {t : G} (htK : t ∈ K) (htH : t ∉ H) : Nat.card H * 2 ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    have e := Subgroup.eq_of_le_of_card_ge hle hc.le
    rw [← e] at htK
    exact htH htK
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (Nat.card_pos (α := K)).ne' hc
  rw [hc]
  exact Nat.mul_le_mul_left _ (by omega)

theorem card_img_eq {G α : Type} [Group G] [Finite G] [MulAction G α] {Y : Subgroup G}
    {ol vl : List G} {t : G} (hid : IdxTwoData Y ol t) {m : ℕ} (pt : Fin m → α)
    (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol}) (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i)
    {k r c : ℕ} (hc : 0 < c) (hV : Nat.card (Subgroup.closure {v | v ∈ vl}) = 2 ^ k)
    (hY : Nat.card Y = c * (2 ^ k * r))
    (hol : Nat.card (Subgroup.closure {x | x ∈ ol}) * c ≤ Nat.card Y)
    (hE : r ∣ Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)})) :
    Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) = r := by
  have hge := ext_core_ge (fun g hg => hid.mem g hg) pt hpt hYp vl hvol hvfix
  rw [hV] at hge
  have hEpos : 0 < Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) :=
    Nat.card_pos
  have h1 : 2 ^ k * Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) * c ≤
      2 ^ k * r * c := by
    calc _ ≤ Nat.card (Subgroup.closure {x | x ∈ ol}) * c := Nat.mul_le_mul_right c hge
      _ ≤ Nat.card Y := hol
      _ = 2 ^ k * r * c := by rw [hY]; ring
  have h2 := Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_right h1 hc) (by positivity)
  exact le_antisymm h2 (Nat.le_of_dvd hEpos hE)

theorem hf23 : ∀ g : CFSG.KD.M23Dc.G, (∀ p < 23, act 23 g p = p) → g = 1 :=
  fun g h => base_of_faithful g fun b hb => h b (List.mem_range.mp hb)

theorem card_member (j : ℕ) (hj : j < 16) :
    Nat.card (m23Member j) = #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9][j]! * 128 := by
  rw [← m23Ctx_Y]
  exact m23_member_card j hj

theorem e2_facts {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 9) {T : List (List ℕ)}
    {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ} {ws vws : List (List ℕ)} {wit ex : List ℕ}
    {bl bi : List (List ℕ)} {r : ℕ} {spec : List (ℕ × List (List ℕ))} {tr : Bool} {cw : List ℕ}
    {alt : Bool} {wcj : List (List ℕ)} {b : List ℕ} {k m : ℕ} (hr : 0 < r)
    (hc : e2Chk T AB Sg (gw j) 23 xs t ws vws wit ex bl bi r spec tr cw alt wcj b = true)
    (hk : vws.length = k) (hm : bl.length = m)
    (hY : Nat.card (m23Member j) = (bif alt then 2 else 1) * (2 ^ k * r)) :
    E2Facts (Set (Fin 23)) (m23Member j) k m r alt tr := by
  subst hk hm
  obtain ⟨hel, hid, halt, hperm, hpt, hYp, hvol, hVn, hvc, hvsq, hvfix, hV, hE, htr⟩ :=
    e2_sound (Γ := CFSG.KD.M23Dc.G) (n := 23) hf23 rep_Sg rep_AB hr hc
  rw [← YT_eq hj1 hj hel] at hY ⊢
  refine ⟨_, _, hid, halt, hperm, bPt 23 bl, hpt, hYp, _, hvol, hVn, hvc, hvsq, hvfix, hV, ?_,
    htr⟩
  have hYol := (Subgroup.closure_le _).mpr fun g hg => hid.mem g hg
  cases alt
  · exact card_img_eq hid _ hpt hYp hvol hvfix one_pos hV hY
      (by rw [mul_one]; exact Subgroup.card_le_of_le hYol) hE
  · exact card_img_eq hid _ hpt hYp hvol hvfix two_pos hV hY
      (card_mul_two_le hYol hid.tmem (halt rfl).2) hE

theorem y3_facts : E2Facts (Set (Fin 23)) (m23Member 3) 4 6 360 false false :=
  e2_facts (j := 3) (by norm_num) (by norm_num) (by norm_num) y3_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 3 (by norm_num)]; rfl)

theorem y4_facts : E2Facts (Set (Fin 23)) (m23Member 4) 4 7 168 false true :=
  e2_facts (j := 4) (by norm_num) (by norm_num) (by norm_num) y4_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 4 (by norm_num)]; rfl)

theorem y5_facts : E2Facts (Set (Fin 23)) (m23Member 5) 4 7 2520 false false :=
  e2_facts (j := 5) (by norm_num) (by norm_num) (by norm_num) y5_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 5 (by norm_num)]; rfl)

theorem y6_facts : E2Facts (Set (Fin 23)) (m23Member 6) 3 7 168 true true :=
  e2_facts (j := 6) (by norm_num) (by norm_num) (by norm_num) y6_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 6 (by norm_num)]; rfl)

theorem y7_facts : E2Facts (Set (Fin 23)) (m23Member 7) 4 5 60 true false :=
  e2_facts (j := 7) (by norm_num) (by norm_num) (by norm_num) y7_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 7 (by norm_num)]; rfl)

theorem y9_facts : E2Facts (Set (Fin 23)) (m23Member 9) 4 5 60 true false :=
  e2_facts (j := 9) (by norm_num) (by norm_num) (by norm_num) y9_chk (eq_of_beq (by quickRfl))
    (eq_of_beq (by quickRfl)) (by rw [card_member 9 (by norm_num)]; rfl)

theorem m22_facts_of_len {G α : Type} [Group G] [MulAction G α] {Y : Subgroup G} {m : ℕ}
    (hm : m = 22) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) {eA eB : G} (hA : eA ∈ Y) (hB : eB ∈ Y)
    (hgA : ∀ i, (rhoFn Y pt hpt hYp eA i).val = m22TabA.toList.getD i.val 0)
    (hgB : ∀ i, (rhoFn Y pt hpt hYp eB i).val = m22TabB.toList.getD i.val 0) :
    M22Facts α Y := by
  subst hm
  exact ⟨pt, hpt, hYp, eA, eB, hA, hB, hgA, hgB⟩

theorem y1_facts : M22Facts (Set (Fin 23)) (m23Member 1) := by
  obtain ⟨hel, h22, hpt, hYp, hA, hB, hgA, hgB⟩ :=
    m22_sound (Γ := CFSG.KD.M23Dc.G) (n := 23) hf23 rep_Sg rep_AB y1_chk
  rw [y1GA_eq] at hgA
  rw [y1GB_eq] at hgB
  rw [← YT_eq (j := 1) le_rfl (by norm_num) hel]
  exact m22_facts_of_len h22 _ hpt hYp hA hB hgA hgB

theorem wordProd_img2_getD {G : Type} [Group G] (u v : G) (r : List (Fin 2 × Bool)) :
    CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 u v)
        (r.map fun l => (l.1.val, l.2)) =
      ((r.map fun l => bif l.2 then l.1.val else l.1.val + 2).map
        fun a => [u, v, u⁻¹, v⁻¹].getD a 1).prod := by
  unfold CFSG.Sporadic.Bridge.wordProd
  rw [List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> rfl

theorem y2_facts : L34Facts (m23Member 2) := by
  obtain ⟨hel, hid, hn, huN, hvN, -, hrel, hgen⟩ :=
    l34_sound (Γ := CFSG.KD.M23Dc.G) (n := 23) hf23 rep_Sg rep_AB y2_chk
  rw [← YT_eq (j := 2) (by norm_num) (by norm_num) hel]
  refine ⟨_, _, hid, hn, _, _, huN, hvN, fun w hw => ?_, hgen⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  rw [wordProd_img2_getD]
  exact hrel _ (by rw [y2Rel_eq]; exact List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem tri_facts_of_len {G α : Type} [Group G] [MulAction G α] {Y : Subgroup G} {m : ℕ}
    (hm : m = 3) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) {x : G} (hx : x ∈ Y) {k : ℕ} (hk : k % 2 = 1)
    (hxk : x ^ k = 1) (hmov : ∃ i, x • pt i ≠ pt i) : TriFacts α Y := by
  subst hm
  exact ⟨pt, hpt, hYp, x, hx, k, hk, hxk, hmov⟩

theorem y8_facts : TriFacts (Set (Fin 23)) (m23Member 8) := by
  obtain ⟨hel, h3, hpt, hYp, hxY, hodd, hpow, hmov⟩ :=
    tri_sound (Γ := CFSG.KD.M23Dc.G) (n := 23) hf23 rep_Sg rep_AB y8_chk
  rw [← YT_eq (j := 8) (by norm_num) (by norm_num) hel]
  exact tri_facts_of_len h3 _ hpt hYp hxY hodd hpow hmov

theorem m23_4170 :
    M22Facts (Set (Fin 23)) (m23Member 1) ∧ L34Facts (m23Member 2) ∧
      E2Facts (Set (Fin 23)) (m23Member 3) 4 6 360 false false ∧
      E2Facts (Set (Fin 23)) (m23Member 4) 4 7 168 false true ∧
      E2Facts (Set (Fin 23)) (m23Member 5) 4 7 2520 false false ∧
      E2Facts (Set (Fin 23)) (m23Member 6) 3 7 168 true true ∧
      E2Facts (Set (Fin 23)) (m23Member 7) 4 5 60 true false ∧
      E2Facts (Set (Fin 23)) (m23Member 9) 4 5 60 true false ∧
      TriFacts (Set (Fin 23)) (m23Member 8) :=
  ⟨y1_facts, y2_facts, y3_facts, y4_facts, y5_facts, y6_facts, y7_facts, y9_facts, y8_facts⟩

end Facts

end CFSG.KD.A312M23

end
