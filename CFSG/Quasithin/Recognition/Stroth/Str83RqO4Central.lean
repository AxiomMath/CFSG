module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
public import CFSG.Quasithin.Vol2.Ch11SecD557B

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem le_left_of_le_sup_of_isPGroup {N E D : Subgroup G}
    (hDE : D ≤ N ⊔ E) (hNE : E ≤ normalizer (N : Set G))
    (hE : IsPGroup 2 E) (hDodd : Odd (Nat.card D)) : D ≤ N := by
  classical
  let X : Subgroup G := N ⊔ E
  have hNX : N ≤ X := le_sup_left
  have hDX : D ≤ X := hDE
  have hXN : X ≤ normalizer (N : Set G) := sup_le Subgroup.le_normalizer hNE
  haveI : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  let π : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' (N.subgroupOf X)
  have hDsub : Nat.card (D.subgroupOf X) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
  have hmapodd : Odd (Nat.card ((D.subgroupOf X).map π)) :=
    hDodd.of_dvd_nat (by simpa [hDsub] using (D.subgroupOf X).card_map_dvd π)
  obtain ⟨k, hkE⟩ := hE.exists_card_eq
  have hrelX : N.relIndex X = N.relIndex E := by
    have hsup : E.subgroupOf X ⊔ N.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right : E ≤ X) (le_sup_left : N ≤ X),
        show E ⊔ N = X by rw [show X = N ⊔ E from rfl, sup_comm], Subgroup.subgroupOf_self]
    have h1 : (N.subgroupOf X).relIndex ⊤ = (N.subgroupOf X).relIndex (E.subgroupOf X) := by
      rw [← hsup, Subgroup.relIndex_sup_right]
    rw [Subgroup.relIndex_top_right] at h1
    change (N.subgroupOf X).index = N.relIndex E
    rw [h1, Subgroup.relIndex_subgroupOf (le_sup_right : E ≤ X)]
  have hquotdvd : Nat.card ((D.subgroupOf X).map π) ∣ 2 ^ k := by
    refine (Subgroup.card_dvd_of_le (le_top : (D.subgroupOf X).map π ≤ ⊤)).trans ?_
    rw [Subgroup.card_top]
    change (N.subgroupOf X).index ∣ 2 ^ k
    have hcard : (N.subgroupOf X).index = N.relIndex E := hrelX
    rw [hcard]
    simpa [hkE] using Subgroup.relIndex_dvd_card (H := N) (K := E)
  have hmapone : Nat.card ((D.subgroupOf X).map π) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hquotdvd
    have hoddpow : Odd (2 ^ j) := hj ▸ hmapodd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hoddpow)
        (Nat.even_pow.mpr ⟨⟨1, by norm_num⟩, hj0⟩)
    rw [hj, hj0]
    norm_num
  have hmapbot : (D.subgroupOf X).map π = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hmapone
  have hDker : D.subgroupOf X ≤ π.ker :=
    (Subgroup.map_eq_bot_iff (H := D.subgroupOf X) (f := π)).mp hmapbot
  rw [QuotientGroup.ker_mk'] at hDker
  intro d hd
  have hx : (⟨d, hDX hd⟩ : ↥X) ∈ D.subgroupOf X := hd
  exact Subgroup.mem_subgroupOf.mp (hDker hx)

private theorem exists_odd_orderOf_mem_oTwoRes {K : Subgroup G} (h : oTwoRes K ≠ ⊥) :
    ∃ g ∈ oTwoRes K, g ∈ K ∧ Odd (orderOf g) ∧ g ≠ 1 := by
  have hSne : ¬ {x : G | x ∈ K ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1} ⊆ {1} := by
    intro hsub
    exact h (Subgroup.closure_eq_bot_iff.mpr hsub)
  obtain ⟨g, hgS, hg1⟩ := Set.not_subset.mp hSne
  refine ⟨g, Subgroup.subset_closure hgS, hgS.1, ?_, by simpa using hg1⟩
  obtain ⟨m, hm, hgm⟩ := hgS.2
  exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hgm)

private theorem exists_arcLMax_above {Y : Subgroup G}
    (hY : t.ArcL Y) (hY2 : IsPGroup 2 Y) :
    ∃ X : Subgroup G, t.ArcLMax X ∧ t.MX Y 1 ≤ t.MX X 1 := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (fun _ _ h => SetLike.coe_injective h)
  let s : Set (Subgroup G) :=
    {Z | t.ArcL Z ∧ IsPGroup 2 Z ∧ t.MX Y 1 ≤ t.MX Z 1}
  have hsne : s.Nonempty := ⟨Y, hY, hY2, le_rfl⟩
  obtain ⟨X, hXs, hXmax⟩ :=
    Set.Finite.exists_maximalFor (f := fun Z : Subgroup G => t.MX Z 1) s
      (Set.toFinite s) hsne
  have hXs' : t.ArcL X ∧ IsPGroup 2 X ∧ t.MX Y 1 ≤ t.MX X 1 := by
    simpa [s] using hXs
  refine ⟨X, ⟨hXs'.1, hXs'.2.1, ?_⟩, hXs'.2.2⟩
  intro W hW hW2 hXW
  have hWs : W ∈ s := ⟨hW, hW2, hXs'.2.2.trans hXW⟩
  exact hXmax hWs hXW

private theorem MX_QT_eq_of_arcLMax {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hmax : ∀ X : Subgroup G, t.ArcLMax X → IsElemAbelian 2 (t.EX X 1) ∧
      t.MX X 1 = t.LX X 1 ⊔ t.K ∧ t.LX X 1 ⊓ t.Qv 1 = t.EX X 1)
    (hL : ∀ X : Subgroup G, t.ArcLMax X → t.MX t.QT 1 ≤ t.MX X 1 →
      t.LX X 1 ≤ t.LX t.QT 1 ⊔ t.EX X 1)
    {X : Subgroup G} (hX : t.ArcLMax X) (hle : t.MX t.QT 1 ≤ t.MX X 1) :
    t.MX X 1 ≤ t.MX t.QT 1 := by
  have hQTleQv : t.QT ≤ t.Qv 1 := t.pCoreOf_GT_le_Qv hfr 1
  have hQTleMXQ : t.QT ≤ t.MX t.QT 1 :=
    le_inf Subgroup.le_normalizer (hQTleQv.trans (t.Qv_le_Gv_self 1))
  have hQTleMX : t.QT ≤ t.MX X 1 := hQTleMXQ.trans hle
  have hQTE : t.QT ≤ t.EX X 1 :=
    le_inf hQTleQv (hQTleMX.trans inf_le_left)
  have hEab : IsElemAbelian 2 (t.EX X 1) := (hmax X hX).1
  have hEXcent : t.EX X 1 ≤ Subgroup.centralizer (t.QT : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hEab.1).trans
      (Subgroup.centralizer_le hQTE)
  have hEXN : t.EX X 1 ≤ normalizer (t.QT : Set G) :=
    hEXcent.trans (Subgroup.centralizer_le_normalizer _)
  have hLQN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G) :=
    (oTwoPrime_le (t.MX t.QT 1)).trans inf_le_left
  have hLXN : t.LX X 1 ≤ normalizer (t.QT : Set G) :=
    (hL X hX hle).trans (sup_le hLQN hEXN)
  have hMXN : t.MX X 1 ≤ normalizer (t.QT : Set G) := by
    rw [(hmax X hX).2.1]
    exact sup_le hLXN t.K_le_normalizer_pCoreOf_GT
  exact le_inf hMXN inf_le_right

theorem arcLMax_QT {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hQ : t.ArcL t.QT)
    (hmax : ∀ X : Subgroup G, t.ArcLMax X → IsElemAbelian 2 (t.EX X 1) ∧
      t.MX X 1 = t.LX X 1 ⊔ t.K ∧ t.LX X 1 ⊓ t.Qv 1 = t.EX X 1)
    (hL : ∀ X : Subgroup G, t.ArcLMax X → t.MX t.QT 1 ≤ t.MX X 1 →
      t.LX X 1 ≤ t.LX t.QT 1 ⊔ t.EX X 1) :
    t.ArcLMax t.QT := by
  change IsArcClassMax (t.Gv 1) (t.Gv 0) (t.Gv (-1)) t.K t.x₁ t.QT
  refine ⟨hQ, pCoreOf_isPGroup 2 t.GT, ?_⟩
  intro Y hY hY2 hle
  obtain ⟨X, hXmax, hYX⟩ := exists_arcLMax_above t hY hY2
  exact hYX.trans (MX_QT_eq_of_arcLMax t hfr hmax hL hXmax (hle.trans hYX))

private theorem le_normalizer_commutator {L Q Y : Subgroup G}
    (hQN : L ≤ normalizer (Q : Set G)) (hYN : L ≤ normalizer (Y : Set G)) :
    L ≤ normalizer ((⁅Q, Y⁆ : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj l).toMonoidHom ⁅Q, Y⁆ = ⁅Q, Y⁆
  rw [Subgroup.map_commutator]
  have hQ : Subgroup.map (MulAut.conj l).toMonoidHom Q = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN hl)
  have hY : Subgroup.map (MulAut.conj l).toMonoidHom Y = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYN hl)
  rw [hQ, hY]

private theorem commutator_QT_zpowers_eq_bot {y : G}
    (hyY : y ∈ t.YX t.QT 1) (hyL : y ∈ t.LX t.QT 1) (hodd : Odd (orderOf y))
    (hQN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G))
    (hW : ⁅t.QT, t.YX t.QT 1⁆ ≤ centerOf (t.LX t.QT 1)) :
    ⁅t.QT, Subgroup.zpowers y⁆ = ⊥ := by
  have hzyY : Subgroup.zpowers y ≤ t.YX t.QT 1 := Subgroup.zpowers_le.mpr hyY
  have hzyL : Subgroup.zpowers y ≤ t.LX t.QT 1 := Subgroup.zpowers_le.mpr hyL
  have hzyN : Subgroup.zpowers y ≤ normalizer (t.QT : Set G) := hzyL.trans hQN
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 t.GT).exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers y)) (Nat.card (t.QT : Subgroup G)) := by
    rw [Nat.card_zpowers, hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hcomm := CFSG.Quasithin.Vol2.Ch11.SecD.commutator_commutator_eq hzyN hcop
  have h1 : ⁅t.QT, Subgroup.zpowers y⁆ ≤ centerOf (t.LX t.QT 1) :=
    (Subgroup.commutator_mono le_rfl hzyY).trans hW
  have h2 : ⁅centerOf (t.LX t.QT 1), Subgroup.zpowers y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right.trans (Subgroup.centralizer_le hzyL)
  have h3 : ⁅⁅t.QT, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ ≤ ⊥ := by
    rw [← h2]
    exact Subgroup.commutator_mono h1 le_rfl
  rw [← hcomm]
  exact le_bot_iff.mp h3

private theorem commutator_EX_YX_le_QT {W : Subgroup G}
    (hWZ : W ⊔ centerOf (t.LX t.QT 1) = t.EX t.QT 1)
    (hWleQ : W ≤ t.QT) (hQTL : t.QT ≤ t.LX t.QT 1)
    (hWnorm : t.LX t.QT 1 ≤ normalizer (W : Set G))
    (hZnorm : t.LX t.QT 1 ≤ normalizer (centerOf (t.LX t.QT 1) : Set G)) :
    ⁅t.EX t.QT 1, t.YX t.QT 1⁆ ≤ t.QT := by
  refine Subgroup.commutator_le.mpr ?_
  intro e he y hy
  have he' : e ∈ ((W ⊔ centerOf (t.LX t.QT 1) : Subgroup G) : Set G) := by
    rw [hWZ]
    exact he
  have hWZprod : ((W ⊔ centerOf (t.LX t.QT 1) : Subgroup G) : Set G) =
      (W : Set G) * (centerOf (t.LX t.QT 1) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right W _ ((hWleQ.trans hQTL).trans hZnorm)
  rw [hWZprod] at he'
  obtain ⟨w, hw, z, hz, rfl⟩ := Set.mem_mul.mp he'
  have hzy : z * y = y * z := by
    have hzC : z ∈ Subgroup.centralizer (t.LX t.QT 1 : Set G) :=
      (Subgroup.mem_inf.mp hz).2
    exact ((Subgroup.mem_centralizer_iff.mp hzC) y ((oTwoRes_le _) hy)).symm
  have hcomm : ⁅w * z, y⁆ = ⁅w, y⁆ := by
    simp only [commutatorElement_def]
    have h1 : w * z * y = w * y * z := by
      rw [mul_assoc, hzy, ← mul_assoc]
    calc w * z * y * (w * z)⁻¹ * y⁻¹
        = w * y * z * (w * z)⁻¹ * y⁻¹ := by rw [h1]
      _ = w * y * w⁻¹ * y⁻¹ := by group
  rw [hcomm]
  exact hWleQ ((Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((oTwoRes_le _).trans hWnorm)) (Subgroup.commutator_mem_commutator hw hy))

private theorem commutator_QT_YX_le_center {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hV2 : ¬ ⁅t.EX t.QT 1, t.YX t.QT 1⁆ ≤ t.EX t.QT (-1)) :
    ⁅t.QT, t.YX t.QT 1⁆ ≤ centerOf (t.LX t.QT 1) := by
  have hQTQv : t.QT ≤ t.Qv 1 := t.pCoreOf_GT_le_Qv hfr 1
  have hQTEX : t.QT ≤ t.EX t.QT 1 := le_inf hQTQv Subgroup.le_normalizer
  have hQTL : t.QT ≤ t.LX t.QT 1 := hQTEX.trans hnat.E_le
  have hLQN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G) :=
    (oTwoPrime_le (t.MX t.QT 1)).trans inf_le_left
  have hYQN : t.YX t.QT 1 ≤ normalizer (t.QT : Set G) :=
    (oTwoRes_le (t.LX t.QT 1)).trans hLQN
  set W := ⁅t.QT, t.YX t.QT 1⁆ with hWdef
  have hWleQ : W ≤ t.QT := by
    rw [hWdef]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hYQN
  have hWleE : W ≤ t.EX t.QT 1 := hWleQ.trans hQTEX
  have hWnorm : t.LX t.QT 1 ≤ normalizer (W : Set G) :=
    le_normalizer_commutator (L := t.LX t.QT 1) (Q := t.QT) (Y := t.YX t.QT 1)
      hLQN (le_normalizer_oTwoRes _)
  have hZnorm : t.LX t.QT 1 ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf _)
  have hWZnorm : t.LX t.QT 1 ≤
      normalizer ((W ⊔ centerOf (t.LX t.QT 1) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hWnorm hZnorm
  have hWZleE : W ⊔ centerOf (t.LX t.QT 1) ≤ t.EX t.QT 1 :=
    sup_le hWleE hnat.Z_le
  rcases hnat.irred (W ⊔ centerOf (t.LX t.QT 1)) le_sup_right hWZleE hWZnorm
    with hWZ | hWZ
  · exact le_sup_left.trans (le_of_eq hWZ)
  · exfalso
    have hEY_le_Q : ⁅t.EX t.QT 1, t.YX t.QT 1⁆ ≤ t.QT :=
      commutator_EX_YX_le_QT (t := t) hWZ hWleQ hQTL hWnorm hZnorm
    have hQEm : t.QT ≤ t.EX t.QT (-1) :=
      le_inf (t.pCoreOf_GT_le_Qv hfr (-1)) Subgroup.le_normalizer
    exact hV2 (hEY_le_Q.trans hQEm)

theorem QT_le_center {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hV2 : ¬ ⁅t.EX t.QT 1, t.YX t.QT 1⁆ ≤ t.EX t.QT (-1)) :
    t.QT ≤ centerOf (t.LX t.QT 1) := by
  have hQTQv : t.QT ≤ t.Qv 1 := t.pCoreOf_GT_le_Qv hfr 1
  have hQTEX : t.QT ≤ t.EX t.QT 1 := le_inf hQTQv Subgroup.le_normalizer
  have hQTL : t.QT ≤ t.LX t.QT 1 := hQTEX.trans hnat.E_le
  have hLQN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G) :=
    (oTwoPrime_le (t.MX t.QT 1)).trans inf_le_left
  have hWleZ : ⁅t.QT, t.YX t.QT 1⁆ ≤ centerOf (t.LX t.QT 1) :=
    commutator_QT_YX_le_center (t := t) hfr hnat hV2
  have hYne : t.YX t.QT 1 ≠ ⊥ := by
    intro hbot
    apply hV2
    rw [hbot, Subgroup.commutator_bot_right]
    exact bot_le
  obtain ⟨y0, hy0Y, hy0L, hodd, hy0ne⟩ := exists_odd_orderOf_mem_oTwoRes hYne
  have hE2 : IsPGroup 2 (t.EX t.QT 1) := (t.isPGroup_Qv 1).to_le inf_le_left
  have hy0notE : y0 ∉ t.EX t.QT 1 := by
    intro hy0E
    obtain ⟨k, hk⟩ := hE2.exists_card_eq
    have hdvd : orderOf y0 ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard (t.EX t.QT 1) hy0E
    have hcop : Nat.Coprime (orderOf y0) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hodd).pow_right k
    have hone : orderOf y0 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    exact hy0ne (orderOf_eq_one_iff.mp hone)
  have hW0bot : ⁅t.QT, Subgroup.zpowers y0⁆ = ⊥ :=
    commutator_QT_zpowers_eq_bot (t := t) hy0Y hy0L hodd hLQN hWleZ
  intro q hq
  have hqZ : q ∈ centerOf (t.LX t.QT 1) := by
    have hqE : q ∈ t.EX t.QT 1 := hQTEX hq
    have hcommZ : ⁅q, y0⁆ ∈ centerOf (t.LX t.QT 1) := by
      have hmem : ⁅q, y0⁆ ∈ ⁅t.QT, Subgroup.zpowers y0⁆ :=
        Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers y0)
      rw [hW0bot] at hmem
      rw [Subgroup.mem_bot.mp hmem]
      exact (centerOf (t.LX t.QT 1)).one_mem
    exact hnat.fpf y0 hy0L hodd hy0notE q hqE hcommZ
  exact Subgroup.mem_inf.mpr ⟨hQTL hq, (Subgroup.mem_inf.mp hqZ).2⟩

theorem D2_le_YX (hQ : t.ArcL t.QT) (hcov : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1) :
    t.D2 ≤ t.YX t.QT 1 := by
  have hD2L2 : t.D2 ≤ L2 := t.hD2hall.1.trans inf_le_left
  have hD2K : t.D2 ≤ t.K := le_sup_right
  have hD2N : t.D2 ≤ normalizer (t.QT : Set G) := hD2K.trans hQ.K_le
  have hLQN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G) :=
    (oTwoPrime_le (t.MX t.QT 1)).trans inf_le_left
  have hLQnormQv : t.LX t.QT 1 ≤ normalizer (t.Qv 1 : Set G) :=
    ((oTwoPrime_le (t.MX t.QT 1)).trans inf_le_right).trans (t.Gv_le_normalizer_Qv 1)
  have hD2sup : t.D2 ≤ t.LX t.QT 1 ⊔ t.EX t.QT 1 := by
    intro d hd
    have hd1 : d ∈ t.Qv 1 ⊔ t.LX t.QT 1 := by
      rw [sup_comm]
      exact (hD2L2.trans hcov) hd
    obtain ⟨q, hq, l, hl, hdq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hLQnormQv).mp hd1
    have hqeq : q = d * l⁻¹ := by rw [hdq]; group
    have hqN : q ∈ normalizer (t.QT : Set G) := by
      rw [hqeq]
      exact (normalizer (t.QT : Set G)).mul_mem (hD2N hd)
        ((normalizer (t.QT : Set G)).inv_mem (hLQN hl))
    have hqE : q ∈ t.EX t.QT 1 := ⟨hq, hqN⟩
    rw [hdq, sup_comm]
    exact Subgroup.mul_mem_sup hqE hl
  have hdisj : Disjoint t.D2 (t.Qv 1) := by
    obtain ⟨k, hk⟩ := (t.isPGroup_Qv 1).exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact (Nat.coprime_two_right.mpr t.hD2hall.2.1).pow_right k
  have hEXMX : t.EX t.QT 1 ≤ t.MX t.QT 1 :=
    le_inf inf_le_right (inf_le_left.trans (t.Qv_le_Gv_self 1))
  have hNEN : t.EX t.QT 1 ≤ normalizer (t.LX t.QT 1 : Set G) :=
    hEXMX.trans (le_normalizer_oTwoPrime (t.MX t.QT 1))
  have hEXP : IsPGroup 2 (t.EX t.QT 1) := (t.isPGroup_Qv 1).to_le inf_le_left
  have hD2LQ : t.D2 ≤ t.LX t.QT 1 :=
    le_left_of_le_sup_of_isPGroup hD2sup hNEN hEXP t.hD2hall.2.1
  intro d hd
  change d ∈ oTwoRes (t.LX t.QT 1)
  refine Subgroup.subset_closure ⟨hD2LQ hd, orderOf d, ?_, pow_orderOf_eq_one d⟩
  exact t.hD2hall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard t.D2 hd)

end Track

end CFSG.Quasithin.Stroth.Rq

end
