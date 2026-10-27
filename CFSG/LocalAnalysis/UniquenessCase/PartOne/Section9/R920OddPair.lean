module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigPi
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem orderOf_uc22p21cPi_eq {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥M}
    (hx : orderOf x = p) : orderOf (uc22p21cPi M x) = p := by
  have hne : uc22p21cPi M x ≠ 1 := by
    intro h1
    have h2 : x ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨x, h2⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : p ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hpow : uc22p21cPi M x ^ p = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  exact ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
    fun h => hne (orderOf_eq_one_iff.1 h)

theorem exists_orderOf_eq_of_dvd_card_bar2 {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (Bar2 X)) : ∃ x ∈ X, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hX : p ∣ Nat.card X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)]
    exact h.mul_right _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hX
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem two_le_pRank_of_pair {M L L' T : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hLL' : L ≠ L') (hZ : center (Bar2 L) = ⊥)
    (hTM : T ≤ M) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L') (hxT : x ∈ T) (hyT : y ∈ T)
    (hx : orderOf x = p) (hy : orderOf y = p) : 2 ≤ CFSG.Open.pRank p T := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x' : ↥M := ⟨x, hTM hxT⟩ with hx'
  set y' : ↥M := ⟨y, hTM hyT⟩ with hy'
  have ha : orderOf (uc22p21cPi M x') = p :=
    orderOf_uc22p21cPi_eq hp hp2 ((Subgroup.orderOf_coe x').symm.trans hx)
  have hb : orderOf (uc22p21cPi M y') = p :=
    orderOf_uc22p21cPi_eq hp hp2 ((Subgroup.orderOf_coe y').symm.trans hy)
  have haL : uc22p21cPi M x' ∈ barImage M L := uc22p21c_mem_barImage.2 ⟨x', hxL, rfl⟩
  have hbL : uc22p21cPi M y' ∈ barImage M L' := uc22p21c_mem_barImage.2 ⟨y', hyL, rfl⟩
  have hbn : uc22p21cPi M y' ∉ zpowers (uc22p21cPi M x') := fun h => by
    have h1 : uc22p21cPi M y' ∈ barImage M L ⊓ barImage M L' :=
      mem_inf.2 ⟨zpowers_le.2 haL h, hbL⟩
    rw [uc22s217j_barImage_inf_eq_bot hL hL' hLL' hZ, mem_bot] at h1
    rw [h1, orderOf_one] at hb
    exact hp.one_lt.ne hb
  obtain ⟨hWel, hWcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    ((Nat.card_zpowers _).trans ha) hb hbn fun c hc =>
      uc22p22l_barImage_commute hL hL' hLL' c (zpowers_le.2 haL hc) _ hbL
  have hWle : zpowers (uc22p21cPi M x') ⊔ zpowers (uc22p21cPi M y') ≤ barImage M T :=
    sup_le (zpowers_le.2 (uc22p21c_mem_barImage.2 ⟨x', hxT, rfl⟩))
      (zpowers_le.2 (uc22p21c_mem_barImage.2 ⟨y', hyT, rfl⟩))
  have h2 : 2 ≤ CFSG.Open.pRank p (barImage M T) := UC6S846.le_pRank' hp hWle hWel hWcard
  rwa [PartTwo.s13_pRank_barImage hp hp2 hTM] at h2

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem false_of_map_conj_ne (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : F07.R76Sig D) (hKF7 : KF7Use D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {E P : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) (hEU : E ∈ uniqueSet D.M) (hP : IsPGroup 3 ↥P) (hPM : P ≤ D.M)
    (hEP : E ≤ P) {h : G} (hh : h ∈ H) (hhP : E.map (MulAut.conj h).toMonoidHom ≤ P)
    (hne : E.map (MulAut.conj h).toMonoidHom ≠ E) : False := by
  classical
  have hhM : h ∈ D.M := mem_of_map_conj_le_of_mem_uniqueSet D.maxLocal hEU (hhP.trans hPM)
  have hLne : L.map (MulAut.conj h).toMonoidHom ≠ L := S.map_conj_L_ne hEX hE3 hP hEP hhP hne
  have hL := S.L_mem
  have hmem : L.map (MulAut.conj h).toMonoidHom ∈ conjSetOf D.M L := ⟨h, hhM, rfl⟩
  have hL'C := uc22p2214_calC_of_mem_conjSetOf hL hmem
  have hc2 : (conjSetOf D.M L).ncard = 2 := by
    have hle := S.ncard_conjSetOf_le_two h82 hnsp
    have hlt : 1 < (conjSetOf D.M L).ncard := (Set.one_lt_ncard_iff (Set.toFinite _)).2
      ⟨_, L, hmem, PartOne.Section8.mem_conjSetOf_self D.M L, hLne⟩
    omega
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2, -⟩ := S.sig_prime_ne_three hSg hnsp hp
  have hpL := S.dvd_card_bar2_of_mem_sig hSg h614 h76 hnsp hc2 hp
  have hpX : p ∣ Nat.card (Bar2 (Opp 3 Y)) := by
    obtain ⟨e⟩ := S.nonempty_bar2_L_opp_equiv
    rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨x, hxX, hx⟩ := exists_orderOf_eq_of_dvd_card_bar2 hpp hpX
  have hxH : x ∈ H := (opp_le 3 Y).trans S.Y_le_H hxX
  have hxM : x ∈ D.M := S.opp_le_M hxX
  have hy : orderOf (h * x * h⁻¹) = p := by
    rw [← hx]
    exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
  have hc : Subgroup.center (Bar2 L) = ⊥ :=
    haveI := S.facts_L.simple
    uc22p21k_center_eq_bot hL.2.2
  have hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) :=
    two_le_pRank_of_pair hpp hp2 hL hL'C hLne.symm hc
      inf_le_right (S.opp_le_L hxX) (Subgroup.mem_map.2 ⟨x, S.opp_le_L hxX, rfl⟩)
      (mem_inf.2 ⟨hxH, hxM⟩)
      (mem_inf.2 ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh),
        D.M.mul_mem (D.M.mul_mem hhM hxM) (D.M.inv_mem hhM)⟩) hx hy
  exact S.false_of_kf7Use hKF7 hSg hp hpX hrank

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
