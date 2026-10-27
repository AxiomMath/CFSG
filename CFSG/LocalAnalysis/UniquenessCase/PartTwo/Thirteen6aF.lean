module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aPairF
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22S13g
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res3Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s136a_pRank_le_one_of_isL2 {D : Data G} (hH : F13.Hyp131 D) {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hLs : IsL2 (Bar2 L) n) :
    CFSG.Open.pRank p L ≤ 1 := by
  rcases uc22s2121e3_pRank_le_of_mem_calC hH hpp hp2 hL with h | ⟨⟨n', -, hU, -⟩, -⟩
  · exact h
  · exact absurd hLs (not_isL2_of_isU3 hU)

private theorem s136a_pRank_barImage_le_one_of_isL2 {D : Data G} (hH : F13.Hyp131 D) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hLs : IsL2 (Bar2 L) n) : CFSG.Open.pRank r (barImage D.M L) ≤ 1 := by
  rw [s13_pRank_barImage hr hr2 (s13_le_of_mem_calC hL)]
  exact s136a_pRank_le_one_of_isL2 hH hr hr2 hL hLs

private theorem s136a_exists_commute_three {M L : Subgroup G} (hL : L ∈ calC M) {n p : ℕ}
    (hLs : IsL2 (Bar2 L) n) (hn : Even n) (hpp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ a ∈ barImage M L, ∃ y ∈ barImage M L, orderOf a = p ∧ orderOf y = 3 ∧ a * y = y * a := by
  have : Fact p.Prime := ⟨hpp⟩
  have h3n : 3 ∣ 2 ^ n - 1 := by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp hn)
  have hpL : p ∣ Nat.card (Bar2 L) := by
    rw [S17.card_of_isL2 hLs]
    exact dvd_mul_of_dvd_right
      (hpn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left n 2))) _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpL
  obtain ⟨y, hy, hay⟩ := isL2_exists_orderOf_commute hLs hpp hp2 hpn Nat.prime_three h3n ha
  obtain ⟨e⟩ := s13_bar_equiv hL
  refine ⟨e a, (e a).2, e y, (e y).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  · have h := congrArg (fun x => ((e x : ↥(barImage M L)) : Bar2 M)) hay
    simpa only [map_mul, Subgroup.coe_mul] using h

private theorem s136a_exists_orderOf_three {M K : Subgroup G} (hK : K ∈ calC M) {m : ℕ}
    (hKs : IsL2 (Bar2 K) m) : ∃ y ∈ barImage M K, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (Bar2 K) := by
    rw [S17.card_of_isL2 hKs]
    exact dvd_mul_of_dvd_right
      (by simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right 2 m)) _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨e⟩ := s13_bar_equiv hK
  exact ⟨e y, (e y).2, by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]⟩

private theorem s136a_exists_lift_pRank_two {M : Subgroup G} {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) {Y : Subgroup (Bar2 M)} (hY : IsElemAbelian p Y) (hYc : Nat.card Y = p ^ 2) :
    ∃ A₀ ≤ M, IsPGroup p ↥A₀ ∧ barImage M A₀ = Y ∧ CFSG.Open.pRank p A₀ = 2 := by
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p ↥(barPreimage M Y)) := inferInstance
  have hA₀M : (S : Subgroup ↥(barPreimage M Y)).map (barPreimage M Y).subtype ≤ M :=
    (map_subtype_le _).trans (uc22p21c_barPreimage_le M Y)
  have hbar := uc22ine229_barImage_map_sylow hY.isPGroup S
  refine ⟨_, hA₀M, S.isPGroup'.map _, hbar, ?_⟩
  rw [← s13_pRank_barImage hpp hp2 hA₀M, hbar]
  have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hpp hY
  rw [hYc] at h
  exact ((Nat.pow_right_inj hpp.one_lt).mp h).symm

private theorem s136a_stronglyEmbedded_of_E9 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) {p : ℕ}
    (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig) {E A₀ : Subgroup G} (hEM : E ≤ D.M)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hEcent : ∀ R : Subgroup G, R ≤ D.M → IsPGroup 3 ↥R → E ≤ R → E ≤ centralizer (R : Set G))
    (hA₀M : A₀ ≤ D.M) (hA₀E : A₀ ≤ centralizer (E : Set G))
    (hA₀r : 2 ≤ CFSG.Open.pRank p A₀) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hE.isPGroup.comap_subtype : IsPGroup 3 ↥(E.subgroupOf D.M)).exists_le_sylow
  have hER : E ≤ (Q : Subgroup ↥D.M).map D.M.subtype := by
    intro x hx
    have hxQ : (⟨x, hEM hx⟩ : ↥D.M) ∈ (Q : Subgroup ↥D.M) := hQ hx
    exact mem_map.mpr ⟨_, hxQ, rfl⟩
  exact PartOne.Section8.stronglyEmbedded_of_two_le_pRank_centralizer
    (R := (Q : Subgroup ↥D.M).map D.M.subtype) hSg hns h76 h614 hp Nat.prime_three
    (by norm_num) h3 ⟨Q, rfl⟩
    (le_inf hER (hEcent _ (map_subtype_le _) (Q.isPGroup'.map _) hER)) hE hEc
    (hA₀r.trans (CFSG.SectionRank.pRank_mono hpp.one_lt (le_inf hA₀M hA₀E)))

theorem s136a_stronglyEmbedded_three (hThin : ThinList13) {D : Data G} (hS : Setting13 D)
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) {p : ℕ}
    (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpK : p ∣ Nat.card (barImage D.M K)) {n m : ℕ} (hLs : IsL2 (Bar2 L) n)
    (hKs : IsL2 (Bar2 K) m) (hn : Even n) (hpn : p ∣ 2 ^ n - 1) (hSp : F13.Sp D.M p ≠ ⊥) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns := s13_normalSimple hThin D hS
  have hLc := s13_barImage_isComponent hL
  have hKc := s13_barImage_isComponent hK
  have hLK : barImage D.M L ≤ centralizer (barImage D.M K : Set (Bar2 D.M)) :=
    s13_components_commute hns hLc hKc hne
  obtain ⟨a, haL, y₁, hy₁L, hao, hy₁o, hay⟩ := s136a_exists_commute_three hL hLs hn hpp hp2 hpn
  obtain ⟨y₂, hy₂K, hy₂o⟩ := s136a_exists_orderOf_three hK hKs
  obtain ⟨s₀, hs₀, hs₀o⟩ := s13_exists_orderOf_of_pElementSubgroup_ne_bot hpp hSp
  have hs₀M : s₀ ∈ D.M := s13_Sp_le D.M p hs₀
  have hsS : uc22p21cPi D.M ⟨s₀, hs₀M⟩ ∈ barImage D.M (F13.Sp D.M p) :=
    uc22p21c_mem_barImage.2 ⟨⟨s₀, hs₀M⟩, hs₀, rfl⟩
  have hSL := s136a_barImage_Sp_le_centralizer hThin hS hp hL
    (hao ▸ Subgroup.orderOf_dvd_natCard _ haL)
  have hSK := s136a_barImage_Sp_le_centralizer hThin hS hp hK hpK
  obtain ⟨hYel, hYc⟩ := s136a_isElemAbelian_sup_zpowers hpp
    (fun x hx y hy => mem_centralizer_iff.mp (hSL hy) x hx)
    (le_bot_iff.mp ((inf_le_inf_left _ hSL).trans (s13_Layer13_inf_centralizer_eq_bot hns hLc).le))
    haL hsS hao (uc22s13g_orderOf_mk hs₀M hpp hp2 hs₀o)
  obtain ⟨A₀, hA₀M, hA₀p, hbar, hA₀r⟩ := s136a_exists_lift_pRank_two hpp hp2 hYel hYc
  have hA₀y : barImage D.M A₀ ≤ centralizer ({y₁, y₂} : Set (Bar2 D.M)) := by
    rw [hbar]
    refine sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr ?_))
      (zpowers_le.mpr (mem_centralizer_iff.mpr ?_)) <;> rintro h (rfl | rfl)
    · exact hay.symm
    · exact mem_centralizer_iff.mp (hLK haL) _ hy₂K
    · exact mem_centralizer_iff.mp (hSL hsS) _ hy₁L
    · exact mem_centralizer_iff.mp (hSK hsS) _ hy₂K
  obtain ⟨E, hEM, hE, hEc, hA₀E, hEcent⟩ := s136a_exists_elemAbelian_pair_of_mem hpp
    Nat.prime_three hp2 (by norm_num) (fun x hx y hy => (mem_centralizer_iff.mp (hLK hx) y hy).symm)
    (le_bot_iff.mp ((inf_le_inf_right _ hLK).trans
      (le_of_eq ((inf_comm ..).trans (s13_Layer13_inf_centralizer_eq_bot hns hKc)))))
    (s136a_pRank_barImage_le_one_of_isL2 hS.hyp131 Nat.prime_three (by norm_num) hL hLs)
    (s136a_pRank_barImage_le_one_of_isL2 hS.hyp131 Nat.prime_three (by norm_num) hK hKs)
    (s13_barImage_normal (hS.hyp131.normal L hL)) (s13_barImage_normal (hS.hyp131.normal K hK))
    hy₁L hy₂K hy₁o hy₂o hA₀M hA₀p hA₀y
  exact s136a_stronglyEmbedded_of_E9 hSg (UC6S846.not_solvable_of_mem_calC hL) h76 h614 hp h3
    hEM hE hEc hEcent hA₀M hA₀E hA₀r.ge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
