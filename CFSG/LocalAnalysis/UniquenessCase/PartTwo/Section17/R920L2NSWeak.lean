module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem isCyclic_sylow_three_of_isL2 {L : Subgroup G} {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (T : Sylow 3 ↥L) : IsCyclic ↥(T : Subgroup ↥L) := by
  have hrank : CFSG.pRank 3 ↥L ≤ 1 := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three L]
    exact le_of_eq (pRank_three_eq_one_of_isL2 hL2)
  refine UCK.K31.isCyclic_of_isPGroup_pRank_le_one Nat.prime_three
    (by norm_num) T.isPGroup' (le_trans ?_ hrank)
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three,
    CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top

private theorem map_conj_L_ne_of_isL2 {L : Subgroup G} {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    {E P : Subgroup G} (hEL : E ≤ L) (hE3 : Nat.card E = 3) (hP : IsPGroup 3 ↥P) (hEP : E ≤ P)
    {h : G} (hhP : E.map (MulAut.conj h).toMonoidHom ≤ P)
    (hne : E.map (MulAut.conj h).toMonoidHom ≠ E) :
    L.map (MulAut.conj h).toMonoidHom ≠ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hL
  apply hne
  have hE'L : E.map (MulAut.conj h).toMonoidHom ≤ L := hL ▸ Subgroup.map_mono hEL
  have hE'3 : Nat.card (E.map (MulAut.conj h).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hE3]
  have hPL : IsPGroup 3 ↥(P ⊓ L) := hP.to_inf_left
  have hC : IsPGroup 3 ↥((P ⊓ L).subgroupOf L) := hPL.comap_subtype
  obtain ⟨T, hT⟩ := hC.exists_le_sylow
  have hE₁ : E.subgroupOf L ≤ (T : Subgroup ↥L) := fun x hx =>
    hT (Subgroup.mem_subgroupOf.2 ⟨hEP hx, hEL hx⟩)
  have hE₂ : (E.map (MulAut.conj h).toMonoidHom).subgroupOf L ≤ (T : Subgroup ↥L) := fun x hx =>
    hT (Subgroup.mem_subgroupOf.2 ⟨hhP hx, hE'L hx⟩)
  haveI : IsCyclic ↥(T : Subgroup ↥L) := isCyclic_sylow_three_of_isL2 hL2 T
  have hcard : Nat.card ((E.map (MulAut.conj h).toMonoidHom).subgroupOf L) =
      Nat.card (E.subgroupOf L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'L).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE'3, hE3]
  have h2 : ((E.map (MulAut.conj h).toMonoidHom).subgroupOf L).subgroupOf T =
      (E.subgroupOf L).subgroupOf T := by
    refine (IsCyclic.subgroup_eq_iff_card_eq (H := _) (K := _)).2 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁).toEquiv]
    exact hcard
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hE₂, inf_of_le_left hE₁] at h2
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hE'L, inf_of_le_left hEL] at h2
  exact h2

private theorem false_of_kf7Use_of_isL2 {D : Data G} (hKF7 : KF7Use D)
    (hSg : UC6S846.SigmaStd D) {L H : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) (hn : 3 ≤ n) (hLH : L ≤ H) (hHt : H ≠ ⊤)
    (hHM : ¬ H ≤ D.M) {p : ℕ} (hp : p ∈ D.sig) (hpL : p ∣ Nat.card (Bar2 L))
    (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M)) : False := by
  classical
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hp
  have hKF := hKF7 p hp H ⟨hpp, hp2, hsp, hHt, hHM, by omega⟩
  have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_isL2_or_isSz (Or.inl hL2)
  have hnotalt : ¬ IsAlt (Bar2 L) 5 := by
    rintro ⟨e5⟩
    have hcard : Nat.card (Bar2 L) = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    rw [card_of_isL2 hL2] at hcard
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h64 : 64 ≤ 2 ^ (2 * n) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : 63 ≤ 2 ^ (2 * n) - 1 := by omega
    have hge : 504 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := by
      calc 504 = 8 * 63 := by norm_num
        _ ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h8 h63
    omega
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  obtain ⟨f, hf⟩ := exists_surjective_map_pPrimeCore_bar2 hpp hLH hsimple hpL
  have hle : ((L.subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_inf hLH hLM))
  rcases hKF with hsolv | ⟨-, hquot⟩
  · haveI : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    haveI : Group.IsSolvable ↥(((L.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact uc22p22a_qs_not_solvable hL.2.2 (solvable_of_surjective hf)
  · haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
    obtain ⟨P, hPperf, hPmap⟩ := exists_perfect_map_eq_top f hf
    let M' := ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))
    let e := P.equivMapOfInjective M'.subtype M'.subtype_injective
    refine hnotalt (hquot (P.map M'.subtype) ((Subgroup.map_subtype_le P).trans hle) ?_ _
      hsimple ((f.comp P.subtype).comp e.symm.toMonoidHom) ?_)
    · rw [← Subgroup.map_commutator, hPperf]
    · intro s
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hPmap ▸ Subgroup.mem_top s)
      exact ⟨e ⟨a, ha⟩, by simp⟩

theorem map_conj_eq_of_le_of_isL2 {D : Data G} (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L H : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hL2 : IsL2 (Bar2 L) n) (hn : 3 ≤ n) (hLH : L ≤ H) (hHt : H ≠ ⊤)
    (hHM : ¬ H ≤ D.M) (hσ : ∃ p ∈ D.sig, p ∣ Nat.card L) {E P : Subgroup G} (hEL : E ≤ L)
    (hE3 : Nat.card E = 3) (hEU : E ∈ uniqueSet D.M) (hP : IsPGroup 3 ↥P) (hPM : P ≤ D.M)
    (hEP : E ≤ P) {h : G} (hh : h ∈ H) (hhP : E.map (MulAut.conj h).toMonoidHom ≤ P) :
    E.map (MulAut.conj h).toMonoidHom = E := by
  classical
  by_contra hne
  have hhM : h ∈ D.M := mem_of_map_conj_le_of_mem_uniqueSet D.maxLocal hEU (hhP.trans hPM)
  have hLne : L.map (MulAut.conj h).toMonoidHom ≠ L :=
    map_conj_L_ne_of_isL2 hL2 hEL hE3 hP hEP hhP hne
  have hmem : L.map (MulAut.conj h).toMonoidHom ∈ conjSetOf D.M L := ⟨h, hhM, rfl⟩
  have hL'C := uc22p2214_calC_of_mem_conjSetOf hL hmem
  have hc2 : (conjSetOf D.M L).ncard = 2 := by
    have hle := R8107Odd.ncard_conjSetOf_le_two h82 hnsp hL (pRank_three_eq_one_of_isL2 hL2)
    have hlt : 1 < (conjSetOf D.M L).ncard := (Set.one_lt_ncard_iff (Set.toFinite _)).2
      ⟨_, L, hmem, PartOne.Section8.mem_conjSetOf_self D.M L, hLne⟩
    omega
  obtain ⟨p, hp, hpd⟩ := hσ
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hpbar : p ∣ Nat.card (Bar2 L) := by
    have hcard : Nat.card L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
    rw [hcard] at hpd
    have h2 : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.pCore 2 ↥L))).mp
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk]
      intro hpk
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hpk))
    exact (hpp.dvd_mul.mp hpd).resolve_right h2
  obtain ⟨x, hxL, hx⟩ := exists_orderOf_eq_of_dvd_card_bar2 hpp hpbar
  have hxH : x ∈ H := hLH hxL
  have hxM : x ∈ D.M := CFSG.Open.IsSubnormal.le hL.1 hxL
  have hy : orderOf (h * x * h⁻¹) = p := by
    rw [← hx]
    exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
  have hc : Subgroup.center (Bar2 L) = ⊥ := by
    haveI : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_isL2_or_isSz (Or.inl hL2)
    exact uc22p21k_center_eq_bot hL.2.2
  have hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) :=
    two_le_pRank_of_pair hpp hp2 hL hL'C hLne.symm hc
      inf_le_right hxL (Subgroup.mem_map.2 ⟨x, hxL, rfl⟩)
      (mem_inf.2 ⟨hxH, hxM⟩)
      (mem_inf.2 ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh),
        D.M.mul_mem (D.M.mul_mem hhM hxM) (D.M.inv_mem hhM)⟩) hx hy
  exact false_of_kf7Use_of_isL2 hKF7 hSg hL hL2 hn hLH hHt hHM hp hpbar hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
