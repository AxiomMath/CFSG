module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen4Q
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen4a
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.RankThree.PartTwo.Sec11 (CyclicSylowThreeOutAbelian)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem s13_Thirteen4_pow_barImage (D : Data G) {Y : Subgroup G} {r : ℕ} (hYM : Y ≤ D.M)
    (hY : Nat.card Y = r) {y : Bar2 D.M} (hy : y ∈ barImage D.M Y) : y ^ r = 1 := by
  change y ∈ (Y.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have horder : orderOf x ∣ r := by
    have h1 : orderOf x ∣ Nat.card (Y.subgroupOf D.M) := Subgroup.orderOf_dvd_natCard _ hx
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv, hY] at h1
  rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp horder, map_one]

theorem s13_engine_case_rank (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D)
    (hrk3 : SigmaRankThree13 D) {p r : ℕ} (hp : p ∈ D.sig) (hr : r.Prime) (h7 : 7 ≤ r)
    (hrank : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank r D.M) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hY : Nat.card Y = r) {g : G} (hg : g ∉ D.M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ D.M.map (MulAut.conj g).toMonoidHom) : False := by
  have hr2 : r ≠ 2 := by omega
  have h3p : 3 ≤ CFSG.Open.pRank p D.M := hSig.three_le p hp
  have h3r : 3 ≤ CFSG.Open.pRank r D.M := le_trans h3p hrank
  have hrsig : r ∈ D.sig := by
    by_cases h4 : 4 ≤ CFSG.Open.pRank r D.M
    · exact hSig.four_mem r hr hr2 h4
    · have hlt : CFSG.Open.pRank r D.M < 4 := Nat.lt_of_not_le h4
      have h3 : CFSG.Open.pRank r D.M = 3 := by omega
      exact hrk3 ⟨p, hp, by omega⟩ r hr h7 (by omega)
  have hse : IsStronglyPEmbedded r D.M := hSig.sig1_sp r (hS.sig_eq ▸ hrsig)
  exact s13_not_dvd_card_cent hse hg hN (s13_dvd_card_cent_self hr hYM hY)

theorem s13_engine_case_centralizer (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D)
    {p r : ℕ} (hp : p ∈ D.sig) (hr : r.Prime) (hr2 : r ≠ 2) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hY : Nat.card Y = r) {g : G} (hg : g ∉ D.M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ D.M.map (MulAut.conj g).toMonoidHom)
    (hYE : barImage D.M Y ≤ pElementSubgroup p (CFSG.layer (Bar2 D.M)))
    (hS0 : pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) ≠ ⊥) : False := by
  obtain ⟨hp1, hp2⟩ := D.sig_prime p hp
  obtain ⟨s, hsS, hs⟩ := s13_exists_orderOf_of_pElementSubgroup_ne_bot hp1 hS0
  have hSE : pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) ≤
      Subgroup.centralizer (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hsC : s ∈ Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) := hSE hsS
  have hcent : barImage D.M Y ≤ Subgroup.centralizer ({s} : Set (Bar2 D.M)) := by
    refine le_trans hYE ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (Subgroup.mem_centralizer_iff.mp hsC e he).symm
  have hYp : IsPGroup r Y := IsPGroup.of_card (n := 1) (by simpa using hY)
  have hse : IsStronglyPEmbedded p D.M := hSig.sig1_sp p (hS.sig_eq ▸ hp)
  exact s13_not_dvd_card_cent hse hg hN (s13_cop hp1 hp2 hr hr2 hYM hYp hs hcent)

theorem s13_engine (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D) (hThin : ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (hrk3 : SigmaRankThree13 D) {r : ℕ} (hr : r.Prime)
    (h7 : 7 ≤ r) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY : Nat.card Y = r) {g : G} (hg : g ∉ D.M)
    (hN : Subgroup.normalizer (Y : Set G) ≤ D.M.map (MulAut.conj g).toMonoidHom)
    (hall : ∀ K ∈ calC D.M, Y ≤ K ⊔ cMStar D.M K)
    (hnu : ∀ K ∈ calC D.M, ¬ ∃ m : ℕ, IsU3 (Bar2 K) m) : False := by
  obtain ⟨p, hp⟩ := hSig.nonempty
  obtain ⟨hp1, hp2⟩ := D.sig_prime p hp
  have hr2 : r ≠ 2 := by omega
  have hse : IsStronglyPEmbedded p D.M := hSig.sig1_sp p (hS.sig_eq ▸ hp)
  have hns : s13_NormalSimple (Bar2 D.M) := s13_normalSimple hThin D hS
  have hcomp := s13_hcomp D hS hp1 hp2 hse hr hr2 hYM hY hg hN hall hnu
  have hsum := s13_pRank_bar_eq_add hThin hCyc D hS hSig hp
  have hsmall := s13_pRank_Sp_bar_le_one D hS hp
  rcases s13_rank_dichotomy hns hp1 hr hcomp hsum hsmall with h | ⟨hS0, hrk⟩
  · rw [s13_pRank_bar_top hp1 hp2 D.M, s13_pRank_bar_top hr hr2 D.M] at h
    exact s13_engine_case_rank D hS hSig hrk3 hp hr h7 h hYM hY hg hN
  · have hYE : barImage D.M Y ≤ pElementSubgroup p (CFSG.layer (Bar2 D.M)) := by
      intro y hy
      have hyr : y ^ r = 1 := s13_Thirteen4_pow_barImage D hYM hY hy
      have hinner : ∀ J : Subgroup (Bar2 D.M), CFSG.IsComponent J →
          y ∈ J ⊔ Subgroup.centralizer (J : Set (Bar2 D.M)) := by
        intro J hJ
        obtain ⟨K, hK, rfl⟩ := s13_exists_calC_of_component D.M hJ
        exact s13_barImage_le_sup_centralizer (s13_le_of_mem_calC hK) (hall K hK) hy
      exact s13_mem_Ep_of_inner hns hp1 hr hrk ⟨1, by rw [pow_one]; exact hyr⟩ hinner
    exact s13_engine_case_centralizer D hS hSig hp hr hr2 hYM hY hg hN hYE hS0

theorem s13_inner_all (D : Data G) (hS : Setting13 D) (h133 : R133 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hLn : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s : ℕ} (hs : Odd s)
    (hsn : s ∣ n) {r : ℕ} (hr : r.Prime) (hrd : r ∣ 2 ^ s - 1) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : Nat.card X = r) {g : G} (hg : g ∉ D.M)
    (hY : X.map (MulAut.conj g).toMonoidHom ≤ D.M)
    (hno : Even n → ∀ K ∈ calC D.M, ¬ (IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r)) :
    (∀ K ∈ calC D.M, X.map (MulAut.conj g).toMonoidHom ≤ K ⊔ cMStar D.M K) ∧
      ∀ K ∈ calC D.M, ¬ ∃ m : ℕ, IsU3 (Bar2 K) m := by
  have h := fun K hK =>
    h133 hS.sig_eq hS.hyp131 L hL K hK n hLn s hs hsn r hr hrd X hXL hXc g hg hY
  refine ⟨?_, ?_⟩
  · intro K hK
    rcases (h K hK).1 with h1 | ⟨h2, hev⟩
    · exact h1
    · exact absurd h2 (hno hev K hK)
  · intro K hK
    exact (h K hK).2

theorem s13_step (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D)
    (hThin : ThinList13) (hCyc : CyclicSylowThreeOutAbelian) (hrk3 : SigmaRankThree13 D)
    (h133 : R133 D) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hLn : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s : ℕ} (hs : Odd s) (hs1 : 1 < s) (hsn : s ∣ n)
    (hno : Even n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
      ∀ K ∈ calC D.M, ¬ (IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r)) : False := by
  obtain ⟨r, hr, hrd⟩ := s13_exists_prime_dvd hs1
  have h7 : 7 ≤ r := s13_seven_le_of_dvd hs hr hrd
  have hrX : r ∣ Nat.card (Bar2 L) := s13_dvd_card_of_isL2_or_isSz hLn hsn hr hrd
  obtain ⟨X, hXL, hXc⟩ := s13_exists_subgroup_of_dvd_card_bar hr hrX
  have huniq := hS.hyp131.uniq L hL n hLn s hs hsn r hr hrd X hXL hXc
  have hXM : X ≤ D.M := hXL.trans (s13_le_of_mem_calC hL)
  obtain ⟨g, hg, hY⟩ := s13_exists_conj_into_M D hXM huniq.2
  obtain ⟨hall, hnu⟩ := s13_inner_all D hS h133 hL hLn hs hsn hr hrd hXL hXc hg hY
    (fun hev K hK => hno hev r hr hrd K hK)
  have hYc : Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = r :=
    (s13_card_map_conj X g).trans hXc
  have hN := s13_normalizer_map_conj_le g huniq.1
  exact s13_engine D hS hSig hThin hCyc hrk3 hr h7 hY hYc hg hN hall hnu

theorem s13_claim_odd (D : Data G) (hS : Setting13 D)
    (hSig : SigmaStd D) (hThin : ThinList13) (hCyc : CyclicSylowThreeOutAbelian)
    (hrk3 : SigmaRankThree13 D) (h133 : R133 D) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hLn : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hodd : Odd n) (hpow : ¬ IsPowTwo n) : False := by
  obtain ⟨hs, hs1, hsn⟩ := s13_odd_divisor_self hodd hpow
  exact s13_step D hS hSig hThin hCyc hrk3 h133 hL hLn hs hs1 hsn
    (fun hev => absurd hev (Nat.not_even_iff_odd.2 hodd))

theorem s13_claim_all (D : Data G) (hS : Setting13 D)
    (hSig : SigmaStd D) (hThin : ThinList13) (hCyc : CyclicSylowThreeOutAbelian)
    (hrk3 : SigmaRankThree13 D) (h133 : R133 D)
    (hnoOdd : ∀ K ∈ calC D.M, ∀ m : ℕ, (IsL2 (Bar2 K) m ∨ IsSz (Bar2 K) m) → Odd m → IsPowTwo m)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hLn : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hpow : ¬ IsPowTwo n) : False := by
  obtain ⟨s, hs, hs1, hsn⟩ := s13_exists_odd_divisor hpow
  refine s13_step D hS hSig hThin hCyc hrk3 h133 hL hLn hs hs1 hsn ?_
  intro _ r hr hrd K hK hshape
  have h7 : 7 ≤ r := s13_seven_le_of_dvd hs hr hrd
  have hr2 : r ≠ 2 := by omega
  exact s13_not_isPowTwo_of_prime hr hr2 (hnoOdd K hK r hshape (hr.odd_of_ne_two hr2))

theorem isPowTwo_of_mem_calC (D : Data G) (hS : Setting13 D)
    (hSig : SigmaStd D) (hThin : ThinList13) (hCyc : CyclicSylowThreeOutAbelian)
    (hrk3 : SigmaRankThree13 D) (h133 : R133 D) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hLn : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : IsPowTwo n := by
  by_contra hpow
  by_cases hex : ∃ K ∈ calC D.M, ∃ m : ℕ,
    (IsL2 (Bar2 K) m ∨ IsSz (Bar2 K) m) ∧ Odd m ∧ ¬ IsPowTwo m
  · obtain ⟨K, hK, m, hm, hodd, hpmm⟩ := hex
    exact s13_claim_odd D hS hSig hThin hCyc hrk3 h133 hK hm hodd hpmm
  · push_neg at hex
    refine s13_claim_all D hS hSig hThin hCyc hrk3 h133 ?_ hL hLn hpow
    intro K hK m hm hodd
    exact hex K hK m hm hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
