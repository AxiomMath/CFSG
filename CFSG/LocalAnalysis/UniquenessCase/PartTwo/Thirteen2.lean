module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.RankThree.PartOne (pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem s13_Thirteen2_pow_bar {M : Subgroup G} {p k : ℕ} {x : G} (hxM : x ∈ M)
    (hx : x ^ p ^ k = 1) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨x, hxM⟩ : Bar2 M) ^ p ^ k = 1 := by
  have h1 : (⟨x, hxM⟩ : ↥M) ^ p ^ k = 1 := by
    apply Subtype.ext
    simpa using hx
  rw [← map_pow, h1, map_one]

theorem s13_Thirteen2_orderOf_bar {M : Subgroup G} {p k : ℕ} {x : G} (hxM : x ∈ M)
    (hx : x ^ p ^ k = 1) :
    orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ⟨x, hxM⟩ : Bar2 M) ∣ p ^ k :=
  orderOf_dvd_of_pow_eq_one (s13_Thirteen2_pow_bar hxM hx)

theorem s13_Thirteen2_pElementSubgroup_le (p : ℕ) (X : Subgroup G) :
    pElementSubgroup p X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

theorem s13_Thirteen2_pElementSubgroup_mono {p : ℕ} {X Y : Subgroup G} (h : X ≤ Y) :
    pElementSubgroup p X ≤ pElementSubgroup p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem s13_opRes_eq_self (D : Data G) (hS : Setting13 D)
    (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ} (hp : p ∈ D.sig) :
    UC22.F10.OpRes p D.M = D.M :=
  UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab
    (D.sig_prime p hp).1 (hSig.sig1_sp p (hS.sig_eq ▸ hp))

theorem s13_pElement_inner (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ}
    (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M) {x : G} (hxM : x ∈ D.M)
    (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈
      barImage D.M L ⊔ Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
  obtain ⟨k, hk⟩ := hx
  have htop : CFSG.GH74.GLS.oResidual p (Bar2 D.M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top (D.sig_prime p hp).1 (s13_opRes_eq_self D hS hSig hp)
  have hcomm : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈
      commutator (Bar2 D.M) :=
    uc22p21c_mem_commutator_of_oResidual_eq_top htop (s13_Thirteen2_orderOf_bar hxM hk)
  haveI : (barImage D.M L).Normal := s13_barImage_normal (hS.hyp131.normal L hL)
  exact s13_commutator_le_sup_centralizer (barImage D.M L)
    (s13_outAbelian_barImage hThin hCyc D hS hL) hcomm

theorem s13_pElement_mem_layer_mul (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ}
    (hp : p ∈ D.sig) {x : G} (hxM : x ∈ D.M) (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    ∃ e ∈ CFSG.layer (Bar2 D.M),
      ∃ c ∈ Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)),
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) = e * c := by
  refine s13_exists_mul_of_inner (s13_normalSimple hThin D hS)
    (x := (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M)) ?_
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
  exact s13_pElement_inner hThin hCyc D hS hSig hp hL hxM hx

theorem s13_pElement_mem_Lp_sup_Sp (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ}
    (hp : p ∈ D.sig) {x : G} (hxM : x ∈ D.M) (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    x ∈ Lp D.M p ⊔ Sp D.M p := by
  have hp' := D.sig_prime p hp
  obtain ⟨k, hk⟩ := hx
  obtain ⟨e, he, c, hc, hec⟩ :=
    s13_pElement_mem_layer_mul hThin hCyc D hS hSig hp hxM ⟨k, hk⟩
  obtain ⟨a', ha', b', hb', hab⟩ :=
    s13_exists_pPart_mul hp'.1
      (A := CFSG.layer (Bar2 D.M))
      (B := Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)))
      (hAB := le_rfl)
      (hx := ⟨k, s13_Thirteen2_pow_bar hxM hk⟩) he hc hec
  have ha'E : a' ∈ barImage D.M (Lp D.M p) := by
    rw [s13_barImage_Lp D.M hp'.1]
    exact ha'
  have hb'S : b' ∈ barImage D.M (Sp D.M p) := by
    rw [s13_barImage_Sp D.M hp'.1]
    exact s13_Thirteen2_pElementSubgroup_mono
      (Subgroup.centralizer_le
        (s13_Thirteen2_pElementSubgroup_le p (CFSG.layer (Bar2 D.M)))) hb'
  have hbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈
      barImage D.M (Lp D.M p ⊔ Sp D.M p) := by
    rw [s13_barImage_sup (s13_Lp_le D.M p) (s13_Sp_le D.M p), hab]
    exact Subgroup.mul_mem_sup ha'E hb'S
  haveI hLpn : ((Lp D.M p).subgroupOf D.M).Normal := s13_Lp_normal D.M p
  haveI hSpn : ((Sp D.M p).subgroupOf D.M).Normal := s13_Sp_normal D.M p
  have hnormal : ((Lp D.M p ⊔ Sp D.M p).subgroupOf D.M).Normal := by
    rw [Subgroup.subgroupOf_sup (s13_Lp_le D.M p) (s13_Sp_le D.M p)]
    infer_instance
  exact s13_mem_of_barImage_of_pPart (sup_le (s13_Lp_le D.M p) (s13_Sp_le D.M p)) hnormal
    hp'.1 hp'.2 hxM ⟨k, hk⟩ hbar

theorem s13_Lp_sup_Sp_le_opp (M : Subgroup G) (p : ℕ) : Lp M p ⊔ Sp M p ≤ Opp p M := by
  apply sup_le
  · show pElementSubgroup p (barPreimage M (CFSG.layer (Bar2 M))) ≤ pElementSubgroup p M
    exact s13_Thirteen2_pElementSubgroup_mono (s13_barPreimage_le M _)
  · show pElementSubgroup p (barPreimage M (Subgroup.centralizer
        (barImage M (Lp M p) : Set (Bar2 M)))) ≤ pElementSubgroup p M
    exact s13_Thirteen2_pElementSubgroup_mono (s13_barPreimage_le M _)

theorem opp_eq_Lp_sup_Sp (D : Data G) (hS : Setting13 D)
    (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {p : ℕ} (hp : p ∈ D.sig) :
    Opp p D.M = Lp D.M p ⊔ Sp D.M p := by
  apply le_antisymm
  · change Subgroup.closure {x : G | x ∈ D.M ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤
      Lp D.M p ⊔ Sp D.M p
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxM, k, hk⟩
    exact s13_pElement_mem_Lp_sup_Sp hThin hCyc D hS hSig hp hxM
      ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  · exact s13_Lp_sup_Sp_le_opp D.M p

theorem s13_pRank_bar_eq_add (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ}
    (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) =
      CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer (Bar2 D.M))) +
        CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
          (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) := by
  have hp' := D.sig_prime p hp
  have hns := s13_normalSimple hThin D hS
  have hle : Lp D.M p ⊔ Sp D.M p ≤ D.M := sup_le (s13_Lp_le D.M p) (s13_Sp_le D.M p)
  have hbar : barImage D.M (Lp D.M p ⊔ Sp D.M p) =
      pElementSubgroup p (CFSG.layer (Bar2 D.M)) ⊔
        pElementSubgroup p (Subgroup.centralizer
          (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) := by
    rw [s13_barImage_sup (s13_Lp_le D.M p) (s13_Sp_le D.M p),
      s13_barImage_Lp D.M hp'.1, s13_barImage_Sp D.M hp'.1]
  have hAB : pElementSubgroup p (Subgroup.centralizer
        (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) ≤
      Subgroup.centralizer
        (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) :=
    s13_Thirteen2_pElementSubgroup_le p _
  have hdisj : pElementSubgroup p (CFSG.layer (Bar2 D.M)) ⊓
        pElementSubgroup p (Subgroup.centralizer
          (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← s13_inf_centralizer_eq_bot hns hp'.1]
    exact ⟨hx.1, hAB hx.2⟩
  calc
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M))
        = CFSG.Open.pRank p D.M := s13_pRank_bar_top hp'.1 hp'.2 D.M
    _ = CFSG.Open.pRank p (Opp p D.M) := (s13_pRank_pElementSubgroup hp'.1 D.M).symm
    _ = CFSG.Open.pRank p (Lp D.M p ⊔ Sp D.M p) := by
          rw [opp_eq_Lp_sup_Sp D hS hSig hThin hCyc hp]
    _ = CFSG.Open.pRank p (barImage D.M (Lp D.M p ⊔ Sp D.M p)) :=
          (s13_pRank_barImage hp'.1 hp'.2 hle).symm
    _ = CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer (Bar2 D.M)) ⊔
          pElementSubgroup p (Subgroup.centralizer
            (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) := by
          rw [hbar]
    _ = CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer (Bar2 D.M))) +
          CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
            (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) :=
          s13_pRank_sup_eq_add hp'.1 hAB hdisj

theorem s13_pRank_Sp_bar_le_one (D : Data G) (hS : Setting13 D) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) ≤ 1 := by
  rw [← s13_barImage_Sp D.M (D.sig_prime p hp).1]
  rw [s13_pRank_barImage (D.sig_prime p hp).1 (D.sig_prime p hp).2 (s13_Sp_le D.M p)]
  exact hS.hyp131.smallS p hp

theorem s13_two_le_pRank_layer (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) (hSig : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {p : ℕ}
    (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer (Bar2 D.M))) := by
  have hp' := D.sig_prime p hp
  have htop : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) = CFSG.Open.pRank p D.M :=
    s13_pRank_bar_top hp'.1 hp'.2 D.M
  have hsum := s13_pRank_bar_eq_add hThin hCyc D hS hSig hp
  have hsumD : CFSG.Open.pRank p D.M =
      CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer (Bar2 D.M))) +
        CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
          (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) :=
    htop ▸ hsum
  have hSp := s13_pRank_Sp_bar_le_one D hS hp
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSig.three_le p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
