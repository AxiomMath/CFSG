module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ThirteenTwoInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2121a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xd_normalSimple (hThin : PartTwo.ThinList13) {D : Data G}
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) :
    PartTwo.s13_NormalSimple (Bar2 D.M) := by
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := PartTwo.s13_exists_calC_of_component D.M hJ
  refine ⟨PartTwo.s13_barImage_normal (hN L hL), ?_⟩
  haveI : IsSimpleGroup (Bar2 L) := by
    rcases hTU L hL with hthin | ⟨n, -, hU⟩
    · exact (PartTwo.s13_list_bar hThin D hL hthin).1
    · exact PartTwo.s13_isSimple_of_isU3 hU
  obtain ⟨e⟩ := PartTwo.s13_bar_equiv hL
  exact MulEquiv.isSimpleGroup e.symm

theorem uc22s13xd_outAbelian (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∀ σ τ : MulAut ↥(barImage D.M L), ∃ y : ↥(barImage D.M L),
      σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  rcases hTU L hL with hthin | ⟨n, ⟨k, hk⟩, hU⟩
  · exact uc22p22u_outAbelian_thin hThin hCyc D hL hthin
  · have htwo : 2 ≤ n := PartTwo.s13_two_le_of_isU3 hU
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    have heven : Even n := by
      rw [hk]
      exact (Nat.even_pow' hk0).2 even_two
    obtain ⟨e⟩ := PartTwo.s13_bar_equiv hL
    exact PartTwo.s13_outAbelian_of_mulEquiv e
      (PartTwo.s13_outAbelian_of_isU3_even hL.2.2 hU heven)

theorem uc22s13xd_pElement_inner (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1) {p : ℕ}
    (hp : p ∈ D.sig) {x : G} (hxM : x ∈ D.M) (hx : ∃ k : ℕ, x ^ p ^ k = 1)
    (J : Subgroup (Bar2 D.M)) (hJ : CFSG.IsComponent J) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈
      J ⊔ Subgroup.centralizer (J : Set (Bar2 D.M)) := by
  obtain ⟨L, hL, rfl⟩ := PartTwo.s13_exists_calC_of_component D.M hJ
  obtain ⟨k, hk⟩ := hx
  have hp' := D.sig_prime p hp
  have htop : CFSG.GH74.GLS.oResidual p (Bar2 D.M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top hp'.1
      (UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp'.1
        (hSig.sig1_sp p (hsig ▸ hp)))
  have hcomm := uc22p21c_mem_commutator_of_oResidual_eq_top htop
    (PartTwo.s13_Thirteen2_orderOf_bar hxM hk)
  haveI : (barImage D.M L).Normal := PartTwo.s13_barImage_normal (hN L hL)
  exact PartTwo.s13_commutator_le_sup_centralizer (barImage D.M L)
    (uc22s13xd_outAbelian hThin hCyc hTU hL) hcomm

theorem uc22s13xd_mem_centE (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1) {p : ℕ}
    (hp : p ∈ D.sig) {x : G} (hx : x ∈ F13.cMStar D.M (F13.Lp D.M p))
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x ∈ barPreimage D.M (centE D.M) := by
  have hp' := D.sig_prime p hp
  have hns := uc22s13xd_normalSimple hThin hTU hN
  have hx' : x ∈ barPreimage D.M
      (Subgroup.centralizer (barImage D.M (F13.Lp D.M p) : Set (Bar2 D.M))) := hx
  obtain ⟨hxM, hxC⟩ := uc22p21c_mem_barPreimage.1 hx'
  have hxE : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈
      Subgroup.centralizer (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) := by
    rw [← PartTwo.s13_barImage_Lp D.M hp'.1]
    exact hxC
  obtain ⟨k, hk⟩ := hxp
  obtain ⟨e, he, c, hc, hec⟩ := PartTwo.s13_exists_mul_of_inner hns
    (uc22s13xd_pElement_inner hThin hCyc hSig hTU hN hsig hp hxM ⟨k, hk⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := PartTwo.s13_exists_pPart_mul hp'.1
    (A := CFSG.layer (Bar2 D.M))
    (B := Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M))) (hAB := le_rfl)
    (hx := ⟨k, PartTwo.s13_Thirteen2_pow_bar hxM hk⟩) he hc hec
  have hbE : b ∈ centE D.M := PartTwo.s13_Thirteen2_pElementSubgroup_le p _ hb
  have hbE' : b ∈ Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) :=
    Subgroup.centralizer_le (PartTwo.s13_Thirteen2_pElementSubgroup_le p _) hbE
  have haC : a ∈ Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) := by
    have h1 : a = (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) * b⁻¹ := by
      rw [hab]
      group
    rw [h1]
    exact Subgroup.mul_mem _ hxE (Subgroup.inv_mem _ hbE')
  have ha1 : a = 1 := by
    have hmem : a ∈ pElementSubgroup p (CFSG.layer (Bar2 D.M)) ⊓
        Subgroup.centralizer (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) :=
      Subgroup.mem_inf.2 ⟨ha, haC⟩
    rw [PartTwo.s13_inf_centralizer_eq_bot hns hp'.1] at hmem
    exact (Subgroup.mem_bot).1 hmem
  refine uc22p21c_mem_barPreimage.2 ⟨hxM, ?_⟩
  show (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈ centE D.M
  rw [hab, ha1, one_mul]
  exact hbE

theorem uc22s13xd_Sp_le_centE (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1) {p : ℕ}
    (hp : p ∈ D.sig) : F13.Sp D.M p ≤ barPreimage D.M (centE D.M) := by
  show Subgroup.closure {x : G | x ∈ F13.cMStar D.M (F13.Lp D.M p) ∧ ∃ k : ℕ, orderOf x = p ^ k} ≤
    barPreimage D.M (centE D.M)
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hx, k, hk⟩
  exact uc22s13xd_mem_centE hThin hCyc hSig hTU hN hsig hp hx
    ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩

theorem uc22s13xd_centE_le_cMStar (M : Subgroup G) (p : ℕ) :
    barPreimage M (centE M) ≤ F13.cMStar M (F13.Lp M p) := by
  show ((centE M).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤
    ((Subgroup.centralizer (barImage M (F13.Lp M p) : Set (Bar2 M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype
  exact Subgroup.map_mono (Subgroup.comap_mono
    (Subgroup.centralizer_le (PartTwo.s13_barImage_Lp_le_layer M p)))

theorem uc22s13xd_smallS (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c) :
    ∀ p ∈ D.sig, CFSG.Open.pRank p (F13.Sp D.M p) ≤ 1 := fun p hp =>
  (CFSG.SectionRank.pRank_mono (D.sig_prime p hp).1.one_lt
    (uc22s13xd_Sp_le_centE hThin hCyc hSig hTU hN hsig hp)).trans
    (uc22p2121_pRank_centE_le_one h61 c hH hp)

theorem uc22s13xd_sylow (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1) (c : Ctx21 D Ch)
    (hH : Hyp2120 D c) :
    ∀ p ∈ D.sig, ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (F13.Sp D.M p) ∧
        P ≤ Subgroup.normalizer (c.B : Set G) := by
  intro p hp
  have hp' := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hp'.1⟩
  obtain ⟨P, hPsyl, hPB⟩ := hH.2.2.1 p hp
  refine ⟨P, hPsyl.of_le ?_ (uc22s13xd_Sp_le_centE hThin hCyc hSig hTU hN hsig hp), hPB⟩
  intro x hxP
  obtain ⟨k, hk⟩ := hPsyl.isPGroup ⟨x, hxP⟩
  have hk' : x ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp'.1).1 (orderOf_dvd_of_pow_eq_one hk')
  show x ∈ Subgroup.closure
    {x : G | x ∈ F13.cMStar D.M (F13.Lp D.M p) ∧ ∃ k : ℕ, orderOf x = p ^ k}
  exact Subgroup.subset_closure ⟨uc22s13xd_centE_le_cMStar D.M p (hPsyl.le hxP), m, hm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
