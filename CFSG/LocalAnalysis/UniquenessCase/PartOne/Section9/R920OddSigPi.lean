module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddConj
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VPair
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.Adapters.LieModelSimple
public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KThinL2Odd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.CGT.PushingUpLit.Transport
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_of_isL2Odd {X : Type} [Group X] {q : ℕ} (hq : q.Prime) (h : IsL2Odd X q) :
    Nat.card (MulAut X) = q * (q ^ 2 - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField q 1) q 1 one_pos
    (by simpa using GaloisField.card q 1 one_ne_zero) h
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.AGLEmbedding.card_mulAut_psl2GF q 1 le_rfl]
  simp

theorem two_mul_card_of_isL2Odd {X : Type} [Group X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : IsL2Odd X q) : 2 * Nat.card X = q * (q ^ 2 - 1) := by
  rw [show Nat.card X = ordA 1 q from by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)]
  exact UC6.N588.two_mul_ordA_one (hq.odd_of_ne_two hq2)

theorem Shape919.of_isL2Odd {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) (hq5 : 5 < q)
    (h : IsL2Odd X q) : Shape919 X where
  simple := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  three_dvd := three_dvd_card_of_isL2Odd (by omega) h
  thin := kThinL2Odd_holds X q hq5 h
  card_mulAut_dvd := dvd_of_eq (by
    rw [card_mulAut_of_isL2Odd hq h, two_mul_card_of_isL2Odd hq (by omega) h])
  not_alt_five := not_isAlt_five_of_isL2Odd hq5 h

theorem centralizesBar_of_not_dvd {L A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card (MulAut (Bar2 L))) (hA : IsPGroup p A)
    (hAN : A ≤ normalizer (L : Set G)) : ∀ a ∈ A, CentralizesBar a L := by
  classical
  let f : ↥A →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hAN)
  have hf : ∀ x : ↥A, f x = 1 := fun x => by
    obtain ⟨k, hk⟩ := hA x
    have h1 : orderOf (f x) ∣ p ^ k := (orderOf_map_dvd f x).trans (orderOf_dvd_of_pow_eq_one hk)
    have h2 : orderOf (f x) ∣ Nat.card (MulAut (Bar2 L)) := orderOf_dvd_natCard (f x)
    have hcop : Nat.Coprime (p ^ k) (Nat.card (MulAut (Bar2 L))) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  intro a ha
  refine ⟨hAN ha, fun l hl => (UC6S846.rhoL_fix_iff L ⟨a, hAN ha⟩ ⟨l, hl⟩).1 ?_⟩
  have h1 : UC6S846.rhoL L ⟨a, hAN ha⟩ = 1 := hf ⟨a, ha⟩
  rw [h1, MulAut.one_apply]

theorem pRank_barImage_le_one_of_shape919 {M X : Subgroup G} (hX : X ∈ calC M)
    (h : Shape919 (Bar2 X)) :
    CFSG.Open.pRank 3 (barImage M X) ≤ 1 ∧ 3 ∣ Nat.card (barImage M X) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
  refine ⟨?_, ?_⟩
  · rw [PartTwo.s13_pRank_barImage Nat.prime_three (by norm_num) hX.1.le,
      ← PartTwo.s13_pRank_bar_top Nat.prime_three (by norm_num) X]
    exact h.thin 3 Nat.prime_three (by norm_num)
  · rw [← Nat.card_congr e.toEquiv]
    exact h.three_dvd

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem dvd_card_bar2_of_mem_sig (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : F07.R76Sig D) (S : SliceCore D L D₃ Y H) (hnsp : ¬ IsStronglyPEmbedded 3 D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {p : ℕ} (hp : p ∈ D.sig) : p ∣ Nat.card (Bar2 L) := by
  classical
  by_contra hpd
  obtain ⟨hpp, hp2, hp3⟩ := S.sig_prime_ne_three hSg hnsp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := S.L_mem
  have hns := S.not_isSolvable_M
  have h3σ := S.three_not_mem_sig hSg hnsp
  have hpA : ∀ K ∈ conjSetOf D.M L, ¬ p ∣ Nat.card (MulAut (Bar2 K)) := by
    rintro K ⟨g, -, rfl⟩ h
    obtain ⟨e⟩ := uc22p20d_bar2_conj g L
    have hc : Nat.card (MulAut (Bar2 L)) =
        Nat.card (MulAut (Bar2 (L.map (MulAut.conj g).toMonoidHom))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    rw [← hc] at h
    rcases (Nat.Prime.dvd_mul hpp).1 (h.trans S.facts_L.card_mulAut_dvd) with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h)
    · exact hpd h
  obtain ⟨K, hK, hKL⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc2]; norm_num) L
  have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hcK : (conjSetOf D.M K).ncard = 2 := by rwa [uc22p2214_conjSetOf_eq hK]
  have hsK := S.facts_of_mem_conjSetOf hK
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  have hA₀p : IsPGroup p A₀ := hA₀el.isPGroup
  have hodd : ∀ a ∈ A₀, Odd (orderOf a) := fun a ha => by
    obtain ⟨k, hk⟩ := hA₀p ⟨a, ha⟩
    exact uc22ine229_odd_orderOf hpp hp2 (k := k) (by simpa using congrArg Subtype.val hk)
  have hA₀L := centralizesBar_of_not_dvd hpp (hpA L (PartOne.Section8.mem_conjSetOf_self D.M L))
    hA₀p fun a ha => uc22p2214_mem_normalizer_of_odd hc2 (hA₀M ha) (hodd a ha)
  have hA₀K := centralizesBar_of_not_dvd hpp (hpA K hK) hA₀p fun a ha =>
    uc22p2214_mem_normalizer_of_odd hcK (hA₀M ha) (hodd a ha)
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    haveI := S.facts_L.simple
    uc22p21k_center_eq_bot hL.2.2
  have hN : ∀ x : ↥D.M, Odd (orderOf x) → uc22p21cPi D.M x ∈
      normalizer (barImage D.M L : Set (Bar2 D.M)) ⊓
        normalizer (barImage D.M K : Set (Bar2 D.M)) := by
    intro x hx
    rw [← Subgroup.orderOf_coe] at hx
    exact ⟨uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hc2 x.2 hx),
      uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcK x.2 hx)⟩
  obtain ⟨E, hEM, hEel, hEcard, hA₀E, hEZ⟩ := uc22s217v_exists_elemAbelian_centralizer hpp
    Nat.prime_three hp2 (by norm_num) hp3 (uc22p22l_barImage_commute hL hKC hKL.symm)
    (uc22s217j_barImage_inf_eq_bot hL hKC hKL.symm hZ)
    (pRank_barImage_le_one_of_shape919 hL S.facts_L) (pRank_barImage_le_one_of_shape919 hKC hsK)
    hN hA₀M hA₀p fun a ha => ⟨uc22s217v_mem_centralizer_barImage hL _ (hA₀L a ha),
      uc22s217v_mem_centralizer_barImage hKC _ (hA₀K a ha)⟩
  have h2p : 3 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hpp (le_inf hA₀M hA₀E) hA₀el hA₀c
  have hΓ := h76 p hp hp2 (S.isStronglyPEmbedded_of_mem_sig hSg hp) 3 Nat.prime_three E hEM hEel
    hEcard (by omega) fun X hXE _ => by
      have := h2p.trans (CFSG.SectionRank.pRank_mono hpp.one_lt (inf_le_inf_left _
        ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hXE)).trans
          (Subgroup.centralizer_le_normalizer _))))
      omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  exact hnsp (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E
    (le_inf hER (hEZ R hR.le hR.isPGroup hER)) hEel hEcard hΓ)

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
