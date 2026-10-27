module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206w
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08J4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

variable {G : Type} [Group G]

theorem uc22s206y_pRank_aut
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (h : IsAlt X 8 ∨ LieModel X .PSL 5 2 1 ∨ IsSpor X .M24 ∨ IsSpor X .J4) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h11 : IsSpor X .J4 → p ≠ 11) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have key : ¬ p ∣ Nat.card (Outer X) → ¬ p ^ 2 ∣ Nat.card X →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := fun hOut h2 =>
    (CFSG.AGLEmbedding.pRank_top_mulAut_le_of_not_dvd hp hZ hOut).trans
      (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (k := 1) hp (by rwa [Subgroup.card_top]))
  have out : ∀ {Y : Type} [Group Y], Nonempty (X ≃* Y) →
      CFSG.AGLEmbedding.SporadicSmallData Y → ¬ p ∣ Nat.card (Outer X) := by
    rintro Y _ ⟨e⟩ ⟨hOut, -⟩ hd
    have h1 : Nat.card (Outer X) = Nat.card (Outer Y) := Nat.card_congr (equivalence e).toEquiv
    have := Nat.le_of_dvd Nat.card_pos hd
    omega
  rcases h with h | h | h | h
  · obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin 8)) := h
    exact (CFSG.AGLEmbedding.pRank_top_mulAut_le (by norm_num) (by norm_num) e hp).trans
      (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)))
  · have hst := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
    refine key (CFSG.AGLEmbedding.not_dvd_card_outer_of_psl_two_of_five_le hst hp hp5) ?_
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hst,
      show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 5 (2 ^ 1) = 9999360 by decide +kernel]
    intro hd
    have hmem : p ∈ Nat.primeFactors 9999360 :=
      Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans hd, by norm_num⟩
    rw [show Nat.primeFactors 9999360 = {2, 3, 5, 7, 31} by norm_num [Nat.primeFactors]] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> first | omega | norm_num at hd
  · obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
    refine key (out ⟨e⟩ CFSG.AGLEmbedding.sporadicSmallData_M24) ?_
    rw [Nat.card_congr e.toEquiv, show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) =
      244823040 from CFSG.Sporadic.Mathieu.card_M24]
    intro hd
    have hmem : p ∈ Nat.primeFactors 244823040 :=
      Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans hd, by norm_num⟩
    rw [show Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} by
      norm_num [Nat.primeFactors]] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | norm_num at hd
  · have hp11 := h11 h
    obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := h
    refine key (out ⟨e⟩ CFSG.AGLEmbedding.sporadicSmallData_J4) ?_
    rw [Nat.card_congr e.toEquiv, show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) =
      86775571046077562880 from CFSG.Sporadic.J4.card_J4]
    intro hd
    have hmem : p ∈ Nat.primeFactors 86775571046077562880 :=
      Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans hd, by norm_num⟩
    rw [show Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} by
      norm_num [Nat.primeFactors]] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | norm_num at hd

theorem uc22s206y_kernel {Y B : Type*} [Group Y] [Finite Y] [Group B] [Finite B] (π : Y →* B)
    {C : Subgroup B} (hCn : C.Normal) {p a : ℕ} (hp : p.Prime)
    (hC : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥C)) ≤ a) {R : Subgroup Y}
    (hR : IsElemAbelian p R) {m : ℕ} (hm : a + 2 ≤ m) (hRc : Nat.card R = p ^ m) :
    ∃ F ≤ R, (∃ j, 2 ≤ j ∧ Nat.card F = p ^ j) ∧ F.map π ≤ centralizer (C : Set B) := by
  haveI := hCn
  haveI : Fact p.Prime := ⟨hp⟩
  let θ : Y →* MulAut ↥C := MulAut.conjNormal.comp π
  refine ⟨θ.ker ⊓ R, inf_le_right, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hR.map θ).isPGroup
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hR.isPGroup.to_le (inf_le_right : θ.ker ⊓ R ≤ R))
    have hia := (CFSG.SectionRank.le_pRank hp.one_lt le_top (hR.map θ) hi).trans hC
    have h := Subgroup.relIndex_mul_card θ.ker R
    rw [Subgroup.relIndex_ker, hi, hj, hRc, ← pow_add] at h
    have := Nat.pow_right_injective hp.two_le h
    exact ⟨j, by omega, hj⟩
  · rintro _ ⟨f, hf, rfl⟩
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have h1 : ((θ f ⟨b, hb⟩ : ↥C) : B) = b := by
      rw [(MonoidHom.mem_ker.mp hf.1 : θ f = 1)]
      rfl
    have h2 : π f * b * (π f)⁻¹ = b := h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem uc22s206y_false
    [Finite G] (D : Data G) (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D)
    (hJ4 : F08.R880J4 D) (hK331 : InS3.K331) (hN : uc22p20rNativeGriess) (h82 : F08.R82 D)
    (hk : D.k = 2) (h3 : CFSG.Open.pRank 3 D.M ≤ 3) {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ D.M = ptPre α i)
    (hKM : ptCore α i ≤ D.M) (hTK : D.T ≤ normalizer (ptCore α i : Set G))
    (hF : ⁅((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)),
      CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥)
    (hNc : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      ((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ≤
        normalizer (J : Set (Bar2 D.M)))
    (hout : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (J ⧸ Subgroup.center J))) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨C, hC, hCn, hZ, hcase, hKC⟩ := uc22s206v_component D hK331 hN h82 hk h3 α hα hker
    hKM D.sylowM hTK hF hNc hout
  obtain ⟨A, hA, ⟨e⟩⟩ := uc22s206r_calC D hC
  have hns := UC6S846.not_solvable_of_mem_calC hA
  have hk3 := uc22s206s_not_stronglyEmbedded D hk
  obtain ⟨p, hpσ, hp11⟩ : ∃ p ∈ D.sig, IsSpor ↥C .J4 → p ≠ 11 := by
    obtain ⟨p₀, hp₀⟩ := hSg.nonempty
    by_cases hJ : IsSpor ↥C .J4
    · by_cases h11 : ∃ p ∈ D.sig, p ≠ 11
      · obtain ⟨p, hp, hp11⟩ := h11
        exact ⟨p, hp, fun _ => hp11⟩
      · have hall : ∀ p ∈ D.sig, p = 11 := fun p hp => by
          by_contra hne
          exact h11 ⟨p, hp, hne⟩
        obtain ⟨f⟩ : Nonempty (↥C ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := hJ
        exact (hJ4 A hA (⟨e.trans f⟩ :
          Nonempty (Bar2 A ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4)) hk3
          (Set.eq_singleton_iff_unique_mem.2 ⟨hall p₀ hp₀ ▸ hp₀, hall⟩)).elim
    · exact ⟨p₀, hp₀, fun h => absurd h hJ⟩
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 fun h3p =>
    hk3 (UC6S846.sp_of_mem_sig hSg hns (h3p ▸ hpσ))
  obtain ⟨R, hRM, hR, hRc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D.M
  have hR' := hR.subgroupOf D.M
  obtain ⟨F, hFR, ⟨j, hj, hFc⟩, hFC⟩ := uc22s206y_kernel (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    hCn hp (uc22s206y_pRank_aut hZ hcase hp hp5 hp11) hR' (hSg.three_le p hpσ)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv).trans hRc)
  obtain ⟨EK, hEK, hEKc, x, hxE, hx3, hxN⟩ := uc22s206w_E9 α hα hker hLM
  obtain ⟨c, hc⟩ := uc22s206w_centralize (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) (C := C) hp hp5
    (E := EK.map (Subgroup.inclusion hKM)) (hEK.map _).isPGroup
    (by rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩; exact hKC k) (hR'.mono hFR).isPGroup hFC
  obtain ⟨EG, hEG⟩ : ∃ EG : Subgroup G, EG = (EK.map (Subgroup.inclusion hKM)).map D.M.subtype :=
    ⟨_, rfl⟩
  have hEGM : EG ≤ D.M := by
    rw [hEG]
    exact map_subtype_le _
  have hEGa : IsElemAbelian 3 EG := by
    rw [hEG]
    exact (hEK.map _).map _
  have hEGc : Nat.card EG = 3 ^ 2 := by
    rw [hEG, card_map_of_injective D.M.subtype_injective,
      card_map_of_injective (Subgroup.inclusion_injective hKM), hEKc]
  have hF₁ : (F.map (MulAut.conj c).toMonoidHom).map D.M.subtype ≤
      D.M ⊓ centralizer (EG : Set G) := by
    rw [hEG]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hz) y hy)
  have hrank : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (EG : Set G)) :=
    hj.trans (CFSG.SectionRank.le_pRank hp.one_lt hF₁ (((hR'.mono hFR).map _).map _)
      (by rw [card_map_of_injective D.M.subtype_injective,
        card_map_of_injective (MulAut.conj c).injective, hFc]))
  have hΓ := h76 p hpσ hp2 hsp 3 Nat.prime_three EG hEGM hEGa hEGc
    (lt_of_lt_of_le (by norm_num) hrank) fun X hX _ =>
      lt_of_lt_of_le (by norm_num) (hrank.trans (CFSG.SectionRank.pRank_mono hp.one_lt
        (inf_le_inf_left _ ((centralizer_le (SetLike.coe_subset_coe.mpr hX)).trans
          (centralizer_le_normalizer _)))))
  have hxEG : (x : G) ∈ EG := by
    rw [hEG]
    exact ⟨Subgroup.inclusion hKM x, mem_map_of_mem _ hxE, rfl⟩
  have hx3G : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  exact hxN ((le_sSup ⟨zpowers (x : G), zpowers_le.mpr hxEG,
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers (by rw [← hx3G]; exact pow_orderOf_eq_one _))
      (by rw [Nat.card_zpowers, hx3G, pow_one]), rfl⟩ :
        normalizer (zpowers (x : G) : Set G) ≤ rankThreeGamma 1 3 EG).trans hΓ)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
