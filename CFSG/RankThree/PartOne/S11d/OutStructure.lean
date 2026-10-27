module

public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.RankThree.PartOne.S11d.FactsNormalizer
public import CFSG.RankThree.PartOne.S11d.FactsFinal
public import CFSG.RankThree.CentralCover.SteinbergBNLinearSplitPrime
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section Rank

variable {Y : Type} [Group Y] [Finite Y]

theorem ker_le_center_of_mulEquiv {A B T : Type*} [Group A] [Group B] [Group T] (e : A ≃* B)
    (ψ : B ⧸ Subgroup.center B ≃* T) :
    (ψ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center B)).comp e.toMonoidHom)).ker ≤
      Subgroup.center A := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hx (e y)

omit [Finite Y] in
theorem isElementaryAbelian_of_isElemAbelian' {p : ℕ} {V : Subgroup Y}
    (h : CFSG.Assembly.IsElemAbelian p V) : CFSG.IsElementaryAbelian p V :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

theorem five_le_of_prime_gt_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have : p = 4 := by omega
  subst this
  norm_num at hp

theorem rank_of_psl_diag {p n m : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 m) (hpn : p ∣ n)
    (hpq : p ∣ 2 ^ m - 1) : n - 3 ≤ CFSG.pRank p Y ∧ n - 3 ≤ localRank p Y := by
  classical
  obtain ⟨⟨hℓ, hm, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime_gt_three hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have hchar : CharP k 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hk])
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  let ψ : Y ⧸ Subgroup.center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : (⊤ : Subgroup Y) →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Y)).comp
      Subgroup.topEquiv.toMonoidHom)
  have hφs : Function.Surjective φ :=
    ψ.surjective.comp ((QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.surjective)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard, hle⟩ :=
    CFSG.RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank (⊤ : Subgroup Y)
      hℓ hp hp3 hpk (by omega) φ hφs (ker_le_center_of_mulEquiv Subgroup.topEquiv ψ)
  have hr : (if (2 : ℕ) = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) = n - 3 := by
    simp only [hpn, ↓reduceIte]
    omega
  rw [hr] at hVcard hle
  exact ⟨CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian hp.one_lt
    (isElementaryAbelian_of_isElemAbelian' hVab) hVcard, hle⟩

theorem rank_of_psu_diag {p n m : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 m) (hpn : p ∣ n)
    (hpq : p ∣ 2 ^ m + 1) : n - 3 ≤ CFSG.pRank p Y ∧ n - 3 ≤ localRank p Y := by
  classical
  obtain ⟨⟨hℓ, hm, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime_gt_three hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have hU : UnitaryFieldData 2 m k := ⟨hℓ, hm, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : Y ⧸ Subgroup.center Y ≃* unitaryPSU hU n :=
    e.trans (unitaryPSUEquiv hU (by omega)).symm
  let φ : (⊤ : Subgroup Y) →* unitaryPSU hU n :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Y)).comp
      Subgroup.topEquiv.toMonoidHom)
  have hφs : Function.Surjective φ :=
    ψ.surjective.comp ((QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.surjective)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank (⊤ : Subgroup Y)
      hU hp hp3 hpq (by omega) φ hφs (ker_le_center_of_mulEquiv Subgroup.topEquiv ψ)
  have hr : (if (2 : ℕ) = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) = n - 3 := by
    simp only [hpn, ↓reduceIte]
    omega
  have hVcard' : Nat.card V = p ^ (n - 3) := by rw [← hr]; exact hVcard
  exact ⟨CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian hp.one_lt
    (isElementaryAbelian_of_isElemAbelian' hVab) hVcard',
    CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
      (le_inf_iff.mp hV).2 hVab hVcard'⟩

theorem not_dvd_gcd_psl_of_pRank {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrk : CFSG.pRank p Y ≤ 1)
    {n m : ℕ} (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 m) :
    ¬ p ∣ Nat.gcd n (2 ^ m - 1) := by
  intro hdvd
  obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hmod
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hn5 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have h := rank_of_psl_diag hp (by omega) hmod hpn (hdvd.trans (Nat.gcd_dvd_right _ _))
  omega

theorem not_dvd_gcd_psu_of_pRank {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrk : CFSG.pRank p Y ≤ 1)
    {n m : ℕ} (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 m) :
    ¬ p ∣ Nat.gcd n (2 ^ m + 1) := by
  intro hdvd
  obtain ⟨⟨-, -, hn3, -⟩, -⟩ := id hmod
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hn5 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have h := rank_of_psu_diag hp (by omega) hmod hpn (hdvd.trans (Nat.gcd_dvd_right _ _))
  omega

theorem not_dvd_gcd_psl_of_evenRank {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hev : CFSG.Assembly.evenRank Y ≤ 3) {n m : ℕ}
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 m) :
    ¬ p ∣ Nat.gcd n (2 ^ m - 1) := by
  intro hdvd
  obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hmod
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hn7 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have h := rank_of_psl_diag hp (by omega) hmod hpn (hdvd.trans (Nat.gcd_dvd_right _ _))
  have hloc : localRank p Y ≤ CFSG.Assembly.evenRank Y :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank p hp (by omega) Y
  omega

theorem not_dvd_gcd_psu_of_evenRank {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hev : CFSG.Assembly.evenRank Y ≤ 3) {n m : ℕ}
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 m) :
    ¬ p ∣ Nat.gcd n (2 ^ m + 1) := by
  intro hdvd
  obtain ⟨⟨-, -, hn3, -⟩, -⟩ := id hmod
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hn7 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have h := rank_of_psu_diag hp (by omega) hmod hpn (hdvd.trans (Nat.gcd_dvd_right _ _))
  have hloc : localRank p Y ≤ CFSG.Assembly.evenRank Y :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank p hp (by omega) Y
  omega

end Rank

section Assembly

open CFSG.Blueprint

theorem outPNice_or_D4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Type} [Group X] {t : StatedLieTag} {n m : ℕ} (hm : 2 ≤ m) (h : LieModel X t n 2 m)
    (hL : StatedClassicalModel X .PSL n 2 m → ¬ p ∣ Nat.gcd n (2 ^ m - 1))
    (hU : StatedClassicalModel X .PSU n 2 m → ¬ p ∣ Nat.gcd n (2 ^ m + 1)) :
    OutPNice p X ∨ ∃ m' : ℕ, StatedClassicalModel X .POmegaPlus 4 2 m' := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases h with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSL_two hp hcl)
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSL_ge_three hp hp2 (by omega) hcl (hL hcl))
    · obtain ⟨⟨-, -, hn3, -⟩, -⟩ := id hcl
      exact Or.inl (outPNice_PSU hp hcl (hU hcl))
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSp_two hp hcl)
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSp_ge_three hp (by omega) hcl)
    · obtain ⟨⟨-, -, -, hp2'⟩, -⟩ := id hcl
      exact absurd rfl hp2'
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      by_cases hn : n = 4
      · subst hn
        exact Or.inr ⟨m, hcl⟩
      · exact Or.inl (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl)
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      exact Or.inl (outPNice_POmegaMinus hp hp2 hn4 hcl)
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (outPNice_G2 hp hch)
    · exact Or.inl (outPNice_F4 hp hch)
    · exact Or.inl (outPNice_E6 hp hp3 hp2 hch)
    · exact Or.inl (outPNice_E7 hp hch)
    · exact Or.inl (outPNice_E8 hp hch)
    · exact Or.inl (outPNice_twistedE6 hp hp3 hch)
    · exact Or.inl (outPNice_trialityD4 hp hch)
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := id hree
      omega
    · exact Or.inl (outPNice_twistedF4 hp hree)
    · obtain ⟨⟨-, -, -, -, hm1⟩, -⟩ := id hree
      omega
  · subst ht
    exact Or.inl (outPNice_Suzuki hp hsz)

end Assembly

end CFSG.RankThree.PartOne.OutStructure

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure

@[expose] def D4OutCentral : Prop :=
  ∀ (X : Type) [Group X] (p m : ℕ), p.Prime → 5 ≤ p →
    StatedClassicalModel X .POmegaPlus 4 2 m → OutPCentral p X

theorem outPCyclic : OutPCyclic := by
  intro G _ _ p J a hset hrk u v hu hv huv hup hvp
  obtain ⟨hp, hp5, hq, -, -, -, -, -, -, t, n, f, hf, hmodel, -⟩ := hset
  have : Group.IsPerfect ↥J := hq.1
  have hm : 2 ≤ p * f := le_trans (by omega) (Nat.le_mul_of_pos_right p hf)
  have hstr := outPNice_or_D4 hp hp5 hm hmodel
    (fun hmod => not_dvd_gcd_psl_of_pRank hp hp5 hrk hmod)
    (fun hmod => not_dvd_gcd_psu_of_pRank hp hp5 hrk hmod)
  have hchain : OutPChain p (↥J ⧸ Subgroup.center ↥J) := by
    rcases hstr with h | ⟨m', hm'⟩
    · exact h.toChain
    · exact outPChain_POmegaPlus_four hp (by omega) hm'
  exact commuting_pElements_of_outPChain J hchain hu hv huv hup hvp

theorem fieldAutNormalizerPower (hD4 : D4OutCentral) : FieldAutNormalizerPower := by
  intro G _ _ p K a x m hset hp7 hx hxm
  obtain ⟨hp, hp5, hq, -, hev, -, ha, ha1, hap, t, n, f, hf, hmodel, -⟩ := hset
  have : Group.IsPerfect ↥K := hq.1
  have hev' : CFSG.Assembly.evenRank ↥K ≤ 3 :=
    (CFSG.RankThree.PartOne.PlaneAux.evenRank_le_of_injective
      (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Subgroup.zpowers a))
      (Subgroup.inclusion_injective _)).trans hev
  have hm : 2 ≤ p * f := le_trans (by omega) (Nat.le_mul_of_pos_right p hf)
  have hstr := outPNice_or_D4 hp hp5 hm hmodel
    (fun hmod => not_dvd_gcd_psl_of_evenRank hp hp7 hev' hmod)
    (fun hmod => not_dvd_gcd_psu_of_evenRank hp hp7 hev' hmod)
  rcases hstr with h | ⟨m', hm'⟩
  · exact normalizer_power_of_outPNice hp K h ha hx hap ha1 hxm
  · exact normalizer_power_of_outPCentral hp K (hD4 _ p m' hp hp5 hm') ha hx hap ha1 hxm

end CFSG.RankThree.PartOne
