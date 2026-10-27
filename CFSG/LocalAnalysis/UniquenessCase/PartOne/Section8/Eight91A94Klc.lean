module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (CentOverO2)

open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_inner)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem k891a94klc_exists_mem_L_eq_rho {G : Type} [Group G] [Finite G] {L M : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) (hLM : L ≤ M) {k : G} (hkM : k ∈ M)
    (hinner : ((rhoL L).comp (Subgroup.inclusion hMN)) ⟨k, hkM⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) :
    ∃ l : ↥L, ((rhoL L).comp (Subgroup.inclusion hMN)) ⟨(l : G), hLM l.2⟩ =
      ((rhoL L).comp (Subgroup.inclusion hMN)) ⟨k, hkM⟩ := by
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hinner
  obtain ⟨t, ht⟩ := hinner
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective t
  refine ⟨l, ?_⟩
  have hsub : (Subgroup.inclusion hMN ⟨(l : G), hLM l.2⟩ : ↥(normalizer (L : Set G))) =
      ⟨(l : G), Subgroup.le_normalizer l.2⟩ := Subtype.ext rfl
  rw [MonoidHom.comp_apply, hsub]
  exact (rhoL_inner L (l : G) l.2).trans ht

private theorem k891a94klc_comp_inclusion_eq_one_of_perfect {G : Type} [Group G] [Finite G] {L M K : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) (hKM : K ≤ M)
    (hcyc : IsCyclic (Outer (Bar2 L))) (hperf : ⁅K, K⁆ = K) :
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
      ((rhoL L).comp (Subgroup.inclusion hMN))).comp (Subgroup.inclusion hKM) = 1 := by
  have : IsCyclic (Outer (Bar2 L)) := hcyc
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hperf
  have htop : (⊤ : Subgroup ↥K) ≤
      (((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
        ((rhoL L).comp (Subgroup.inclusion hMN))).comp (Subgroup.inclusion hKM)).ker := by
    have h := Abelianization.commutator_subset_ker
      (((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
        ((rhoL L).comp (Subgroup.inclusion hMN))).comp (Subgroup.inclusion hKM))
    simpa using h
  exact (MonoidHom.ker_eq_top_iff).mp (top_le_iff.mp htop)

private theorem k891a94klc_comp_inclusion_eq_one_of_opp {G : Type} [Group G] [Finite G] {L M K : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) (hKM : K ≤ M)
    (hK1 : Opp 2 K = K) (hcard : Nat.card (Outer (Bar2 L)) = 3) :
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
      ((rhoL L).comp (Subgroup.inclusion hMN))).comp (Subgroup.inclusion hKM) = 1 := by
  let ψ : ↥K →* Outer (Bar2 L) :=
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
      ((rhoL L).comp (Subgroup.inclusion hMN))).comp (Subgroup.inclusion hKM)
  have hS : {x : G | x ∈ K ∧ ∃ j : ℕ, orderOf x = 2 ^ j} ⊆ (ψ.ker).map K.subtype := by
    rintro x ⟨hxK, j, hj⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hdvd1 : orderOf (ψ ⟨x, hxK⟩) ∣ 2 ^ j := by
      rw [← hj, ← Subgroup.orderOf_mk x hxK]
      exact orderOf_map_dvd ψ ⟨x, hxK⟩
    have hdvd2 : orderOf (ψ ⟨x, hxK⟩) ∣ 3 := by
      rw [← hcard]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ j) 3 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (by norm_num)).pow_left j
    have hone : orderOf (ψ ⟨x, hxK⟩) = 1 := by
      have hgcd : orderOf (ψ ⟨x, hxK⟩) ∣ Nat.gcd (2 ^ j) 3 := Nat.dvd_gcd hdvd1 hdvd2
      rw [hcop.gcd_eq_one] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact orderOf_eq_one_iff.mp hone
  have hKle : K ≤ (ψ.ker).map K.subtype := by
    have hcl : Subgroup.closure {x : G | x ∈ K ∧ ∃ j : ℕ, orderOf x = 2 ^ j} = K := hK1
    exact hcl.ge.trans ((Subgroup.closure_le ((ψ.ker).map K.subtype)).mpr hS)
  have hmap : (ψ.ker).map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.map_subtype_le _) hKle
  have hker : ψ.ker = ⊤ := Subgroup.map_subtype_inj.mp hmap
  exact (MonoidHom.ker_eq_top_iff).mp hker

theorem s891_a94_klc {G : Type} [Group G] [Finite G] (D : Data G) (hOut : R891OutCore)
    (L S A K K₀ : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hcfg : R891Cfg894 D A K K₀ n) :
    K ≤ L ⊔ CentOverO2 D.M L := by
  intro k hk
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hset.mem.1
  have hφ1 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)))
      (((rhoL L).comp (Subgroup.inclusion hbasic.normal)) ⟨k, hcfg.kM hk⟩) = 1 := by
    change (((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
      ((rhoL L).comp (Subgroup.inclusion hbasic.normal))).comp (Subgroup.inclusion hcfg.kM))
      ⟨k, hk⟩ = 1
    by_cases hn : n = 1
    · have hcard : Nat.card (Outer (Bar2 L)) = 3 := by
        have h3 := (hOut (Bar2 L) n hset.d4).2
        rw [hn] at h3
        simpa using h3
      have hcomp := k891a94klc_comp_inclusion_eq_one_of_opp hbasic.normal hcfg.kM
        (hcfg.k2 hn) hcard
      have heval := congrArg (fun f : ↥K →* Outer (Bar2 L) => f ⟨k, hk⟩) hcomp
      exact heval
    · have hperf : ⁅K, K⁆ = K := by
        rcases hcfg.shape with ⟨-, -, hperf, -⟩ | ⟨hn1, -⟩
        · exact hperf
        · exact absurd hn1 hn
      have hcomp := k891a94klc_comp_inclusion_eq_one_of_perfect hbasic.normal hcfg.kM
        (hOut (Bar2 L) n hset.d4).1 hperf
      have heval := congrArg (fun f : ↥K →* Outer (Bar2 L) => f ⟨k, hk⟩) hcomp
      exact heval
  have hinner : ((rhoL L).comp (Subgroup.inclusion hbasic.normal)) ⟨k, hcfg.kM hk⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) :=
    (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))
      (((rhoL L).comp (Subgroup.inclusion hbasic.normal)) ⟨k, hcfg.kM hk⟩)).mp hφ1
  obtain ⟨l, hl_eq⟩ :=
    k891a94klc_exists_mem_L_eq_rho hbasic.normal hLM (hcfg.kM hk) hinner
  have hlm : l⁻¹ * k ∈ CentOverO2 D.M L := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map hbasic.normal]
    refine Subgroup.mem_map.mpr ⟨⟨(l : G), hLM l.2⟩⁻¹ * ⟨k, hcfg.kM hk⟩, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hl_eq, inv_mul_cancel]
    · rfl
  convert Subgroup.mul_mem_sup l.2 hlm using 1
  rw [Subgroup.coe_inv]
  group

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
