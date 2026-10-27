module

public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPrimeRankWitness
import CFSG.RankThree.PartOne.KC.UnitaryDefiningComponent

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)

theorem alternating_central_quotient_degree_lt_sq {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hrank : localRank p G ≤ 3) {L : Subgroup G} {n : ℕ}
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) : n < p ^ 2 := by
  by_contra hcon
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)
  have h5p : 5 * p ≤ p * p := Nat.mul_le_mul_right p hp5
  have hn : 4 * p + 4 ≤ n := by nlinarith [not_lt.mp hcon]
  let π : L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ Subgroup.center L := by
    intro x hx
    have h1 : e (QuotientGroup.mk' (Subgroup.center L) x) = 1 := hx
    rw [map_eq_one_iff e e.injective] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have h4 := (alternating_central_cover_two_local_prime_rank_witness (G := G) (K := L) (k := 4)
    hp hp3 (by norm_num) hn π hπ hker).2
  omega

theorem alternating_component_selected_prime_local_core_centralization {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hrank : localRank p G ≤ 3)
    {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G}
    (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {n : ℕ} (hn5 : 5 ≤ n)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G)) :
    ComponentLocalCoreCentralizes p E t L := by
  have hp2 : p ≠ 2 := by omega
  have hnp := alternating_central_quotient_degree_lt_sq hp hp3 hrank e
  have hplane := PlaneLocalCoreInner.of_mulEquiv hp e
    (planeLocalCoreInner_alternating hp hp3 hn5 hnp)
  have hout := not_dvd_outer_alternating hp hp3 hn5
  have hinnAll : ∀ x : MulAut (L ⧸ center L), x ^ p = 1 →
      x ∈ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := by
    intro x hx
    have h1 := KCUnitaryDefining.mem_inner_of_pow_eq_one hp hout
      (x := MulAut.congr e x) (by rw [← map_pow, hx, map_one])
    have h2 : MulAut.congr e x ∈
        ((MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range).map
          (MulAut.congr e).toMonoidHom := by
      rw [map_conj_range_mulAutCongr e]
      exact h1
    have h3 := Subgroup.mem_map_equiv.mp h2
    rwa [MulEquiv.symm_apply_apply] at h3
  have hinner := KCUnitaryDefining.actualPlane_le_inner (L := L) hE hinnAll
  obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard ht ht1
    hL hEL hSL hplane (Or.inr ⟨trivial, hinner⟩)
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

theorem alternatingComponentSelectedPrimeLocalCoreCentralization :
    AlternatingComponentSelectedPrimeLocalCoreCentralization := by
  intro G _ _ p hp hp3 hrank E hE hEcard t ht ht1 L hL hLn hEL hSL
  obtain ⟨n, hn5, ⟨e⟩⟩ := hLn
  exact alternating_component_selected_prime_local_core_centralization hp hp3 hrank hE hEcard ht
    ht1 hL hn5 e hEL hSL

end CFSG.RankThree.PartOne
