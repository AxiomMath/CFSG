module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairA
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_pair_five_central (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {B : Fin (4 + 1) → Subgroup G} {σ : Equiv.Perm (Fin (4 + 1))} {bb : Fin (4 + 1) → G}
    (he : Nine3PairEnum V K S A g 4 B σ bb) (hcard : Nat.card ↥(nineDelta V S) = 5) :
    ∀ h ∈ nineH V K, ⁅bb 1 * bb 2 * bb 3 * bb 4, h⁆ ∈ nineI V K := by
  classical
  have hp3 : p = 3 := nine3_p_eq_three hc hI (Or.inr hcard)
  subst hp3
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  obtain ⟨n, hΩ, hΔ⟩ := hc.core.card_nineOmegaIn
  have hm : Nat.card ↥(nineOmegaIn V K S) = 4 := by rw [hΩ]; omega
  have hframe : Nine3OddFrame 3 4 (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) := by
    have h := nine3_oddFrame hc hI hρ
    rwa [hm] at h
  have hi : Nine3FibreIndep 3 (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) :=
    nine3_fibreIndep hc hI (by omega) hρ
  have hBΩ : ∀ k : Fin (4 + 1), k ≠ 0 → B k ∈ omegaIn V K (nineE V K) := fun k hk =>
    ⟨(he.Ω k hk).1, (he.Ω k hk).2.trans hc.core.S_le_K⟩
  let u : Fin (4 + 1) → ↥(nineH V K) := fun k => ⟨bb k, by
    by_cases hk : k = 0
    · subst hk; rw [he.bb0]; exact (nineH V K).one_mem
    · exact (le_iSup₂_of_le (B k) (hBΩ k hk) le_rfl : B k ≤ nineH V K)
        (he.bb_mem k hk).1⟩
  let d : Fin (4 + 1) → Nine3Hbar V K := fun k => QuotientGroup.mk (u k)
  have hBfib : ∀ k : Fin (4 + 1), k ≠ 0 → Nine3Fib K 3 ρ (B k) 0 := fun k hk =>
    (nine3_fib_zero_iff hc hρ (hBΩ k hk)).mpr (he.Ω k hk).2
  have hdmem : ∀ k : Fin (4 + 1), k ≠ 0 → d k ∈ Nine3Dbar V K := fun k hk =>
    (nine3_mk_mem_dbar (hBΩ k hk) hρ.le_ker (hBfib k hk)
      (he.bb_mem k hk).1 (he.bb_mem k hk).2).1
  have hdpi : ∀ k : Fin (4 + 1), k ≠ 0 →
      nine3Pi V K ρ hρ.le_ker (d k) = zmodRefl 3 0 := fun k hk =>
    (nine3_mk_mem_dbar (hBΩ k hk) hρ.le_ker (hBfib k hk)
      (he.bb_mem k hk).1 (he.bb_mem k hk).2).2
  have hdinj : ∀ k k' : Fin (4 + 1), k ≠ 0 → k' ≠ 0 → d k = d k' → k = k' := by
    intro k k' hk hk' h
    exact he.inj (nine3_eq_of_mk_eq hc hI (hBΩ k hk) (hBΩ k' hk')
      (he.bb_mem k hk).1 (he.bb_mem k' hk').1 (he.bb_mem k hk).2 (he.bb_mem k' hk').2 h)
  let l : List (Nine3Hbar V K) := ([1, 2, 3, 4] : List (Fin (4 + 1))).map d
  have hl : l.Nodup := by
    show (([1, 2, 3, 4] : List (Fin (4 + 1))).map d).Nodup
    refine List.Nodup.map_on ?_ (by decide)
    intro a ha b hb hab
    exact hdinj a b (by rintro rfl; simp at ha) (by rintro rfl; simp at hb) hab
  have hlen : l.length = 4 := by
    show (([1, 2, 3, 4] : List (Fin (4 + 1))).map d).length = 4
    simp
  have hF : ∀ x ∈ l, x ∈ nine3FibreSet (nine3Pi V K ρ hρ.le_ker) (Nine3Dbar V K) 0 := by
    intro x hx
    rw [show l = ([1, 2, 3, 4] : List (Fin (4 + 1))).map d from rfl, List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨hdmem k (by rintro rfl; simp at hk), hdpi k (by rintro rfl; simp at hk)⟩
  have hcent : l.prod ∈ Subgroup.center (Nine3Hbar V K) :=
    nine3OddFrame_four_prod_central hframe hi 0 hl hlen hF
  have hprod : l.prod = QuotientGroup.mk (u 1 * u 2 * u 3 * u 4) := by
    show (([1, 2, 3, 4] : List (Fin (4 + 1))).map d).prod =
      QuotientGroup.mk (u 1 * u 2 * u 3 * u 4)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, d]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    group
  intro h hh
  let Hh : ↥(nineH V K) := ⟨h, hh⟩
  let A : ↥(nineH V K) := u 1 * u 2 * u 3 * u 4
  have hcentA : (QuotientGroup.mk A : Nine3Hbar V K) ∈ Subgroup.center (Nine3Hbar V K) := by
    rw [← hprod]
    exact hcent
  have hmemN : ⁅A, Hh⁆ ∈ (nineI V K).subgroupOf (nineH V K) := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K)) ⁅A, Hh⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hcentA
      (QuotientGroup.mk' ((nineI V K).subgroupOf (nineH V K)) Hh)).symm
  have hcoe : ((⁅A, Hh⁆ : ↥(nineH V K)) : G) = ⁅bb 1 * bb 2 * bb 3 * bb 4, h⁆ := by
    show (Subgroup.subtype (nineH V K)) ⁅A, Hh⁆ = ⁅bb 1 * bb 2 * bb 3 * bb 4, h⁆
    rw [map_commutatorElement]
    rfl
  rw [← hcoe]
  exact Subgroup.mem_subgroupOf.mp hmemN

end CFSG.LocalAnalysis.WeakClosure81
