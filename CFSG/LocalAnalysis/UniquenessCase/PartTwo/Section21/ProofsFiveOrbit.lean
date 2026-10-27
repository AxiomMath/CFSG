module

public import CFSG.GroupTheory.CyclicDiagonal
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsEleven
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_orderOf_not_mem_normalizer {T M L₀ B : Subgroup G}
    (hB : B ∈ calB1 T M L₀) {L : Subgroup G}
    (h : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    ∃ a ∈ B, (orderOf a).Prime ∧ orderOf a ≠ 2 ∧
      a ∉ Subgroup.normalizer (L : Set G) := by
  classical
  obtain ⟨b, hbB, hbN⟩ := Set.not_subset.mp h
  obtain ⟨hodd, hsq⟩ := orderOf_odd_and_squarefree_of_mem_calB1 hB hbB
  by_contra hcon
  push Not at hcon
  refine hbN (mem_of_forall_prime_orderOf_pow_mem hsq ?_)
  intro k hk
  exact hcon (b ^ k) (B.pow_mem hbB k) hk
    (hodd.ne_two_of_dvd_nat (orderOf_pow_dvd k))

theorem conjugatePower_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) {a : G} (ha : a ∈ M)
    (i : ℕ) : conjugatePower a L i ∈ calC M := by
  have h := uc22p22u_calC_conj (X := M) (M := M) (K := L)
    (Subgroup.le_normalizer : M ≤ Subgroup.normalizer (M : Set G)) hL
    (m := (a ^ i)⁻¹) (M.inv_mem (M.pow_mem ha i))
  simpa [conjugatePower, CFSG.Open.uniqueFourConj] using h

theorem barImage_conjugatePower {M L : Subgroup G} (hLM : L ≤ M) {a : G} (ha : a ∈ M) (i : ℕ) :
    barImage M (conjugatePower a L i) =
      conjugatePower (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L) i := by
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  let q : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hsub : (conjugatePower a L i).subgroupOf M =
      uc22p20bCj ((⟨a, ha⟩ : ↥M) ^ i) (L.subgroupOf M) := by
    ext x
    rw [Subgroup.mem_subgroupOf, conjugatePower, Subgroup.mem_map, uc22p20b_mem_cj]
    constructor
    · rintro ⟨z, hz, hzy⟩
      refine ⟨⟨z, hLM hz⟩, hz, ?_⟩
      ext
      simpa [← map_pow, MulAut.conj_apply] using hzy
    · rintro ⟨z, hz, hzy⟩
      refine ⟨(z : G), hz, ?_⟩
      have h := congrArg Subtype.val hzy
      simpa [← map_pow, MulAut.conj_apply] using h
  calc barImage M (conjugatePower a L i)
      = ((conjugatePower a L i).subgroupOf M).map q := rfl
    _ = (uc22p20bCj ((⟨a, ha⟩ : ↥M) ^ i) (L.subgroupOf M)).map q := by rw [hsub]
    _ = uc22p20bCj (q ((⟨a, ha⟩ : ↥M) ^ i)) ((L.subgroupOf M).map q) :=
      (uc22p20d_cj_map q ((⟨a, ha⟩ : ↥M) ^ i) (L.subgroupOf M)).symm
    _ = uc22p20bCj ((q ⟨a, ha⟩) ^ i) (barImage M L) := by rw [map_pow]; rfl
    _ = conjugatePower (q ⟨a, ha⟩) (barImage M L) i := rfl

theorem exists_orderOf_prime_not_mem_center_barImage {M L : Subgroup G}
    (hL : L ∈ calC M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card (Bar2 L)) :
    ∃ u : ↥(barImage M L), orderOf u = p ∧
      u ∉ Subgroup.center ↥(barImage M L) := by
  obtain ⟨x, hxord, hxnc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hL.2.2 hp hp2 hdvd
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  refine ⟨e x, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hxord]
  · intro h
    apply hxnc
    rw [Subgroup.mem_center_iff] at h ⊢
    intro z
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e z)

theorem conjugatesCommute_barImage {M L : Subgroup G} (hL : L ∈ calC M) {a : G} (ha : a ∈ M)
    (hr : (orderOf a).Prime) (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    ConjugatesCommute (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩) (barImage M L)
      (orderOf a) := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  intro i j hij x hx y hy
  have hLi : conjugatePower a L (i : ℕ) ∈ calC M := conjugatePower_mem_calC hL ha i
  have hLj : conjugatePower a L (j : ℕ) ∈ calC M := conjugatePower_mem_calC hL ha j
  have hne : conjugatePower a L (i : ℕ) ≠ conjugatePower a L (j : ℕ) := by
    intro heq
    have hval := conjugatePower_injOn hr haL (Set.mem_Iio.mpr i.isLt)
      (Set.mem_Iio.mpr j.isLt) heq
    exact hij (Fin.ext hval)
  rw [← barImage_conjugatePower hLM ha i] at hx
  rw [← barImage_conjugatePower hLM ha j] at hy
  exact uc22p22l_barImage_commute hLi hLj hne x hx y hy

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
