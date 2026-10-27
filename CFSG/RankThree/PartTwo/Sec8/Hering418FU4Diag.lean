module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Blk
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item419Res3
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0)
open CFSG.Assembly.RankThreeEven (projSU)

theorem nine_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) (h3 : 3 ∣ n) : 9 ∣ 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ := h3
  have hm : Odd m := (Nat.odd_mul.mp hn).2
  have h := Odd.nat_add_dvd_pow_add_pow 8 1 hm
  rw [one_pow, show (8 : ℕ) + 1 = 9 by norm_num] at h
  rwa [pow_mul, show (2 : ℕ) ^ 3 = 8 by norm_num]

theorem closure_pair_exp {X : Type*} [Group X] {x y : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) :
    (∀ z ∈ Subgroup.closure ({x, y} : Set X), z ^ 3 = 1) ∧
      ∀ z ∈ Subgroup.closure ({x, y} : Set X), ∀ w ∈ Subgroup.closure ({x, y} : Set X),
        z * w = w * z := by
  have hS : ({x, y} : Set X).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hc : IsMulCommutative (Subgroup.closure ({x, y} : Set X)) :=
    Subgroup.isMulCommutative_closure hS
  refine ⟨fun z hz => ?_, fun z hz w hw => congrArg Subtype.val (hc.is_comm.comm ⟨z, hz⟩ ⟨w, hw⟩)⟩
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  | one => exact one_pow 3
  | mul z w hz hw ihz ihw =>
    have hzw : Commute z w := congrArg Subtype.val (hc.is_comm.comm ⟨z, hz⟩ ⟨w, hw⟩)
    rw [hzw.mul_pow, ihz, ihw, one_mul]
  | inv z hz ihz => rw [inv_pow, ihz, inv_one]

section Main

theorem blockData_of_equiv {M : Type} [Group M] {n : ℕ} (hn : Odd n) (h3n : 3 ∣ n)
    (e : M ≃* projSU 4 2 n) {x y : M} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) : BlockData (Subgroup.centralizer ({x} : Set M)) y := by
  have hn1 : 1 ≤ n := hn.pos
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := h3n
    have : m ≠ 0 := by
      rintro rfl
      omega
    omega
  set K := GaloisField 2 (2 * n) with hKdef
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have hfin := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hn
  have h9 : 9 ∣ 2 ^ n + 1 := nine_dvd_two_pow_add_one hn h3n
  set ψ₀ := Res417Six.unitarySUEquivProjSU hn1 with hψ₀
  have hx3' : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hy3' : (e y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hxy' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  obtain ⟨hFexp, hFcomm⟩ := closure_pair_exp hx3' hy3' hxy'
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3 ψ₀
    (Subgroup.closure ({e x, e y} : Set (projSU 4 2 n))) hFexp hFcomm
  set s := ψ.symm (e x) with hs
  set t := ψ.symm (e y) with ht
  have hsT : (s : GL (Fin 4) K) ∈ torusSU 3 4 K :=
    hψ s (by rw [hs, MulEquiv.apply_symm_apply]; exact Subgroup.subset_closure (by simp))
  have htT : (t : GL (Fin 4) K) ∈ torusSU 3 4 K :=
    hψ t (by rw [ht, MulEquiv.apply_symm_apply]; exact Subgroup.subset_closure (by simp))
  obtain ⟨v, hv3, hvp, hvs⟩ := mem_torusSU_iff.mp hsT
  obtain ⟨u, hu3, hup, hut⟩ := mem_torusSU_iff.mp htT
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : (s : GL (Fin 4) K) = 1 := by
      rw [← hvs]
      exact CFSG.RankThree.PartOne.KFU.diagU_one
    have h2 : s = 1 := Subtype.ext h1
    have h3' : e x = 1 := by rw [← ψ.apply_symm_apply (e x), ← hs, h2, map_one]
    exact e.injective (by rw [h3', map_one])
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨σ, ω, hω3, hω1, hnf⟩ := exists_perm_normal_form hζ hv3 hvp hv1
  set P : GL (Fin 4) K := permGL σ with hP
  have hPU : P ∈ unitarySU 2 n K 4 := permGL_mem_unitarySU hU σ
  set θ : M ≃* unitarySU 2 n K 4 :=
    (e.trans ψ.symm).trans (MulAut.conj (⟨P, hPU⟩ : unitarySU 2 n K 4)) with hθ
  have hθx : ((θ x : unitarySU 2 n K 4) : GL (Fin 4) K) = diagU (v ∘ σ.symm) := by
    have h1 : ((θ x : unitarySU 2 n K 4) : GL (Fin 4) K) = P * (s : GL (Fin 4) K) * P⁻¹ := by
      simp only [hθ, MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [h1, ← hvs]
    exact permGL_conj_diagU σ v
  have hθy : ((θ y : unitarySU 2 n K 4) : GL (Fin 4) K) = diagU (u ∘ σ.symm) := by
    have h1 : ((θ y : unitarySU 2 n K 4) : GL (Fin 4) K) = P * (t : GL (Fin 4) K) * P⁻¹ := by
      simp only [hθ, MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [h1, ← hut]
    exact permGL_conj_diagU σ u
  have hu3' : ∀ i, (u ∘ σ.symm) i ^ 3 = 1 := fun i => hu3 _
  have hup' : ∏ i, (u ∘ σ.symm) i = 1 := by
    rw [← hup]
    exact Equiv.prod_comp σ.symm u
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hh]
      exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  have hB : BlockData (unitarySU 2 n K 4 ⊓ Subgroup.centralizer {diagU (v ∘ σ.symm)})
      (diagU (u ∘ σ.symm)) := by
    rcases hnf with hA | hB | hC'
    · rw [hA]
      exact blockData_A hU hn2 h3 h9 hω1 hu3' hup'
    · rw [hB]
      exact blockData_B hU hn2 h3 hω1 hω2 hu3' hup'
    · rw [hC']
      exact blockData_C hU hn2 h3 hω2 hu3' hup'
  have hxmem : diagU (v ∘ σ.symm) ∈ unitarySU 2 n K 4 := hθx ▸ (θ x).2
  have hymem : diagU (u ∘ σ.symm) ∈ unitarySU 2 n K 4 := hθy ▸ (θ y).2
  have hT := BlockData.transport θ.symm hxmem hymem hB
  have hxe : θ.symm ⟨diagU (v ∘ σ.symm), hxmem⟩ = x := by
    have : (⟨diagU (v ∘ σ.symm), hxmem⟩ : unitarySU 2 n K 4) = θ x := Subtype.ext hθx.symm
    rw [this, MulEquiv.symm_apply_apply]
  have hye : θ.symm ⟨diagU (u ∘ σ.symm), hymem⟩ = y := by
    have : (⟨diagU (u ∘ σ.symm), hymem⟩ : unitarySU 2 n K 4) = θ y := Subtype.ext hθy.symm
    rw [this, MulEquiv.symm_apply_apply]
  rw [hxe, hye] at hT
  exact hT

end Main

end CFSG.RankThree.PartTwo.Sec8.Hering418
