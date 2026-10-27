module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.Asc80BPSL3Parabolics
import CFSG.LocalAnalysis.WeakClosure81.Asc80BPSL3Model
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem psl3_graph_involution_centralizer_escape {Q : Type} [Group Q] [Finite Q]
    {L T : Subgroup Q} (hLn : L.Normal) (hT : IsSylowIn 2 T ⊤) {f : ℕ}
    (hL : CFSG.Models.LieModel ↥L .PSL 3 2 f) {a : Q} (ha : a * a = 1)
    (haD : ActsOnDynkinMod ⊥ L a) :
    ¬ L ⊓ centralizer ({a} : Set Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hL.admissible.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel (hL.toBlueprint (by decide))
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  let α : MulAut ↥L := MulAut.conjNormal a
  have hα : ∀ x : ↥L, (α x : Q) = a * (x : Q) * a⁻¹ := fun x => MulAut.conjNormal_apply a x
  obtain ⟨D, σ, ε, hε, hstd⟩ :=
    (automorphism_generation (K := K) (n := 3) (by norm_num)).2 (MulAut.congr e α)
  obtain rfl : ε = 1 := graphExponent_eq_one_of_actsOnDynkinMod e α hα haD D σ hε hstd
  rw [pow_one] at hstd
  have hαα : α * α = 1 := by
    ext x
    rw [MulAut.mul_apply, hα, hα]
    simp only [MulAut.one_apply]
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    rw [hainv, ← mul_assoc, ← mul_assoc, ha, one_mul, mul_assoc, ha, mul_one]
  have hβ : (conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1 := by
    rw [← hstd, sq, ← map_mul, hαα, map_one]
  let S : Subgroup (projectiveSL 3 K) := (T.subgroupOf L).map e.toMonoidHom
  have hTL : IsSylowIn 2 (T.subgroupOf L) ⊤ := by
    haveI := hLn
    have h := hT.inf_normal (H := ⊤) (N := L) le_top inferInstance
    have h2 := (E1.isSylowIn_subgroupOf_iff (H := L) inf_le_right le_rfl).2 h
    rwa [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_self] at h2
  have hS : IsSylowIn 2 S ⊤ := by
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact (E1.isSylowIn_map_mulEquiv e).2 hTL
  obtain ⟨x, hxfix, hxN⟩ := psl3_graph_involution_model_escape hf hK S hS D σ hβ
  intro hle
  apply hxN
  have hαy : α (e.symm x) = e.symm x := by
    apply e.injective
    have h := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ x) hstd
    simp only [MulAut.congr_apply] at h
    rw [MulEquiv.apply_symm_apply]
    exact h.trans hxfix
  have hyC : ((e.symm x : ↥L) : Q) ∈ centralizer ({a} : Set Q) := by
    rw [mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val hαy
    rw [hα] at h
    calc ((e.symm x : ↥L) : Q) * a
        = a * ((e.symm x : ↥L) : Q) * a⁻¹ * a := by rw [h]
      _ = a * ((e.symm x : ↥L) : Q) := by group
  have hyN := hle ⟨(e.symm x).2, hyC⟩
  have hyN' : e.symm x ∈ normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [← Subgroup.inf_subgroupOf_right, ← Subgroup.subgroupOf_normalizer_eq inf_le_right]
    exact hyN
  have hxmem := Subgroup.mem_map_of_mem e.toMonoidHom hyN'
  rw [Subgroup.map_equiv_normalizer_eq] at hxmem
  change e (e.symm x) ∈ _ at hxmem
  rwa [MulEquiv.apply_symm_apply] at hxmem

end CFSG.LocalAnalysis.WeakClosure81

end
