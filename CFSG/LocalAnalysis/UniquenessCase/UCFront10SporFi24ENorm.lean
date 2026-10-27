module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Fi24 CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] rAction

section Realizes


theorem conj_mem_fi24EB {r : R} {σ : Equiv.Perm (Fin 24)} (hr : Realizes bbar r σ) {x : R}
    (hx : x ∈ fi24EB) : r * x * r⁻¹ ∈ fi24EB := by
  unfold fi24EB at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← hr i]
    exact subset_closure ⟨σ i, rfl⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul y z _ _ hy hz =>
    have := mul_mem hy hz
    rwa [show r * y * r⁻¹ * (r * z * r⁻¹) = r * (y * z) * r⁻¹ by group] at this
  | inv y _ hy =>
    have := inv_mem hy
    rwa [show (r * y * r⁻¹)⁻¹ = r * y⁻¹ * r⁻¹ by group] at this

theorem mem_normalizer_of_realizes {n : CFSG.Sporadic.Fi24.J} {σ : Equiv.Perm (Fin 24)}
    (h : Realizes bbar (jR n) σ) : n ∈ normalizer (fi24E : Set CFSG.Sporadic.Fi24.J) := by
  rw [mem_normalizer_iff]
  intro g
  rw [mem_fi24E_iff, mem_fi24E_iff, map_mul, map_mul, map_inv]
  refine ⟨conj_mem_fi24EB h, fun hg => ?_⟩
  have := conj_mem_fi24EB (Realizes.inv bbar h) hg
  rwa [inv_inv, show (jR n)⁻¹ * (jR n * jR g * (jR n)⁻¹) * jR n = jR g by group] at this


theorem smul_bbarPt_of_mem {x : R} (hx : x ∈ fi24EB) (j : Fin 24) : x • bbarPt j = bbarPt j := by
  apply cls_injective
  rw [cls_smul_R]
  show x * bbar j * x⁻¹ = bbar j
  rw [fi24EB_comm hx j, mul_inv_cancel_right]

theorem realizes_bbar_zero : Realizes bbar (bbar 0) 1 := fun i => by
  rw [Equiv.Perm.one_apply, bbar_comm 0 i, mul_inv_cancel_right]

end Realizes

section Pi


theorem exists_smul_bbarPt {n : CFSG.Sporadic.Fi24.J} (hn : n ∈ normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (j : Fin 24) :
    ∃ k, bbarPt k = jR n • bbarPt j := by
  refine exists_bbarPt_of_fix fun i => ?_
  obtain ⟨e, he, hee⟩ := bbar_mul_bbar_mem_fi24E 0 i
  have h1 : n⁻¹ * e * n ∈ fi24E := by
    have := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
    rwa [inv_inv] at this
  have h2 := smul_bbarPt_of_mem (mem_fi24E_iff.1 h1) j
  rw [map_mul, map_mul, map_inv, hee] at h2
  rw [smul_smul, show bbar 0 * bbar i * jR n =
    jR n * ((jR n)⁻¹ * (bbar 0 * bbar i) * jR n) by group, mul_smul, h2]

noncomputable def fi24PiFun (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (j : Fin 24) : Fin 24 :=
  Classical.choose (exists_smul_bbarPt n.2 j)

theorem bbarPt_fi24PiFun (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (j : Fin 24) :
    bbarPt (fi24PiFun n j) = jR n • bbarPt j :=
  Classical.choose_spec (exists_smul_bbarPt n.2 j)

theorem fi24PiFun_mul (n m : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (j : Fin 24) :
    fi24PiFun (n * m) j = fi24PiFun n (fi24PiFun m j) :=
  bbarPt_injective (by
    rw [bbarPt_fi24PiFun, bbarPt_fi24PiFun, bbarPt_fi24PiFun, coe_mul, map_mul, mul_smul])

theorem fi24PiFun_one (j : Fin 24) : fi24PiFun 1 j = j :=
  bbarPt_injective (by rw [bbarPt_fi24PiFun, coe_one, map_one, one_smul])

@[expose] noncomputable def fi24Pi : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J) →* Equiv.Perm (Fin 24) where
  toFun n :=
    { toFun := fi24PiFun n
      invFun := fi24PiFun n⁻¹
      left_inv := fun j => by rw [← fi24PiFun_mul, inv_mul_cancel, fi24PiFun_one]
      right_inv := fun j => by rw [← fi24PiFun_mul, mul_inv_cancel, fi24PiFun_one] }
  map_one' := Equiv.ext fi24PiFun_one
  map_mul' n m := Equiv.ext (fi24PiFun_mul n m)

theorem bbarPt_fi24Pi (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (j : Fin 24) :
    bbarPt (fi24Pi n j) = jR n • bbarPt j :=
  bbarPt_fi24PiFun n j

theorem realizes_fi24Pi (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) : Realizes bbar (jR n) (fi24Pi n) :=
  fun j => by rw [bbar, bbar, bbarPt_fi24Pi, cls_smul_R]

theorem fi24Pi_of_realizes {n : CFSG.Sporadic.Fi24.J} {σ : Equiv.Perm (Fin 24)} (h : Realizes bbar (jR n) σ) :
    fi24Pi ⟨n, mem_normalizer_of_realizes h⟩ = σ := by
  refine Equiv.ext fun j => ?_
  apply bbar_injective
  rw [realizes_fi24Pi _ j, h j]

theorem mem_range_of_realizes {r : R} (hr : r ∈ JR) {σ : Equiv.Perm (Fin 24)}
    (h : Realizes bbar r σ) : σ ∈ fi24Pi.range := by
  rw [← range_jR] at hr
  obtain ⟨n, rfl⟩ := hr
  exact ⟨_, fi24Pi_of_realizes h⟩

theorem permE_mem_range (l : Fin 2) : permE l ∈ fi24Pi.range := by
  by_cases hN : normElt l ∈ JR
  · exact mem_range_of_realizes hN (realizes_normElt l)
  · refine mem_range_of_realizes (r := bbar 0 * normElt l) ?_ ?_
    · rw [mul_mem_iff_of_index_two index_JR]
      exact iff_of_false (bbar_not_mem_JR 0) hN
    · have := Realizes.mul bbar realizes_bbar_zero (realizes_normElt l)
      rwa [one_mul] at this


theorem fi24Pi_eq_one_iff {n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)} :
    fi24Pi n = 1 ↔ (n : CFSG.Sporadic.Fi24.J) ∈ fi24E := by
  constructor
  · intro h
    refine mem_fi24E_iff.2 (mem_fi24EB_of_comm fun i => ?_)
    have e := realizes_fi24Pi n i
    rw [h, Equiv.Perm.one_apply] at e
    calc jR n * bbar i = jR n * bbar i * (jR n)⁻¹ * jR n := by group
      _ = bbar i * jR n := by rw [← e]
  · intro h
    refine Equiv.ext fun j => ?_
    rw [Equiv.Perm.one_apply]
    apply bbarPt_injective
    rw [bbarPt_fi24Pi, smul_bbarPt_of_mem (mem_fi24E_iff.1 h)]

theorem ker_fi24Pi : fi24Pi.ker = fi24E.subgroupOf (normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) := by
  ext n
  rw [MonoidHom.mem_ker, fi24Pi_eq_one_iff, mem_subgroupOf]

end Pi

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
