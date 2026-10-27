module

public import CFSG.Quasithin.H13.KG14726Core

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup
open scoped Pointwise

variable {M : Type*} [Group M] {P S C J : Subgroup M}

theorem mem_of_mem_centralizer_localPair {z : M}
    (hcen : ((center S).map S.subtype : Set M) = {1, z})
    (hC : C = P ⊓ centralizer ((center S).map S.subtype : Set M)) (hzP : z ∈ P) {c : ↥P}
    (hc : c ∈ centralizer ({(⟨z, hzP⟩ : ↥P)} : Set ↥P)) : (c : M) ∈ C := by
  rw [hC]
  refine mem_inf.mpr ⟨c.2, mem_centralizer_iff.mpr ?_⟩
  intro y hy
  have hy' : y ∈ ({1, z} : Set M) := by rw [← hcen]; exact hy
  rcases hy' with rfl | rfl
  · simp
  · have := mem_centralizer_singleton_iff.mp hc
    exact (congrArg Subtype.val this).symm

theorem constrainedAt_localPair {z : M} (hcen : ((center S).map S.subtype : Set M) = {1, z})
    (hC : C = P ⊓ centralizer ((center S).map S.subtype : Set M)) (hzP : z ∈ P)
    (hJp : IsPGroup 2 J) (hJC : J ≤ C) (hJn : (J.subgroupOf C).Normal)
    (hCJ : C ⊓ centralizer (J : Set M) ≤ J) : ConstrainedAt (⟨z, hzP⟩ : ↥P) := by
  have hCP : C ≤ P := hC ▸ inf_le_left
  have hJP : J ≤ P := hJC.trans hCP
  have hCz : ∀ x ∈ C, x * z = z * x := by
    intro x hx
    rw [hC] at hx
    have hz : z ∈ ((center S).map S.subtype : Set M) := by
      rw [hcen]
      exact Set.mem_insert_of_mem _ rfl
    exact (mem_centralizer_iff.mp (mem_inf.mp hx).2 z hz).symm
  refine ⟨J.subgroupOf P, hJp.comap_of_injective _ P.subtype_injective, ?_, ?_, ?_⟩
  · intro q hq
    rw [mem_subgroupOf] at hq
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hCz _ (hJC hq))
  · intro c hc q hq
    rw [mem_subgroupOf] at hq ⊢
    have hcC := mem_of_mem_centralizer_localPair hcen hC hzP hc
    have := hJn.conj_mem ⟨(q : M), hJC hq⟩ hq ⟨c, hcC⟩
    simpa [mem_subgroupOf] using this
  · intro c hc hcQ
    rw [mem_subgroupOf]
    refine hCJ ⟨mem_of_mem_centralizer_localPair hcen hC hzP hc, mem_centralizer_iff.mpr
      fun j hj => ?_⟩
    have := hcQ ⟨j, hJP hj⟩ (by rw [mem_subgroupOf]; exact hj)
    exact (congrArg Subtype.val this).symm

theorem twoCentralConstrained_of_localPair [Finite P] (hSP : S ≤ P)
    (hSyl : ∃ T : Sylow 2 ↥P, (T : Subgroup ↥P) = S.subgroupOf P) {z : M}
    (hcen : ((center S).map S.subtype : Set M) = {1, z})
    (hC : C = P ⊓ centralizer ((center S).map S.subtype : Set M))
    (hJp : IsPGroup 2 J) (hJC : J ≤ C) (hJn : (J.subgroupOf C).Normal)
    (hCJ : C ⊓ centralizer (J : Set M) ≤ J) : TwoCentralConstrained ↥P := by
  have hzS : z ∈ S := by
    have hz : z ∈ ((center S).map S.subtype : Set M) := by
      rw [hcen]
      exact Set.mem_insert_of_mem _ rfl
    obtain ⟨y, -, hy⟩ := hz
    rw [← hy]
    exact y.2
  have hzP : z ∈ P := hSP hzS
  have hconstr := constrainedAt_localPair hcen hC hzP hJp hJC hJn hCJ
  intro T t hT hTi htT htc ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hSyl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P P₀ (hT.toSylow hTi)
  have hTg : T = MulAut.conj g • (P₀ : Subgroup ↥P) := by
    have := congrArg (fun Q : Sylow 2 ↥P => (Q : Subgroup ↥P)) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  set p : ↥P := g⁻¹ * t * g with hpdef
  have hpP : p ∈ (P₀ : Subgroup ↥P) := by
    rw [hTg, mem_pointwise_smul_iff_inv_smul_mem] at htT
    simpa [hpdef, MulAut.conj_apply, mul_assoc] using htT
  have hpc : ∀ x ∈ (P₀ : Subgroup ↥P), x * p = p * x := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ T := by
      rw [hTg]
      exact ⟨x, hx, rfl⟩
    have h1 := htc _ hx'
    calc x * p = g⁻¹ * ((g * x * g⁻¹) * t) * g := by rw [hpdef]; group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [h1]
      _ = p * x := by rw [hpdef]; group
  have hpS : (p : M) ∈ S := by
    rw [hP₀, mem_subgroupOf] at hpP
    exact hpP
  have hpZ : (⟨p, hpS⟩ : ↥S) ∈ center S := by
    rw [mem_center_iff]
    intro y
    have hy : (⟨y, hSP y.2⟩ : ↥P) ∈ (P₀ : Subgroup ↥P) := by
      rw [hP₀, mem_subgroupOf]
      exact y.2
    have h2 := congrArg Subtype.val (hpc _ hy)
    exact Subtype.ext h2
  have hp1 : (p : M) ∈ ({1, z} : Set M) := by
    rw [← hcen]
    exact ⟨_, hpZ, rfl⟩
  have hpord : orderOf p = 2 := by
    rw [hpdef, show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq]
    exact ht
  have hpz : p = ⟨z, hzP⟩ := by
    rcases hp1 with h | h
    · exfalso
      have : p = 1 := Subtype.ext h
      rw [this, orderOf_one] at hpord
      norm_num at hpord
    · exact Subtype.ext h
  have htg : t = MulAut.conj g ⟨z, hzP⟩ := by
    rw [← hpz, MulAut.conj_apply, hpdef]
    group
  rw [htg]
  exact hconstr.map (MulAut.conj g)

end CFSG.Quasithin.H13.KG14726

end
