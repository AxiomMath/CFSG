module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusHall
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusEdge

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

variable {G₀ G₁ G₂ : Subgroup G}

theorem exists_normalizer_smul_nbrs {ν y : CosetGeom G₀ G₁ G₂} (hy : y ∈ nbrs ν)
    {T : Subgroup G} (hTH : T ≤ stab ν ⊓ stab y)
    (hHT : stab ν ⊓ stab y ≤ Subgroup.normalizer (T : Set G)) (hT : IsPGroup 2 T)
    (hodd : Odd (T.relIndex (stab ν ⊓ stab y))) {X : Subgroup G} (hX : IsEdgeHall ν y X)
    (hXy : X ≤ ballStab 1 y) {e e' : CosetGeom G₀ G₁ G₂} (he : e ∈ nbrs y) (he' : e' ∈ nbrs y) :
    ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y ∧ n • e = e' := by
  set H : Subgroup G := stab ν ⊓ stab y with hH
  set K : Subgroup G := ballStab 1 y with hK
  have hKν : K ≤ stab ν := by
    rw [hK]
    exact CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := y) (δ := ν)
      (CosetGeom.dist_eq_one_iff_adj.mpr hy.symm).le
  have hKH : K ≤ H := by
    intro x hx
    refine ⟨hKν hx, ?_⟩
    rw [hK] at hx
    exact CosetGeom.ballStab_le_stab 1 y hx
  have hTK : T ⊓ K ≤ K := inf_le_right
  have hKT : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun t ht => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHT (hKH hx)) t).mp ht.1
    · exact K.mul_mem (K.mul_mem hx ht.2) (K.inv_mem hx)
  have hodd' : Odd ((T ⊓ K).relIndex K) :=
    odd_relIndex_inf_of_normal_two hTH hHT hodd hKH
  obtain ⟨k, hk⟩ := hX.2.2
  obtain ⟨m, hm⟩ := exists_relIndex_eq_two_pow_of_le hXy hKH hk
  obtain ⟨g, hg, hge⟩ := CosetGeom.stab_transitive_on_nbrs he he'
  have hgK : (g : G) ∈ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact CosetGeom.le_normalizer_ballStab 1 y hg
  obtain ⟨c, hcK, hcN⟩ := exists_mem_mul_normalizer_of_hall hTK hKT
    (hT.to_le inf_le_left) hodd' hXy hX.2.1 hm hgK
  have hcBall : c ∈ ballStab 1 y := hK ▸ hcK
  have hcG : c ∈ G₀ := CosetGeom.stab_le y (CosetGeom.ballStab_le_stab 1 y hcBall)
  have hnG : c⁻¹ * g ∈ G₀ := G₀.mul_mem (G₀.inv_mem hcG) g.2
  have hcy : (⟨c, hcG⟩ : ↥G₀) • y = y :=
    CosetGeom.smul_eq_of_mem_stab (CosetGeom.ballStab_le_stab 1 y hcBall)
  have hcy' : (⟨c, hcG⟩ : ↥G₀)⁻¹ • y = y := inv_smul_eq_iff.mpr hcy.symm
  have hcStabE' : c ∈ stab e' :=
    CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := y) (δ := e')
      (CosetGeom.dist_eq_one_iff_adj.mpr he').le hcBall
  have hce' : (⟨c, hcG⟩ : ↥G₀)⁻¹ • e' = e' :=
    inv_smul_eq_iff.mpr (CosetGeom.smul_eq_of_mem_stab (g := ⟨c, hcG⟩) hcStabE').symm
  have hgy : g • y = y := CosetGeom.smul_eq_of_mem_stab hg
  refine ⟨⟨c⁻¹ * g, hnG⟩, hcN, ?_, ?_⟩
  · show (⟨c⁻¹ * g, hnG⟩ : ↥G₀) • y = y
    have heq : (⟨c⁻¹ * g, hnG⟩ : ↥G₀) = (⟨c, hcG⟩ : ↥G₀)⁻¹ * g := rfl
    rw [heq, mul_smul, hgy, hcy']
  · show (⟨c⁻¹ * g, hnG⟩ : ↥G₀) • e = e'
    have heq : (⟨c⁻¹ * g, hnG⟩ : ↥G₀) = (⟨c, hcG⟩ : ↥G₀)⁻¹ * g := rfl
    rw [heq, mul_smul, hge, hce']

theorem BenderLocal.exists_normalizer_swap {ν : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (hB : BenderLocal ν L) {y y' : CosetGeom G₀ G₁ G₂} (hy : y ∈ nbrs ν) (hy' : y' ∈ nbrs ν)
    (hne : y ≠ y') {T : Subgroup G} (hTH : T ≤ stab ν ⊓ stab y)
    (hHT : stab ν ⊓ stab y ≤ Subgroup.normalizer (T : Set G)) (hT : IsPGroup 2 T)
    (hodd : Odd (T.relIndex (stab ν ⊓ stab y))) {X : Subgroup G} (hX : IsEdgeHall ν y X)
    (hXy' : X ≤ stab y') :
    ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • ν = ν ∧ n • y = y' ∧
      n • y' = y := by
  obtain ⟨g, hgν, hgy, hgy'⟩ := hB.exists_swap hy hy' hne
  have hgνs : g • ν = ν := CosetGeom.smul_eq_of_mem_stab hgν
  set H : Subgroup G := stab ν ⊓ stab y with hH
  set H' : Subgroup G := stab ν ⊓ stab y ⊓ stab y' with hH'
  have hH'H : H' ≤ H := fun _ hx => hx.1
  have hgH' : (g : G) ∈ Subgroup.normalizer (H' : Set G) := by
    apply CosetGeom.mem_normalizer_of_conjSub_eq
    have hν : conjSub (g : G) (stab ν) = stab ν := by
      rw [← CosetGeom.stab_smul g ν, hgνs]
    have hy1 : conjSub (g : G) (stab y) = stab y' := by
      rw [← CosetGeom.stab_smul g y, hgy]
    have hy2 : conjSub (g : G) (stab y') = stab y := by
      rw [← CosetGeom.stab_smul g y', hgy']
    rw [hH', conjSub_inf, conjSub_inf, hν, hy1, hy2, inf_right_comm]
  have hXH' : X ≤ H' := fun x hx => ⟨hX.1 hx, hXy' hx⟩
  have hTH' : T ⊓ H' ≤ H' := inf_le_right
  have hH'T : H' ≤ Subgroup.normalizer ((T ⊓ H' : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun t ht => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHT (hH'H hx)) t).mp ht.1
    · exact H'.mul_mem (H'.mul_mem hx ht.2) (H'.inv_mem hx)
  have hodd' : Odd ((T ⊓ H').relIndex H') :=
    odd_relIndex_inf_of_normal_two hTH hHT hodd hH'H
  obtain ⟨k, hk⟩ := hX.2.2
  obtain ⟨m, hm⟩ := exists_relIndex_eq_two_pow_of_le hXH' hH'H hk
  obtain ⟨c, hcH', hcN⟩ := exists_mem_mul_normalizer_of_hall hTH' hH'T
    (hT.to_le inf_le_left) hodd' hXH' hX.2.1 hm hgH'
  have hcH'1 := hcH'
  rw [hH'] at hcH'1
  have hcν : c ∈ stab ν := hcH'1.1.1
  have hcy : c ∈ stab y := hcH'1.1.2
  have hcy'mem : c ∈ stab y' := hcH'1.2
  have hcG : c ∈ G₀ := CosetGeom.stab_le ν hcν
  have hnG : c⁻¹ * g ∈ G₀ := G₀.mul_mem (G₀.inv_mem hcG) g.2
  have hcνs : (⟨c, hcG⟩ : ↥G₀) • ν = ν := CosetGeom.smul_eq_of_mem_stab hcν
  have hcνs' : (⟨c, hcG⟩ : ↥G₀)⁻¹ • ν = ν := inv_smul_eq_iff.mpr hcνs.symm
  have hcys : (⟨c, hcG⟩ : ↥G₀) • y = y := CosetGeom.smul_eq_of_mem_stab hcy
  have hcys' : (⟨c, hcG⟩ : ↥G₀)⁻¹ • y = y := inv_smul_eq_iff.mpr hcys.symm
  have hcy's : (⟨c, hcG⟩ : ↥G₀) • y' = y' := CosetGeom.smul_eq_of_mem_stab hcy'mem
  have hcy's' : (⟨c, hcG⟩ : ↥G₀)⁻¹ • y' = y' := inv_smul_eq_iff.mpr hcy's.symm
  refine ⟨⟨c⁻¹ * g, hnG⟩, hcN, ?_, ?_, ?_⟩
  · show (⟨c⁻¹ * g, hnG⟩ : ↥G₀) • ν = ν
    have heq : (⟨c⁻¹ * g, hnG⟩ : ↥G₀) = (⟨c, hcG⟩ : ↥G₀)⁻¹ * g := rfl
    rw [heq, mul_smul, hgνs, hcνs']
  · show (⟨c⁻¹ * g, hnG⟩ : ↥G₀) • y = y'
    have heq : (⟨c⁻¹ * g, hnG⟩ : ↥G₀) = (⟨c, hcG⟩ : ↥G₀)⁻¹ * g := rfl
    rw [heq, mul_smul, hgy, hcy's']
  · show (⟨c⁻¹ * g, hnG⟩ : ↥G₀) • y' = y
    have heq : (⟨c⁻¹ * g, hnG⟩ : ↥G₀) = (⟨c, hcG⟩ : ↥G₀)⁻¹ * g := rfl
    rw [heq, mul_smul, hgy', hcys']

end CFSG.Quasithin.F112Crit

end
