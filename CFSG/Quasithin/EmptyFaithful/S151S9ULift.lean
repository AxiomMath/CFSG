module

public import CFSG.Quasithin.EmptyFaithful.S151S9UPerf

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

open scoped commutatorElement

section Central

variable {X : Type*} [Group X]

theorem eq_bot_of_perfect_of_le_center {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hc : K ≤ Subgroup.center X) : K = ⊥ := by
  have h : ⁅K, K⁆ ≤ ⊥ := by
    refine Subgroup.commutator_le.mpr fun x hx y _ => ?_
    exact Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hc hx) y).symm)
  exact eq_bot_iff.mpr (hK.symm.le.trans h)

theorem commutatorElement_mul_central_mul_central {x y c d : X} (hc : c ∈ Subgroup.center X)
    (hd : d ∈ Subgroup.center X) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
  have hd' : ∀ g, d * g = g * d := fun g => (Subgroup.mem_center_iff.mp hd g).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹
      = x * (y * d * c) * (c⁻¹ * x⁻¹) * (d⁻¹ * y⁻¹) := by
        rw [mul_inv_rev, mul_inv_rev, mul_assoc x c (y * d), hc' (y * d)]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [hd' x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem exists_mul_mem_ker {Q : Type*} [Group Q] (π : X →* Q) {J K : Subgroup X}
    (hJK : K.map π ≤ J.map π) {x : X} (hx : x ∈ K) : ∃ j ∈ J, ∃ c ∈ π.ker, x = j * c := by
  obtain ⟨j, hj, hjx⟩ := hJK (Subgroup.mem_map_of_mem π hx)
  refine ⟨j, hj, j⁻¹ * x, ?_, (mul_inv_cancel_left j x).symm⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hjx, inv_mul_cancel]

end Central

theorem perfCore_of_map {X Q : Type} [Group X] [Finite X] [Group Q] [Finite Q] (π : X →* Q)
    (hker : π.ker ≤ Subgroup.center X) {M B : Subgroup X} (hkB : π.ker ≤ B) (hBM : B ≤ M)
    (h : PerfCore (B.map π) (M.map π)) : PerfCore B M := by
  obtain ⟨hne, hcomp, hsup⟩ := h
  have hmap : (perfectCore M).map π = perfectCore (M.map π) := map_perfectCore π M
  have hK : perfectCore M ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.map_bot] at hmap
    exact hne hmap.symm
  refine ⟨hK, ⟨hK, perfectCore_perfect M, IsSubnormal.refl _, ?_⟩, ?_⟩
  · intro J hJK hJne hJperf hJsub
    have hJbarperf : ⁅J.map π, J.map π⁆ = J.map π := by
      rw [← Subgroup.map_commutator, hJperf]
    have hJbarsub : IsSubnormal (J.map π) (perfectCore (M.map π)) := by
      rw [← hmap]
      exact A3.subnormal_map π hJsub
    have hJbarle : J.map π ≤ perfectCore (M.map π) := by
      rw [← hmap]
      exact Subgroup.map_mono hJK.le
    by_cases hJbar : J.map π = ⊥
    · exact hJne (eq_bot_of_perfect_of_le_center hJperf
        fun x hx => hker ((Subgroup.map_eq_bot_iff J).mp hJbar hx))
    · have heq : J.map π = perfectCore (M.map π) := by
        by_contra hne'
        exact not_subnormal_of_mem_cComp hcomp (lt_of_le_of_ne hJbarle hne') hJbar hJbarperf
          hJbarsub
      have hle : perfectCore M ≤ J := by
        refine (perfectCore_perfect M).symm.le.trans
          (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
        obtain ⟨j, hj, c, hc, rfl⟩ := exists_mul_mem_ker π (hmap.trans heq.symm).le hx
        obtain ⟨j', hj', c', hc', rfl⟩ := exists_mul_mem_ker π (hmap.trans heq.symm).le hy
        rw [commutatorElement_mul_central_mul_central (hker hc) (hker hc')]
        exact hJperf.le (Subgroup.commutator_mem_commutator hj hj')
      exact hJK.not_ge hle
  · refine le_antisymm (sup_le (perfectCore_le M) hBM) fun x hx => ?_
    have hx' : π x ∈ (perfectCore M ⊔ B).map π := by
      rw [Subgroup.map_sup, hmap, hsup]
      exact Subgroup.mem_map_of_mem π hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    have hc : z⁻¹ * x ∈ B :=
      hkB (by rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel])
    have := Subgroup.mul_mem _ hz (le_sup_right (a := perfectCore M) hc)
    simpa using this

theorem perfCore_lift {G : Type} [Group G] [Finite G] {L M B : Subgroup G} {Q : Type} [Group Q]
    [Finite Q] (π : ↥L →* Q) (hker : π.ker ≤ Subgroup.center ↥L)
    (hker2 : IsPGroup 2 ↥π.ker) (hML : M ≤ L) (hBM : B ≤ M) (hB : IsSylowTwoOf B L)
    (h : PerfCore ((B.subgroupOf L).map π) ((M.subgroupOf L).map π)) :
    perfectCore M ≠ ⊥ ∧ perfectCore M ∈ cComp (perfectCore M) ∧ perfectCore M ⊔ B = M := by
  have hBL : B ≤ L := hB.1
  have hB2 : IsPGroup 2 ↥(B.subgroupOf L) :=
    hB.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  have hkerB : π.ker ≤ B.subgroupOf L := IsPGroup.le_sylow_of_normal hker2 (hB2.toSylow hB.2.2)
  obtain ⟨h1, h2, h3⟩ := perfCore_of_map π hker hkerB (Subgroup.subgroupOf_mono L hBM) h
  have hM : (M.subgroupOf L).map L.subtype = M := Subgroup.map_subgroupOf_eq_of_le hML
  have hB' : (B.subgroupOf L).map L.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBL
  have hK : perfectCore M = (perfectCore (M.subgroupOf L)).map L.subtype := by
    rw [map_perfectCore, hM]
  refine ⟨?_, ?_, ?_⟩
  · rwa [hK, Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
  · rw [hK]
    exact map_mem_cComp_of_injective L.subtype L.subtype_injective h2
  · calc perfectCore M ⊔ B
        = (perfectCore (M.subgroupOf L)).map L.subtype ⊔ (B.subgroupOf L).map L.subtype := by
          rw [← hK, hB']
      _ = (perfectCore (M.subgroupOf L) ⊔ B.subgroupOf L).map L.subtype :=
          (Subgroup.map_sup _ _ _).symm
      _ = M := by rw [h3, hM]

end CFSG.Quasithin.S151S9U
