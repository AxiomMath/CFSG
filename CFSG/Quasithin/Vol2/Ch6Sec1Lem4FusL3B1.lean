module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section B1

theorem isSylowTwoOf_inf_normal614 {G : Type*} [Group G] [Finite G] {N T : Subgroup G}
    (hN : N.Normal) (hTs : IsSylowTwoOf T (N ⊔ T)) : IsSylowTwoOf (T ⊓ N) N := by
  unfold IsSylowTwoOf at hTs ⊢
  obtain ⟨-, hT2, hodd⟩ := hTs
  refine ⟨inf_le_right, hT2.to_inf_left, ?_⟩
  have hNT : N.relIndex T ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 : (T ⊓ N).relIndex N * N.relIndex (N ⊔ T) = (T ⊓ N).relIndex (N ⊔ T) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left
  have h2 : (T ⊓ N).relIndex T * T.relIndex (N ⊔ T) = (T ⊓ N).relIndex (N ⊔ T) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
  rw [Subgroup.relIndex_sup_left] at h1
  rw [Subgroup.inf_relIndex_left] at h2
  have key : (T ⊓ N).relIndex N * N.relIndex T = T.relIndex (N ⊔ T) * N.relIndex T := by
    rw [h1, ← h2]
    exact mul_comm _ _
  have heq : (T ⊓ N).relIndex N = T.relIndex (N ⊔ T) := mul_right_cancel₀ hNT key
  show ¬ 2 ∣ (T ⊓ N).relIndex N
  rw [heq]
  exact hodd

theorem leviOfL3_conj {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (g u : G) :
    leviOfL3 N (g * u * g⁻¹) = (leviOfL3 N u).map (MulAut.conj g).toMonoidHom := by
  have hA : N ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set G) =
      (N ⊓ Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hxN, hxC⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC
      refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · have h := hN.conj_mem x hxN g⁻¹
        rwa [inv_inv] at h
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * u * g⁻¹ * x) * g := by rw [hxC]
          _ = u * (g⁻¹ * x * g) := by group
      · show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwN, hwC⟩ := Subgroup.mem_inf.mp hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hwC
      refine Subgroup.mem_inf.mpr ⟨hN.conj_mem w hwN g, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show g * w * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * u * g⁻¹) = g * (w * u) * g⁻¹ := by group
        _ = g * (u * w) * g⁻¹ := by rw [hwC]
        _ = g * u * g⁻¹ * (g * w * g⁻¹) := by group
  unfold leviOfL3
  rw [Subgroup.map_commutator, ← hA]

theorem conj_eq_of_normalizes_zpowers614 {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    {p : ℕ} (hp5 : 5 < p) (h : L3FusFacts N p) {y z g : G} (hyN : y ∈ N) (hy5 : orderOf y = 5)
    (hzN : z ∈ N) (hz2 : orderOf z = 2) (hyz : y ∈ leviOfL3 N z) (hcz : Commute z y)
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) : g * z * g⁻¹ = z := by
  have hgy : g⁻¹ * y * g ∈ Subgroup.zpowers y := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp
      (Subgroup.mem_zpowers y)
    rwa [inv_inv] at h1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hgy
  have hyw : (g * y * g⁻¹) ^ m = y := by
    rw [conj_zpow, hm]
    group
  have hz'N : g * z * g⁻¹ ∈ N := hN.conj_mem z hzN g
  have hz'2 : orderOf (g * z * g⁻¹) = 2 := by
    have h2 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
    rw [hz2] at h2
    exact h2
  have hcz' : Commute (g * z * g⁻¹) y := by
    have hc : Commute (g * z * g⁻¹) (g * y * g⁻¹) := hcz.map (MulAut.conj g)
    have hc' := hc.zpow_right m
    rwa [hyw] at hc'
  have hmem : g * y * g⁻¹ ∈ leviOfL3 N (g * z * g⁻¹) := by
    rw [leviOfL3_conj hN g z]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hyz
  have hyz' : y ∈ leviOfL3 N (g * z * g⁻¹) := by
    have h3 := zpow_mem hmem m
    rwa [hyw] at h3
  exact h.uniq hp5 y hyN hy5 (g * z * g⁻¹) hz'N z hzN hz'2 hz2 hcz' hcz hyz' hyz

end B1

end CFSG.Quasithin.H13
