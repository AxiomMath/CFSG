module

public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_lA {E K : Subgroup G} {e : G} (hK : K ∈ lA E e)
    (he3 : e ^ 3 = 1) (heK : e ∉ K) {b : G} (hbE : b ∈ E) (hbK : b ∈ K) (hb1 : b ≠ 1)
    {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxe : x * e = e * x) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have hxe' : x * e * x⁻¹ = e := by rw [hxe, mul_inv_cancel_right]
  have hK' : K.map (MulAut.conj x).toMonoidHom ∈ lA E e := by
    have h := (CFSG.RankThree.PartTwo.Sec13.map_conj_mem_lA_iff (c := e) (L := K) hxE).mpr hK
    rwa [hxe'] at h
  by_contra hxK
  set K' : Subgroup G := K.map (MulAut.conj x).toMonoidHom with hK'def
  set N₀ : Subgroup G := Subgroup.normalizer (Subgroup.zpowers e : Set G) with hN₀def
  have hne : K' ≠ K := fun h =>
    hxK ((CFSG.RankThree.PartTwo.Sec13.map_conj_eq_iff_mem_normalizer (H := K) (g := x)).mp h)
  have hKN : K ≤ N₀ := le_normalizer_zpowers_of_mem hK.1
  have hK'N : K' ≤ N₀ := le_normalizer_zpowers_of_mem hK'.1
  have hKs := subgroupOf_normalizer_mem_thetaComponents hK.1
  have hK's := subgroupOf_normalizer_mem_thetaComponents hK'.1
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N₀) with hπdef
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hKs
  have hK'c := isComponent_map_of_mem_thetaComponents Nat.prime_three hK's
  have hne₁ : K.subgroupOf N₀ ≠ K'.subgroupOf N₀ := by
    intro h
    apply hne
    have h' := congrArg (Subgroup.map N₀.subtype) h
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKN, inf_eq_left.mpr hK'N] at h'
    exact h'.symm
  have hneb : (K.subgroupOf N₀).map π ≠ (K'.subgroupOf N₀).map π := fun h =>
    hne₁ ((theta_component_quotient_correspondence Nat.prime_three).1.injOn hKs hK's h)
  have hcomm : ⁅(K.subgroupOf N₀).map π, (K'.subgroupOf N₀).map π⁆ = ⊥ :=
    (LocalCores.distinct_components_commute hKc hK'c).resolve_left hneb
  have hcommElt : ∀ u ∈ (K.subgroupOf N₀).map π, ∀ v ∈ (K'.subgroupOf N₀).map π,
      v * u = u * v := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu) v hv
  have hb'E : x * b * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxE b).mp hbE
  have hb'K' : x * b * x⁻¹ ∈ K' := Subgroup.mem_map.mpr ⟨b, hbK, rfl⟩
  have hb'N : x * b * x⁻¹ ∈ N₀ := hK'N hb'K'
  have hθK : ∀ k ∈ K, x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹ ∈
      (aschbacherSolvableCore 3 K).map K.subtype := by
    intro k hk
    have hkN : k ∈ N₀ := hKN hk
    have hcK : x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK.2.1 hb'E) k).mp hk) (K.inv_mem hk)
    have hcN : x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹ ∈ N₀ :=
      N₀.mul_mem (N₀.mul_mem (N₀.mul_mem hb'N hkN) (N₀.inv_mem hb'N)) (N₀.inv_mem hkN)
    have hu : π ⟨k, hkN⟩ ∈ (K.subgroupOf N₀).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
    have hv : π ⟨x * b * x⁻¹, hb'N⟩ ∈ (K'.subgroupOf N₀).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb'K')
    have huv := hcommElt _ hu _ hv
    have hπc : π ⟨x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹, hcN⟩ = 1 := by
      have heq : (⟨x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹, hcN⟩ : N₀) =
          ⟨x * b * x⁻¹, hb'N⟩ * ⟨k, hkN⟩ * ⟨x * b * x⁻¹, hb'N⟩⁻¹ * ⟨k, hkN⟩⁻¹ := rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, huv, mul_inv_cancel_right,
        mul_inv_cancel]
    have hθc : (⟨x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹, hcN⟩ : N₀) ∈
        aschbacherSolvableCore 3 N₀ := (QuotientGroup.eq_one_iff _).mp hπc
    have hΘc : x * b * x⁻¹ * k * (x * b * x⁻¹)⁻¹ * k⁻¹ ∈
        (aschbacherSolvableCore 3 N₀).map N₀.subtype :=
      Subgroup.mem_map.mpr ⟨_, hθc, rfl⟩
    exact inf_inSubgroup_theta_le hKN ⟨hcK, hΘc⟩
  have hmemZ : x * b * x⁻¹ ∈ (Subgroup.zpowers e : Set G) := by
    rw [← hK.2.2.1]
    exact ⟨hb'E, hθK⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmemZ
  have hconj : x⁻¹ * e ^ n * x = e ^ n := by
    have h := (Commute.zpow_right (show Commute x e from hxe) n).inv_left
    rw [h.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hb_eq : b = x⁻¹ * e ^ n * x := by
    rw [hn]
    group
  have hbz : b ∈ Subgroup.zpowers e := by
    rw [hb_eq, hconj]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hbm : b ∈ Subgroup.zpowers e ⊓ K := Subgroup.mem_inf.mpr ⟨hbz, hbK⟩
  rw [CFSG.RankThree.PartTwo.Sec13.zpowers_inf_eq_bot he3 heK, Subgroup.mem_bot] at hbm
  exact hb1 hbm

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
