module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GroupTheory

open Subgroup

theorem le_normalizer_component_of_coprime_action
    {G : Type*} [Group G] [Finite G] {S Y : Subgroup G} {u : G}
    (hS : CFSG.IsComponent S) (huS : u ∈ S)
    (huZ : u ∉ Subgroup.centralizer (S : Set G))
    (huY : u ∈ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (orderOf u) (Nat.card Y)) :
    Y ≤ Subgroup.normalizer (S : Set G) := by
  intro y hy
  by_contra hyN
  have hSy : CFSG.IsComponent (S.map (MulAut.conj y).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hS
  rcases CFSG.LocalCores.distinct_components_commute hS hSy with hEq | hcomm
  · exact hyN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq.symm)
  · have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have huv : (MulAut.conj y) u ∈ S.map (MulAut.conj y) := ⟨u, huS, rfl⟩
    have hcomm_uv : Commute u ((MulAut.conj y) u) :=
      ((Subgroup.mem_centralizer_iff.mp (hcent huS)) ((MulAut.conj y) u) huv).symm
    let c : G := u * ((MulAut.conj y) u)⁻¹
    have hcY : c ∈ Y := by
      have hyY : u * y * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp huY y).mp hy
      have hc : c = (u * y * u⁻¹) * y⁻¹ := by
        simp [c, MulAut.conj_apply, mul_assoc]
      rw [hc]
      exact Y.mul_mem hyY (Y.inv_mem hy)
    have hc_pow : c ^ orderOf u = 1 := by
      have hv : ((MulAut.conj y) u) ^ orderOf u = 1 := by
        simp
      calc
        c ^ orderOf u = (u * ((MulAut.conj y) u)⁻¹) ^ orderOf u := rfl
        _ = u ^ orderOf u * (((MulAut.conj y) u)⁻¹) ^ orderOf u :=
          hcomm_uv.inv_right.mul_pow _
        _ = 1 * (((MulAut.conj y) u) ^ orderOf u)⁻¹ := by
          rw [pow_orderOf_eq_one, inv_pow]
        _ = 1 := by rw [hv, inv_one, mul_one]
    have hdvd₁ : orderOf c ∣ orderOf u := orderOf_dvd_of_pow_eq_one hc_pow
    have hdvd₂ : orderOf c ∣ Nat.card Y := Y.orderOf_dvd_natCard hcY
    have hc1 : c = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd₁ hdvd₂)
    have hueq : u = (MulAut.conj y) u := by
      exact mul_inv_eq_one.mp (show u * ((MulAut.conj y) u)⁻¹ = 1 from hc1)
    have huSy : u ∈ S.map (MulAut.conj y) := by
      rw [hueq]
      exact ⟨u, huS, rfl⟩
    apply huZ
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hcent hs)) u huSy).symm

theorem mixed_commutator_eq_bot_of_component_action
    {G : Type*} [Group G] [Finite G] {S Y E F : Subgroup G} {u : G}
    (hS : CFSG.IsComponent S)
    (huS : u ∈ S)
    (huZ : u ∉ Subgroup.centralizer (S : Set G))
    (huY : u ∈ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (orderOf u) (Nat.card Y))
    (hFS : F ≤ S)
    (hES : E ≤ Subgroup.centralizer (S : Set G)) :
    ⁅⁅Y, E⁆, F⁆ = ⊥ := by
  have hYN : Y ≤ Subgroup.normalizer (S : Set G) :=
    le_normalizer_component_of_coprime_action hS huS huZ huY hcop
  have hSYS : ⁅S, Y⁆ ≤ S :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hYN
  have hFYS : ⁅F, Y⁆ ≤ S :=
    (Subgroup.commutator_mono hFS le_rfl).trans hSYS
  have hESbot : ⁅E, S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hES
  have hEF : ⁅E, F⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅E, F⁆ ≤ ⁅E, S⁆ := Subgroup.commutator_mono le_rfl hFS
      _ = ⊥ := hESbot
  have h1 : ⁅⁅E, F⁆, Y⁆ = ⊥ := by
    rw [hEF, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅F, Y⁆, E⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅F, Y⁆, E⁆ ≤ ⁅S, E⁆ := Subgroup.commutator_mono hFYS le_rfl
      _ = ⁅E, S⁆ := Subgroup.commutator_comm S E
      _ = ⊥ := hESbot
  exact Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Y) (H₂ := E) (H₃ := F) h1 h2

end CFSG.GroupTheory
