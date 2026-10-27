module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Inter

public section

namespace CFSG.Quasithin.H13.GM22.CaseA3

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] {T L V D : Subgroup G} {z : G}
  {φ : ↥(NV V) →* Equiv.Perm (Fin 5)}

namespace Setup

variable (C : Setup T L V D z φ) {d₀ : G} (hd : IsD0 T L z d₀)

include C hd in
theorem not_fixed {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : d₀ * v * d₀⁻¹ ≠ v := by
  intro hfix
  obtain ⟨m, hmL, hm⟩ := C.transitive z C.z_mem v hv C.z_ne_one hv1
  have hmN : m ∈ NV V := C.L_le hmL
  have hdN : d₀ ∈ NV V := C.L_le hd.mem_L
  have hc : m⁻¹ * d₀ * m ∈ T := by
    refine C.centralizer_le _ ((NV V).mul_mem ((NV V).mul_mem ((NV V).inv_mem hmN) hdN) hmN) ?_
    have e1 : z = m⁻¹ * v * m := by rw [← hm]; group
    have hcomm : d₀ * v = v * d₀ := mul_inv_eq_iff_eq_mul.mp hfix
    calc m⁻¹ * d₀ * m * z = m⁻¹ * (d₀ * v) * m := by rw [e1]; group
      _ = m⁻¹ * (v * d₀) * m := by rw [hcomm]
      _ = z * (m⁻¹ * d₀ * m) := by rw [e1]; group
  have hord : orderOf (m⁻¹ * d₀ * m) = orderOf d₀ := by
    have := MulEquiv.orderOf_eq (MulAut.conj m⁻¹) d₀
    simpa [MulAut.conj_apply] using this
  exact orderOf_ne_prime_of_isPGroup C.isPGroup_T hc hd.prime hd.ne_two hord

variable [Finite G] in
include C hd in
theorem not_normalizes_V0 : ¬ ∀ v ∈ V ⊓ D, d₀ * v * d₀⁻¹ ∈ V ⊓ D := by
  intro hall
  have hnz := d0_mem_normalizer_zs C hd
  have hsub : ((zs T L V : Subgroup G) : Set G) ⊆ ((V ⊓ D : Subgroup G) : Set G) :=
    fun u hu => ⟨hu.1, C.zs_le_D hu⟩
  let S : Set G := ((V ⊓ D : Subgroup G) : Set G) \ ((zs T L V : Subgroup G) : Set G)
  have hScard : S.ncard = 4 := by
    rw [Set.ncard_sdiff hsub]
    have h1 : ((V ⊓ D : Subgroup G) : Set G).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]
      exact C.card_V_inf_D
    have h2 : ((zs T L V : Subgroup G) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact C.card_zs
    omega
  have hS : ∀ v ∈ S, d₀ * v * d₀⁻¹ ∈ S := by
    intro v hv
    refine ⟨hall v hv.1, fun hz => hv.2 ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp hnz v).mpr hz
  obtain ⟨v, hvS, hfix⟩ := exists_fixed_of_prime_order hd.prime hd.ne_two rfl (Set.toFinite S)
    hScard hS
  refine C.not_fixed hd hvS.1.1 (fun h1 => hvS.2 ?_) hfix
  rw [h1]
  exact (zs T L V).one_mem

variable [Finite G] in
include C hd in
theorem inter_V0_le_zs {x : G} (hx : x ∈ V ⊓ D) (hx' : d₀⁻¹ * x * d₀ ∈ V ⊓ D) :
    x ∈ zs T L V := by
  have hzV0 : zs T L V ≤ V ⊓ D := fun u hu => ⟨hu.1, C.zs_le_D hu⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = (V ⊓ D) ⊓ conjSubgroup (V ⊓ D) d₀⁻¹ := ⟨_, rfl⟩
  have hYV0 : Y ≤ V ⊓ D := hY ▸ inf_le_left
  have hzY : zs T L V ≤ Y := by
    rw [hY]
    refine le_inf hzV0 fun u hu => mem_conjSubgroup_iff.mpr ?_
    exact hzV0 (by simpa using inv_conj_mem_zs C hd hu)
  have hdvd8 : Nat.card ↥Y ∣ 8 := C.card_V_inf_D ▸ Subgroup.card_dvd_of_le hYV0
  have hdvd4 : 4 ∣ Nat.card ↥Y := C.card_zs ▸ Subgroup.card_dvd_of_le hzY
  have hcase : Nat.card ↥Y = 4 ∨ Nat.card ↥Y = 8 := by
    have hle8 := Nat.le_of_dvd (by norm_num) hdvd8
    have hpos : 0 < Nat.card ↥Y := Nat.card_pos
    omega
  rcases hcase with h4 | h8
  · have heq : zs T L V = Y := Subgroup.eq_of_le_of_card_ge hzY (by rw [h4, C.card_zs])
    have hxY : x ∈ Y := by
      rw [hY]
      exact ⟨hx, mem_conjSubgroup_iff.mpr (by simpa using hx')⟩
    rwa [← heq] at hxY
  · exfalso
    apply not_normalizes_V0 C hd
    have hYeq : Y = V ⊓ D := Subgroup.eq_of_le_of_card_ge hYV0 (by rw [h8, C.card_V_inf_D])
    have hnorm : d₀ ∈ Subgroup.normalizer ((V ⊓ D : Subgroup G) : Set G) := by
      refine mem_normalizer_of_conj_le fun v hv => ?_
      have hvY : v ∈ Y := by rw [hYeq]; exact hv
      rw [hY] at hvY
      simpa [mem_conjSubgroup_iff] using hvY.2
    exact fun v hv => (Subgroup.mem_normalizer_iff.mp hnorm v).mp hv

variable [Finite G] in
include C in
theorem exists_inter : ∃ d₀ : G, d₀ ∈ L ∧ d₀ * z * d₀⁻¹ ∈ D ∧ d₀ * z * d₀⁻¹ ≠ z ∧
    D ⊓ conjSubgroup D d₀⁻¹ = zs T L V := by
  obtain ⟨d₀, hd⟩ := C.exists_d0
  have hdN := d0_mem_NV C hd
  refine ⟨d₀, hd.mem_L, C.zs_le_D (conj_z_mem_zs C hd), hd.moves, le_antisymm ?_ ?_⟩
  · rintro x ⟨hxD, hxc⟩
    have hxV := inter_mem_V C hd hxD hxc
    have hx' : d₀⁻¹ * x * d₀ ∈ V ⊓ D := by
      refine ⟨?_, by simpa [mem_conjSubgroup_iff] using hxc⟩
      simpa using (Subgroup.mem_normalizer_iff.mp ((NV V).inv_mem hdN) x).mp hxV
    exact inter_V0_le_zs C hd ⟨hxV, hxD⟩ hx'
  · intro u hu
    refine ⟨C.zs_le_D hu, mem_conjSubgroup_iff.mpr ?_⟩
    simpa using C.zs_le_D (inv_conj_mem_zs C hd hu)

end Setup

end CFSG.Quasithin.H13.GM22.CaseA3
