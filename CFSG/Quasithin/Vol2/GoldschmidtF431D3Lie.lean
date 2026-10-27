module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Cent
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutSetting

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Lie


theorem d3T_le_autStab_H : d3T ≤ autStab d4H := by
  rintro _ ⟨u, hu, rfl⟩
  exact conj_mem_autStab (d4U_le_d4H hu)

theorem d3T_le_autStab_N : d3T ≤ autStab d4N := by
  rintro _ ⟨u, hu, rfl⟩
  exact conj_mem_autStab (d4U_le_d4B hu).2

theorem d3_sylow (hs : IsSimpleGroup D)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) :
    IsSylowTwoOf d3T (⊤ : Subgroup (MulAut D)) := by
  have hinj := conj_injective hs
  refine ⟨le_top, d4_sylow.2.1.of_equiv (Subgroup.equivMapOfInjective d4U MulAut.conj hinj), ?_⟩
  change ¬ 2 ∣ d3T.relIndex ⊤
  have hle : d3T ≤ (MulAut.conj : D →* MulAut D).range := Subgroup.map_le_range _ _
  have key := Subgroup.relIndex_mul_index hle
  have h1 : d3T.relIndex (MulAut.conj : D →* MulAut D).range = d4U.relIndex ⊤ := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  rw [Subgroup.relIndex_top_right, ← key, h1]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
  · exact d4_sylow.2.2 h
  · exact hodd h

theorem orderOf_d3z (hs : IsSimpleGroup D) : orderOf d3z = 2 := by
  rw [d3z, orderOf_conj (conj_injective hs), orderOf_d4z]

theorem orderOf_d3t (hs : IsSimpleGroup D) : orderOf d3t = 2 := by
  rw [d3t, orderOf_conj (conj_injective hs), orderOf_d4t]

theorem d3_not_conj_zt (hs : IsSimpleGroup D) : ¬ IsConj d3z d3t := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [d3z, d3t, aut_mul_conj_inv] at hc
  have h1 : c d4z = d4t := conj_injective hs hc
  obtain ⟨c', hc'⟩ := exists_aut_d4z c
  exact d4_not_conj_zt (isConj_iff.2 ⟨c', by rw [← hc', h1]⟩)

theorem mem_range_conj_of_orderOf_two
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) {x : MulAut D}
    (hx : orderOf x = 2) : x ∈ (MulAut.conj : D →* MulAut D).range := by
  have := normal_conj_range D
  have hsq : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  let π := QuotientGroup.mk' (MulAut.conj : D →* MulAut D).range
  have h1 : orderOf (π x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hsq, map_one])
  have h2 : orderOf (π x) ∣ (MulAut.conj : D →* MulAut D).range.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.gcd 2 (MulAut.conj : D →* MulAut D).range.index = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have h3 : orderOf (π x) = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem d3_classes (hs : IsSimpleGroup D)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) :
    ∀ x : MulAut D, orderOf x = 2 → IsConj d3z x ∨ IsConj d3t x := by
  intro x hx
  obtain ⟨g, rfl⟩ := mem_range_conj_of_orderOf_two hodd hx
  have hg : orderOf g = 2 := by
    rw [← orderOf_conj (conj_injective hs) g]
    exact hx
  obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hg
  · exact Or.inl (MonoidHom.map_isConj MulAut.conj (isConj_iff.2 ⟨c, hc.symm⟩))
  · exact Or.inr (MonoidHom.map_isConj MulAut.conj (isConj_iff.2 ⟨c, hc.symm⟩))

theorem d3_cent_z (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z) :
    Subgroup.centralizer ({d3z} : Set (MulAut D)) = autStab d4H := by
  ext α
  rw [d3z, mem_centralizer_conj_iff (conj_injective hs), mem_autStab_H_iff_cu hCU]

section T


theorem d3_cent_t (hs : IsSimpleGroup D) :
    Subgroup.centralizer ({d3t} : Set (MulAut D)) ≤ autStab d4N := by
  intro α hα
  rw [d3t, mem_centralizer_conj_iff (conj_injective hs)] at hα
  exact mem_autStab_N_of_fix_t hα

end T

theorem d3_center_T (hs : IsSimpleGroup D) : ∀ w ∈ d3T, (∀ y ∈ d3T, y * w = w * y) → w ≠ 1 →
    ∃ m ∈ autStab d4H ⊓ autStab d4N, m * d3z * m⁻¹ = w := by
  intro w hw hc hw1
  obtain ⟨u, hu, rfl⟩ := mem_d3T_iff.1 hw
  have hinj := conj_injective hs
  have hu1 : u ≠ 1 := fun h => hw1 (by rw [h, map_one])
  have hcu : ∀ y ∈ d4U, y * u = u * y := fun y hy =>
    hinj (by rw [map_mul, map_mul]; exact hc _ (conj_mem_d3T hy))
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  rw [center_T_spec hu hcu hu1]
  simp [d3z]

theorem invStep_conj {i j : D} (h : InvStep d4U d4H d4N i j) :
    InvStep d3T (autStab d4H) (autStab d4N) (MulAut.conj i) (MulAut.conj j) := by
  obtain ⟨hi, hj, c, hc, hjc⟩ := h
  refine ⟨conj_mem_d3T hi, conj_mem_d3T hj, MulAut.conj c, ?_, ?_⟩
  · rcases hc with hc | hc
    · exact Or.inl (conj_mem_autStab hc)
    · exact Or.inr (conj_mem_autStab hc)
  · rw [hjc]
    simp [map_mul, map_inv]

theorem d3_inv_chain (hs : IsSimpleGroup D) : ∀ i ∈ d3T, orderOf i = 2 →
    Relation.ReflTransGen (InvStep d3T (autStab d4H) (autStab d4N)) d3z i ∨
      Relation.ReflTransGen (InvStep d3T (autStab d4H) (autStab d4N)) d3t i := by
  intro i hi hio
  obtain ⟨u, hu, rfl⟩ := mem_d3T_iff.1 hi
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_conj (conj_injective hs) u]
    exact hio
  rcases inv_chain_spec u hu hu2 with h | h
  · exact Or.inl (Relation.ReflTransGen.lift (⇑(MulAut.conj : D →* MulAut D))
      (fun _ _ h => invStep_conj h) _ _ h)
  · exact Or.inr (Relation.ReflTransGen.lift (⇑(MulAut.conj : D →* MulAut D))
      (fun _ _ h => invStep_conj h) _ _ h)

end Lie

section Main


theorem d3_F431LieI (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) :
    F431LieI d3T (autStab d4H) (autStab d4N) d3z d3t where
  sylow := d3_sylow hs hodd
  T_le₁ := d3T_le_autStab_H
  T_le₂ := d3T_le_autStab_N
  z_mem := d3z_mem_d3T
  t_mem := d3t_mem_d3T
  hz := orderOf_d3z hs
  ht := orderOf_d3t hs
  not_conj := d3_not_conj_zt hs
  classes := d3_classes hs hodd
  cent_z := d3_cent_z hs hCU
  cent_t := d3_cent_t hs
  center_T := d3_center_T hs
  inv_chain := d3_inv_chain hs

end Main

end CFSG.Quasithin.D4Hex
