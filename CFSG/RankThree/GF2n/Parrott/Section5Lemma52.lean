module

public import CFSG.RankThree.GF2n.Parrott.Section5Basic
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem card_inf_centralizer_z1
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    Nat.card (H z ⊓ Subgroup.centralizer ({z₁} : Set G) : Subgroup G) = 2 ^ 16 * 3 ^ 4 * 5 := by
  have hcard := Subgroup.relIndex_mul_card
    (H z ⊓ Subgroup.centralizer ({z₁} : Set G)) (H z)
  rw [inf_eq_left.mpr inf_le_left, relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord,
    card_H_eq h] at hcard
  norm_num at hcard ⊢
  omega

private theorem factorization_card_inf_centralizer_z1
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    (Nat.card (H z ⊓ Subgroup.centralizer ({z₁} : Set G) : Subgroup G)).factorization 2 = 16 := by
  rw [card_inf_centralizer_z1 h hZ hz₁ hz₁z hord]
  have h35 : (3 ^ 4 * 5 : ℕ).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have hsplit : (2 ^ 16 * 3 ^ 4 * 5 : ℕ) = 2 ^ 16 * (3 ^ 4 * 5) := by ring
  rw [hsplit, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, h35, add_zero]

theorem centerIn_eq_of_isSylowOf_inf_centralizer_z1 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (Y : Subgroup G) (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({z₁} : Set G))) :
    centerIn Y = centerIn (J z) := by
  let C : Subgroup G := H z ⊓ Subgroup.centralizer ({z₁} : Set G)
  have hJC : J z ≤ C := by
    intro j hj
    exact Subgroup.mem_inf.mpr ⟨J_le_H hj,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hz₁.2 j hj)⟩
  have hCN : C ≤ Subgroup.normalizer (J z : Set G) := by
    have hHnorm : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z)
    intro x hx
    exact hHnorm hx.1
  have hJY : J z ≤ Y :=
    le_isSylowOf_of_isPGroup_of_le_normalizer hY hJC hCN (isPGroup_J h)
  have hYH : Y ≤ H z := hY.le.trans inf_le_left
  have hYC : Y ≤ Subgroup.centralizer ({z₁} : Set G) := hY.le.trans inf_le_right
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H z := hYH hx.1
    have hxJ : x ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_iff.mp hx.2 j (hJY hj)
    rw [← centralizer_J_eq_centerIn h]
    exact ⟨hxH, hxJ⟩
  · intro x hx
    have hxY : x ∈ Y := hJY hx.1
    refine ⟨hxY, ?_⟩
    have hzC : z ∈ Subgroup.centralizer (Y : Set G) :=
      Subgroup.centralizer_le hYH (z_centralizes_H h)
    have hz₁C : z₁ ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hzC
    · exact hz₁C
    · exact Subgroup.mul_mem _ hzC hz₁C

theorem isSylowOf_centralizer_z1 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (Y : Subgroup G) (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({z₁} : Set G))) :
    IsSylowOf 2 Y (centralizer ({z₁} : Set G)) := by
  have hZY : centerIn Y = centerIn (J z) :=
    centerIn_eq_of_isSylowOf_inf_centralizer_z1 h hz₁ hz₁z hord Y hY
  refine isSylowOf_of_normalizer_inf_le hY ?_
  rintro n ⟨hnN, _⟩
  rw [← normalizer_centerIn_eq_H (z := z) h, ← hZY]
  simpa [CFSG.centerIn, CFSG.Quasithin.centerOf] using
    (CFSG.Quasithin.H13.C23.mem_normalizer_centerOf hnN)

theorem not_isConj_z_z1 (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) : ¬ IsConj z z₁ := by
  obtain ⟨Y, hY⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({z₁} : Set G))
  have hZY : centerIn Y = centerIn (J z) :=
    centerIn_eq_of_isSylowOf_inf_centralizer_z1 h hz₁ hz₁z hord Y hY
  have hN : ∀ g ∈ Subgroup.centralizer ({z₁} : Set G),
      g ∈ Subgroup.normalizer (Y : Set G) → IsPGroup 2 (Subgroup.zpowers g) → g ∈ H z := by
    intro g _ hgN _
    rw [← normalizer_centerIn_eq_H (z := z) h, ← hZY]
    simpa [CFSG.centerIn, CFSG.Quasithin.centerOf] using
      (CFSG.Quasithin.H13.C23.mem_normalizer_centerOf hgN)
  refine CFSG.GroupTheory.not_isConj_of_isSylowOf_inf_centralizer (p := 2) (K := Y) ?_ ?_ ?_
  · simpa [H_eq_centralizer] using hY
  · simpa [H_eq_centralizer] using hN
  · rw [← H_eq_centralizer, relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord]

private theorem sylow_map_conj_of_sylow {x z₁ : G} {K Y : Subgroup G}
    (hK' : IsSylowOf 2 K (H z ⊓ centralizer ({x} : Set G)))
    (hKcard : Nat.card K = 2 ^ 16)
    (hYtop : IsSylowOf 2 Y (centralizer ({z₁} : Set G)))
    (hYcard : Nat.card Y = 2 ^ 16)
    {g : G} (hgx : g * x * g⁻¹ = z₁) :
    IsSylowOf 2 (K.map (MulAut.conj g).toMonoidHom) (centralizer ({z₁} : Set G)) := by
  have hKg_le : K.map (MulAut.conj g).toMonoidHom ≤ centralizer ({z₁} : Set G) := by
    intro y hy
    obtain ⟨k, hkK, hky⟩ := Subgroup.mem_map.mp hy
    have hkC : k * x = x * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hK'.le hkK)).2
    have hgx' : g⁻¹ * z₁ = x * g⁻¹ := by
      calc g⁻¹ * z₁ = g⁻¹ * (g * x * g⁻¹) := by rw [hgx]
        _ = x * g⁻¹ := by group
    have hky' : g * k * g⁻¹ = y := by simpa [MulAut.conj_apply] using hky
    rw [← hky', Subgroup.mem_centralizer_singleton_iff]
    calc (g * k * g⁻¹) * z₁ = g * k * (g⁻¹ * z₁) := by group
      _ = g * k * (x * g⁻¹) := by rw [hgx']
      _ = g * (k * x) * g⁻¹ := by group
      _ = g * (x * k) * g⁻¹ := by rw [hkC]
      _ = (g * x * g⁻¹) * (g * k * g⁻¹) := by group
      _ = z₁ * (g * k * g⁻¹) := by rw [hgx]
  have hKgcard : Nat.card (K.map (MulAut.conj g).toMonoidHom) = 2 ^ 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hKcard]
  have hCgfac :
      2 ^ (Nat.card (Subgroup.centralizer ({z₁} : Set G))).factorization 2 = 2 ^ 16 := by
    rw [← hYtop.card_eq, hYcard]
  exact isSylowOf_of_card hKg_le (by rw [hKgcard, ← hCgfac])

private theorem exists_conj_map_of_isSylow {x z₁ g : G} {K Y : Subgroup G}
    (hKcard : Nat.card K = 2 ^ 16)
    (hYtop : IsSylowOf 2 Y (centralizer ({z₁} : Set G)))
    (hYcard : Nat.card Y = 2 ^ 16)
    (hKgSylow : IsSylowOf 2 (K.map (MulAut.conj g).toMonoidHom)
      (centralizer ({z₁} : Set G)))
    (hgx : g * x * g⁻¹ = z₁) :
    ∃ k : G, k * x * k⁻¹ = z₁ ∧ K.map (MulAut.conj k).toMonoidHom = Y := by
  let Kg : Subgroup G := K.map (MulAut.conj g).toMonoidHom
  obtain ⟨c, hcC, hc⟩ := hYtop.exists_mem_conj hKgSylow
  let k : G := c⁻¹ * g
  have hkK : ∀ y ∈ K, k * y * k⁻¹ ∈ Y := by
    intro y hy
    have hyKg : MulAut.conj g y ∈ Kg := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hcy := (hc (MulAut.conj g y)).mp hyKg
    rw [MulAut.conj_apply] at hcy
    have hkconj : c⁻¹ * (g * y * g⁻¹) * c = k * y * k⁻¹ := by
      simp only [k]
      group
    rwa [hkconj] at hcy
  have hKmap_le : K.map (MulAut.conj k).toMonoidHom ≤ Y := by
    rintro w ⟨y, hy, hky⟩
    have hky' : k * y * k⁻¹ = w := by simpa [MulAut.conj_apply] using hky
    rw [← hky']
    exact hkK y hy
  have hKeq : K.map (MulAut.conj k).toMonoidHom = Y := by
    refine Subgroup.eq_of_le_of_card_ge hKmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hKcard, hYcard]
  have hkx : k * x * k⁻¹ = z₁ := by
    have hc₁ : c * z₁ = z₁ * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hc₁' : c⁻¹ * z₁ * c = z₁ := by
      calc c⁻¹ * z₁ * c = c⁻¹ * (z₁ * c) := by group
        _ = c⁻¹ * (c * z₁) := by rw [← hc₁]
        _ = z₁ := by group
    calc k * x * k⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by
          simp only [k]; group
      _ = c⁻¹ * z₁ * c := by rw [hgx]
      _ = z₁ := hc₁'
  exact ⟨k, hkx, hKeq⟩

private theorem conj_mem_centerIn_of_map_eq {K Y : Subgroup G} {k z : G}
    (hKeq : K.map (MulAut.conj k).toMonoidHom = Y) (hzk : z ∈ centerIn K) :
    k * z * k⁻¹ ∈ centerIn Y := by
  refine ⟨?_, ?_⟩
  · rw [← hKeq]
    exact Subgroup.mem_map.mpr ⟨z, hzk.1, by simp [MulAut.conj_apply]⟩
  · change k * z * k⁻¹ ∈ Subgroup.centralizer (Y : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hKeq] at hy
    obtain ⟨t, htK, hty⟩ := Subgroup.mem_map.mp hy
    have hcomm : t * z = z * t := Subgroup.mem_centralizer_iff.mp hzk.2 t htK
    have hty' : k * t * k⁻¹ = y := by simpa [MulAut.conj_apply] using hty
    rw [← hty']
    calc (k * t * k⁻¹) * (k * z * k⁻¹) = k * (t * z) * k⁻¹ := by group
      _ = k * (z * t) * k⁻¹ := by rw [hcomm]
      _ = (k * z * k⁻¹) * (k * t * k⁻¹) := by group

private theorem mem_centerIn_of_conj_eq_z (h : Tim79a.ParrottHyp z)
    {z₁ x k : G} (hz₁ : z₁ ∈ centerIn (J z)) (hkx : k * x * k⁻¹ = z₁)
    (hz : k * z * k⁻¹ = z) : x ∈ centerIn (J z) := by
  have hkH : k ∈ H z := by
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc k * z = (k * z * k⁻¹) * k := by group
      _ = z * k := by rw [hz]
  have hx_eq : x = k⁻¹ * z₁ * k := by
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = k⁻¹ * z₁ * k := by rw [hkx]
  rw [hx_eq]
  have hHN : H z ≤ Subgroup.normalizer (centerIn (J z) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
      (centerIn_subgroupOf_normal z)
  have := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem hkH)) z₁).mp hz₁
  simpa using this

private theorem x_eq_z_of_conj_eq_z1 {x z₁ k : G}
    (hkx : k * x * k⁻¹ = z₁) (hz₁' : k * z * k⁻¹ = z₁) : x = z := by
  have h2 : MulAut.conj k x = MulAut.conj k z := by
    rw [MulAut.conj_apply, MulAut.conj_apply, hkx, hz₁']
  exact (MulAut.conj k).injective h2

private theorem not_isConj_z_z1_of_conj_eq_mul
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {k : G} (hzz : k * z * k⁻¹ = z * z₁) : False := by
  obtain ⟨a, haH, haC⟩ := exists_mem_H_not_mem_centralizer_z1 h hZ hz₁ hz₁z hord
  have ha_conj : a * z₁ * a⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord haH haC
  apply not_isConj_z_z1 h hZ hz₁ hz₁z hord
  have hz_conj : (k⁻¹ * a) * z₁ * (k⁻¹ * a)⁻¹ = z := by
    calc (k⁻¹ * a) * z₁ * (k⁻¹ * a)⁻¹ = k⁻¹ * (a * z₁ * a⁻¹) * k := by group
      _ = k⁻¹ * (z * z₁) * k := by rw [ha_conj]
      _ = k⁻¹ * (k * z * k⁻¹) * k := by rw [hzz]
      _ = z := by group
  exact (isConj_iff.mpr ⟨k⁻¹ * a, hz_conj⟩).symm

private theorem not_isConj_z1_of_mem_centerIn (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ x : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hx2 : orderOf x = 2) (hxz₁ : x ≠ z₁) (hxzz₁ : x ≠ z * z₁)
    (hxZ : x ∈ centerIn (J z)) : ¬ IsConj z₁ x := by
  intro hconj
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hxZ with h1 | h1 | h1 | h1
  · rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  · exact not_isConj_z_z1 h hZ hz₁ hz₁z hord (by simpa [h1] using hconj.symm)
  · exact hxz₁ h1
  · exact hxzz₁ h1

private theorem not_isConj_z1_of_not_mem_centerIn
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hK : ∀ j ∈ J z, orderOf j = 2 → j ∉ centerIn (J z) →
      ∀ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) →
        Nat.card K = 2 ^ 16 ∧ centerIn K = Subgroup.closure {z, j})
    {x : G} (hx : x ∈ J z) (hx2 : orderOf x = 2) (hxZ : x ∉ centerIn (J z)) :
    ¬ IsConj z₁ x := by
  intro hconj
  obtain ⟨g, hgx⟩ := isConj_iff.mp hconj.symm
  obtain ⟨K, hK'⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({x} : Set G))
  obtain ⟨hKcard, hKcenter⟩ := hK x hx hx2 hxZ K hK'
  obtain ⟨Y, hY⟩ := exists_isSylowOf 2 (H z ⊓ Subgroup.centralizer ({z₁} : Set G))
  have hYcenter : centerIn Y = centerIn (J z) :=
    centerIn_eq_of_isSylowOf_inf_centralizer_z1 h hz₁ hz₁z hord Y hY
  have hYtop : IsSylowOf 2 Y (Subgroup.centralizer ({z₁} : Set G)) :=
    isSylowOf_centralizer_z1 h hz₁ hz₁z hord Y hY
  have hYcard : Nat.card Y = 2 ^ 16 := by
    rw [hY.card_eq, factorization_card_inf_centralizer_z1 h hZ hz₁ hz₁z hord]
  have hKgSylow := sylow_map_conj_of_sylow hK' hKcard hYtop hYcard hgx
  obtain ⟨k, hkx, hKeq⟩ := exists_conj_map_of_isSylow hKcard hYtop hYcard hKgSylow hgx
  have hzk : z ∈ centerIn K := by
    rw [hKcenter]
    exact Subgroup.subset_closure (by simp)
  have hzkY := conj_mem_centerIn_of_map_eq hKeq hzk
  have hkz_mem : k * z * k⁻¹ ∈ centerIn (J z) := by
    rw [← hYcenter]
    exact hzkY
  have hkz_ord : orderOf (k * z * k⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hkz_mem with h1 | hz | hz₁' | hzz
  · rw [h1, orderOf_one] at hkz_ord
    exact absurd hkz_ord (by norm_num)
  · exact hxZ (mem_centerIn_of_conj_eq_z h hz₁ hkx hz)
  · exact hxZ (by rw [x_eq_z_of_conj_eq_z1 hkx hz₁']; exact z_mem_centerIn_J h)
  · exact not_isConj_z_z1_of_conj_eq_mul h hZ hz₁ hz₁z hord hzz

theorem not_isConj_z1_of_mem_J (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hK : ∀ j ∈ J z, orderOf j = 2 → j ∉ centerIn (J z) →
      ∀ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) →
        Nat.card K = 2 ^ 16 ∧ centerIn K = Subgroup.closure {z, j})
    {x : G} (hx : x ∈ J z) (hx2 : orderOf x = 2) (hxz₁ : x ≠ z₁) (hxzz₁ : x ≠ z * z₁) :
    ¬ IsConj z₁ x := by
  intro hconj
  by_cases hxZ : x ∈ centerIn (J z)
  · exact not_isConj_z1_of_mem_centerIn h hZ hz₁ hz₁z hord hx2 hxz₁ hxzz₁ hxZ hconj
  · exact not_isConj_z1_of_not_mem_centerIn h hZ hz₁ hz₁z hord hK hx hx2 hxZ hconj

end CFSG.RankThree.GF2n.Parrott
