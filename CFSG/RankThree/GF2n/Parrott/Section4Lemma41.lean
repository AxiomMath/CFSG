module

public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qd
public import CFSG.Quasithin.SteinbergCDSwappedFactorsCoreSupports

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem J_le_of_isSylowOf (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) : J z ≤ T := by
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  have hJQ : (J z).subgroupOf (H z) ≤ (Q : Subgroup ↥(H z)) := by
    have hp : IsPGroup 2 ((J z).subgroupOf (H z)) := by
      rw [J_subgroupOf_eq_pCore]
      exact pCore_isPGroup
    exact IsPGroup.le_sylow_of_normal hp Q
  rw [hQ] at hJQ
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hJQ (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, J_le_H hx⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z)))

theorem inf_centralizer_eq_centerIn_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    T ⊓ Subgroup.centralizer (T : Set G) = centerIn (J z) := by
  have hJT : J z ≤ T := J_le_of_isSylowOf T hT
  have hTH : T ≤ H z := hT.le
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    have hxJ : x ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp hxC w (hJT hw)
    rw [← centralizer_J_eq_centerIn h]
    exact ⟨hTH hxT, hxJ⟩
  · intro x hx
    have hxH : x ∈ centerIn (H z) := hZ ▸ hx
    refine Subgroup.mem_inf.mpr ⟨hJT hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp hxH.2 t (hTH ht)

theorem centralizer_centerIn_J_eq (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) :
    Subgroup.centralizer (centerIn (J z) : Set G) = H z := by
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  apply le_antisymm
  · intro x hx
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx z hzZ).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyH : y ∈ centerIn (H z) := hZ ▸ hy
    exact (Subgroup.mem_centralizer_iff.mp hyH.2 x hx).symm

theorem normalizer_centerIn_J_le (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) :
    Subgroup.normalizer (centerIn (J z) : Set G) ≤ H z := by
  intro n hn
  have key : ∀ m ∈ Subgroup.normalizer (centerIn (J z) : Set G),
      ∀ c ∈ Subgroup.centralizer (centerIn (J z) : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (centerIn (J z) : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m ∈ centerIn (J z) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) w).mp hw
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hw'
    calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [hcomm]
      _ = m * c * m⁻¹ * w := by group
  have hnH : n ∈ Subgroup.normalizer (H z : Set G) := by
    rw [← centralizer_centerIn_J_eq h hZ, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key n hn y, fun hy => ?_⟩
    have h1 := key n⁻¹ (inv_mem hn) _ hy
    simpa [mul_assoc] using h1
  have hnJ : n ∈ Subgroup.normalizer (J z : Set G) :=
    CFSG.Quasithin.SteinbergCD.mem_normalizer_inSubgroup_pCore 2 hnH
  have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
  have hz2 : orderOf z = 2 := h.1
  have hmap : (⁅J z, J z⁆).map (MulAut.conj n).toMonoidHom = ⁅J z, J z⁆ := by
    rw [Subgroup.map_commutator]
    have h1 : (J z).map (MulAut.conj n).toMonoidHom = J z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnJ
    rw [h1]
  have hzJ : z ∈ ⁅J z, J z⁆ := by
    rw [hcomm]
    exact Subgroup.mem_zpowers z
  have hzn : n * z * n⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hcomm, ← hmap]
    exact ⟨z, hzJ, rfl⟩
  have hnz : n * z * n⁻¹ ≠ 1 := by
    intro h1
    have : z = 1 := by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzn' : n * z * n⁻¹ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzn
    have hk' : z ^ (k % 2) = z ^ k := by
      have := zpow_mod_orderOf z k
      rwa [hz2] at this
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · rw [← hk, ← hk', h0] at hnz
      exact absurd (by simp) hnz
    · rw [← hk, ← hk', h1]
      simp
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [hzn']

theorem normalizer_le_H_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    Subgroup.normalizer (T : Set G) ≤ H z := by
  intro n hn
  apply normalizer_centerIn_J_le h hZ
  rw [← inf_centralizer_eq_centerIn_of_isSylowOf h hZ T hT]
  have key : ∀ m ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ T ⊓ Subgroup.centralizer (T : Set G),
      m * x * m⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set G) := by
    intro m hm x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hm x).mp hxT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : m⁻¹ * t * m ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) t).mp ht
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ ht'
    calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [hcomm]
      _ = m * x * m⁻¹ * t := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have h1 := key n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using h1

theorem isSylowOf_top_of_isSylowOf_H (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (T : Subgroup G) (hT : IsSylowOf 2 T (H z)) :
    IsSylowOf 2 T ⊤ := by
  have hT' : IsSylowOf 2 T (H z ⊓ ⊤) := by rwa [inf_top_eq]
  refine isSylowOf_of_normalizer_inf_le hT' ?_
  rw [inf_top_eq]
  exact normalizer_le_H_of_isSylowOf h hZ T hT

theorem eq_of_isConj_of_mem_centerIn_J (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {a b : G} (ha : a ∈ centerIn (J z))
    (hb : b ∈ centerIn (J z)) (hab : IsConj a b) : a = b := by
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
  have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H h hZ T hT
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hcen : ∀ y ∈ T, ∀ x ∈ centerIn (J z), y * x = x * y := by
    intro y hy x hx
    have hxH : x ∈ centerIn (H z) := hZ ▸ hx
    exact Subgroup.mem_centralizer_iff.mp hxH.2 y (hT.le hy)
  obtain ⟨n, hn, hnx⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22q_fusion_of_central
    (p := 2) hTtop (A := centerIn (J z)) (X := Subgroup.zpowers a)
    (Subgroup.zpowers_le.mpr ha) hcen (g := c⁻¹) (by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [inv_inv, ← conj_zpow, hc]
      exact Subgroup.zpow_mem _ hb k)
  have hnH : n ∈ H z := normalizer_le_H_of_isSylowOf h hZ T hT hn
  have h1 := hnx a (Subgroup.mem_zpowers a)
  rw [inv_inv, hc] at h1
  have haH : a ∈ centerIn (H z) := hZ ▸ ha
  have h2 : n⁻¹ * a * n = a := by
    have := Subgroup.mem_centralizer_iff.mp haH.2 n⁻¹ (inv_mem hnH)
    calc n⁻¹ * a * n = a * n⁻¹ * n := by rw [this]
      _ = a := by group
  exact h2.symm.trans h1.symm

end CFSG.RankThree.GF2n.Parrott
