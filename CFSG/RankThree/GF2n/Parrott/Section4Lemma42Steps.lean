module

public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma41
public import CFSG.RankThree.GF2n.Parrott.OmegaOneSylow

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem z_mem_centerIn_J (h : Tim79a.ParrottHyp z) : z ∈ centerIn (J z) :=
  Subgroup.mem_inf.mpr ⟨z_mem_J h, z_centralizes_J h⟩

theorem normalizer_le_H_of_card_eight (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {W : Subgroup G}
    (hfus : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ W → g * z * g⁻¹ = z)
    (hWc : Nat.card W = 8) (hZW : centerIn (J z) ≤ W) :
    normalizer (W : Set G) ≤ H z :=
  normalizer_le_centralizer_of_pairwise_nonconj (card_centerIn_J h) hWc hZW (z_mem_centerIn_J h)
    (fun _ ha _ hb hab => eq_of_isConj_of_mem_centerIn_J h hZ ha hb hab) hfus

section Certified


theorem not_isConj_of_mem_J_sub_centerIn (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z)
    {j : G} (hj : j ∈ J z) (hjc : j ∉ centerIn (J z)) (hj2 : orderOf j = 2) :
    ¬ IsConj z j := by
  have hjH : j ∈ H z := J_le_H hj
  have hJp : IsPGroup 2 (J z) := isPGroup_J h
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hjj : j * j = 1 := by
    have h1 := pow_orderOf_eq_one j
    rwa [hj2, pow_two] at h1
  obtain ⟨K, hK⟩ := exists_isSylowOf 2 (H z ⊓ centralizer ({j} : Set G))
  have hJj : J z ⊓ centralizer ({j} : Set G) ≤ K := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hK
      (fun x hx => Subgroup.mem_inf.mpr ⟨J_le_H hx.1, hx.2⟩) ?_ hJp.to_inf_left
    have key : ∀ c ∈ H z ⊓ centralizer ({j} : Set G), ∀ x ∈ J z ⊓ centralizer ({j} : Set G),
        c * x * c⁻¹ ∈ J z ⊓ centralizer ({j} : Set G) := by
      intro c hc x hx
      refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) x).mp hx.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hcj : c * j = j * c := mem_centralizer_singleton_iff.mp hc.2
      have hxj : x * j = j * x := mem_centralizer_singleton_iff.mp hx.2
      have hcj' : c⁻¹ * j = j * c⁻¹ := by
        calc c⁻¹ * j = c⁻¹ * (j * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * j) * c⁻¹ := by rw [hcj]
          _ = j * c⁻¹ := by group
      calc c * x * c⁻¹ * j = c * x * (c⁻¹ * j) := by group
        _ = c * x * (j * c⁻¹) := by rw [hcj']
        _ = c * (x * j) * c⁻¹ := by group
        _ = c * (j * x) * c⁻¹ := by rw [hxj]
        _ = (c * j) * x * c⁻¹ := by group
        _ = (j * c) * x * c⁻¹ := by rw [hcj]
        _ = j * (c * x * c⁻¹) := by group
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key c hc x, fun hx => ?_⟩
    have h1 := key c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using h1
  have hAj : ∀ a ∈ centerIn (J z), Commute a j := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp ha.2 j hj).symm
  have hdisj : centerIn (J z) ⊓ Subgroup.zpowers j = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hj2 hx.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) hjc
  have hWc : Nat.card (centerIn (J z) ⊔ Subgroup.zpowers j : Subgroup G) = 8 := by
    rw [CFSG.card_sup_eq_mul_of_commute (centerIn (J z)) (Subgroup.zpowers j) (fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (hAj a ha).zpow_right k) hdisj, card_centerIn_J h, Nat.card_zpowers, hj2]
  have hWJ : centerIn (J z) ⊔ Subgroup.zpowers j ≤ J z :=
    sup_le (fun x hx => hx.1) (Subgroup.zpowers_le.mpr hj)
  have hNW : normalizer ((centerIn (J z) ⊔ Subgroup.zpowers j : Subgroup G) : Set G) ≤ H z :=
    normalizer_le_H_of_card_eight h hZ (fun g hg hgW => hA g hg (hWJ hgW)) hWc le_sup_left
  have hAK : centerIn (J z) ≤ K := fun a ha => hJj (Subgroup.mem_inf.mpr
    ⟨ha.1, mem_centralizer_singleton_iff.mpr (hAj a ha).eq⟩)
  have hjK : j ∈ K := hJj (Subgroup.mem_inf.mpr ⟨hj, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hjJ : ¬ (⟨j, hj⟩ : J z) ∈ Subgroup.center (J z) := by
    intro hmem
    exact hjc ((CFSG.centerIn_eq_map_center (J z)) ▸ ⟨_, hmem, rfl⟩)
  have hconj : ∀ g ∈ normalizer (K : Set G), ∀ x : G, (x ∈ centerIn (J z) ∨ x = j) →
      g * x * g⁻¹ ∈ centerIn (J z) ⊔ Subgroup.zpowers j := by
    intro g hg x hx
    have hxK : x ∈ K := by
      rcases hx with hx | rfl
      · exact hAK hx
      · exact hjK
    have hxC : ∀ k ∈ K, k * x = x * k := by
      intro k hk
      rcases hx with hx | rfl
      · have hxH : x ∈ centerIn (H z) := hZ ▸ hx
        exact Subgroup.mem_centralizer_iff.mp hxH.2 k (hK.le hk).1
      · exact mem_centralizer_singleton_iff.mp (hK.le hk).2
    have hx2 : x * x = 1 := by
      rcases hx with hx | rfl
      · exact centerIn_J_sq h hx
      · exact hjj
    have hyK : g * x * g⁻¹ ∈ K := (mem_normalizer_iff.mp hg x).mp hxK
    have hyH : g * x * g⁻¹ ∈ H z := (hK.le hyK).1
    have hyC : ∀ k ∈ K, k * (g * x * g⁻¹) = (g * x * g⁻¹) * k := by
      intro k hk
      have hk' : g⁻¹ * k * g ∈ K := by
        have := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
        simpa using this
      have hc := hxC _ hk'
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * k := by group
    have hy2 : (g * x * g⁻¹) ^ 2 = 1 := by
      calc (g * x * g⁻¹) ^ 2 = (g * x * g⁻¹) * (g * x * g⁻¹) := pow_two _
        _ = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hmem := omega_one_center_le h hjJ (K := K.subgroupOf (H z))
      (fun w hw => by
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
        have hu' : (u : G) * j = j * (u : G) := by
          have := Subgroup.mem_centralizer_singleton_iff.mp hu
          exact congrArg Subtype.val this
        exact Subgroup.mem_subgroupOf.mpr (hJj (Subgroup.mem_inf.mpr
          ⟨u.2, mem_centralizer_singleton_iff.mpr hu'⟩)))
      (w := ⟨g * x * g⁻¹, hyH⟩)
      (fun k hk => Subtype.ext (hyC (k : G) (Subgroup.mem_subgroupOf.mp hk)))
      hy2
    rw [← CFSG.centerIn_eq_map_center, sup_comm] at hmem
    exact hmem
  have hgW : ∀ g ∈ normalizer (K : Set G),
      g ∈ normalizer ((centerIn (J z) ⊔ Subgroup.zpowers j : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : (centerIn (J z) ⊔ Subgroup.zpowers j).map (MulAut.conj g).toMonoidHom ≤
        centerIn (J z) ⊔ Subgroup.zpowers j := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact hconj g hg a (Or.inl ha)
      · exact hconj g hg j (Or.inr rfl)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hNK : ∀ g ∈ normalizer (K : Set G), g ∈ H z := fun g hg => hNW (hgW g hg)
  refine not_isConj_of_isSylowOf_inf_centralizer (K := K) hK ?_ ?_
  · intro g _ hg _
    exact hNK g hg
  · refine dvd_relIndex_inf_centralizer_of_normal_pGroup (J_le_H (z := z)) hHN hJp ?_
    intro hJle
    apply hjc
    refine Subgroup.mem_inf.mpr ⟨hj, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hJle hx)

theorem not_isConj_of_mem_J (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z)
    {j : G} (hj : j ∈ J z) (hjz : j ∉ Subgroup.zpowers z) : ¬ IsConj z j := by
  by_cases hjc : j ∈ centerIn (J z)
  · intro hconj
    exact hjz (eq_of_isConj_of_mem_centerIn_J h hZ (z_mem_centerIn_J h) hjc hconj ▸
      Subgroup.mem_zpowers z)
  · by_cases hj2 : orderOf j = 2
    · exact not_isConj_of_mem_J_sub_centerIn h hZ hA hj hjc hj2
    · intro hconj
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      apply hj2
      rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact h.1

end Certified

end CFSG.RankThree.GF2n.Parrott
