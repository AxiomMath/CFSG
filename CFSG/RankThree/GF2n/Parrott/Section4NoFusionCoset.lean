module

public import CFSG.GroupTheory.CentralizerSylowFusionOfLe
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified


private theorem exists_sylow_normalizer_le_H_of_mem_J (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z)
    {j : G} (hj : j ∈ J z) (hjc : j ∉ centerIn (J z)) (hj2 : orderOf j = 2) :
    ∃ K : Subgroup G, IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)) ∧
      ∀ g ∈ normalizer (K : Set G), g ∈ H z := by
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
  exact ⟨K, hK, fun g hg => hNW (hgW g hg)⟩

theorem not_isConj_of_mem_centerIn_of_mem_J_sub (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z)
    {e : G} (he : e ∈ centerIn (J z)) {j : G} (hj : j ∈ J z) (hjc : j ∉ centerIn (J z))
    (hj2 : orderOf j = 2) : ¬ IsConj e j := by
  obtain ⟨K, hK, hNK⟩ := exists_sylow_normalizer_le_H_of_mem_J h hZ hA hj hjc hj2
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have heH : e ∈ centerIn (H z) := hZ ▸ he
  have hHe : H z ≤ centralizer ({e} : Set G) := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp heH.2 x hx
  refine not_isConj_of_isSylowOf_inf_centralizer_of_le hHe hK (fun g _ hg _ => hNK g hg) ?_
  refine dvd_relIndex_inf_centralizer_of_normal_pGroup (J_le_H (z := z)) hHN (isPGroup_J h) ?_
  intro hJle
  apply hjc
  refine Subgroup.mem_inf.mpr ⟨hj, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hJle hx)

theorem eq_of_isConj_of_mem_J (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z)
    {e : G} (he : e ∈ centerIn (J z)) (he1 : e ≠ 1) {j : G} (hj : j ∈ J z) (hconj : IsConj e j) :
    j = e := by
  have hjZ : j ∈ centerIn (J z) := by
    by_contra hjc
    have he2 : orderOf e = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact centerIn_J_sq h he) he1
    have hj2 : orderOf j = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact he2
    exact not_isConj_of_mem_centerIn_of_mem_J_sub h hZ hA he hj hjc hj2 hconj
  exact (eq_of_isConj_of_mem_centerIn_J h hZ he hjZ hconj).symm

theorem not_isConj_of_centre_in_J_union (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z)
    {x : G} (hxH : x ∈ H z) (hxJ : x ∉ J z) (hxx : x * x = 1)
    {X : Subgroup G} (hX : IsSylowOf 2 X (H z ⊓ centralizer ({x} : Set G)))
    (hZs : ∀ w ∈ X ⊓ centralizer (X : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j) :
    ¬ IsConj z x := by
  have hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ J z → g * z * g⁻¹ = z := fun g hg hgJ => A0 g hg (J_le_H hgJ)
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hz2 : orderOf z = 2 := h.1
  have hdvd : 2 ∣ (H z ⊓ centralizer ({x} : Set G)).relIndex (H z) := by
    refine dvd_relIndex_inf_centralizer_of_normal_pGroup (J_le_H (z := z)) hHN (isPGroup_J h) ?_
    intro hJle
    apply hxJ
    have hxc : x ∈ H z ⊓ centralizer (J z : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxH, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact mem_centralizer_singleton_iff.mp (hJle hj)
    rw [centralizer_J_eq_centerIn h] at hxc
    exact hxc.1
  refine not_isConj_of_isSylowOf_inf_centralizer (K := X) hX ?_ hdvd
  intro n _ hnN _
  have hZC : centerIn (J z) ≤ H z ⊓ centralizer ({x} : Set G) := fun e he => by
    refine Subgroup.mem_inf.mpr ⟨J_le_H he.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have heH : e ∈ centerIn (H z) := hZ ▸ he
    exact (mem_centralizer_iff.mp heH.2 x hxH).symm
  have hZX : centerIn (J z) ≤ X := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hX hZC ?_
      (IsPGroup.of_card (n := 2) (by rw [card_centerIn_J h]; norm_num))
    intro c hc
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro e he
    have heH : e ∈ centerIn (H z) := hZ ▸ he
    exact (mem_centralizer_iff.mp heH.2 c hc.1).symm
  have hnZ : ∀ e ∈ centerIn (J z), n * e * n⁻¹ ∈ X ⊓ centralizer (X : Set G) := by
    intro e he
    have heX : e ∈ X := hZX he
    have heC : ∀ y ∈ X, y * e = e * y := fun y hy => by
      have heH : e ∈ centerIn (H z) := hZ ▸ he
      exact mem_centralizer_iff.mp heH.2 y (hX.le hy).1
    refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hnN e).mp heX, ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ X := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hnN) y).mp hy
      simpa using h1
    have hc := heC _ hy'
    calc y * (n * e * n⁻¹) = n * ((n⁻¹ * y * n) * e) * n⁻¹ := by group
      _ = n * (e * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
      _ = (n * e * n⁻¹) * y := by group
  obtain ⟨z₁, hZeq, hz₁z, -⟩ := exists_z1 h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hzz₁ : z * z₁ ∈ centerIn (J z) := (centerIn (J z)).mul_mem (z_mem_centerIn_J h) hz₁
  have hzZ : z ∈ centerIn (J z) := z_mem_centerIn_J h
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxJn : ∀ j ∈ J z, x * j * x ∈ J z := fun j hj => by
    have h1 := (mem_normalizer_iff.mp (hHN hxH) j).mp hj
    rwa [hxinv] at h1
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := hz2
    rw [h1, orderOf_one] at h2
    omega
  have hz₁1 : z₁ ≠ 1 := fun h1 => hz₁z (h1 ▸ Subgroup.one_mem _)
  have hzz₁1 : z * z₁ ≠ 1 := fun h1 => hz₁z (by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z))
  have key : ∃ e' ∈ centerIn (J z), e' ≠ 1 ∧ n * e' * n⁻¹ ∈ J z := by
    rcases hZs _ (hnZ z hzZ) with hf₁ | ⟨j₁, hj₁, hf₁⟩
    · exact ⟨z, hzZ, hz1, hf₁⟩
    · rcases hZs _ (hnZ z₁ hz₁) with hf₂ | ⟨j₂, hj₂, hf₂⟩
      · exact ⟨z₁, hz₁, hz₁1, hf₂⟩
      · refine ⟨z * z₁, hzz₁, hzz₁1, ?_⟩
        have h1 : n * (z * z₁) * n⁻¹ = (n * z * n⁻¹) * (n * z₁ * n⁻¹) := by group
        rw [h1, hf₁, hf₂]
        have h3 : x * j₁ * (x * j₂) = (x * j₁ * x) * j₂ := by group
        rw [h3]
        exact (J z).mul_mem (hxJn j₁ hj₁) hj₂
  obtain ⟨e', he', he'1, hfJ⟩ := key
  have hfe : n * e' * n⁻¹ = e' :=
    eq_of_isConj_of_mem_J h hZ hA he' he'1 hfJ (isConj_iff.mpr ⟨n, rfl⟩)
  rw [mem_centralizer_singleton_iff]
  by_cases he'z : e' = z
  · rw [he'z] at hfe
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hfe]
  · have hnC' : n ∈ centralizer ({e'} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc n * e' = n * e' * n⁻¹ * n := by group
        _ = e' * n := by rw [hfe]
    have hnz := A0 n ⟨e', he', he'1, he'z, hnC'⟩ (hX.le (hnZ z hzZ).1).1
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnz]

end Certified

end CFSG.RankThree.GF2n.Parrott
