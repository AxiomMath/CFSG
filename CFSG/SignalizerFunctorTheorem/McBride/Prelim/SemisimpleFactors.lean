module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents)

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

private theorem exists_mul_ne_of_not_isMulCommutative {H : Type*} [Mul H]
    (h : ¬ IsMulCommutative H) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact h (IsMulCommutative.of_comm hcon)

private theorem exists_mem_mul_ne_of_not_isMulCommutative {T : Subgroup G}
    (h : ¬ IsMulCommutative T) : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_not_isMulCommutative h
  exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩

private theorem not_isMulCommutative_of_mem_mul_ne {T : Subgroup G}
    (h : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) : ¬ IsMulCommutative T := by
  intro hT
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact hxy (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩))

private theorem eq_one_of_forall_mul_comm {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) {z : H} (hz : ∀ t : H, t * z = z * t) : z = 1 := by
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have : z ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr hz
  rwa [hZ, Subgroup.mem_bot] at this

private theorem isComponent_subgroupOf_of_mem_lcal {Y J : Subgroup G} (hJ : J ∈ lcal Y) :
    CFSG.IsComponent (J.subgroupOf Y) := by
  obtain ⟨hJY, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  obtain ⟨hq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (exists_mul_ne_of_not_isMulCommutative hnc)
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY).symm hq,
    hsub⟩

private theorem mul_comm_of_mem_lcal [Finite G] {Y J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ lcal Y)
    (h₂ : J₂ ∈ lcal Y) (hne : J₁ ≠ J₂) {x y : G} (hx : x ∈ J₁) (hy : y ∈ J₂) :
    x * y = y * x := by
  have hJ₁Y := (mem_lcal_iff.mp h₁).1
  have hJ₂Y := (mem_lcal_iff.mp h₂).1
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf_of_mem_lcal h₁)
      (isComponent_subgroupOf_of_mem_lcal h₂) with h | h
  · refine absurd ?_ hne
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hJ₁Y, inf_eq_left.mpr hJ₂Y] at this
  · have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hJ₁Y h
    rw [inf_eq_left.mpr hJ₂Y] at h'
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h' hx)
      y hy).symm

private theorem IsSemisimple.eq_one_of_forall_commute [Finite G] {K : Subgroup G}
    (hK : IsSemisimple K) {z : G} (hzK : z ∈ K)
    (hz : ∀ T ∈ simpleComponents K, ∀ t ∈ T, z * t = t * z) : z = 1 := by
  have h1 : (⟨z, hzK⟩ : K) = 1 := by
    refine IsDirectProduct.ext_coord hK fun T hT => ?_
    rw [map_one]
    have hTs := hT.2.2.1
    refine eq_one_of_forall_mul_comm ?_ fun t => ?_
    · obtain ⟨x, hx, y, hy, hxy⟩ := hT.2.2.2
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
    · have ht : IsDirectProduct.coord hK hT ⟨(t : G), hK.le hT t.2⟩ = t :=
        Subtype.ext (IsDirectProduct.coord_of_mem hK hT t.2)
      have e : (⟨(t : G), hK.le hT t.2⟩ : K) * ⟨z, hzK⟩ = ⟨z, hzK⟩ * ⟨(t : G), hK.le hT t.2⟩ :=
        Subtype.ext (hz T hT t t.2).symm
      calc t * IsDirectProduct.coord hK hT ⟨z, hzK⟩
          = IsDirectProduct.coord hK hT (⟨(t : G), hK.le hT t.2⟩ * ⟨z, hzK⟩) := by
            rw [map_mul, ht]
        _ = IsDirectProduct.coord hK hT (⟨z, hzK⟩ * ⟨(t : G), hK.le hT t.2⟩) := by rw [e]
        _ = IsDirectProduct.coord hK hT ⟨z, hzK⟩ * t := by rw [map_mul, ht]
  exact congrArg Subtype.val h1

private theorem IsSemisimple.exists_le_of_mem_lcal [Finite G] {K J : Subgroup G}
    (hK : IsSemisimple K) (hJ : J ∈ lcal K) : ∃ T ∈ simpleComponents K, J ≤ T := by
  obtain ⟨hJK, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_mul_ne_of_not_isMulCommutative hnc
  have hcomp := isComponent_subgroupOf_of_mem_lcal hJ
  by_contra hcon
  push Not at hcon
  have hcent : ∀ T ∈ simpleComponents K, ∀ x ∈ J, ∀ y ∈ T, x * y = y * x := by
    intro T hT x hx y hy
    rcases CFSG.LocalCores.component_normal_subgroup hcomp hT.2.1 with h | h
    · exact absurd (CFSG.LocalCores.le_of_subgroupOf_le hJK h) (hcon T hT)
    · have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hJK h
      rw [inf_eq_left.mpr hT.1] at h'
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h' hx) y hy).symm
  have hKJ : K ≤ Subgroup.centralizer (J : Set G) := by
    rw [← hK.sSup_eq]
    exact sSup_le fun T hT y hy =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => hcent T hT x hx y hy
  exact hxy (Subgroup.mem_centralizer_iff.mp (hKJ (hJK hy)) x hx)

private theorem mul_comm_of_normal_of_not_le {K N T : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hT : T ∈ simpleComponents K) (hTN : ¬ T ≤ N) {n t : G}
    (hn : n ∈ N) (ht : t ∈ T) : n * t = t * n := by
  obtain ⟨hTK, hTn, hTs, -⟩ := hT
  have hNconj : ∀ n ∈ N, ∀ k ∈ K, k * n * k⁻¹ ∈ N := fun n hn k hk =>
    (Subgroup.normal_subgroupOf_iff hNK).mp hN n k hn hk
  have hTconj : ∀ s ∈ T, ∀ k ∈ K, k * s * k⁻¹ ∈ T := fun s hs k hk =>
    (Subgroup.normal_subgroupOf_iff hTK).mp hTn s k hs hk
  have hD : ((N ⊓ T).subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro u v hu hv
    obtain ⟨huN, huT⟩ := Subgroup.mem_inf.mp hu
    exact Subgroup.mem_inf.mpr ⟨hNconj u huN v (hTK hv), mul_mem (mul_mem hv huT) (inv_mem hv)⟩
  have hbot : N ⊓ T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ T).subgroupOf T) with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : T) ∈ (N ⊓ T).subgroupOf T := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    · refine absurd (fun x hx => ?_) hTN
      have hmem : (⟨x, hx⟩ : T) ∈ (N ⊓ T).subgroupOf T := by rw [h]; trivial
      exact (Subgroup.mem_inf.mp hmem).1
  have hmem : n * t * n⁻¹ * t⁻¹ ∈ N ⊓ T := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := mul_mem hn (hNconj n⁻¹ (inv_mem hn) t (hTK ht))
      simpa [mul_assoc] using this
    · exact mul_mem (hTconj t ht n (hNK hn)) (inv_mem ht)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
  exact hmem

theorem IsSemisimple.lcal_eq [Finite G] {K : Subgroup G} (hK : IsSemisimple K) :
    lcal K = CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents K := by
  ext J
  refine ⟨fun hJ => ?_, fun hJ => ?_⟩
  · obtain ⟨T, hT, hJT⟩ := hK.exists_le_of_mem_lcal hJ
    suffices hJeq : J = T from hJeq ▸ hT
    obtain ⟨-, hsub, -, hnc⟩ := mem_lcal_iff.mp hJ
    obtain ⟨hTK, -, hTs, -⟩ := hT
    have hsub' : (J.subgroupOf T).IsSubnormal := by
      have heq : (J.subgroupOf K).comap (Subgroup.inclusion hTK) = J.subgroupOf T := by
        ext t
        rfl
      exact heq ▸ hsub.comap (Subgroup.inclusion hTK)
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hTs hsub' with h | h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_mul_ne_of_not_isMulCommutative hnc
      have hx1 : x = 1 := by
        have hmem : (⟨x, hJT hx⟩ : T) ∈ J.subgroupOf T := hx
        rw [h, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      exact hxy (by rw [hx1, one_mul, mul_one])
    · refine le_antisymm hJT fun x hx => ?_
      have hmem : (⟨x, hx⟩ : T) ∈ J.subgroupOf T := by rw [h]; trivial
      exact hmem
  · exact mem_lcal_iff.mpr ⟨hJ.1, hJ.2.1.isSubnormal, hJ.2.2.1,
      not_isMulCommutative_of_mem_mul_ne hJ.2.2.2⟩

theorem IsSemisimple.isDirectProduct_lcal [Finite G] {K : Subgroup G} (hK : IsSemisimple K) :
    IsDirectProduct (lcal K) K := by
  rw [hK.lcal_eq]
  exact hK

theorem IsSemisimple.isDirectPair_of_normal [Finite G] {K N : Subgroup G} (hK : IsSemisimple K)
    (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) :
    IsDirectPair N (K ⊓ Subgroup.centralizer (N : Set G)) K := by
  refine ⟨fun x hx y hy => ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x hx
  ·
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨hzN, hzKC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨hzK, hzC⟩ := Subgroup.mem_inf.mp hzKC
    refine Subgroup.mem_bot.mpr (hK.eq_one_of_forall_commute hzK fun T hT t ht => ?_)
    by_cases hTN : T ≤ N
    · exact (Subgroup.mem_centralizer_iff.mp hzC t (hTN ht)).symm
    · exact mul_comm_of_normal_of_not_le hNK hN hT hTN hzN ht
  ·
    refine le_antisymm (sup_le hNK inf_le_left) ?_
    calc K = sSup (simpleComponents K) := hK.sSup_eq.symm
      _ ≤ _ := sSup_le fun T hT => ?_
    by_cases hTN : T ≤ N
    · exact le_sup_of_le_left hTN
    · refine le_sup_of_le_right fun t ht => Subgroup.mem_inf.mpr ⟨hT.1 ht, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun n hn =>
        mul_comm_of_normal_of_not_le hNK hN hT hTN hn ht

theorem isDirectProduct_orbit [Finite G] {A Y J : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hJ : J ∈ lcal Y) :
    IsDirectProduct {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} (orbitClosure J A) := by
  have hmem : ∀ K ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}, K ∈ lcal Y := by
    rintro K ⟨a, ha, rfl⟩
    exact map_conj_mem_lcal hJ (hAY ha)
  refine ⟨fun K₁ h₁ K₂ h₂ hne x hx y hy => ?_, fun K₁ hK₁ => ?_, ?_⟩
  · exact mul_comm_of_mem_lcal (hmem K₁ h₁) (hmem K₂ h₂) hne hx hy
  ·
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hxL⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp (hmem K₁ hK₁)
    have hs := (mem_lcal_iff.mp (hmem K₁ hK₁)).2.2.1
    have hcent : sSup ({K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} \ {K₁}) ≤
        Subgroup.centralizer (K₁ : Set G) := by
      refine sSup_le fun K' hK' y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun h hh => mul_comm_of_mem_lcal (hmem K₁ hK₁) (hmem K' hK'.1) (Ne.symm hK'.2) hh hy
    have h1 : (⟨x, hx₁⟩ : K₁) = 1 := by
      refine eq_one_of_forall_mul_comm (exists_mul_ne_of_not_isMulCommutative hnc) fun t => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hxL) t t.2)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · refine le_antisymm (sSup_le ?_) (orbitClosure_le fun a ha => le_sSup ⟨a, ha, rfl⟩)
    rintro K ⟨a, ha, rfl⟩
    exact map_conj_le_orbitClosure J ha

end CFSG.SignalizerFunctorTheorem.McBride
