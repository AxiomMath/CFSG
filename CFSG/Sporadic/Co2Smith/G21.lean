module

public import CFSG.Sporadic.Co2Smith.WP1Basic

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u

variable {G : Type u} [Group G] {z : G}

@[expose] def zC (z : G) : centralizer ({z} : Set G) :=
  ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

theorem zC_mem_center (z : G) : zC z ∈ center (centralizer ({z} : Set G)) := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact (mem_centralizer_singleton_iff.mp g.2)

theorem zC_mem_pCore (hz : orderOf z = 2) : zC z ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) := by
  have hn : (zpowers (zC z)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [show g * zC z ^ k * g⁻¹ = zC z ^ k by
      rw [mem_center_iff.mp (Subgroup.zpow_mem _ (zC_mem_center z) k) g]
      group]
    exact zpow_mem_zpowers _ k
  have hp : IsPGroup 2 (zpowers (zC z)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : orderOf (zC z) = orderOf z :=
      (orderOf_injective (centralizer ({z} : Set G)).subtype Subtype.val_injective (zC z)).symm
    rw [this, hz]
  have hle : zpowers (zC z) ≤ CFSG.pCore 2 (centralizer ({z} : Set G)) := by
    unfold CFSG.pCore
    exact le_sSup ⟨hn, hp⟩
  exact hle (mem_zpowers _)

theorem pCore_le_sylow' (T : Sylow 2 (centralizer ({z} : Set G))) :
    CFSG.pCore 2 (centralizer ({z} : Set G)) ≤ (T : Subgroup _) := by
  have : (CFSG.pCore 2 (centralizer ({z} : Set G))).Normal := CFSG.pCore_normal
  exact CFSG.pCore_isPGroup.le_sylow_of_normal T

variable [Finite G]

theorem zE_ofLocal
    (hH : SmithLocal (centralizer ({z} : Set G))) (hz : orderOf z = 2) :
    ((LocalConfig.ofLocal hH).zE.1 : centralizer ({z} : Set G)) = zC z := by
  have hmem : (⟨zC z, zC_mem_pCore hz⟩ : (LocalConfig.ofLocal hH).E) ∈
      center (LocalConfig.ofLocal hH).E := by
    rw [mem_center_iff]
    intro e
    apply Subtype.ext
    exact mem_center_iff.mp (zC_mem_center z) e.1
  rcases ((LocalConfig.ofLocal hH).mem_center_iff _).mp hmem with h | h
  · exfalso
    have h1 : zC z = 1 := congrArg Subtype.val h
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact (congrArg Subtype.val h).symm

theorem center_sylow_eq
    (hH : SmithLocal (centralizer ({z} : Set G))) (hz : orderOf z = 2)
    (T : Sylow 2 (centralizer ({z} : Set G))) {x : centralizer ({z} : Set G)}
    (hx : ∀ y ∈ (T : Subgroup _), x * y = y * x) : x = 1 ∨ x = zC z := by
  obtain ⟨e₀, he₀, hxe⟩ :=
    (LocalConfig.ofLocal hH).centralizer_E x fun e => hx e.1 (pCore_le_sylow' T e.2)
  rcases ((LocalConfig.ofLocal hH).mem_center_iff e₀).mp he₀ with rfl | rfl
  · exact Or.inl hxe
  · exact Or.inr (hxe.trans (zE_ofLocal hH hz))

theorem exists_sylow_eq_map
    (hH : SmithLocal (centralizer ({z} : Set G))) (hz : orderOf z = 2)
    (T : Sylow 2 (centralizer ({z} : Set G))) :
    ∃ P : Sylow 2 G,
      (P : Subgroup G) = (T : Subgroup _).map (centralizer ({z} : Set G)).subtype := by
  set T' := (T : Subgroup (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
    with hT'
  have hT'p : IsPGroup 2 T' := T.isPGroup'.map _
  obtain ⟨P, hP⟩ := hT'p.exists_le_sylow
  refine ⟨P, ?_⟩
  by_contra hne
  have hlt : T'.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun g hg => ?_) hP
    have : (⟨g, hg⟩ : P) ∈ T'.subgroupOf P := htop ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  obtain ⟨⟨u, huP⟩, hu, hunot⟩ :
      ∃ u ∈ normalizer ((T'.subgroupOf P : Subgroup P) : Set P), u ∉ T'.subgroupOf P :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hnorm : ∀ (v : P), v ∈ normalizer ((T'.subgroupOf P : Subgroup P) : Set P) → ∀ t ∈ T',
      (v : G) * t * (v : G)⁻¹ ∈ T' := by
    intro v hv t ht
    exact (mem_normalizer_iff.mp hv ⟨t, hP ht⟩).mp ht
  have hnorm1 := hnorm ⟨u, huP⟩ hu
  have hnorm2 : ∀ t ∈ T', u⁻¹ * t * u ∈ T' := by
    intro t ht
    have h := hnorm (⟨u, huP⟩ : P)⁻¹ (inv_mem hu) t ht
    simpa using h
  have hzT : zC z ∈ (T : Subgroup (centralizer ({z} : Set G))) :=
    pCore_le_sylow' T (zC_mem_pCore hz)
  have hzT' : z ∈ T' := ⟨zC z, hzT, rfl⟩
  have huz : u * z * u⁻¹ = z := by
    obtain ⟨w, hwT, hw⟩ := hnorm1 z hzT'
    have hcen : ∀ y ∈ (T : Subgroup (centralizer ({z} : Set G))), w * y = y * w := by
      intro y hy
      apply Subtype.ext
      have hy' : u⁻¹ * (y : G) * u ∈ T' := hnorm2 y ⟨y, hy, rfl⟩
      obtain ⟨y', -, hy'e⟩ := hy'
      have hzy : z * (u⁻¹ * (y : G) * u) = (u⁻¹ * (y : G) * u) * z := by
        rw [← hy'e]
        exact (mem_centralizer_singleton_iff.mp y'.2).symm
      show (w : G) * y = y * w
      rw [show (w : G) = u * z * u⁻¹ from hw]
      calc u * z * u⁻¹ * (y : G) = u * (z * (u⁻¹ * y * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * y * u) * z) * u⁻¹ := by rw [hzy]
        _ = (y : G) * (u * z * u⁻¹) := by group
    rcases center_sylow_eq hH hz T hcen with h | h
    · exfalso
      have h1 : u * z * u⁻¹ = 1 := by rw [← hw, h]; rfl
      have h2 : z = 1 := by
        have := congrArg (fun x => u⁻¹ * x * u) h1
        simpa [mul_assoc] using this
      rw [h2, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · rw [← hw, h]
      rfl
  have huC : u ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc u * z = u * z * u⁻¹ * u := by group
      _ = z * u := by rw [huz]
  set T'' := Subgroup.closure
    (((T : Subgroup (centralizer ({z} : Set G))) : Set (centralizer ({z} : Set G))) ∪
      {⟨u, huC⟩}) with hT''
  have hle : T''.map (centralizer ({z} : Set G)).subtype ≤ (P : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hP ⟨x, hx, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact huP
  have hp'' : IsPGroup 2 T'' :=
    (P.isPGroup'.to_le hle).of_equiv
      (T''.equivMapOfInjective (centralizer ({z} : Set G)).subtype Subtype.val_injective).symm
  have heq : T'' = (T : Subgroup (centralizer ({z} : Set G))) :=
    T.is_maximal' hp'' fun x hx => Subgroup.subset_closure (Set.mem_union_left _ hx)
  have huT :
      (⟨u, huC⟩ : centralizer ({z} : Set G)) ∈ (T : Subgroup (centralizer ({z} : Set G))) := by
    rw [← heq]
    exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
  exact hunot ⟨⟨u, huC⟩, huT, rfl⟩

end CFSG.Sporadic.Co2Smith
