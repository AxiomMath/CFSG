module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Group

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

theorem mem_ker_conjPermHom_iff {H U : Subgroup G} {X : Set G}
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hXU : X ⊆ U) (hUX : U ≤ Subgroup.closure X)
    (g : H) : g ∈ (conjPermHom H X hX).ker ↔ (g : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [mem_ker_conjPermHom]
  constructor
  · intro hfix
    have hC : (g : G) ∈ Subgroup.centralizer X := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have e := hfix x hx
      calc x * g = (g * x * (g : G)⁻¹) * g := by rw [e]
        _ = g * x := by group
    rw [← Subgroup.centralizer_closure] at hC
    exact Subgroup.centralizer_le hUX hC
  · intro hC x hx
    rw [← Subgroup.mem_centralizer_iff.mp hC x (hXU hx), mul_inv_cancel_right]

theorem ker_conjPermHom_eq [Finite G] {H U : Subgroup G} {X : Set G}
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hXU : X ⊆ U) (hUX : U ≤ Subgroup.closure X)
    (hker : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H) :
    (conjPermHom H X hX).ker = CFSG.Open.pCore 2 H := by
  ext g
  rw [mem_ker_conjPermHom_iff hX hXU hUX]
  constructor
  · intro hg
    have hmem : (g : G) ∈ pCoreOf 2 H := hker ▸ ⟨g.2, hg⟩
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp hmem
  · intro hg
    have hmem : (g : G) ∈ pCoreOf 2 H := (Subgroup.mem_map_iff_mem H.subtype_injective).mpr hg
    exact (hker.symm ▸ hmem : (g : G) ∈ H ⊓ _).2

theorem card_range_conjPermHom [Finite G] {H U : Subgroup G} {X : Set G}
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hXU : X ⊆ U) (hUX : U ≤ Subgroup.closure X) :
    Nat.card (conjPermHom H X hX).range = (H ⊓ Subgroup.centralizer (U : Set G)).relIndex H := by
  have e1 := Subgroup.relIndex_ker (⊤ : Subgroup H) (conjPermHom H X hX)
  rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map] at e1
  rw [← e1]
  have e2 : (conjPermHom H X hX).ker = (H ⊓ Subgroup.centralizer (U : Set G)).subgroupOf H := by
    ext g
    rw [mem_ker_conjPermHom_iff hX hXU hUX, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [e2]
  rfl

theorem quotientIso_sym3 [Finite G] {H U : Subgroup G} (hU4 : Nat.card U = 4)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hker : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H)
    (hcard : 6 ≤ (H ⊓ Subgroup.centralizer (U : Set G)).relIndex H) :
    quasithinO2QuotientIso H (Equiv.Perm (Fin 3)) := by
  classical
  set X : Set G := (U : Set G) \ {1} with hXdef
  have hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    rintro h hh x ⟨hxU, hx1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHU hh) x).mp hxU, fun he => hx1 ?_⟩
    have he' : h * x * h⁻¹ = 1 := he
    have : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [this, he']
    simp
  have hXU : X ⊆ U := fun x hx => hx.1
  have hUX : U ≤ Subgroup.closure X := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hu, hu1⟩
  have hXcard : Nat.card X = 3 := by
    rw [Nat.card_coe_set_eq, hXdef, Set.ncard_sdiff_singleton_of_mem (U.one_mem),
      ← Nat.card_coe_set_eq]
    show Nat.card U - 1 = 3
    rw [hU4]
  set e : X ≃ Fin 3 := Finite.equivFinOfCardEq hXcard
  set ψ := conjPermHom H X hX
  refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp ψ, ?_, ?_⟩
  · have hrange : ψ.range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ (le_antisymm ?_ ?_)
      · exact Subgroup.card_le_card_group _
      · rw [card_range_conjPermHom hX hXU hUX, Nat.card_perm, hXcard]
        exact hcard
    intro σ
    obtain ⟨g, hg⟩ := MonoidHom.range_eq_top.mp hrange ((Equiv.permCongrHom e).symm σ)
    refine ⟨g, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hg, MulEquiv.apply_symm_apply]
  · rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective]
    exact ker_conjPermHom_eq hX hXU hUX hker

theorem exists_equiv_fin_six {α : Type*} {X₁ X₂ : Set α} (hd : Disjoint X₁ X₂)
    (h₁ : Nat.card X₁ = 3) (h₂ : Nat.card X₂ = 3) :
    ∃ e : ↑(X₁ ∪ X₂) ≃ Fin 6, ∀ x : ↑(X₁ ∪ X₂), ((e x).val < 3 ↔ (x : α) ∈ X₁) := by
  classical
  have : Finite X₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; norm_num)
  have : Finite X₂ := Nat.finite_of_card_ne_zero (by rw [h₂]; norm_num)
  let e₁ := Finite.equivFinOfCardEq h₁
  let e₂ := Finite.equivFinOfCardEq h₂
  let e : ↑(X₁ ∪ X₂) ≃ Fin (3 + 3) :=
    (Equiv.Set.union hd).trans ((Equiv.sumCongr e₁ e₂).trans finSumFinEquiv)
  refine ⟨e, fun x => ?_⟩
  by_cases hx : (x : α) ∈ X₁
  · have h1 : e x = Fin.castAdd 3 (e₁ ⟨x, hx⟩) := by
      show finSumFinEquiv (Equiv.sumCongr e₁ e₂ (Equiv.Set.union hd x)) = _
      rw [Equiv.Set.union_apply_left hd hx, Equiv.sumCongr_apply, Sum.map_inl,
        finSumFinEquiv_apply_left]
    rw [h1]
    simp only [Fin.val_castAdd, hx, iff_true]
    exact (e₁ ⟨x, hx⟩).isLt
  · have hx2 : (x : α) ∈ X₂ := x.2.resolve_left hx
    have h1 : e x = Fin.natAdd 3 (e₂ ⟨x, hx2⟩) := by
      show finSumFinEquiv (Equiv.sumCongr e₁ e₂ (Equiv.Set.union hd x)) = _
      rw [Equiv.Set.union_apply_right hd hx2, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right]
    rw [h1]
    simp only [Fin.val_natAdd, hx, iff_false, not_lt]
    exact Nat.le_add_right 3 _

theorem div_three_eq_iff (i j : Fin 6) : i.val / 3 = j.val / 3 ↔ (i.val < 3 ↔ j.val < 3) := by
  revert i j
  decide

theorem card_diff_one [Finite G] {A : Subgroup G} (hA : Nat.card A = 4) :
    Nat.card ↑((A : Set G) \ {1}) = 3 := by
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem A.one_mem, ← Nat.card_coe_set_eq]
  change Nat.card A - 1 = 3
  rw [hA]

theorem conj_mem_diff_one {A : Subgroup G} {g x : G} (hx : x ∈ (A : Set G) \ {1}) :
    g * x * g⁻¹ ∈ (cjSub g A : Set G) \ {1} := by
  refine ⟨?_, fun he => hx.2 ?_⟩
  · show g * x * g⁻¹ ∈ cjSub g A
    rw [mem_cjSub]
    simpa [mul_assoc] using hx.1
  · have he' : g * x * g⁻¹ = 1 := he
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [Set.mem_singleton_iff, this, he']
    group

theorem conj_mem_union {V₁ V₂ : Subgroup G} (h12 : V₁ ⊓ V₂ = ⊥) {g : G}
    (hg : (cjSub g V₁ = V₁ ∧ cjSub g V₂ = V₂) ∨ (cjSub g V₁ = V₂ ∧ cjSub g V₂ = V₁)) {x : G}
    (hx : x ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1})) :
    g * x * g⁻¹ ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}) ∧
      ((g * x * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ x ∈ (V₁ : Set G) \ {1}) ∧
          (∀ y ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}),
            (g * y * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ y ∈ (V₁ : Set G) \ {1})) ∨
        (g * x * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ x ∉ (V₁ : Set G) \ {1}) ∧
          (∀ y ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}),
            (g * y * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ y ∉ (V₁ : Set G) \ {1}))) := by
  have hd : ∀ y, y ∈ (V₁ : Set G) \ {1} → y ∉ (V₂ : Set G) \ {1} := fun y h1 h2 => h1.2 (by
    have hy : y ∈ V₁ ⊓ V₂ := ⟨h1.1, h2.1⟩
    rw [h12] at hy
    exact hy)
  rcases hg with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · have key : ∀ y ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}),
        g * y * g⁻¹ ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}) ∧
          (g * y * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ y ∈ (V₁ : Set G) \ {1}) := by
      intro y hy
      rcases hy with hy | hy
      · have h1 := conj_mem_diff_one (g := g) hy
        rw [e₁] at h1
        exact ⟨Or.inl h1, iff_of_true h1 hy⟩
      · have h1 := conj_mem_diff_one (g := g) hy
        rw [e₂] at h1
        exact ⟨Or.inr h1, iff_of_false (fun h => hd _ h h1) (fun h => hd _ h hy)⟩
    exact ⟨(key x hx).1, Or.inl ⟨(key x hx).2, fun y hy => (key y hy).2⟩⟩
  · have key : ∀ y ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}),
        g * y * g⁻¹ ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}) ∧
          (g * y * g⁻¹ ∈ (V₁ : Set G) \ {1} ↔ y ∉ (V₁ : Set G) \ {1}) := by
      intro y hy
      rcases hy with hy | hy
      · have h1 := conj_mem_diff_one (g := g) hy
        rw [e₁] at h1
        exact ⟨Or.inr h1, iff_of_false (fun h => hd _ h h1) (fun h => h hy)⟩
      · have h1 := conj_mem_diff_one (g := g) hy
        rw [e₂] at h1
        exact ⟨Or.inl h1, iff_of_true h1 (fun h => hd _ h hy)⟩
    exact ⟨(key x hx).1, Or.inr ⟨(key x hx).2, fun y hy => (key y hy).2⟩⟩

theorem quotientIso_wreath [Finite G] {H V₁ V₂ : Subgroup G} (h₁ : Nat.card V₁ = 4)
    (h₂ : Nat.card V₂ = 4) (h12 : V₁ ⊓ V₂ = ⊥)
    (hperm : ∀ g ∈ H, (cjSub g V₁ = V₁ ∧ cjSub g V₂ = V₂) ∨ (cjSub g V₁ = V₂ ∧ cjSub g V₂ = V₁))
    (hker : H ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) = pCoreOf 2 H)
    (hcard : 72 ≤ (H ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G)).relIndex H) :
    quasithinO2QuotientIso H wreathSThreeTwo := by
  classical
  have hd : Disjoint ((V₁ : Set G) \ {1}) ((V₂ : Set G) \ {1}) := by
    refine Set.disjoint_left.mpr fun x hx1 hx2 => hx1.2 ?_
    have hx : x ∈ V₁ ⊓ V₂ := ⟨hx1.1, hx2.1⟩
    rw [h12] at hx
    exact hx
  have hX : ∀ h ∈ H, ∀ x ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}),
      h * x * h⁻¹ ∈ ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}) := fun g hg x hx =>
    (conj_mem_union h12 (hperm g hg) hx).1
  have hXU : ((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}) ⊆ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
    rintro x (hx | hx)
    · exact Subgroup.mem_sup_left hx.1
    · exact Subgroup.mem_sup_right hx.1
  have hUX : V₁ ⊔ V₂ ≤ Subgroup.closure (((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1})) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Or.inl ⟨hu, hu1⟩)
    · by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Or.inr ⟨hu, hu1⟩)
  obtain ⟨e, he⟩ := exists_equiv_fin_six hd (card_diff_one h₁) (card_diff_one h₂)
  let φ := conjPermHom H (((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1})) hX
  let ψ := (Equiv.permCongrHom e).toMonoidHom.comp φ
  have hψapp : ∀ (g : H) (x : ↑(((V₁ : Set G) \ {1}) ∪ ((V₂ : Set G) \ {1}))),
      ψ g (e x) = e (φ g x) := fun g x => by
    show e (φ g (e.symm (e x))) = e (φ g x)
    rw [Equiv.symm_apply_apply]
  have hψW : ∀ g, ψ g ∈ wreathSThreeTwo := by
    intro g i j
    obtain ⟨x, rfl⟩ := e.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    rw [hψapp, hψapp, div_three_eq_iff, div_three_eq_iff, he, he, he, he]
    change ((x : G) ∈ (V₁ : Set G) \ {1} ↔ (y : G) ∈ (V₁ : Set G) \ {1}) ↔
      ((g : G) * x * (g : G)⁻¹ ∈ (V₁ : Set G) \ {1} ↔
        (g : G) * y * (g : G)⁻¹ ∈ (V₁ : Set G) \ {1})
    rcases (conj_mem_union h12 (hperm g g.2) x.2).2 with ⟨hx, hall⟩ | ⟨hx, hall⟩
    · rw [hx, hall y y.2]
    · rw [hx, hall y y.2]
      tauto
  have hrange : ψ.range = wreathSThreeTwo := by
    refine Subgroup.eq_of_le_of_card_ge (fun σ hσ => ?_) ?_
    · obtain ⟨g, rfl⟩ := hσ
      exact hψW g
    · have e1 : Nat.card ψ.range = Nat.card φ.range := by
        have hr : ψ.range = φ.range.map (Equiv.permCongrHom e).toMonoidHom :=
          MonoidHom.range_comp _ _
        rw [hr, Subgroup.card_map_of_injective (Equiv.permCongrHom e).injective]
      rw [card_wreathSThreeTwo, e1, card_range_conjPermHom hX hXU hUX]
      exact hcard
  refine ⟨ψ.codRestrict wreathSThreeTwo hψW, ?_, ?_⟩
  · rintro ⟨σ, hσ⟩
    rw [← hrange] at hσ
    obtain ⟨g, hg⟩ := hσ
    exact ⟨g, Subtype.ext hg⟩
  · rw [MonoidHom.ker_codRestrict, MonoidHom.ker_comp_of_injective _ _
      (Equiv.permCongrHom e).injective]
    exact ker_conjPermHom_eq hX hXU hUX hker

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
