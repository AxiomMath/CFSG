module

public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore
public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

section Bridge

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem inclMod_mem_map_iff {U : Subgroup (IntMod V hV)} {w : IntMod V hV} :
    inclMod hV w ∈ U.map (inclMod hV) ↔ w ∈ U :=
  Subgroup.mem_map_iff_mem (inclMod_injective hV)

theorem mem_map_inclMod_iff {U : Subgroup (IntMod V hV)} {v : G} :
    v ∈ U.map (inclMod hV) ↔ ∃ w ∈ U, w.val = v := by
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨w, hw, e⟩ => ⟨w, hw, e⟩, fun ⟨w, hw, e⟩ => ⟨w, hw, e⟩⟩

theorem map_inclMod_le (U : Subgroup (IntMod V hV)) : U.map (inclMod hV) ≤ V := by
  rintro _ ⟨w, -, rfl⟩
  exact w.val_mem

theorem mem_normalizer_map_inclMod_iff {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (U : Subgroup (IntMod V hV)) :
    x ∈ Subgroup.normalizer ((U.map (inclMod hV) : Subgroup G) : Set G) ↔
      convI hV ⟨x, hx⟩ ∈ stabSub U := by
  rw [mem_stabSub, Subgroup.mem_normalizer_iff]
  constructor
  · intro h u
    have h1 := h u.val
    have h2 : (convI hV ⟨x, hx⟩ u).val = x * u.val * x⁻¹ := convI_apply_val hV ⟨x, hx⟩ u
    have A : inclMod hV u ∈ U.map (inclMod hV) ↔ u ∈ U := inclMod_mem_map_iff hV
    have B : inclMod hV (convI hV ⟨x, hx⟩ u) ∈ U.map (inclMod hV) ↔
        convI hV ⟨x, hx⟩ u ∈ U := inclMod_mem_map_iff hV
    rw [inclMod_apply, h2] at B
    rw [inclMod_apply] at A
    exact B.symm.trans (h1.symm.trans A)
  · intro h g
    by_cases hg : g ∈ V
    · set u : IntMod V hV := IntMod.mk hV ⟨g, hg⟩ with hu
      have h2 : (convI hV ⟨x, hx⟩ u).val = x * g * x⁻¹ := convI_apply_val hV ⟨x, hx⟩ u
      have A : inclMod hV u ∈ U.map (inclMod hV) ↔ u ∈ U := inclMod_mem_map_iff hV
      have B : inclMod hV (convI hV ⟨x, hx⟩ u) ∈ U.map (inclMod hV) ↔
          convI hV ⟨x, hx⟩ u ∈ U := inclMod_mem_map_iff hV
      rw [inclMod_apply, h2] at B
      have A' : g ∈ U.map (inclMod hV) ↔ u ∈ U := A
      exact A'.trans ((h u).symm.trans B.symm)
    · constructor
      · intro hgU
        exact absurd (map_inclMod_le hV U hgU) hg
      · intro hgU
        exact absurd ((Subgroup.mem_normalizer_iff.mp hx g).mpr (map_inclMod_le hV U hgU)) hg

theorem mem_centralizer_map_inclMod_iff {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G))
    (U : Subgroup (IntMod V hV)) :
    m ∈ Subgroup.centralizer ((U.map (inclMod hV) : Subgroup G) : Set G) ↔
      ∀ u ∈ U, convI hV ⟨m, hm⟩ u = u := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have h1 := h u.val ⟨u, hu, rfl⟩
    apply IntMod.val_injective
    rw [convI_apply_val]
    calc m * u.val * m⁻¹ = (u.val * m) * m⁻¹ := by rw [← h1]
      _ = u.val := by group
  · rintro h v ⟨u, hu, rfl⟩
    have h1 := congrArg IntMod.val (h u hu)
    rw [convI_apply_val] at h1
    have : (inclMod hV u) * m = m * (inclMod hV u) := by
      rw [inclMod_apply]
      calc u.val * m = (m * u.val * m⁻¹) * m := by rw [h1]
        _ = m * u.val := by group
    exact this

theorem inf_centralizer_eq_preI {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {t : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) L₁ L₂ t) :
    M ⊓ Subgroup.centralizer (((commV L₂).map (inclMod hV) : Subgroup G) : Set G) =
      preI hV M hMN L₁ := by
  ext m
  rw [mem_preI hV]
  constructor
  · rintro ⟨hmM, hmC⟩
    refine ⟨hmM, ?_⟩
    rw [convHom_apply]
    have hmem : convI hV ⟨m, hMN hmM⟩ ∈ autI hV M := convI_mem_autI hV hmM (hMN hmM)
    refine (hS.mem_L₁_iff hmem).2 ?_
    exact (mem_centralizer_map_inclMod_iff hV (hMN hmM) (commV L₂)).1 hmC
  · rintro ⟨hmM, hmL⟩
    refine ⟨hmM, ?_⟩
    rw [convHom_apply] at hmL
    have hmem : convI hV ⟨m, hMN hmM⟩ ∈ autI hV M := convI_mem_autI hV hmM (hMN hmM)
    exact (mem_centralizer_map_inclMod_iff hV (hMN hmM) (commV L₂)).2 ((hS.mem_L₁_iff hmem).1 hmL)

end Bridge

structure Decomp153 {G : Type} [Group G] [Finite G] (T M V₁ V₂ : Subgroup G) (t : G) : Prop where
  le₁ : V₁ ≤ VZ T M
  le₂ : V₂ ≤ VZ T M
  inf : V₁ ⊓ V₂ = ⊥
  sup : V₁ ⊔ V₂ = VZ T M
  card₁ : Nat.card V₁ = 4
  card₂ : Nat.card V₂ = 4
  definite : ∃ q : ↥(VZ T M) → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧ IsPlusType q ∧
    autOn M (VZ T M) = orthogonalGroupOf q ∧
    ∀ (v : G) (hv : v ∈ VZ T M), q ⟨v, hv⟩ = 1 ↔ (v ∈ V₁ ∨ v ∈ V₂) ∧ v ≠ 1
  t_mem : t ∈ M
  swap₁ : ∀ v ∈ V₁, t * v * t⁻¹ ∈ V₂
  swap₂ : ∀ v ∈ V₂, t * v * t⁻¹ ∈ V₁
  t_sq : t * t ∈ Subgroup.centralizer (VZ T M : Set G)
  t_ne : t ∉ Subgroup.centralizer (VZ T M : Set G)
  comm₁ : ⁅VZ T M, M ⊓ Subgroup.centralizer (V₂ : Set G)⁆ = V₁
  comm₂ : ⁅VZ T M, M ⊓ Subgroup.centralizer (V₁ : Set G)⁆ = V₂
  iso₁ : Nonempty (autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M) ≃* Equiv.Perm (Fin 3))
  iso₂ : Nonempty (autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M) ≃* Equiv.Perm (Fin 3))
  inf_aut : autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M) ⊓
    autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M) = ⊥
  comm_aut : ∀ a ∈ autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M),
    ∀ b ∈ autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M), a * b = b * a
  conj_aut : ∀ ht : t ∈ Subgroup.normalizer (VZ T M : Set G),
    (autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M)).map
      (MulAut.conj (conjAct (VZ T M) ⟨t, ht⟩)).toMonoidHom =
        autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M)
  factor : ∀ ht : t ∈ Subgroup.normalizer (VZ T M : Set G),
    autOn M (VZ T M) = (autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M) ⊔
      autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M)) ⊔
        Subgroup.zpowers (conjAct (VZ T M) ⟨t, ht⟩)
  model : ∃ (hV : IsElemAbelian 2 (VZ T M)) (L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) hV)))
      (tb : MulAut (IntMod (VZ T M) hV)), OfourStruct (autI hV M) L₁ L₂ tb ∧
        V₁ = (commV L₁).map (inclMod hV) ∧ V₂ = (commV L₂).map (inclMod hV) ∧
        ∃ ht : t ∈ Subgroup.normalizer (VZ T M : Set G), conjAct (VZ T M) ⟨t, ht⟩ = tb

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem exists_decomp (h : Hyp153 G T Mc M) :
    ∃ (V₁ V₂ : Subgroup G) (t : G), Decomp153 T M V₁ V₂ t := by
  obtain ⟨q, L₁, L₂, tb, hq1, hq2, hq3, hX, hS, hns⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  obtain ⟨g, hgM, hg⟩ := (mem_autI hV).1 hS.t_mem
  have hM₁ := inf_centralizer_eq_preI hV hMN hS
  have hM₂ := inf_centralizer_eq_preI hV hMN hS.symm
  have hA₁ : autI hV (M ⊓ Subgroup.centralizer
      (((commV L₂).map (inclMod hV) : Subgroup G) : Set G)) = L₁ := by
    rw [hM₁]
    exact autI_preI hV hS.L₁_le
  have hA₂ : autI hV (M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) = L₂ := by
    rw [hM₂]
    exact autI_preI hV hS.L₂_le
  have hAut₁ : autOn (M ⊓ Subgroup.centralizer
      (((commV L₂).map (inclMod hV) : Subgroup G) : Set G)) (VZ T M) = L₁ := hA₁
  have hAut₂ : autOn (M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) (VZ T M) = L₂ := hA₂
  have hgconj : ∀ ht : (g : G) ∈ Subgroup.normalizer (VZ T M : Set G),
      conjAct (VZ T M) ⟨(g : G), ht⟩ = tb := fun ht => hg
  have hswap : ∀ (U U' : Subgroup (IntMod (VZ T M) hV)), (∀ u ∈ U, tb u ∈ U') →
      ∀ v ∈ U.map (inclMod hV), (g : G) * v * (g : G)⁻¹ ∈ U'.map (inclMod hV) := by
    intro U U' hUU' v hv
    obtain ⟨u, hu, rfl⟩ := (mem_map_inclMod_iff hV).1 hv
    refine ⟨tb u, hUU' u hu, ?_⟩
    rw [inclMod_apply, ← hg, convI_apply_val]
  refine ⟨(commV L₁).map (inclMod hV), (commV L₂).map (inclMod hV), (g : G), ?_⟩
  exact
    { le₁ := map_inclMod_le hV _
      le₂ := map_inclMod_le hV _
      inf := by
        rw [← Subgroup.map_inf _ _ _ (inclMod_injective hV), hS.inf, Subgroup.map_bot]
      sup := by
        rw [← Subgroup.map_sup, hS.sup, map_inclMod_top]
      card₁ := by
        rw [Subgroup.card_map_of_injective (inclMod_injective hV)]
        exact hS.card_U₁
      card₂ := by
        rw [Subgroup.card_map_of_injective (inclMod_injective hV)]
        exact (card_of_actsAsNaturalL2 hS.nat₂).2
      definite := by
        refine ⟨q, hq1, hq2, hq3, hX, fun v hv => ?_⟩
        have e1 : (IntMod.mk hV ⟨v, hv⟩ : IntMod (VZ T M) hV).val = v := rfl
        have hm₁ : v ∈ (commV L₁).map (inclMod hV) ↔ IntMod.mk hV ⟨v, hv⟩ ∈ commV L₁ :=
          inclMod_mem_map_iff hV (w := IntMod.mk hV ⟨v, hv⟩)
        have hm₂ : v ∈ (commV L₂).map (inclMod hV) ↔ IntMod.mk hV ⟨v, hv⟩ ∈ commV L₂ :=
          inclMod_mem_map_iff hV (w := IntMod.mk hV ⟨v, hv⟩)
        have hne : IntMod.mk hV ⟨v, hv⟩ ≠ (1 : IntMod (VZ T M) hV) ↔ v ≠ 1 := by
          constructor
          · intro h1 h2
            exact h1 (IntMod.val_injective (by rw [e1, h2]; rfl))
          · intro h1 h2
            exact h1 (by rw [← e1, h2]; rfl)
        have := hns (IntMod.mk hV ⟨v, hv⟩)
        rw [hm₁, hm₂, ← hne]
        exact this
      t_mem := hgM
      swap₁ := hswap _ _ hS.swap₁
      swap₂ := hswap _ _ hS.swap₂
      t_sq := by
        refine (convI_eq_one_iff hV (g * g)).1 ?_
        rw [map_mul, hg]
        exact hS.tsq
      t_ne := by
        intro hc
        have h1 : convI hV g = 1 := (convI_eq_one_iff hV g).2 hc
        rw [hg] at h1
        exact hS.t_not_mem_sup (h1 ▸ Subgroup.one_mem _)
      comm₁ := by
        rw [hM₁, commutator_eq_map_commV hV ((preI_le hV).trans hMN), autI_preI hV hS.L₁_le]
      comm₂ := by
        rw [hM₂, commutator_eq_map_commV hV ((preI_le hV).trans hMN), autI_preI hV hS.L₂_le]
      iso₁ := by
        rw [hAut₁]
        exact nonempty_equiv_perm hS.nat₁
      iso₂ := by
        rw [hAut₂]
        exact nonempty_equiv_perm hS.nat₂
      inf_aut := by
        rw [hAut₁, hAut₂]
        exact hS.Linf
      comm_aut := by
        intro a ha b hb
        rw [hAut₁] at ha
        rw [hAut₂] at hb
        exact hS.comm a ha b hb
      conj_aut := by
        intro ht
        rw [hAut₁, hAut₂, hgconj ht]
        exact (conjAut_eq_map tb L₁).symm.trans hS.conj₁
      factor := by
        intro ht
        rw [hAut₁, hAut₂, hgconj ht]
        exact hS.eq
      model := ⟨hV, L₁, L₂, tb, hS, rfl, rfl, g.2, hg⟩ }

end Hyp153

end CFSG.Quasithin
