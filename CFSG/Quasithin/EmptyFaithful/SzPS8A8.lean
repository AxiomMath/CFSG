module

public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs
public import CFSG.Quasithin.EmptyFaithful.SzPS8OvgMap
public import CFSG.Quasithin.EmptyFaithful.SzPS8A8Data
public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.G10Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
  CFSG.Quasithin.G11.P4InspOrth

namespace SzPS8

section Vec8

@[expose] def a8 : ↥(permCore 8) :=
  ⟨![1, 1, 1, 1, 0, 0, 0, 0], by
    show ∑ i : Fin 8, (![1, 1, 1, 1, 0, 0, 0, 0] : Fin 8 → ZMod 2) i = 0
    decide⟩

@[expose] def w8 : p4insporth_V8 := Submodule.Quotient.mk a8

@[expose] def d1 : Perm8 :=
  Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 7 * (Equiv.swap 1 5 * Equiv.swap 1 2 *
    Equiv.swap 1 6)

@[expose] def d2 : Perm8 :=
  Equiv.swap 0 5 * Equiv.swap 0 2 * Equiv.swap 0 6 * (Equiv.swap 1 4 * Equiv.swap 1 3 *
    Equiv.swap 1 7)

theorem d1_mem : d1 ∈ T8 ⊓ alternatingGroup (Fin 8) :=
  mem_T8_inf_iff.2 (by decide +kernel)

theorem d2_mem : d2 ∈ T8 ⊓ alternatingGroup (Fin 8) :=
  mem_T8_inf_iff.2 (by decide +kernel)

theorem mk_eq_iff (x y : ↥(permCore 8)) :
    (Submodule.Quotient.mk y : p4insporth_V8) = Submodule.Quotient.mk x ↔
      (∀ i, (y : Fin 8 → ZMod 2) i = (x : Fin 8 → ZMod 2) i) ∨
        (∀ i, (y : Fin 8 → ZMod 2) i = (x : Fin 8 → ZMod 2) i + 1) := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply, p4insporth_ker8]
  constructor
  · rintro (h | ⟨-, h⟩)
    · left
      intro i
      have := congrFun (congrArg Subtype.val h) i
      simpa [sub_eq_zero] using this
    · right
      intro i
      have h' := h i
      simp only [Submodule.coe_sub, Pi.sub_apply] at h'
      exact sub_eq_iff_eq_add'.1 h'
  · rintro (h | h)
    · left
      apply Subtype.ext
      funext i
      simp [h i]
    · right
      refine ⟨by decide, fun i => ?_⟩
      simp [h i]

theorem fixed_finite : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    ((∀ i, x (d1⁻¹ i) = x i) ∨ (∀ i, x (d1⁻¹ i) = x i + 1)) →
    ((∀ i, x (d2⁻¹ i) = x i) ∨ (∀ i, x (d2⁻¹ i) = x i + 1)) →
    x = 0 ∨ x = (fun _ => 1) ∨ x = ![1, 1, 1, 1, 0, 0, 0, 0] ∨
      x = ![0, 0, 0, 0, 1, 1, 1, 1] := by
  decide +kernel

theorem c8_move_fin :
    ¬ ((∀ i : Fin 8, (![1, 1, 1, 1, 0, 0, 0, 0] : Fin 8 → ZMod 2) (c8⁻¹ i) =
        ![1, 1, 1, 1, 0, 0, 0, 0] i) ∨
      (∀ i : Fin 8, (![1, 1, 1, 1, 0, 0, 0, 0] : Fin 8 → ZMod 2) (c8⁻¹ i) =
        ![1, 1, 1, 1, 0, 0, 0, 0] i + 1)) := by
  decide +kernel

theorem fixed_class8 (w : p4insporth_V8) (hw0 : w ≠ 0)
    (hfix : ∀ s ∈ T8 ⊓ alternatingGroup (Fin 8), p4insporth_perm8Hom s w = w) : w = w8 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have h1 := hfix d1 d1_mem
  have h2 := hfix d2 d2_mem
  rw [p4insporth_perm8Hom_mk, mk_eq_iff] at h1 h2
  have hsum : ∑ i, (x : Fin 8 → ZMod 2) i = 0 := x.2
  have key := fixed_finite (x : Fin 8 → ZMod 2) hsum h1 h2
  rcases key with h | h | h | h
  · exfalso
    apply hw0
    have : x = 0 := Subtype.ext h
    rw [this]
    exact Submodule.Quotient.mk_zero _
  · exfalso
    apply hw0
    rw [← Submodule.mkQ_apply, p4insporth_ker8]
    exact Or.inr ⟨by decide, fun i => by rw [h]⟩
  · have : x = a8 := Subtype.ext h
    rw [this, w8]
  · rw [w8, mk_eq_iff]
    right
    intro i
    rw [h]
    fin_cases i <;> decide

theorem c8_moves : p4insporth_perm8Hom c8 w8 ≠ w8 := by
  rw [w8, p4insporth_perm8Hom_mk, Ne, mk_eq_iff]
  exact c8_move_fin

end Vec8

section Model

theorem false_of_model8 {K : Subgroup Perm8} (hK : K = alternatingGroup (Fin 8) ∨ K = ⊤)
    {S' : Subgroup (p4insporth_V8 ≃ₗ[ZMod 2] p4insporth_V8)}
    (hS' : IsSylowTwoOf S' (K.map p4insporth_perm8Hom)) {v' : p4insporth_V8} (hv0 : v' ≠ 0)
    (hfix : ∀ s ∈ S', s v' = v') (hF : OvgFix S' p4insporth_H8 v') : False := by
  have hAK : alternatingGroup (Fin 8) ≤ K := by
    rcases hK with rfl | rfl
    · exact le_rfl
    · exact le_top
  have hT8K : IsSylowTwoOf (T8 ⊓ K) K := by
    rcases hK with rfl | rfl
    · exact isSylowTwoOf_T8_inf
    · rw [inf_top_eq]
      exact isSylowTwoOf_T8_top
  have hT' : IsSylowTwoOf ((T8 ⊓ K).map p4insporth_perm8Hom) (K.map p4insporth_perm8Hom) :=
    isSylowTwoOf_map_of_injective p4insporth_perm8Hom_injective hT8K
  obtain ⟨γ, hγ, hγT⟩ := exists_conj_eq_of_isSylowTwoOf hS' hT'
  obtain ⟨g, hgK, rfl⟩ := hγ
  have hnorm : ∀ n ∈ p4insporth_H8,
      (p4insporth_perm8Hom g)⁻¹ * n * p4insporth_perm8Hom g ∈ p4insporth_H8 := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨g⁻¹ * τ * g, ?_, by simp [map_mul, map_inv]⟩
    have := (alternatingGroup.normal : (alternatingGroup (Fin 8)).Normal).conj_mem τ hτ g⁻¹
    simpa using this
  have hF' := hF.conj_of hnorm hγT
  have hw0 : p4insporth_perm8Hom g v' ≠ 0 := fun h0 =>
    hv0 ((map_eq_zero_iff (p4insporth_perm8Hom g) (p4insporth_perm8Hom g).injective).mp h0)
  have hwfix : ∀ s ∈ T8 ⊓ alternatingGroup (Fin 8),
      p4insporth_perm8Hom s (p4insporth_perm8Hom g v') = p4insporth_perm8Hom g v' := by
    intro s hs
    have hs' : p4insporth_perm8Hom s ∈ (T8 ⊓ K).map p4insporth_perm8Hom :=
      ⟨s, ⟨hs.1, hAK hs.2⟩, rfl⟩
    obtain ⟨y, hy, hys⟩ := (hγT _).mp hs'
    have h1 : p4insporth_perm8Hom g (y v') = p4insporth_perm8Hom g v' := by rw [hfix y hy]
    calc p4insporth_perm8Hom s (p4insporth_perm8Hom g v')
        = (p4insporth_perm8Hom g * y * (p4insporth_perm8Hom g)⁻¹)
            (p4insporth_perm8Hom g v') := by rw [← hys]
      _ = p4insporth_perm8Hom g (y v') := by simp
      _ = p4insporth_perm8Hom g v' := h1
  have hw := fixed_class8 _ hw0 hwfix
  have hJA : J8.map p4insporth_perm8Hom ≤ p4insporth_H8 := Subgroup.map_mono J8_le_alt
  have hJn : ∀ t ∈ (T8 ⊓ K).map p4insporth_perm8Hom, ∀ j' ∈ J8.map p4insporth_perm8Hom,
      t * j' * t⁻¹ ∈ J8.map p4insporth_perm8Hom := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨j, hj, rfl⟩
    refine ⟨s * j * s⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 (T8_le_normalizer_J8 hs.1) j).1 hj
  have hidx : ((T8 ⊓ K).map p4insporth_perm8Hom).relIndex (J8.map p4insporth_perm8Hom) = 3 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ p4insporth_perm8Hom_injective,
      ← Subgroup.relIndex_inf_mul_relIndex, inf_of_le_right (J8_le_alt.trans hAK),
      Subgroup.relIndex_eq_one.mpr (J8_le_alt.trans hAK), mul_one]
    exact relIndex_T8_J8
  have := hF' (J8.map p4insporth_perm8Hom) hJA hJn (Or.inl hidx)
    (p4insporth_perm8Hom c8) ⟨c8, c8_mem, rfl⟩
  rw [hw] at this
  exact c8_moves this

end Model

section Concl5

theorem alt_le_of_normal {K N : Subgroup Perm8} (hK : K = alternatingGroup (Fin 8) ∨ K = ⊤)
    (hNK : N ≤ K) (hn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hN1 : N ≠ ⊥) :
    alternatingGroup (Fin 8) ≤ N := by
  rcases hK with rfl | rfl
  · have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    have hnorm : (N.subgroupOf (alternatingGroup (Fin 8))).Normal := by
      refine ⟨fun n hn' g => ?_⟩
      exact hn g.1 g.2 n hn'
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 8)))
      with h | h
    · exfalso
      apply hN1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNK hx⟩ : ↥(alternatingGroup (Fin 8))) ∈
          N.subgroupOf (alternatingGroup (Fin 8)) := hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ N.subgroupOf (alternatingGroup (Fin 8)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
  · have : N.Normal := ⟨fun n hn' g => hn g (Subgroup.mem_top g) n hn'⟩
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((Subgroup.nontrivial_iff_ne_bot N).2 hN1)

theorem false_of_concl5 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}
    (S : OvgSymp B Γ T0 v) (hC5 : G112Concl5 B Γ) : False := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨hdim, q, hq, -, ⟨W, hW3, hWq⟩, hΓO, hrel⟩ := hC5
  have hf : IsSymplectic B := ⟨S.alt, S.nondegenerate⟩
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hq) :=
    ⟨W, by rw [hW3, hdim], fun x hx => hWq x hx⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff (n := 3)
    (p4insporth_nondegenerate_quad hf hq)
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    hdim p4insporth_finrank8 (iff_of_true hplus p4insporth_plus8)
  have hι : ∀ x, p4insporth_q8 (e.toLinearEquiv x) = q x := fun x => e.map_app x
  set ι := e.toLinearEquiv with hιdef
  set c := p4insporth_cg ι with hcdef
  have hc : ∀ (γ : V ≃ₗ[ZMod 2] V) (x : V), c γ (ι x) = ι (γ x) := fun γ x => by
    rw [hcdef, p4insporth_cg_apply, LinearEquiv.symm_apply_apply]
  have hOeq : orthogonalSubgroupOf q = orthSub q := by
    ext g
    exact Iff.rfl
  rw [hOeq] at hΓO hrel
  have hmapO : (orthSub q).map c.toMonoidHom = orthSub p4insporth_q8 :=
    p4insporth_map_cg_orthSub ι hι
  set Γ' := Γ.map c.toMonoidHom with hΓ'def
  have hΓ'le : Γ' ≤ p4insporth_perm8Hom.range := by
    rw [p4insporth_range_perm8, ← hmapO]
    exact Subgroup.map_mono hΓO
  set K := Γ'.comap p4insporth_perm8Hom with hKdef
  have hΓ'K : Γ' = K.map p4insporth_perm8Hom := by
    rw [hKdef, Subgroup.map_comap_eq, inf_eq_right.2 hΓ'le]
  have hKindex : K.index ≤ 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective Γ (orthSub q) (f := c.toMonoidHom) c.injective
    rw [hmapO, ← p4insporth_range_perm8] at h1
    rw [← hΓ'def, hΓ'K, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective K ⊤ p4insporth_perm8Hom_injective,
      Subgroup.relIndex_top_right] at h1
    exact h1.trans_le hrel
  have hK : K = alternatingGroup (Fin 8) ∨ K = ⊤ := by
    have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : K.index = 1 ∨ K.index = 2) with h | h
    · exact Or.inr (Subgroup.index_eq_one.1 h)
    · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)
  obtain ⟨N, hNn, hN1, hF0⟩ := S.toOvgSetting.exists_normal_subtype
  set N' : Subgroup (p4insporth_V8 ≃ₗ[ZMod 2] p4insporth_V8) :=
    (N.map Γ.subtype).map c.toMonoidHom with hN'def
  have hN'Γ' : N' ≤ Γ' := Subgroup.map_mono (Subgroup.map_subtype_le N)
  have hN'norm : ∀ γ ∈ Γ', ∀ x ∈ N', γ * x * γ⁻¹ ∈ N' := by
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨γ * (n : V ≃ₗ[ZMod 2] V) * γ⁻¹, ⟨⟨γ, hγ⟩ * n * ⟨γ, hγ⟩⁻¹,
      hNn.conj_mem n hn ⟨γ, hγ⟩, rfl⟩, by simp [map_mul, map_inv]⟩
  set N'' := N'.comap p4insporth_perm8Hom with hN''def
  have hN''K : N'' ≤ K := fun n hn => hN'Γ' hn
  have hN''norm : ∀ k ∈ K, ∀ n ∈ N'', k * n * k⁻¹ ∈ N'' := by
    intro k hk n hn
    have := hN'norm (p4insporth_perm8Hom k) hk (p4insporth_perm8Hom n) hn
    show p4insporth_perm8Hom (k * n * k⁻¹) ∈ N'
    rw [map_mul, map_mul, map_inv]
    exact this
  have hN''1 : N'' ≠ ⊥ := by
    intro hbot
    apply hN1
    have hN'bot : N' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := hΓ'le (hN'Γ' hx)
      have hn : n ∈ N'' := hx
      rw [hbot, Subgroup.mem_bot] at hn
      rw [hn, map_one]
      exact Subgroup.one_mem _
    have h1 : N.map Γ.subtype = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ c.injective).mp hN'bot
    exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h1
  have hAN'' : alternatingGroup (Fin 8) ≤ N'' := alt_le_of_normal hK hN''K hN''norm hN''1
  have hHN' : p4insporth_H8 ≤ N' := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hAN'' hτ
  have hF1 : OvgFix (T0.map c.toMonoidHom) p4insporth_H8 (ι v) :=
    (hF0.map c ι hc).mono hHN'
  have hS'syl : IsSylowTwoOf (T0.map c.toMonoidHom) (K.map p4insporth_perm8Hom) := by
    rw [← hΓ'K]
    exact isSylowTwoOf_map_of_injective c.injective S.sylow
  have hv0 : ι v ≠ 0 := fun h0 => S.ne_zero (ι.injective (by rw [h0, map_zero]))
  have hfix : ∀ s ∈ T0.map c.toMonoidHom, s (ι v) = ι v := by
    rintro _ ⟨t, ht, rfl⟩
    change c t (ι v) = ι v
    rw [hc, S.fix t ht]
  exact false_of_model8 hK hS'syl hv0 hfix hF1

theorem excl5_of_ovg (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) :
    Lemma14315Excl5 := by
  intro G _ _ T M hyp hnot hU D hc
  obtain ⟨v, S⟩ := exists_ovgSymp h11 h113 h35 hyp hnot hU D
  exact (false_of_concl5 S hc).elim

end Concl5

end SzPS8

end CFSG.Quasithin
