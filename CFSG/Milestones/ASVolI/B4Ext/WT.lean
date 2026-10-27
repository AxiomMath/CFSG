module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.GroupTheory.GLnTwoSplitting Module

section WFix

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49x_wfix (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {x | ∀ e ∈ E, e x = x}
  add_mem' := fun {x y} hx hy e he => by rw [map_add, hx e he, hy e he]
  zero_mem' := fun e _ => map_zero e
  smul_mem' := fun c x hx e he => by rw [map_smul, hx e he]

@[expose] def burnsideB49x_wcomm (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {y | ∃ e ∈ E, ∃ x, e x - x = y}

theorem burnsideB49x_sub_mem_wcomm {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) (x : W) : e x - x ∈ burnsideB49x_wcomm E :=
  Submodule.subset_span ⟨e, he, x, rfl⟩

theorem burnsideB49x_wcomm_le_ker {E : Subgroup (W ≃ₗ[ZMod 2] W)} {ψ : Dual (ZMod 2) W}
    (h : ∀ e ∈ E, ∀ x, ψ (e x - x) = 0) : burnsideB49x_wcomm E ≤ LinearMap.ker ψ := by
  rw [burnsideB49x_wcomm, Submodule.span_le]
  rintro _ ⟨e, he, x, rfl⟩
  exact h e he x

theorem burnsideB49x_card_le_hom [FiniteDimensional (ZMod 2) W]
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Nat.card E ≤ 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) (burnsideB49x_wfix E)) *
      finrank (ZMod 2) (burnsideB49x_wcomm E)) := by
  classical
  set C := burnsideB49x_wfix E
  set B := burnsideB49x_wcomm E
  let D : ↥E → (W →ₗ[ZMod 2] W) := fun e => ((e : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) - LinearMap.id
  have hDB : ∀ e : ↥E, ∀ x, D e x ∈ B := fun e x => burnsideB49x_sub_mem_wcomm e.2 x
  have hDC : ∀ e : ↥E, C ≤ LinearMap.ker (LinearMap.codRestrict B (D e) (hDB e)) := by
    intro e x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero, D, LinearMap.sub_apply,
      LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [hx e e.2, sub_self]
  let Φ : ↥E → (W ⧸ C →ₗ[ZMod 2] ↥B) := fun e =>
    C.liftQ (LinearMap.codRestrict B (D e) (hDB e)) (hDC e)
  have hΦ : Function.Injective Φ := by
    intro e e' h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have h1 := congrArg (fun F : W ⧸ C →ₗ[ZMod 2] ↥B => ((F (Submodule.Quotient.mk x) : ↥B) : W)) h
    simp only [Φ, Submodule.liftQ_apply, LinearMap.codRestrict_apply, D, LinearMap.sub_apply,
      LinearEquiv.coe_coe, LinearMap.id_apply] at h1
    exact sub_left_injective h1
  have hfin : Finite (W ⧸ C →ₗ[ZMod 2] ↥B) := Module.finite_of_finite (ZMod 2)
  calc Nat.card E ≤ Nat.card (W ⧸ C →ₗ[ZMod 2] ↥B) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) C) * finrank (ZMod 2) B) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap,
        Submodule.finrank_quotient]

end WFix

section WT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

@[expose] noncomputable def burnsideB49x_hatW (A : Subgroup (MulAut V)) :
    Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) :=
  (A.subgroupOf G).map (burnsideB49_iota hV U G hG)

theorem burnsideB49x_iota_mk (g : ↥G) (v : V) :
    burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
      F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v)) := by
  change F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk v)) = _
  rw [burnsideB49_quotAut_mk]

theorem burnsideB49x_card_hatW (hinj : Function.Injective (burnsideB49_iota hV U G hG))
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) :
    Nat.card (burnsideB49x_hatW hV U G hG A) = Nat.card A := by
  rw [burnsideB49x_hatW, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv

theorem burnsideB49x_hatW_elem {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    (∀ e ∈ burnsideB49x_hatW hV U G hG A, ∀ e' ∈ burnsideB49x_hatW hV U G hG A,
      e * e' = e' * e) ∧ ∀ e ∈ burnsideB49x_hatW hV U G hG A, e * e = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ hg _ hg')
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_one (burnsideB49_iota hV U G hG)]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact hA.2 _ hg

theorem burnsideB49x_card_fixV_le_W [Finite V] (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV A ⊓ U) *
      Nat.card ↥(burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A)) := by
  let f : ↥(fixV A) →* V ⧸ U := (QuotientGroup.mk' U).comp (fixV A).subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : f.ker = U.subgroupOf (fixV A) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hker2 : Nat.card f.ker = Nat.card ↥(fixV A ⊓ U) := by
    rw [hker, ← Subgroup.card_map_of_injective (f := (fixV A).subtype)
      (Subgroup.subtype_injective _), Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Nat.card f.range ≤
      Nat.card ↥(burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A)) := by
    refine Nat.card_le_card_of_injective
      (fun y => ⟨F2Vec.ofV (burnsideB49_hW hV U) (y : V ⧸ U), ?_⟩) ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨v, hv⟩ := y.2
      rw [← hv]
      show burnsideB49_iota hV U G hG g (F2Vec.ofV _ (QuotientGroup.mk ((v : V)))) =
        F2Vec.ofV _ (QuotientGroup.mk (v : V))
      rw [burnsideB49x_iota_mk]
      have hfix : (g : MulAut V) (v : V) = v := v.2 _ hg
      rw [hfix]
    · intro y y' h
      have h' := congrArg (fun x : ↥(burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A)) =>
        F2Vec.toV (burnsideB49_hW hV U) (x : burnsideB49_W hV U)) h
      exact Subtype.ext h'
  calc Nat.card ↥(fixV A) = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ _ := by
      rw [hker2]
      exact Nat.mul_le_mul_left _ hrange

theorem burnsideB49x_card_fixU_le_dual [Finite V] (φ : V ⧸ U ≃* DualGrp ↥U)
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A ⊓ U) ≤
      Nat.card ↥(burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)).dualAnnihilator := by
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  let ψ : ↥U → Dual (ZMod 2) (burnsideB49_W hV U) := fun u =>
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk'
      (fun w => Multiplicative.toAdd ((φ (F2Vec.toV (burnsideB49_hW hV U) w)) u))
      (fun w w' => by
        rw [F2Vec.toV_add, map_mul, DualGrp.mul_apply, toAdd_mul]))
  have hψ : ∀ u w, ψ u w = Multiplicative.toAdd ((φ (F2Vec.toV (burnsideB49_hW hV U) w)) u) :=
    fun u w => rfl
  have hψinj : Function.Injective ψ := by
    intro u u' h
    by_contra hne
    have hne' : u * u'⁻¹ ≠ 1 := fun h' => hne (mul_inv_eq_one.1 h')
    obtain ⟨χ, hχ⟩ := exists_dualChar_ne_one hU2 hne'
    obtain ⟨x, hx⟩ := φ.surjective χ
    apply hχ
    have h1 := congrArg (fun F : Dual (ZMod 2) (burnsideB49_W hV U) =>
      F (F2Vec.ofV (burnsideB49_hW hV U) x)) h
    simp only [hψ, F2Vec.toV_ofV, hx] at h1
    rw [map_mul, map_inv, Multiplicative.toAdd.injective h1, mul_inv_cancel]
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  haveI : Finite (Dual (ZMod 2) (burnsideB49_W hV U)) := Module.finite_of_finite (ZMod 2)
  refine Nat.card_le_card_of_injective (fun u => ⟨ψ ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩, ?_⟩)
    ?_
  · rw [Submodule.mem_dualAnnihilator]
    intro w hw
    have hle := burnsideB49x_wcomm_le_ker (ψ := ψ ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩)
      (E := burnsideB49x_hatW hV U G hG A) (by
        rintro _ ⟨g, hg, rfl⟩ x
        obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) x)
        have hx : x = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
          rw [hv, F2Vec.ofV_toV]
        subst hx
        rw [map_sub, burnsideB49x_iota_mk, hψ, hψ, F2Vec.toV_ofV, F2Vec.toV_ofV, sub_eq_zero]
        congr 1
        exact hφ (g : MulAut V) g.2 v _ _ ((Subgroup.mem_inf.1 u.2).1 _ hg))
    exact hle hw
  · intro u u' h
    have h' := congrArg (fun x : ↥(burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)).dualAnnihilator =>
      (x : Dual (ZMod 2) (burnsideB49_W hV U))) h
    have h'' := hψinj h'
    exact Subtype.ext (congrArg (fun x : ↥U => (x : V)) h'')

end WT

section WTCard

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49x_card_V_W (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) :
    Nat.card V = 2 ^ (2 * n) := by
  have hU : Nat.card ↥U = 2 ^ n := by rw [burnsideB49_card_U hreal, hK]
  have hW : Nat.card (V ⧸ U) = 2 ^ n := by
    have h1 := burnsideB49_finrank_W hV hK hreal hquot
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := burnsideB49_W hV U)
    rw [Nat.card_zmod, h1] at h2
    rw [← h2]
    exact (Nat.card_congr Additive.toMul).symm
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup U, hU, hW, ← pow_add, two_mul]

include hV in
theorem burnsideB49x_offender_dual (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    2 ^ ((n - finrank (ZMod 2) (burnsideB49x_wfix
        (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) +
      finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) ≤
      Nat.card (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A) := by
  set hG := burnsideB49_hG hreal with hGdef
  set Â := burnsideB49x_hatW hV U G hG A with hÂ
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = n := burnsideB49_finrank_W hV hK hreal hquot
  have hcardV := burnsideB49x_card_V_W hV hK hreal hquot
  have hcardA : Nat.card Â = Nat.card A :=
    burnsideB49x_card_hatW hV U G hG (burnsideB49_iota_injective hV hreal hquot) hAG
  obtain ⟨φ, hφ⟩ := hdual
  have h1 := burnsideB49x_card_fixV_le_W hV U G hG A
  have h2 := burnsideB49x_card_fixU_le_dual hV U G hG φ hφ A
  set c := finrank (ZMod 2) (burnsideB49x_wfix Â) with hc
  set b := finrank (ZMod 2) (burnsideB49x_wcomm Â) with hb
  have hcn : c ≤ n := hn ▸ Submodule.finrank_le _
  have hbn : b ≤ n := hn ▸ Submodule.finrank_le _
  have hfix : Nat.card ↥(burnsideB49x_wfix Â) = 2 ^ c := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hann : Nat.card ↥(burnsideB49x_wcomm Â).dualAnnihilator = 2 ^ (n - b) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (burnsideB49x_wcomm Â)
    rw [hn] at this
    congr 1
    omega
  rw [hfix] at h1
  rw [hann] at h2
  have key : 2 ^ (2 * n) ≤ Nat.card Â * (2 ^ (n - b) * 2 ^ c) := by
    rw [← hcardV, hcardA]
    calc Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A) := hoff
      _ ≤ Nat.card A * (Nat.card ↥(fixV A ⊓ U) * 2 ^ c) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card A * (2 ^ (n - b) * 2 ^ c) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
  rw [← pow_add] at key
  have e : 2 * n = ((n - c) + b) + ((n - b) + c) := by omega
  rw [e, pow_add] at key
  exact Nat.le_of_mul_le_mul_right key (by positivity)

end WTCard

section WTFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49x_card_fixV_le_dual (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A) ≤ 2 ^ (n - finrank (ZMod 2) (burnsideB49x_wcomm
        (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) *
      2 ^ finrank (ZMod 2) (burnsideB49x_wfix (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A)) := by
  set hG := burnsideB49_hG hreal with hGdef
  set Â := burnsideB49x_hatW hV U G hG A with hÂ
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = n := burnsideB49_finrank_W hV hK hreal hquot
  obtain ⟨φ, hφ⟩ := hdual
  have h1 := burnsideB49x_card_fixV_le_W hV U G hG A
  have h2 := burnsideB49x_card_fixU_le_dual hV U G hG φ hφ A
  have hfix : Nat.card ↥(burnsideB49x_wfix Â) = 2 ^ finrank (ZMod 2) (burnsideB49x_wfix Â) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hann : Nat.card ↥(burnsideB49x_wcomm Â).dualAnnihilator =
      2 ^ (n - finrank (ZMod 2) (burnsideB49x_wcomm Â)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (burnsideB49x_wcomm Â)
    rw [hn] at this
    congr 1
    omega
  rw [hfix] at h1
  rw [hann] at h2
  exact h1.trans (Nat.mul_le_mul_right _ h2)

end WTFix

section OffBasic

variable {V : Type} [CommGroup V] [Finite V]

theorem burnsideB49x_offender_card {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A) := by
  have := hA.2.2.2 ⊥ bot_le
  rwa [B1.card_bot_mul_card_fixV] at this

theorem burnsideB49x_offender_mono {T G' A : Subgroup (MulAut V)} (hTG : T ≤ G')
    (hA : IsFFStarOffender T A) : IsFFStarOffender G' A :=
  ⟨hA.1.trans hTG, hA.2.1, hA.2.2.1, hA.2.2.2⟩

end OffBasic

section ElemConv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V]

theorem burnsideB49x_isElemAbelian2_map {T : Subgroup (MulAut V)} (E : Subgroup ↥T)
    [hE : CFSG.IsElementaryAbelian 2 E] : IsElemAbelian2 (E.map T.subtype) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h : (⟨a, ha⟩ : ↥E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      hE.toIsMulCommutative.is_comm.comm _ _
    have h' := congrArg (fun x : ↥E => ((x : ↥T) : MulAut V)) h
    simpa using h'
  · rintro _ ⟨a, ha, rfl⟩
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a ha
    simpa using congrArg (fun x : ↥T => (x : MulAut V)) h

theorem burnsideB49x_isElementaryAbelian_subgroupOf {T A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) : CFSG.IsElementaryAbelian 2 (A.subgroupOf T) where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Subtype.ext (hA.1 _ a.2 _ b.2))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (Subtype.ext (by simpa using hA.2 _ x.2))

end ElemConv

end CFSG.ASVolI
