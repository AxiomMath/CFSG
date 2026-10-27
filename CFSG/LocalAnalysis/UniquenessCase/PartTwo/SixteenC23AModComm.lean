module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs
public import CFSG.LocalAnalysis.SteinbergBVGL3InvolutionDimensionBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module CFSG.Quasithin CFSG.Quasithin.FFC

variable {V : Type} [CommGroup V]

private theorem c23a_sl3_eq_of_smul {A B : SL3F2}
    (h : ∀ x : Fin 3 → ZMod 2, A • x = B • x) : A = B := by
  apply Subtype.ext
  funext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simp only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.mulVec_single_one, Matrix.col_apply] at h1
  exact h1

private theorem c23a_span_eq_top_of_closure {W : Type*} [CommGroup W]
    [Module (ZMod 2) (Additive W)] (T : Set W) (hT : Subgroup.closure T = ⊤) :
    Submodule.span (ZMod 2) (Additive.ofMul '' T) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have key : ∀ w : W, w ∈ Subgroup.closure T →
      Additive.ofMul w ∈ Submodule.span (ZMod 2) (Additive.ofMul '' T) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | one => exact Submodule.zero_mem _
    | mul a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | inv a _ ha => exact Submodule.neg_mem _ ha
  exact key (Additive.toMul x) (by rw [hT]; exact Subgroup.mem_top _)

theorem c23a_not_commSub_le {L : Subgroup (MulAut V)} {E Z : Subgroup V} (h : C23ABlock L E Z)
    {l : MulAut V} (hl : l ∈ L) (hl1 : l ≠ 1) :
    ¬ commSub E (Subgroup.zpowers l) ≤ Z := by
  classical
  intro hle
  obtain ⟨D⟩ := h.nat
  obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
  have hγ' : ((D.ρ γ : ↥L) : MulAut V) = l := congrArg Subtype.val hγ
  have hγ1 : γ ≠ 1 := by
    intro h1
    have h2 : (⟨l, hl⟩ : ↥L) = 1 := by
      rw [← hγ, h1, map_one]
    exact hl1 (Subtype.ext_iff.1 h2)
  have hx : ∃ x : Fin 3 → ZMod 2, γ • x ≠ x := by
    by_contra hcon
    apply hγ1
    apply c23a_sl3_eq_of_smul
    intro x
    rw [one_smul]
    by_contra hne
    exact hcon ⟨x, hne⟩
  obtain ⟨x, hx⟩ := hx
  obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd x)
  have hlu : l (u : V) ∈ E := hγ' ▸ D.inv γ (u : V) u.2
  have he : l (u : V) * (u : V)⁻¹ ∈ E := E.mul_mem hlu (E.inv_mem u.2)
  have hmem : l (u : V) * (u : V)⁻¹ ∈ commSub E (Subgroup.zpowers l) :=
    Subgroup.subset_closure ⟨l, Subgroup.mem_zpowers l, (u : V), u.2, rfl⟩
  have hZ : l (u : V) * (u : V)⁻¹ ∈ Z := hle hmem
  let w1 : ↥E := ⟨l (u : V), hlu⟩
  let w2 : ↥E := u⁻¹
  have hw1' : w1 = (⟨((D.ρ γ : ↥L) : MulAut V) (u : V), D.inv γ (u : V) u.2⟩ : ↥E) :=
    Subtype.ext (DFunLike.congr_fun hγ' (u : V)).symm
  have hw1 : D.θ w1 = Multiplicative.ofAdd (γ • x) := by
    rw [hw1', D.equiv γ u, hu, toAdd_ofAdd]
  have hw2 : D.θ w2 = Multiplicative.ofAdd (-x) := by
    have h : w2 = u⁻¹ := rfl
    rw [h, map_inv, hu, ofAdd_neg]
  have hprod : D.θ (w1 * w2) = Multiplicative.ofAdd (γ • x - x) := by
    rw [map_mul, hw1, hw2, ← ofAdd_add]
    congr 1
    abel
  have hne : Multiplicative.ofAdd (γ • x - x) ≠ 1 := by
    intro h
    exact hx (sub_eq_zero.1 ((ofAdd_eq_one).1 h))
  have hnotZ : ((w1 * w2 : ↥E) : V) ∉ Z := by
    intro hz
    exact hne (hprod ▸ (D.θ_ker (w1 * w2)).2 hz)
  exact hnotZ (by simpa [w1, w2] using hZ)

theorem c23a_rk_le_three_mul_commSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {E Z : Subgroup V} (h : C23ABlock L E Z) {a : MulAut V}
    (ha : a ∈ L) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    rk ↥E ≤ 3 * rk ↥(commSub E (Subgroup.zpowers a)) := by
  classical
  obtain ⟨D⟩ := h.nat
  have hV3 : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := Module.finrank_fin_fun (ZMod 2)
  letI : Module (ZMod 2) (Additive ↥E) :=
    AddCommGroup.zmodModule fun x => by
      apply Additive.toMul.injective
      change (Additive.toMul x) ^ 2 = (1 : ↥E)
      exact Subtype.ext (hV ((Additive.toMul x : ↥E) : V))
  haveI : FiniteDimensional (ZMod 2) (Additive ↥E) := Module.Finite.of_finite
  have hLE : ∀ g ∈ L, ∀ w ∈ E, g w ∈ E := by
    intro g hg w hw
    obtain ⟨γ, hγ⟩ := D.surj ⟨g, hg⟩
    have hγ' : ((D.ρ γ : ↥L) : MulAut V) = g := congrArg Subtype.val hγ
    rw [← hγ']
    exact D.inv γ w hw
  let linAct : ↥L →* (Additive ↥E →ₗ[ZMod 2] Additive ↥E) :=
    { toFun := fun g => (muW hLE g).toZModLinearMap 2
      map_one' := LinearMap.ext fun x => DFunLike.congr_fun (map_one (muW hLE)) x
      map_mul' := fun g h => LinearMap.ext fun x => DFunLike.congr_fun (map_mul (muW hLE) g h) x }
  let eGL : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* GL (Fin 3) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm
  let eS : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥L :=
    (eGL.trans (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
      c23a_toGL_bijective).symm).trans (MulEquiv.ofBijective D.ρ ⟨D.inj, D.surj⟩)
  let ρ' : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (Additive ↥E) := linAct.comp eS.toMonoidHom
  let a' : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := eS.symm ⟨a, ha⟩
  have ha'2 : a' * a' = 1 := by
    apply eS.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact Subtype.ext ha2
  have ha'1 : a' ≠ 1 := by
    intro h1
    have h2 : (⟨a, ha⟩ : ↥L) = 1 := by
      have := congrArg (fun x => eS x) h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact ha1 (Subtype.ext_iff.1 h2)
  let s : Set V := {c | ∃ x ∈ L, ∃ w ∈ E, x w * w⁻¹ = c}
  have hperf : E = Subgroup.closure s := by
    rw [show Subgroup.closure s = commSub E L from rfl, h.perf]
  have htop : Subgroup.closure ((Subtype.val : ↥E → V) ⁻¹' s) = ⊤ := by
    rw [hperf]
    exact Subgroup.closure_closure_coe_preimage
  let T : Set (Additive ↥E) := {x | ∃ g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
    ∃ e : Additive ↥E, x = ρ' g e - e}
  have hmono : Additive.ofMul '' ((Subtype.val : ↥E → V) ⁻¹' s) ⊆ T := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨x, hx, w, hw, hxw⟩ := hu
    have hρ : ρ' (eS.symm ⟨x, hx⟩) = linAct ⟨x, hx⟩ := by
      show linAct (eS (eS.symm ⟨x, hx⟩)) = linAct ⟨x, hx⟩
      rw [MulEquiv.apply_symm_apply]
    refine ⟨eS.symm ⟨x, hx⟩, Additive.ofMul ⟨w, hw⟩, ?_⟩
    rw [hρ]
    have h1 : Additive.toMul (linAct ⟨x, hx⟩ (Additive.ofMul ⟨w, hw⟩) -
        Additive.ofMul ⟨w, hw⟩) = u := by
      apply Subtype.ext
      show ((Additive.toMul (muW hLE ⟨x, hx⟩ (Additive.ofMul ⟨w, hw⟩) -
        Additive.ofMul ⟨w, hw⟩) : ↥E) : V) = (u : V)
      rw [muW_sub_apply]
      simpa using hxw
    rw [← h1, ofMul_toMul]
  have hspanT : Submodule.span (ZMod 2) T = ⊤ := by
    rw [eq_top_iff, ← c23a_span_eq_top_of_closure ((Subtype.val : ↥E → V) ⁻¹' s) htop]
    exact Submodule.span_mono hmono
  have hbound := @CFSG.LocalAnalysis.SteinbergBV.GL3_three_involution_commutator_dimension_bound
    (Fin 3 → ZMod 2) inferInstance (Pi.Function.module (Fin 3) (ZMod 2) (ZMod 2)) hV3 (ZMod 2)
    (Additive ↥E) inferInstance inferInstance inferInstance inferInstance ρ' hspanT a' ha'2 ha'1
  have hrange : finrank (ZMod 2) (LinearMap.range (ρ' a' - LinearMap.id)) ≤
      rk ↥(commSub E (Subgroup.zpowers a)) := by
    have hρa : ρ' a' = linAct ⟨a, ha⟩ := by
      show linAct (eS (eS.symm ⟨a, ha⟩)) = linAct ⟨a, ha⟩
      rw [MulEquiv.apply_symm_apply]
    let f : ↥(LinearMap.range (ρ' a' - LinearMap.id)) → ↥(commSub E (Subgroup.zpowers a)) :=
      fun x => ⟨((Additive.toMul (x : Additive ↥E) : ↥E) : V), by
        obtain ⟨e, he⟩ := x.2
        have hxe : (x : Additive ↥E) = linAct ⟨a, ha⟩ e - e := by
          rw [← he, hρa]
          rfl
        have hcomm : Additive.toMul (x : Additive ↥E) =
            Additive.toMul (linAct ⟨a, ha⟩ e - e) := by
          rw [hxe]
        rw [hcomm]
        show ((Additive.toMul (muW hLE ⟨a, ha⟩ e - e) : ↥E) : V) ∈
          commSub E (Subgroup.zpowers a)
        rw [muW_sub_apply]
        exact Subgroup.subset_closure
          ⟨a, Subgroup.mem_zpowers a, ((Additive.toMul e : ↥E) : V), (Additive.toMul e).2, rfl⟩⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : ((Additive.toMul (x : Additive ↥E) : ↥E) : V) =
          ((Additive.toMul (y : Additive ↥E) : ↥E) : V) :=
        congrArg (fun z : ↥(commSub E (Subgroup.zpowers a)) => (z : V)) hxy
      apply Subtype.ext
      apply Additive.toMul.injective
      exact Subtype.ext h1
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := ↥(LinearMap.range (ρ' a' - LinearMap.id))), Nat.card_zmod,
      card_eq_two_pow hV (commSub E (Subgroup.zpowers a))] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  have hrkE : rk ↥E = finrank (ZMod 2) (Additive ↥E) := by
    unfold rk
    rw [← Nat.card_congr (Additive.toMul : Additive ↥E ≃ ↥E)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥E), Nat.card_zmod]
    rw [padicValNat.prime_pow]
  rw [hrkE]
  exact hbound.trans (Nat.mul_le_mul_left 3 hrange)

private theorem c23a_card_block {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) : Nat.card ↥E = 2 ^ 3 * Nat.card ↥Z := by
  obtain ⟨D⟩ := h.nat
  have hZE : Z ≤ E := h.fix ▸ inf_le_left
  have h1 := Subgroup.card_ker_mul_card_range D.θ
  have hker : D.θ.ker = Z.subgroupOf E := by
    ext u
    rw [MonoidHom.mem_ker, D.θ_ker]
    rfl
  have hrange : Nat.card D.θ.range = 2 ^ 3 := by
    rw [MonoidHom.range_eq_top.2 D.θ_surj, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hZ : Nat.card ↥(Z.subgroupOf E) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  rw [hker, hZ, hrange] at h1
  rw [← h1, mul_comm]

theorem c23a_two_le_rk_commSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    {E Z : Subgroup V} (h : C23ABlock L E Z) (hZ : Z ≠ ⊥) {l : MulAut V} (hl : l ∈ L)
    (hl1 : l ≠ 1) (hl2 : ∃ j : ℕ, orderOf l = 2 ^ j) :
    2 ≤ rk ↥(commSub E (Subgroup.zpowers l)) := by
  obtain ⟨j, hj⟩ := hl2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    exact hl1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hord : orderOf (l ^ 2 ^ k) = 2 := by
    have h2 : orderOf l / 2 = 2 ^ k := by
      rw [hj, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [← h2]
    exact orderOf_pow_orderOf_div (by rw [hj]; positivity)
      (by rw [hj]; exact dvd_pow_self 2 (by omega))
  have ha2 : l ^ 2 ^ k * l ^ 2 ^ k = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 hord.dvd
  have ha1 : l ^ 2 ^ k ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    omega
  have hle : commSub E (Subgroup.zpowers (l ^ 2 ^ k)) ≤ commSub E (Subgroup.zpowers l) :=
    commSub_mono le_rfl (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers l) _))
  have h3 := c23a_rk_le_three_mul_commSub hV h (pow_mem hl _) ha2 ha1
  have hrkE : rk ↥E = 3 + rk ↥Z := by
    unfold rk
    rw [c23a_card_block h, padicValNat.mul (by norm_num) Nat.card_pos.ne',
      padicValNat.prime_pow]
  have hZpos : rk ↥Z ≠ 0 := fun h0 => hZ ((rk_eq_zero_iff hV).1 h0)
  exact (show 2 ≤ rk ↥(commSub E (Subgroup.zpowers (l ^ 2 ^ k))) by omega).trans
    (rk_mono hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
