module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CTensor
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CMov
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN3MovedContradictionFinal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.Quasithin.G11 CFSG.ASVolI.ChH

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_addHom_smul_of_commute_scalar
    (T : M₄ →+ M₄) {c : F₄} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hTc : ∀ X, T (c • X) = c • T X) (a : F₄) (X : M₄) :
    T (a • X) = a • T X := by
  classical
  letI : Fintype F₄ := Fintype.ofFinite F₄
  have hc : Fintype.card F₄ = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h1c : (1 : F₄) ≠ c := fun h => hc1 h.symm
  have hc10 : c + 1 ≠ 0 := fun h => hc1 (add_right_cancel (by
    rw [CharTwo.add_self_eq_zero (1 : F₄)]
    exact h))
  have hc11 : c + 1 ≠ 1 := fun h => hc0 (add_right_cancel (by
    rw [zero_add]
    exact h : c + 1 = 0 + 1))
  have hc1c : c + 1 ≠ c := fun h => one_ne_zero (add_left_cancel (by
    rw [add_zero]
    exact h : c + 1 = c + 0))
  have huniv : ({0, 1, c, c + 1} : Finset F₄) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hc]
    simp [hc0.symm, h1c, hc10.symm, hc11.symm, hc1c.symm]
  have hcases : a = 0 ∨ a = 1 ∨ a = c ∨ a = c + 1 := by
    have : a ∈ ({0, 1, c, c + 1} : Finset F₄) := huniv ▸ Finset.mem_univ a
    simpa using this
  rcases hcases with h | h | h | h
  · subst h; simp
  · subst h; simp
  · subst h; exact hTc X
  · subst h
    rw [add_smul, one_smul, map_add, hTc, add_smul, one_smul]

private theorem w1369_restrictLinearOf_commute_restrictActionHom
    {W : Type} [CommGroup W] [Finite W] {Y' : Subgroup (MulAut W)} {U : Subgroup W}
    (hYU : ∀ y ∈ Y', ∀ u ∈ U, y u ∈ U) [Module (ZMod 2) (Additive ↥U)]
    {x : MulAut W} (hxU : ∀ u ∈ U, x u ∈ U)
    (hxN : Y'.map (MulAut.conj x).toMonoidHom = Y')
    (y : ↥Y') (hxy : x * (y : MulAut W) = (y : MulAut W) * x) :
    restrictLinearOf x hxU * restrictActionHom hYU y =
      restrictActionHom hYU y * restrictLinearOf x hxU := by
  have hconj := restrictLinearOf_conj hYU hxN hxU y
  have hy : (⟨x * (y : MulAut W) * x⁻¹, mem_conj_of_map_conj_eq hxN y.2⟩ : ↥Y') = y := by
    apply Subtype.ext
    change x * (y : MulAut W) * x⁻¹ = (y : MulAut W)
    rw [hxy]
    simp
  rw [hy] at hconj
  have h2 := congrArg (fun t => t * restrictLinearOf x hxU) hconj
  simpa [mul_assoc] using h2

private lemma w1369_natCard_range_sub_eq_four
    {W : Type} [CommGroup W] [Finite W] {U : Subgroup W}
    (hw2 : ∀ w : W, w ^ 2 = 1) [Module (ZMod 2) (Additive ↥U)]
    {e : MulAut W} (he : ∀ u ∈ U, e u ∈ U) (he2 : e * e = 1)
    (hrk : rk ↥(commSub U (Subgroup.zpowers e)) = 2) :
    Nat.card ↥(LinearMap.range ((restrictLinearOf e he).toLinearMap -
      (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) = 4 := by
  classical
  let Zsub : Subgroup W := commSub U (Subgroup.zpowers e)
  have hZU : Zsub ≤ U := by
    apply commSub_le_of_invariant
    intro x hx w hw
    have heS : e ∈ stabSub U := by
      rw [mem_stabSub]
      intro u
      exact ⟨fun h => by
        have := inv_mem_of_forall_mem e he (e u) h
        simpa using this, fun hu => he u hu⟩
    exact ((mem_stabSub.mp (Subgroup.zpowers_le.mpr heS hx)) w).mpr hw
  let Φ : ↥U →* ↥U :=
    { toFun := fun u => (⟨e (u : W), he (u : W) u.2⟩ : ↥U) * u⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul,
          mul_inv_rev]
        ac_rfl }
  have hmem : ∀ x ∈ Subgroup.zpowers e, x = 1 ∨ x = e := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
    · right
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one,
        zpow_one]
  have hZgen : Zsub = Subgroup.closure {c | ∃ w ∈ U, e w * w⁻¹ = c} := by
    change commSub U (Subgroup.zpowers e) = _
    unfold commSub
    congr 1
    ext c
    constructor
    · rintro ⟨x, hx, w, hw, rfl⟩
      rcases hmem x hx with rfl | rfl
      · refine ⟨1, U.one_mem, ?_⟩
        simp
      · exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e, Subgroup.mem_zpowers e, w, hw, rfl⟩
  have hmap : Φ.range.map U.subtype = Zsub := by
    rw [hZgen]
    apply le_antisymm
    · rintro z ⟨u, ⟨v, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨v, v.2, ?_⟩
      rfl
    · rw [Subgroup.closure_le]
      rintro c ⟨w, hw, rfl⟩
      refine ⟨Φ ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
      rfl
  have hcardΦ : Nat.card ↥Φ.range = 4 := by
    have h1 : Nat.card ↥Zsub = Nat.card ↥Φ.range := by
      rw [← hmap]
      exact Subgroup.card_map_of_injective U.subtype_injective
    rw [← h1, card_eq_two_pow hw2 Zsub, hrk]
    norm_num
  have hε : ∀ w : Additive ↥U,
      ((restrictLinearOf e he).toLinearMap - (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) w =
        Additive.ofMul (Φ (Additive.toMul w)) := by
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
    change (restrictLinearOf e he) (Additive.ofMul u) - Additive.ofMul u = _
    rw [restrictLinearOf_ofMul]
    change Additive.ofMul (⟨e (u : W), he (u : W) u.2⟩ : ↥U) - Additive.ofMul u =
      Additive.ofMul ((⟨e (u : W), he (u : W) u.2⟩ : ↥U) * u⁻¹)
    rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
  have hrange : (LinearMap.range ((restrictLinearOf e he).toLinearMap -
      (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) =
      Additive.ofMul '' (Φ.range : Set ↥U) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Φ (Additive.toMul w), ⟨Additive.toMul w, rfl⟩, (hε w).symm⟩
    · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
      refine ⟨Additive.ofMul w, ?_⟩
      rw [hε (Additive.ofMul w)]
      rfl
  have hcardrange : Nat.card ↥(LinearMap.range ((restrictLinearOf e he).toLinearMap -
      (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) =
      Nat.card ↥(Additive.ofMul '' (Φ.range : Set ↥U)) := by
    rw [hrange]
  exact hcardrange.trans ((Nat.card_congr
    (Equiv.Set.image Additive.ofMul (Φ.range : Set ↥U) Additive.ofMul.injective).symm).trans
      hcardΦ)

theorem Std139.moved_axis (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d) :
    ∀ e ∈ D, e ∉ centSub (commSub ⊤ (swapPair K d)) →
      ∀ u ∈ commSub ⊤ (swapPair K d), e u = u ↔ u ∈ commSub ⊤ (swapPair K d) ⊓ Y := by
  intro e he henot u hu
  have he1 : e ≠ 1 := fun h => henot (h ▸ (centSub (commSub ⊤ (swapPair K d))).one_mem)
  constructor
  · intro heu
    have hmem : u ∈ fixV (Subgroup.zpowers e) := mem_fixV_zpowers_iff.mpr heu
    rw [Std139.fixV_eq_axis hw2 S he he1] at hmem
    exact ⟨hu, hmem⟩
  · rintro ⟨-, huY⟩
    exact mem_fixV_zpowers_iff.mp (by rw [Std139.fixV_eq_axis hw2 S he he1]; exact huY)

theorem Std139.moved_transvection (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} {d : MulAut W} (hK : IsComponentOf K G) (hd : d ∈ D)
    (hd1 : d ≠ 1) (hKd : K.map (MulAut.conj d).toMonoidHom ≠ K) (h134 : Conc4_134 G K d)
    (hYU : ∀ y ∈ swapPair K d, ∀ u ∈ commSub ⊤ (swapPair K d), y u ∈ commSub ⊤ (swapPair K d))
    (hDU : ∀ e ∈ D, ∀ u ∈ commSub ⊤ (swapPair K d), e u ∈ commSub ⊤ (swapPair K d))
    [Module (ZMod 2) (Additive ↥(commSub ⊤ (swapPair K d)))]
    (H : Subgroup (GLV (Additive ↥(commSub ⊤ (swapPair K d)))))
    (hHY : H = (restrictActionHom hYU).range)
    (φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄))
    (ψ : Additive ↥(commSub ⊤ (swapPair K d)) ≃ₗ[ZMod 2] M₄)
    (hψ : ∀ (h : ↥H) (v : Additive ↥(commSub ⊤ (swapPair K d))),
      ψ ((h : GLV (Additive ↥(commSub ⊤ (swapPair K d)))) v) =
        (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
          ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ) :
    ∀ e (he : e ∈ D), e ∉ centSub (commSub ⊤ (swapPair K d)) →
      IsFTransvectionOn F₄ M₄ (transportedAutHom ψ (restrictLinearOf e (hDU e he))) := by
  classical
  intro e he henot
  generalize hU : commSub ⊤ (swapPair K d) = U at *
  obtain ⟨x, hxgen, hx3, hxne, hfixX, hsx⟩ := Std139.exists_gen hw2 S
  have hxmem : x ∈ X := hxgen ▸ Subgroup.mem_zpowers x
  have hKd' : IsComponentOf (K.map (MulAut.conj d).toMonoidHom) G :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (S.DG hd)
  have hLle : swapPair K d ≤ Subgroup.centralizer ({x} : Set (MulAut W)) := by
    rw [swapPair]
    refine sup_le ?_ ?_
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact (Std139.component_commutes_X S hK k hk x hxmem).symm
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact (Std139.component_commutes_X S hKd' k hk x hxmem).symm
  have hcommL : ∀ v ∈ swapPair K d, x * v = v * x := fun v hv =>
    Subgroup.mem_centralizer_iff.mp (hLle hv) x (Set.mem_singleton x)
  have hcomm2 : ∀ y ∈ swapPair K d, ∀ b ∈ Subgroup.zpowers x, y * b = b * y := by
    intro y hy b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute y x from (hcommL y hy).symm) j).eq
  have hUinv : StableUnder (Subgroup.zpowers x) U := by
    rw [← hU]
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (V := W) (Y := swapPair K d)
      (B := Subgroup.zpowers x) (M := ⊤) hcomm2 (fun _ _ _ _ => Subgroup.mem_top _)
  have hxU : ∀ u ∈ U, x u ∈ U := fun u hu =>
    hUinv x (Subgroup.mem_zpowers x) u hu
  have hxN : (swapPair K d).map (MulAut.conj x).toMonoidHom = swapPair K d := by
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      have hw' : (MulEquiv.toMonoidHom (MulAut.conj x)) w = w := by
        change x * w * x⁻¹ = w
        rw [hcommL w hw]
        simp
      rw [hw']
      exact hw
    · intro v hv
      refine ⟨v, hv, ?_⟩
      change x * v * x⁻¹ = v
      rw [hcommL v hv]
      simp
  let εe : GLV (Additive ↥U) := restrictLinearOf e (hDU e he)
  let εx : GLV (Additive ↥U) := restrictLinearOf x hxU
  have he2 : e * e = 1 := by simpa [pow_two] using S.elem.2 e he
  have hee : εe * εx = εx * εe := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    change restrictLinearOf e (hDU e he) (restrictLinearOf x hxU (Additive.ofMul u)) =
      restrictLinearOf x hxU (restrictLinearOf e (hDU e he) (Additive.ofMul u))
    rw [restrictLinearOf_ofMul, restrictLinearOf_ofMul, restrictLinearOf_ofMul,
      restrictLinearOf_ofMul]
    exact congrArg Additive.ofMul (Subtype.ext
      (congrArg (fun f : MulAut W => f (u : W)) (S.DX e he x hxmem)))
  have hHcomm : ∀ h : ↥H, εx * (h : GLV (Additive ↥U)) =
      (h : GLV (Additive ↥U)) * εx := by
    intro h
    have hh : (h : GLV (Additive ↥U)) ∈ (restrictActionHom hYU).range := by
      rw [← hHY]
      exact h.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hh
    rw [← hy]
    exact w1369_restrictLinearOf_commute_restrictActionHom hYU hxU hxN y (hcommL y y.2)
  obtain ⟨c, hc⟩ := tensor22_commute_scalar H φ ψ hψ εx hHcomm
  let A : M₄ →+ M₄ :=
    { toFun := fun X => ψ (εe (ψ.symm X))
      map_zero' := by simp
      map_add' := fun X Y => by simp [map_add] }
  have hAc : ∀ X : M₄, A (c • X) = c • A X := by
    intro X
    have h1 : ψ.symm (c • X) = εx (ψ.symm X) := by
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hc, LinearEquiv.apply_symm_apply]
    change ψ (εe (ψ.symm (c • X))) = c • ψ (εe (ψ.symm X))
    rw [h1]
    have h2 : εe (εx (ψ.symm X)) = εx (εe (ψ.symm X)) := by
      have h := congrArg (fun f : GLV (Additive ↥U) => f (ψ.symm X)) hee
      simpa [LinearEquiv.mul_apply] using h
    rw [h2, hc]
  have hUne : U ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥U := by rw [hbot]; infer_instance
    haveI : Subsingleton (Additive ↥U) := inferInstance
    haveI : Subsingleton M₄ :=
      ⟨fun x y => by
        have h : ψ.symm x = ψ.symm y := Subsingleton.elim _ _
        simpa using congrArg ψ h⟩
    exact one_ne_zero (Subsingleton.elim (1 : M₄) 0)
  have hc0 : c ≠ 0 := by
    intro hc0'
    have h := hc (ψ.symm (1 : M₄))
    rw [hc0', zero_smul] at h
    have h1 : εx (ψ.symm (1 : M₄)) = 0 := ψ.injective (by simpa using h)
    have h2 : ψ.symm (1 : M₄) = 0 := εx.injective (by simpa using h1)
    have h3 : (1 : M₄) = 0 := by
      have := congrArg ψ h2
      simpa using this
    exact one_ne_zero h3
  have hc1 : c ≠ 1 := by
    intro hc1'
    have hεx1 : εx = 1 := by
      apply LinearEquiv.ext
      intro v
      have h := hc v
      rw [hc1', one_smul] at h
      exact ψ.injective h
    have hUbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hfix : u ∈ fixV (Subgroup.zpowers x) := by
        rw [mem_fixV_zpowers_iff]
        have h := congrArg (fun f : GLV (Additive ↥U) =>
          f (Additive.ofMul ⟨u, hu⟩)) hεx1
        have h2 : restrictLinearOf x hxU (Additive.ofMul ⟨u, hu⟩) =
            Additive.ofMul ⟨u, hu⟩ := by
          simpa using h
        have h4 : (restrictLinearOf x hxU (Additive.ofMul ⟨u, hu⟩)).toMul =
            (⟨u, hu⟩ : ↥U) := by
          simpa using congrArg (fun z : Additive ↥U => (Additive.toMul z : ↥U)) h2
        have h5 : x u = (u : W) := by
          simpa [restrictLinearOf_ofMul] using congrArg Subtype.val h4
        exact h5
      rw [← hxgen, hfixX] at hfix
      exact Subgroup.mem_bot.mp hfix
    exact hUne hUbot
  have hlin : ∀ (a : F₄) (X : M₄), A (a • X) = a • A X :=
    fun a X => w1369_addHom_smul_of_commute_scalar A hc0 hc1 hAc a X
  let gLin : M₄ →ₗ[F₄] M₄ :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun a X => hlin a X }
  have hAbij : Function.Bijective (A : M₄ → M₄) :=
    ψ.bijective.comp (εe.bijective.comp ψ.symm.bijective)
  let g : M₄ ≃ₗ[F₄] M₄ := LinearEquiv.ofBijective gLin hAbij
  have hg : linToMulAut F₄ M₄ g = transportedAutHom ψ εe := by
    apply MulEquiv.ext
    intro v
    obtain ⟨X, rfl⟩ : ∃ X : M₄, Multiplicative.ofAdd X = v :=
      ⟨Multiplicative.toAdd v, rfl⟩
    rw [linToMulAut_ofAdd, transportedAutHom_apply]
    rfl
  have hee2 : εe * εe = 1 := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    change restrictLinearOf e (hDU e he)
      (restrictLinearOf e (hDU e he) (Additive.ofMul u)) = Additive.ofMul u
    rw [restrictLinearOf_ofMul, restrictLinearOf_ofMul]
    change Additive.ofMul (⟨e (e (u : W)), _⟩ : ↥U) = Additive.ofMul u
    exact congrArg Additive.ofMul (Subtype.ext
      (congrArg (fun f : MulAut W => f (u : W)) (by
        simpa [pow_two, MulAut.mul_apply] using he2)))
  have hAA : ∀ X : M₄, A (A X) = X := by
    intro X
    have h2 : εe (εe (ψ.symm X)) = ψ.symm X := by
      have h := congrArg (fun f : GLV (Additive ↥U) => f (ψ.symm X)) hee2
      simpa [LinearEquiv.mul_apply] using h
    change ψ (εe (ψ.symm (ψ (εe (ψ.symm X))))) = X
    rw [LinearEquiv.symm_apply_apply, h2, LinearEquiv.apply_symm_apply]
  have hne : commSub U (Subgroup.zpowers e) ≠ ⊥ := by
    intro hbot
    apply henot
    rw [mem_centSub]
    intro u hu
    by_contra hne'
    have hmem : e u * u⁻¹ ∈ commSub U (Subgroup.zpowers e) :=
      Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne' (mul_inv_eq_one.mp hmem)
  have hcomm_e : ∀ y ∈ Subgroup.zpowers e, ∀ b ∈ X, y * b = b * y := by
    intro y hy b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute e b from S.DX e he b hb) i).eq
  have hcommX : ∀ y ∈ swapPair K d, ∀ b ∈ X, y * b = b * y := by
    intro y hy b hb
    rw [hxgen] at hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute y x from (hcommL y hy).symm) j).eq
  have h1U : StableUnder X U := by
    rw [← hU]
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (V := W) (Y := swapPair K d)
      (B := X) (M := ⊤) hcommX (fun _ _ _ _ => Subgroup.mem_top _)
  have hxinv : StableUnder X (commSub U (Subgroup.zpowers e)) := by
    intro b hb c hc
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (V := W) (Y := Subgroup.zpowers e)
      (B := X) (M := U) hcomm_e (fun b hb m hm => h1U b hb m hm) b hb c hc
  have he1 : e ≠ 1 := fun h => henot (h ▸ (centSub U).one_mem)
  have hrk : rk ↥(commSub U (Subgroup.zpowers e)) = 2 := by
    have hle : commSub U (Subgroup.zpowers e) ≤ commSub ⊤ (Subgroup.zpowers e) :=
      commSub_mono le_top le_rfl
    have h2 := xstable_two_le_rk hw2 hfixX hxinv hne
    have h3 : rk ↥(commSub U (Subgroup.zpowers e)) ≤ 2 := by
      have := rk_mono hle
      rwa [(Std139.commSub_axis hw2 S he he1).1] at this
    omega
  have hcard_range_ε : Nat.card ↥(LinearMap.range ((restrictLinearOf e (hDU e he)).toLinearMap -
      (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) = 4 :=
    w1369_natCard_range_sub_eq_four hw2 (hDU e he) he2 hrk
  have hcard_range_g : Nat.card ↥(LinearMap.range (g.toLinearMap -
      (1 : M₄ →ₗ[F₄] M₄)) : Set M₄) = 4 := by
    have hrange : (LinearMap.range (g.toLinearMap - (1 : M₄ →ₗ[F₄] M₄)) : Set M₄) =
        ψ '' (LinearMap.range ((restrictLinearOf e (hDU e he)).toLinearMap -
          (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) := by
      ext X
      constructor
      · rintro ⟨Y, rfl⟩
        refine ⟨εe (ψ.symm Y) - ψ.symm Y, ⟨ψ.symm Y, rfl⟩, ?_⟩
        change ψ (εe (ψ.symm Y) - ψ.symm Y) = ψ (εe (ψ.symm Y)) - Y
        rw [map_sub, LinearEquiv.apply_symm_apply]
      · rintro ⟨w, ⟨Y, rfl⟩, rfl⟩
        refine ⟨ψ Y, ?_⟩
        change ψ (εe (ψ.symm (ψ Y))) - ψ Y = ψ (εe Y - Y)
        rw [LinearEquiv.symm_apply_apply, map_sub]
    calc Nat.card ↥(LinearMap.range (g.toLinearMap - (1 : M₄ →ₗ[F₄] M₄)) : Set M₄)
        = Nat.card ↥(ψ '' (LinearMap.range ((restrictLinearOf e (hDU e he)).toLinearMap -
            (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U))) := by
          rw [hrange]
      _ = Nat.card ↥(LinearMap.range ((restrictLinearOf e (hDU e he)).toLinearMap -
            (1 : Additive ↥U →ₗ[ZMod 2] Additive ↥U)) : Set (Additive ↥U)) :=
          Nat.card_congr (Equiv.Set.image ψ _ ψ.injective).symm
      _ = 4 := hcard_range_ε
  have hdim : Module.finrank F₄ (LinearMap.range (g.toLinearMap -
      (1 : M₄ →ₗ[F₄] M₄))) = 1 := by
    haveI : Fintype F₄ := Fintype.ofFinite F₄
    have hcard := Module.natCard_eq_pow_finrank (K := F₄)
      (V := ↥(LinearMap.range (g.toLinearMap - (1 : M₄ →ₗ[F₄] M₄)) : Set M₄))
    have hF4 : Nat.card F₄ = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [hcard_range_g, hF4] at hcard
    have h1 : 4 ^ Module.finrank F₄ ↥(LinearMap.range (g.toLinearMap -
        (1 : M₄ →ₗ[F₄] M₄)) : Set M₄) = 4 ^ 1 := by
      rw [← hcard]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h1
  have hsq : (g.toLinearMap - (1 : M₄ →ₗ[F₄] M₄)) ∘ₗ
      (g.toLinearMap - (1 : M₄ →ₗ[F₄] M₄)) = 0 := by
    apply LinearMap.ext
    intro X
    change g.toLinearMap (g.toLinearMap X - X) - (g.toLinearMap X - X) = 0
    rw [map_sub]
    have hadd : ∀ Y : M₄, Y + Y = 0 := by
      intro Y
      have h2 : (2 : F₄) = 0 := CharP.cast_eq_zero F₄ 2
      have h : (2 : F₄) • Y = 0 := by rw [h2, zero_smul]
      rwa [two_smul] at h
    have hXX : g.toLinearMap (g.toLinearMap X) = X := hAA X
    rw [hXX]
    abel
    simp only [two_smul, hadd, CharP.cast_eq_zero F₄ 2, zero_smul, neg_zero, add_zero,
      neg_smul, one_smul]
  exact ⟨g, hg, hdim, hsq⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
