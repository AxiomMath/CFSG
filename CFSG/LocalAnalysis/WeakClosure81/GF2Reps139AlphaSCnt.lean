module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaE
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private def w1369_perp (B : W →* W →* Multiplicative (ZMod 2)) (Y : Subgroup W) :
    Subgroup W where
  carrier := {w | ∀ a ∈ Y, B a w = 1}
  one_mem' := by intro a _; simp
  mul_mem' := by
    intro u v hu hv a ha
    rw [map_mul, hu a ha, hv a ha, one_mul]
  inv_mem' := by
    intro u hu a ha
    rw [map_inv, hu a ha, inv_one]

private theorem w1369_mem_perp {B : W →* W →* Multiplicative (ZMod 2)} {Y : Subgroup W}
    {w : W} : w ∈ w1369_perp B Y ↔ ∀ a ∈ Y, B a w = 1 := Iff.rfl

private noncomputable def w1369_biaddForm [Module (ZMod 2) (Additive W)] (β : W → W → ZMod 2)
    (hl : ∀ x x' y, β (x * x') y = β x y + β x' y)
    (hr : ∀ x y y', β x (y * y') = β x y + β x y') :
    LinearMap.BilinForm (ZMod 2) (Additive W) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun u => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk' (fun v => β u.toMul v.toMul) fun _ _ => hr _ _ _)
      map_zero' := by
        ext v
        change β 1 v.toMul = 0
        have h := hl 1 1 v.toMul
        rw [mul_one] at h
        linear_combination -h
      map_add' := fun _ _ => by
        ext v
        exact hl _ _ _ }

private theorem w1369_card_Y (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 1 ≤ n) : Nat.card Y = 4 ^ (n - 1) := by
  have hVtop : IsPGroup 2 (⊤ : Subgroup W) := (isPGroup_two_of_sq_eq_one hw2).to_subgroup ⊤
  have hmq : E3.mQuot (⊤ : Subgroup W) Y = rkIdx Y := by
    rw [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
  have h1 : Nat.card (⊤ : Subgroup W) =
      2 ^ E3.mQuot (⊤ : Subgroup W) Y * Nat.card Y :=
    E3.card_eq_two_pow_mul hVtop le_top
  rw [hmq, S.Yrk, Subgroup.card_top, S.card] at h1
  have h4n : (4 : ℕ) ^ n = 4 * 4 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
    ring
  have h1' : (4 : ℕ) ^ n = 4 * Nat.card Y := by simpa using h1
  rw [h4n] at h1'
  exact (Nat.mul_left_cancel (by norm_num : 0 < 4) h1').symm

private theorem w1369_perp_card (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 4 ≤ n) (B : W →* W →* Multiplicative (ZMod 2))
    (hBnd : ∀ x, (∀ y, B x y = 1) → x = 1) (hBalt : ∀ x, B x x = 1) :
    Nat.card (w1369_perp B Y) = 4 := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.Quasithin.H13.Mult.zmodModuleW hw2
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let β : W → W → ZMod 2 := fun x y => (B x y).toAdd
  have hl : ∀ x x' y, β (x * x') y = β x y + β x' y := by
    intro x x' y
    show (B (x * x') y).toAdd = (B x y).toAdd + (B x' y).toAdd
    have h : B (x * x') y = B x y * B x' y := by
      rw [map_mul B x x']
      rfl
    rw [h, toAdd_mul]
  have hr : ∀ x y y', β x (y * y') = β x y + β x y' := by
    intro x y y'
    show (B x (y * y')).toAdd = (B x y).toAdd + (B x y').toAdd
    rw [map_mul (B x) y y', toAdd_mul]
  let B' : LinearMap.BilinForm (ZMod 2) (Additive W) := w1369_biaddForm β hl hr
  have hB'apply : ∀ u v : Additive W, B' u v = β u.toMul v.toMul := fun u v => rfl
  have hB'alt : B'.IsAlt := by
    intro u
    rw [hB'apply]
    simp only [β]
    rw [hBalt u.toMul, toAdd_one]
  have hB'refl : B'.IsRefl := hB'alt.isRefl
  have hB'sep : B'.SeparatingLeft := by
    intro u hu
    have h : ∀ y, B u.toMul y = 1 := by
      intro y
      have hy := hu (Additive.ofMul y)
      rw [hB'apply] at hy
      have hy' : (B u.toMul y).toAdd = 0 := by simpa [β, toMul_ofMul] using hy
      exact Multiplicative.toAdd.injective (by rw [hy', toAdd_one])
    exact Additive.toMul.injective (by simpa using hBnd u.toMul h)
  have hB'nd : B'.Nondegenerate := hB'refl.nondegenerate_iff_separatingLeft.mpr hB'sep
  let Y' : Submodule (ZMod 2) (Additive W) := CFSG.Quasithin.H13.Mult.toSub Y
  haveI : Module.Finite (ZMod 2) Y' := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) (B'.orthogonal Y') := Module.Finite.of_finite
  have hle : Module.finrank (ZMod 2) Y' ≤ Module.finrank (ZMod 2) (Additive W) :=
    Submodule.finrank_le Y'
  have hfin : Module.finrank (ZMod 2) (B'.orthogonal Y') + Module.finrank (ZMod 2) Y' =
      Module.finrank (ZMod 2) (Additive W) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB'nd Y']
    omega
  have hprod : Nat.card (B'.orthogonal Y') * Nat.card Y' = Nat.card (Additive W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B'.orthogonal Y'),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y'),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)]
    simp only [Nat.card_zmod]
    rw [← pow_add, hfin]
  have hcardY : Nat.card Y = 4 ^ (n - 1) := w1369_card_Y hw2 S (by omega)
  have hVcard : Nat.card (Additive W) = 4 ^ n := by
    rw [← Nat.card_congr Additive.ofMul, S.card]
  have h4n : (4 : ℕ) ^ n = 4 * 4 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [pow_succ]
    ring
  have hcardO : Nat.card (B'.orthogonal Y') = 4 := by
    have hY' : Nat.card Y' = 4 ^ (n - 1) := by
      rw [CFSG.Quasithin.H13.Mult.card_toSub, hcardY]
    have h2 : Nat.card (B'.orthogonal Y') * 4 ^ (n - 1) = 4 * 4 ^ (n - 1) := by
      calc Nat.card (B'.orthogonal Y') * 4 ^ (n - 1)
          = Nat.card (B'.orthogonal Y') * Nat.card Y' := by rw [hY']
        _ = Nat.card (Additive W) := hprod
        _ = 4 ^ n := hVcard
        _ = 4 * 4 ^ (n - 1) := h4n
    exact Nat.mul_right_cancel (by positivity : 0 < 4 ^ (n - 1)) h2
  have hcard : Nat.card (w1369_perp B Y) = Nat.card (B'.orthogonal Y') := by
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨Additive.ofMul w.1, ?_⟩
        invFun := fun v => ⟨v.1.toMul, ?_⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun v => by ext; rfl }
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      rw [hB'apply]
      have hy' : y.toMul ∈ Y := CFSG.Quasithin.H13.Mult.mem_toSub.mp hy
      have hw := w1369_mem_perp.mp w.2 y.toMul hy'
      have hh := congrArg Multiplicative.toAdd hw
      simpa [β, toMul_ofMul] using hh
    · intro a ha
      have hav : Additive.ofMul a ∈ Y' := CFSG.Quasithin.H13.Mult.mem_toSub.mpr ha
      have hv := v.2 (Additive.ofMul a) hav
      rw [hB'apply] at hv
      refine Multiplicative.toAdd.injective ?_
      have hv' : (B a v.1.toMul).toAdd = 0 := by
        simpa [β, toMul_ofMul] using hv
      rw [hv', toAdd_one]
  rw [hcard, hcardO]

private theorem w1369_generated (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {x : MulAut W} (hxX : X = Subgroup.zpowers x) (hx3 : x ^ 3 = 1)
    (hfix : fixV X = ⊥) {v₀ : W} (hv₀ : v₀ ∉ Y) :
    ⊤ = Y ⊔ Subgroup.zpowers v₀ ⊔ Subgroup.zpowers (x v₀) := by
  classical
  have hxmem : x ∈ X := by rw [hxX]; exact Subgroup.mem_zpowers x
  have hfixx : fixV (Subgroup.zpowers x) = ⊥ := by rwa [← hxX]
  set H : Subgroup W := Y ⊔ Subgroup.zpowers v₀ ⊔ Subgroup.zpowers (x v₀) with hH
  have hxY : Y.map x.toMonoidHom = Y := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact S.Yinv x hxmem y hy
    · intro y hy
      exact ⟨x⁻¹ y, S.Yinv x⁻¹ (X.inv_mem hxmem) y hy,
        MulEquiv.apply_symm_apply x y⟩
  have hv0H : v₀ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v₀))
  have hxv0H : x v₀ ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers (x v₀))
  have hxxv0 : x (x v₀) = x v₀ * v₀ := by
    have h := CFSG.LocalAnalysis.WeakClosure81.mulAut_norm_mul_eq_one hx3 hfixx v₀
    have h' : x (x v₀) * (x v₀ * v₀) = 1 := by rw [← mul_assoc]; exact h
    rw [mul_eq_one_iff_eq_inv] at h'
    rw [h', mul_inv_rev, inv_eq_self_of_sq_eq_one hw2 (x v₀),
      inv_eq_self_of_sq_eq_one hw2 v₀, mul_comm]
  have hHmap : H.map x.toMonoidHom ≤ H := by
    rw [hH]
    simp only [Subgroup.map_sup, hxY, MonoidHom.map_zpowers]
    apply sup_le
    · apply sup_le
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right
    · apply Subgroup.zpowers_le.mpr
      show x (x v₀) ∈ H
      rw [hxxv0]
      exact H.mul_mem hxv0H hv0H
  have hHmap_eq : H.map x.toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hHmap
      (Subgroup.card_map_of_injective (K := H) x.injective).ge
  have hxstab : x ∈ stabSub H := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have : x u ∈ H.map x.toMonoidHom := by rwa [hHmap_eq]
      obtain ⟨u', hu', hu''⟩ := Subgroup.mem_map.mp this
      have huu : u' = u := x.injective (by simpa using hu'')
      rwa [huu] at hu'
    · intro hu
      have : x u ∈ H.map x.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [hHmap_eq] at this
  have hHinv : StableUnder X H := by
    rw [hxX]
    intro y hy h hh
    exact (mem_stabSub.mp (Subgroup.zpowers_le.mpr hxstab hy) h).mpr hh
  have hYH : Y ≤ H := fun y hy => Subgroup.mem_sup_left (Subgroup.mem_sup_left hy)
  have hYltH : Y < H := lt_of_le_of_ne hYH (fun heq => hv₀ (heq ▸ hv0H))
  have hHtop : H = ⊤ := by
    by_contra hHne
    have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHne
    have h2 : 2 ≤ E3.mQuot (⊤ : Subgroup W) H :=
      xstable_two_le_mQuot hw2 S.Xcard hfix (fun _ _ _ _ => Subgroup.mem_top _) hHinv hHlt
    have hmq : E3.mQuot (⊤ : Subgroup W) Y = 2 := by
      have h : E3.mQuot (⊤ : Subgroup W) Y = rkIdx Y := by
        rw [E3.mQuot, rkIdx, Subgroup.relIndex_top_right]
      rw [h, S.Yrk]
    have hadd := E3.mQuot_add hYH le_top
    have hH2 : IsPGroup 2 H := (isPGroup_two_of_sq_eq_one hw2).to_subgroup H
    have hne0 : E3.mQuot H Y ≠ 0 := fun h0 =>
      (ne_of_lt hYltH) ((E3.mQuot_eq_zero_iff hH2 hYH).mp h0)
    omega
  rw [hH]
  exact hHtop.symm

private theorem w1369_eq_one_of_fixes (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {x : MulAut W} (hxX : X = Subgroup.zpowers x) (hx3 : x ^ 3 = 1)
    (hfix : fixV X = ⊥) {v₀ : W} (hv₀ : v₀ ∉ Y) {g : MulAut W}
    (hgY : ∀ y ∈ Y, g y = y) (hgv : g v₀ = v₀) (hgx : g (x v₀) = x v₀) : g = 1 := by
  classical
  have htop := w1369_generated hw2 S hxX hx3 hfix hv₀
  have hfixg : Y ⊔ Subgroup.zpowers v₀ ⊔ Subgroup.zpowers (x v₀) ≤
      fixV (Subgroup.zpowers g) := by
    apply sup_le
    · apply sup_le
      · intro y hy
        rw [mem_fixV_zpowers_iff]
        exact hgY y hy
      · intro w hw
        rw [Subgroup.mem_zpowers_iff] at hw
        obtain ⟨k, rfl⟩ := hw
        rw [mem_fixV_zpowers_iff, map_zpow, hgv]
    · intro w hw
      rw [Subgroup.mem_zpowers_iff] at hw
      obtain ⟨k, rfl⟩ := hw
      rw [mem_fixV_zpowers_iff, map_zpow, hgx]
  have htop' : fixV (Subgroup.zpowers g) = ⊤ :=
    le_antisymm le_top (htop.symm ▸ hfixg)
  ext w
  have hw : w ∈ fixV (Subgroup.zpowers g) := by rw [htop']; exact Subgroup.mem_top w
  rw [mem_fixV_zpowers_iff] at hw
  simpa using hw

private theorem w1369_e_preserves (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 4 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (B : W →* W →* Multiplicative (ZMod 2))
    (hBnd : ∀ x, (∀ y, B x y = 1) → x = 1) (hBalt : ∀ x, B x x = 1)
    (hBinv : ∀ k ∈ K, ∀ x y, B (k x) (k y) = B x y)
    {x₀ : MulAut W} (hxX : X = Subgroup.zpowers x₀) (hx3 : x₀ ^ 3 = 1) (hxne : x₀ ≠ 1)
    (hfix : fixV X = ⊥) {e : MulAut W} (he : e ∈ D) (he1 : e ≠ 1) :
    ∀ a b, B (e a) (e b) = B a b := by
  classical
  have hn3 : 3 ≤ n := by omega
  letI : Module (ZMod 2) (Additive W) := CFSG.Quasithin.H13.Mult.zmodModuleW hw2
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let β : W → W → ZMod 2 := fun x y => (B x y).toAdd
  have hl : ∀ x x' y, β (x * x') y = β x y + β x' y := by
    intro x x' y
    show (B (x * x') y).toAdd = (B x y).toAdd + (B x' y).toAdd
    have h : B (x * x') y = B x y * B x' y := by
      rw [map_mul B x x']
      rfl
    rw [h, toAdd_mul]
  have hr : ∀ x y y', β x (y * y') = β x y + β x y' := by
    intro x y y'
    show (B x (y * y')).toAdd = (B x y).toAdd + (B x y').toAdd
    rw [map_mul (B x) y y', toAdd_mul]
  let B' : LinearMap.BilinForm (ZMod 2) (Additive W) := w1369_biaddForm β hl hr
  have hB'apply : ∀ u v : Additive W, B' u v = β u.toMul v.toMul := fun u v => rfl
  have hB'alt : B'.IsAlt := by
    intro u
    rw [hB'apply]
    simp only [β]
    rw [hBalt u.toMul, toAdd_one]
  have hB'refl : B'.IsRefl := hB'alt.isRefl
  have hB'symm : ∀ u v : Additive W, B' u v = B' v u := fun u v => by
    have h := hB'alt.neg_eq u v
    rwa [ZMod.neg_eq_self_mod_two] at h
  have hsymm : ∀ x y : W, B x y = B y x := by
    intro x y
    apply Multiplicative.toAdd.injective
    rw [show (B x y).toAdd = B' (Additive.ofMul x) (Additive.ofMul y) from rfl,
      show (B y x).toAdd = B' (Additive.ofMul y) (Additive.ofMul x) from rfl]
    exact hB'symm _ _
  have hB'sep : B'.SeparatingLeft := by
    intro u hu
    have h : ∀ y, B u.toMul y = 1 := by
      intro y
      have hy := hu (Additive.ofMul y)
      rw [hB'apply] at hy
      have hy' : (B u.toMul y).toAdd = 0 := by simpa [β, toMul_ofMul] using hy
      exact Multiplicative.toAdd.injective (by rw [hy', toAdd_one])
    exact Additive.toMul.injective (by simpa using hBnd u.toMul h)
  have hB'nd : B'.Nondegenerate := hB'refl.nondegenerate_iff_separatingLeft.mpr hB'sep
  let g : Additive W ≃ₗ[ZMod 2] Additive W := CFSG.Quasithin.H13.Mult.linEquiv e
  let b' : LinearMap.BilinForm (ZMod 2) (Additive W) :=
    B'.compl₁₂ (g : Additive W →ₗ[ZMod 2] Additive W) (g : Additive W →ₗ[ZMod 2] Additive W)
  have hb'sepR : b'.SeparatingRight := by
    intro u hu
    have h : ∀ z : Additive W, B' z (g u) = 0 := by
      intro z
      obtain ⟨z', rfl⟩ := g.surjective z
      exact hu z'
    have hgu : g u = 0 := hB'nd.2 (g u) h
    exact g.injective (by simpa using hgu)
  let Tlin : Additive W →ₗ[ZMod 2] Additive W :=
    (B'.flip.toDual hB'nd.flip).symm.toLinearMap ∘ₗ b'.flip
  have hTlin : ∀ u v, B' u (Tlin v) = b' u v := by
    intro u v
    change B'.flip ((B'.flip.toDual hB'nd.flip).symm (b'.flip v)) u = b' u v
    rw [LinearMap.BilinForm.apply_toDual_symm_apply, LinearMap.BilinForm.flip_apply]
  have hTlin_inj : Function.Injective Tlin := by
    intro u v huv
    have hzero : Tlin (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 : u - v = 0 := by
      apply hb'sepR
      intro w
      rw [← hTlin w (u - v), hzero]
      exact map_zero (B' w)
    exact sub_eq_zero.mp h1
  let T : Additive W ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective Tlin ⟨hTlin_inj, LinearMap.injective_iff_surjective.mp hTlin_inj⟩
  let Tmul : MulAut W := (CFSG.Quasithin.H13.Mult.linEquiv).symm T
  have hTmul_apply : ∀ y : W, Tmul y = (T (Additive.ofMul y)).toMul := by
    intro y
    have h1 : CFSG.Quasithin.H13.Mult.linEquiv Tmul = T := by
      rw [show Tmul = (CFSG.Quasithin.H13.Mult.linEquiv).symm T from rfl,
        MulEquiv.apply_symm_apply]
    have h : T (Additive.ofMul y) = Additive.ofMul (Tmul y) := by
      rw [← h1, CFSG.Quasithin.H13.Mult.linEquiv_apply]
      rfl
    rw [h, toMul_ofMul]
  have hg_apply : ∀ y : W, g (Additive.ofMul y) = Additive.ofMul (e y) := by
    intro y
    rw [show g = CFSG.Quasithin.H13.Mult.linEquiv e from rfl,
      CFSG.Quasithin.H13.Mult.linEquiv_apply]
    rfl
  have hTmul : ∀ a b : W, B (e a) (e b) = B a (Tmul b) := by
    intro a b
    have h1 : B' (Additive.ofMul a) (Tlin (Additive.ofMul b)) =
        B' (Additive.ofMul (e a)) (Additive.ofMul (e b)) := by
      have h := hTlin (Additive.ofMul a) (Additive.ofMul b)
      rw [h]
      simp only [b', LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
      rw [hg_apply a, hg_apply b]
    have h2 : B' (Additive.ofMul a) (Tlin (Additive.ofMul b)) =
        B' (Additive.ofMul a) (Additive.ofMul (Tmul b)) := rfl
    rw [h2] at h1
    apply Multiplicative.toAdd.injective
    rw [show (B (e a) (e b)).toAdd = B' (Additive.ofMul (e a)) (Additive.ofMul (e b)) from rfl,
      show (B a (Tmul b)).toAdd = B' (Additive.ofMul a) (Additive.ofMul (Tmul b)) from rfl]
    exact h1.symm
  have hTcomm : ∀ k ∈ K, ∀ y : W, Tmul (k y) = k (Tmul y) := by
    intro k hk y
    have heke : e * k * e⁻¹ ∈ K := by
      have h := hK.normal e (S.DG he)
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
    have h1 : ∀ x z, B (e (k x)) (e (k z)) = B (e x) (e z) := by
      intro x z
      have h := hBinv (e * k * e⁻¹) heke (e x) (e z)
      simpa [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.apply_inv_self] using h
    have h2 : ∀ x, B (k x) (Tmul (k y)) = B x (Tmul y) := by
      intro x
      have h := h1 x y
      rw [hTmul (k x) (k y), hTmul x y] at h
      exact h
    have h3 : ∀ x, B (k x) (Tmul (k y)) = B x (k⁻¹ (Tmul (k y))) := by
      intro x
      have h := hBinv k hk x (k⁻¹ (Tmul (k y)))
      simpa [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.apply_inv_self] using h
    have h4 : ∀ x, B x (k⁻¹ (Tmul (k y))) = B x (Tmul y) := fun x => by rw [← h3 x, h2 x]
    have h4' : ∀ z, B (k⁻¹ (Tmul (k y)) * (Tmul y)⁻¹) z = 1 := by
      intro z
      rw [hsymm (k⁻¹ (Tmul (k y)) * (Tmul y)⁻¹) z, map_mul, map_inv, h4 z,
        mul_inv_cancel]
    have h5 : k⁻¹ (Tmul (k y)) = Tmul y := by
      have h := hBnd (k⁻¹ (Tmul (k y)) * (Tmul y)⁻¹) h4'
      rwa [mul_inv_eq_one] at h
    have := congrArg (fun z => k z) h5
    simpa using this
  have hTmemX : Tmul ∈ X := by
    rw [← Std139.alpha_centralizer hw2 S hn3 hK hirr]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    ext y
    exact (hTcomm k hk y).symm
  have hTone : Tmul = 1 := by
    by_contra hTne
    have hzp : Subgroup.zpowers Tmul = X := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [hxX]
        exact Subgroup.zpowers_le.mpr (hxX ▸ hTmemX)
      · rw [S.Xcard, Nat.card_zpowers]
        have hx3ord : orderOf x₀ = 3 := by
          have hd : orderOf x₀ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
          rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) (orderOf x₀) hd)
            with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hxne
          · exact h
        have hdvd : orderOf Tmul ∣ 3 := by
          have h := Subgroup.card_dvd_of_le
            (show Subgroup.zpowers Tmul ≤ Subgroup.zpowers x₀ from by
              rw [← hxX]; exact Subgroup.zpowers_le.mpr hTmemX)
          rwa [Nat.card_zpowers, Nat.card_zpowers, hx3ord] at h
        rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) (orderOf Tmul) hdvd)
          with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hTne
        · omega
    have hfixT : fixV (Subgroup.zpowers Tmul) = ⊥ := by rw [hzp]; exact hfix
    have hYperp_card := w1369_perp_card hw2 S hn B hBnd hBalt
    have hYcard : Nat.card Y = 4 ^ (n - 1) := w1369_card_Y hw2 S (by omega)
    have hYge : 4 < Nat.card Y := by
      rw [hYcard]
      calc (4 : ℕ) < 4 ^ 3 := by norm_num
        _ ≤ 4 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    let φ : W →* W :=
      { toFun := fun b => Tmul b * b⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [map_mul, mul_inv_rev]
          ac_rfl }
    have hker : φ.ker = fixV (Subgroup.zpowers Tmul) := by
      ext b
      rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff]
      constructor
      · intro h
        change Tmul b * b⁻¹ = 1 at h
        rwa [mul_inv_eq_one] at h
      · intro h
        show Tmul b * b⁻¹ = 1
        rw [h, mul_inv_cancel]
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, hfixT]
    have hmap : ∀ b : Y, Tmul (b : W) * (b : W)⁻¹ ∈ w1369_perp B Y := by
      intro b
      rw [w1369_mem_perp]
      intro a ha
      rw [map_mul, map_inv]
      have hea : e a = a := mem_fixV.mp (S.YD ha) e he
      have heb : e (b : W) = (b : W) := mem_fixV.mp (S.YD b.2) e he
      have h1 : B a (Tmul (b : W)) = B a (b : W) := by
        rw [← hTmul a (b : W), hea, heb]
      rw [h1, mul_inv_cancel]
    have hle : Nat.card Y ≤ Nat.card (w1369_perp B Y) :=
      Nat.card_le_card_of_injective
        (fun b : Y => (⟨Tmul (b : W) * (b : W)⁻¹, hmap b⟩ : w1369_perp B Y))
        (fun b1 b2 h => Subtype.ext (hφinj (Subtype.ext_iff.mp h)))
    omega
  intro a b
  have h := hTmul a b
  rw [hTone] at h
  simpa using h

theorem Std139.alpha_not_symplectic_ge4 (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 4 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    (hB : HasSympForm K) : False := by
  classical
  obtain ⟨B, hBnd, hBalt, hBinv⟩ := hB
  obtain ⟨x, hxX, hx3, hxne, hfix, -⟩ := Std139.exists_gen hw2 S
  have hYne_top : Y ≠ ⊤ := by
    intro htop
    have h := S.Yrk
    rw [htop, rkIdx, Subgroup.index_top,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 1)] at h
    exact absurd h (by norm_num)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : W, v₀ ∉ Y := by
    by_contra h
    exact hYne_top (eq_top_iff.mpr fun v _ => by
      by_contra hv
      exact h ⟨v, hv⟩)
  have hmem : ∀ e' : D, (e' : MulAut W) v₀ * v₀⁻¹ ∈ w1369_perp B Y := by
    intro e'
    by_cases he1 : (e' : MulAut W) = 1
    · rw [he1, MulAut.one_apply, mul_inv_cancel]
      exact (w1369_perp B Y).one_mem
    · rw [w1369_mem_perp]
      intro a ha
      have hpres := w1369_e_preserves hw2 S hn hK hirr B hBnd hBalt hBinv hxX hx3 hxne hfix
        e'.2 he1
      rw [map_mul, map_inv]
      have hea : (e' : MulAut W) a = a := mem_fixV.mp (S.YD ha) (e' : MulAut W) e'.2
      have h1 : B a ((e' : MulAut W) v₀) = B a v₀ := by
        rw [← hpres a v₀, hea]
      rw [h1, mul_inv_cancel]
  let F : D → w1369_perp B Y := fun e' => ⟨(e' : MulAut W) v₀ * v₀⁻¹, hmem e'⟩
  have hinjF : Function.Injective F := by
    intro e1 e2 heq
    have hv : (e1 : MulAut W) v₀ = (e2 : MulAut W) v₀ := by
      have h := congrArg Subtype.val heq
      exact mul_right_cancel h
    apply Subtype.ext
    have hxmem : x ∈ X := by rw [hxX]; exact Subgroup.mem_zpowers x
    have hg : (e2 : MulAut W)⁻¹ * (e1 : MulAut W) = 1 :=
      w1369_eq_one_of_fixes hw2 S hxX hx3 hfix hv₀
        (g := (e2 : MulAut W)⁻¹ * (e1 : MulAut W))
        (fun y hy => by
          show ((e2 : MulAut W)⁻¹ * (e1 : MulAut W)) y = y
          rw [MulAut.mul_apply]
          have h1 : (e1 : MulAut W) y = y := mem_fixV.mp (S.YD hy) (e1 : MulAut W) e1.2
          have h2 : (e2 : MulAut W) y = y := mem_fixV.mp (S.YD hy) (e2 : MulAut W) e2.2
          rw [h1]
          conv_lhs => rw [← h2]
          exact MulEquiv.symm_apply_apply (e2 : MulAut W) y)
        (by
          show ((e2 : MulAut W)⁻¹ * (e1 : MulAut W)) v₀ = v₀
          rw [MulAut.mul_apply, hv]
          exact MulEquiv.symm_apply_apply (e2 : MulAut W) v₀)
        (by
          show ((e2 : MulAut W)⁻¹ * (e1 : MulAut W)) (x v₀) = x v₀
          rw [MulAut.mul_apply]
          have hx1 : (e1 : MulAut W) (x v₀) = x ((e1 : MulAut W) v₀) := by
            calc (e1 : MulAut W) (x v₀) = ((e1 : MulAut W) * x) v₀ := rfl
              _ = (x * (e1 : MulAut W)) v₀ := by rw [S.DX (e1 : MulAut W) e1.2 x hxmem]
              _ = x ((e1 : MulAut W) v₀) := rfl
          have hx2 : x ((e2 : MulAut W) v₀) = (e2 : MulAut W) (x v₀) := by
            calc x ((e2 : MulAut W) v₀) = (x * (e2 : MulAut W)) v₀ := rfl
              _ = ((e2 : MulAut W) * x) v₀ := by rw [← S.DX (e2 : MulAut W) e2.2 x hxmem]
              _ = (e2 : MulAut W) (x v₀) := rfl
          rw [hx1, hv, hx2]
          exact MulEquiv.symm_apply_apply (e2 : MulAut W) (x v₀))
    have := congrArg (fun z => (e2 : MulAut W) * z) hg
    simpa using this
  have hcard_le : Nat.card D ≤ Nat.card (w1369_perp B Y) :=
    Nat.card_le_card_of_injective F hinjF
  have hDge : 8 ≤ Nat.card D := by
    rw [S.Dcard]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperp := w1369_perp_card hw2 S hn B hBnd hBalt
  omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
