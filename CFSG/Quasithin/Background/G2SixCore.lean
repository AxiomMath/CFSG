module

public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G1HalfSum

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

@[expose, instance_reducible] def distribMulActionAdditive {K M : Type*} [Monoid K] [CommGroup M]
    (ρ : K →* MulAut M) : DistribMulAction K (Additive M) where
  smul k a := Additive.ofMul (ρ k (Additive.toMul a))
  one_smul a := by
    show Additive.ofMul (ρ 1 (Additive.toMul a)) = a
    rw [map_one]
    rfl
  mul_smul k l a := by
    show Additive.ofMul (ρ (k * l) (Additive.toMul a)) =
      Additive.ofMul (ρ k (Additive.toMul (Additive.ofMul (ρ l (Additive.toMul a)))))
    rw [map_mul]
    rfl
  smul_zero k := by
    show Additive.ofMul (ρ k (Additive.toMul (0 : Additive M))) = 0
    exact congrArg Additive.ofMul (map_one (ρ k))
  smul_add k a b := by
    show Additive.ofMul (ρ k (Additive.toMul (a + b))) = _
    exact congrArg Additive.ofMul (map_mul (ρ k) (Additive.toMul a) (Additive.toMul b))

variable {G : Type*} [Group G]

namespace QuotSetting

variable {I Sx S₂ : Subgroup G} (Q : QuotSetting I Sx S₂) [(S₂.subgroupOf Sx).Normal]

@[expose] noncomputable def actOfHom {K : Type*} [Group K] (β : ↥I →* K)
    (hβ : Function.Surjective β) (hβk : ∀ x : ↥I, β x = 1 → (x : G) ∈ Sx) :
    K →* MulAut (SecQuot Sx S₂) :=
  β.liftOfRightInverse (Function.surjInv hβ) (Function.rightInverse_surjInv hβ)
    ⟨Q.convAct, fun x hx => Q.convAct_ker x (hβk x hx)⟩

theorem actOfHom_apply {K : Type*} [Group K] (β : ↥I →* K) (hβ : Function.Surjective β)
    (hβk : ∀ x : ↥I, β x = 1 → (x : G) ∈ Sx) (x : ↥I) :
    Q.actOfHom β hβ hβk (β x) = Q.convAct x :=
  β.liftOfRightInverse_comp_apply (Function.surjInv hβ) (Function.rightInverse_surjInv hβ)
    ⟨Q.convAct, fun x hx => Q.convAct_ker x (hβk x hx)⟩ x

end QuotSetting

section Main

variable {G : Type} [Group G] [Finite G] {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_sum_natural_of_halves (hG13 : Theorem_G_1_3 F 2 (le_refl 2))
    {I Sx S₂ W W' Uc : Subgroup G} (Q : QuotSetting I Sx S₂)
    (β : ↥I →* SL(2, F)) (hβ : Function.Surjective β) (hβk : ∀ x : ↥I, β x = 1 → (x : G) ∈ Sx)
    (hS₂W : S₂ ≤ W) (hWSx : W ≤ Sx) (h : ↥I) (hh : (β h).1 1 0 ≠ 0)
    (hW' : ∀ y : G, y ∈ W' ↔ (h : G)⁻¹ * y * h ∈ W)
    (hinv : ∀ i : ↥I, (β i).1 1 0 = 0 → ∀ w ∈ W, (i : G) * w * (i : G)⁻¹ ∈ W)
    (hRU : ∀ r ∈ Rg F, ∃ u : ↥I, (u : G) ∈ Uc ∧ β u = r)
    (hcomm : ∀ u ∈ Uc, ∀ s ∈ Sx, ⁅u, s⁆ ∈ W) (hfix : ∀ u ∈ Uc, ∀ w ∈ W, ⁅u, w⁆ ∈ S₂)
    (hdisj : W ⊓ W' = S₂) (hsup : W ⊔ W' = Sx) :
    ∃ (s : ℕ) (φ : ↥Sx →* Multiplicative (Fin s → Fin 2 → F)),
      Function.Surjective φ ∧ (∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ S₂) ∧
      (∀ (m : ↥I) (x y : ↥Sx), (y : G) = m * x * m⁻¹ →
        φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)) ∧
      Nat.card ↥W = Nat.card ↥S₂ * Nat.card F ^ s ∧
      ∀ x ∈ Sx, (∀ u ∈ Uc, ⁅u, x⁆ ∈ S₂) ↔ x ∈ W := by
  have hN := Q.normal
  let _ : CommGroup (SecQuot Sx S₂) := Q.quotCommGroup
  have hW'Sx : W' ≤ Sx := le_sup_right.trans hsup.le
  have hS₂W' : S₂ ≤ W' := hdisj ▸ inf_le_right
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SL(2, F) →* MulAut (SecQuot Sx S₂), ∀ x : ↥I, ρ (β x) = Q.convAct x :=
    ⟨Q.actOfHom β hβ hβk, Q.actOfHom_apply β hβ hβk⟩
  let _ : DistribMulAction SL(2, F) (Additive (SecQuot Sx S₂)) := distribMulActionAdditive ρ
  have hconj : ∀ (i : ↥I) (x : ↥Sx), ρ (β i) (secMk Sx S₂ x) =
      secMk Sx S₂ ⟨(i : G) * x * (i : G)⁻¹, Q.nS i i.2 x x.2⟩ := fun i x => by
    rw [hρ, Q.convAct_mk]
  let Y : AddSubgroup (Additive (SecQuot Sx S₂)) := Subgroup.toAddSubgroup (secImg Sx S₂ W)
  have hY : ∀ a : SecQuot Sx S₂, Additive.ofMul a ∈ Y ↔ a ∈ secImg Sx S₂ W := fun a => Iff.rfl
  have hm3 : Y.map (actU (β h)) = Subgroup.toAddSubgroup (secImg Sx S₂ W') := by
    ext z
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    show Additive.ofMul a ∈ Y.map (actU (β h)) ↔ a ∈ secImg Sx S₂ W'
    constructor
    · rintro ⟨y, hy, hya⟩
      obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
      obtain ⟨x, hxW, rfl⟩ := mem_secImg.1 ((hY b).1 hy)
      have ha : a = ρ (β h) (secMk Sx S₂ x) := (congrArg Additive.toMul hya).symm
      rw [ha, hconj]
      refine secMk_mem_secImg ((hW' _).2 ?_)
      have e : (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * h = x := by group
      show (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * h ∈ W
      rw [e]
      exact hxW
    · intro ha
      obtain ⟨z, hzW', rfl⟩ := mem_secImg.1 ha
      have hxS : (h : G)⁻¹ * z * h ∈ Sx := by
        have := Q.nS ((h : G)⁻¹) (inv_mem h.2) z z.2
        simpa using this
      refine ⟨Additive.ofMul (secMk Sx S₂ ⟨(h : G)⁻¹ * z * h, hxS⟩),
        (hY _).2 (secMk_mem_secImg ((hW' _).1 hzW')), ?_⟩
      show Additive.ofMul (ρ (β h) (secMk Sx S₂ ⟨(h : G)⁻¹ * z * h, hxS⟩)) =
        Additive.ofMul (secMk Sx S₂ z)
      rw [hconj]
      congr 2
      apply Subtype.ext
      show (h : G) * ((h : G)⁻¹ * z * h) * (h : G)⁻¹ = z
      group
  have hm1 : secImg Sx S₂ W ⊓ secImg Sx S₂ W' = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, ha'⟩
    obtain ⟨x, hxW, rfl⟩ := mem_secImg.1 ha
    obtain ⟨x', hxW', hxx'⟩ := mem_secImg.1 ha'
    have h1 := secMk_eq_secMk_iff.1 hxx'
    have hxW'' : (x : G) ∈ W' := by
      have e : (x : G) = (x' : G) * ((x' : G)⁻¹ * x) := by group
      rw [e]
      exact mul_mem hxW' (hS₂W' h1)
    have h2 : (x : G) ∈ S₂ := by
      rw [← hdisj]
      exact ⟨hxW, hxW''⟩
    exact Subgroup.mem_bot.2 (secMk_eq_one_iff.2 h2)
  have hm2 : secImg Sx S₂ W ⊔ secImg Sx S₂ W' = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨x, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) a
    have hx : x ∈ (W.subgroupOf Sx) ⊔ (W'.subgroupOf Sx) := by
      rw [← Subgroup.subgroupOf_sup hWSx hW'Sx, hsup, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top x
    have hle : (W.subgroupOf Sx) ⊔ (W'.subgroupOf Sx) ≤
        (secImg Sx S₂ W ⊔ secImg Sx S₂ W').comap (secMk Sx S₂) := by
      refine sup_le ?_ ?_
      · intro w hw
        exact Subgroup.mem_sup_left (secMk_mem_secImg (A := Sx) (B := S₂) (x := w) hw)
      · intro w hw
        exact Subgroup.mem_sup_right (secMk_mem_secImg (A := Sx) (B := S₂) (x := w) hw)
    exact hle hx
  have hdisj' : Y ⊓ Y.map (actU (β h)) = ⊥ := by
    rw [hm3, eq_bot_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    have h1 : a ∈ secImg Sx S₂ W ⊓ secImg Sx S₂ W' :=
      Subgroup.mem_inf.2 ⟨(AddSubgroup.mem_inf.1 hz).1, (AddSubgroup.mem_inf.1 hz).2⟩
    rw [hm1] at h1
    rw [Subgroup.mem_bot.1 h1]
    exact AddSubgroup.mem_bot.2 rfl
  have hsup' : Y ⊔ Y.map (actU (β h)) = ⊤ := by
    rw [hm3, eq_top_iff]
    intro z _
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective z
    have ha : a ∈ secImg Sx S₂ W ⊔ secImg Sx S₂ W' := by
      rw [hm2]
      exact Subgroup.mem_top a
    have h1 : Additive.ofMul a ∈
        Subgroup.toAddSubgroup (secImg Sx S₂ W ⊔ secImg Sx S₂ W') := ha
    rwa [OrderIso.map_sup] at h1
  have hinv' : ∀ k : SL(2, F), k.1 1 0 = 0 → ∀ y ∈ Y, k • y ∈ Y := by
    intro k hk y hy
    obtain ⟨i, rfl⟩ := hβ k
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
    obtain ⟨x, hxW, rfl⟩ := mem_secImg.1 ((hY b).1 hy)
    show Additive.ofMul (ρ (β i) (secMk Sx S₂ x)) ∈ Y
    rw [hconj]
    exact (hY _).2 (secMk_mem_secImg (hinv i hk x hxW))
  have hcomm' : ∀ t ∈ Rg F, ∀ u : Additive (SecQuot Sx S₂), t • u - u ∈ Y := by
    intro t ht u
    obtain ⟨i, hiU, rfl⟩ := hRU t ht
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective u
    obtain ⟨x, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) b
    show Additive.ofMul (ρ (β i) (secMk Sx S₂ x) / secMk Sx S₂ x) ∈ Y
    rw [hconj, div_eq_mul_inv, ← map_inv (secMk Sx S₂) x, ← map_mul]
    exact (hY _).2 (secMk_mem_secImg (hcomm i hiU x x.2))
  have hfix' : ∀ t ∈ Rg F, ∀ y ∈ Y, t • y = y := by
    intro t ht y hy
    obtain ⟨i, hiU, rfl⟩ := hRU t ht
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
    obtain ⟨x, hxW, rfl⟩ := mem_secImg.1 ((hY b).1 hy)
    show Additive.ofMul (ρ (β i) (secMk Sx S₂ x)) = Additive.ofMul (secMk Sx S₂ x)
    rw [hconj]
    congr 1
    rw [secMk_eq_secMk_iff]
    have h1 := hfix i hiU ((x : G)⁻¹) (inv_mem hxW)
    have e : ((i : G) * x * (i : G)⁻¹)⁻¹ * x = ⁅(i : G), (x : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    show ((i : G) * x * (i : G)⁻¹)⁻¹ * x ∈ S₂
    rw [e]
    exact h1
  have hsq : ∀ u : Additive (SecQuot Sx S₂), u + u = 0 := fun u => by
    show Additive.ofMul (Additive.toMul u * Additive.toMul u) = Additive.ofMul 1
    exact congrArg Additive.ofMul (Q.quot_sq _)
  obtain ⟨s, Θ, hΘ, hcard, hC⟩ := exists_equiv_of_halves (U := Additive (SecQuot Sx S₂)) hG13 hsq Y
    (β h) hh hinv' hcomm' hfix' hdisj' hsup'
  let ψ : Additive (SecQuot Sx S₂) →+ (Fin s → Fin 2 → F) := Θ.symm.toAddMonoidHom
  let φ : ↥Sx →* Multiplicative (Fin s → Fin 2 → F) :=
    (AddMonoidHom.toMultiplicativeRight ψ).comp (secMk Sx S₂)
  have hφ : ∀ x : ↥Sx, φ x =
      Multiplicative.ofAdd (Θ.symm (Additive.ofMul (secMk Sx S₂ x))) := fun x => rfl
  have hΘsymm : ∀ (k : SL(2, F)) (u : Additive (SecQuot Sx S₂)),
      Θ.symm (k • u) = fun j => k • (Θ.symm u) j := by
    intro k u
    apply Θ.injective
    rw [AddEquiv.apply_symm_apply, hΘ k (Θ.symm u), AddEquiv.apply_symm_apply]
  refine ⟨s, φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨a, ha⟩ : ∃ a : SecQuot Sx S₂, Additive.ofMul a = Θ (Multiplicative.toAdd v) :=
      ⟨Additive.toMul (Θ (Multiplicative.toAdd v)), rfl⟩
    obtain ⟨x, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) a
    refine ⟨x, ?_⟩
    rw [hφ, ha, AddEquiv.symm_apply_apply]
    rfl
  · intro x
    rw [hφ]
    constructor
    · intro hx
      have h1 : Θ.symm (Additive.ofMul (secMk Sx S₂ x)) = 0 := hx
      have h2 : Additive.ofMul (secMk Sx S₂ x) = 0 := by
        have := congrArg Θ h1
        rwa [AddEquiv.apply_symm_apply, map_zero] at this
      exact secMk_eq_one_iff.1 h2
    · intro hx
      have h1 : secMk Sx S₂ x = 1 := secMk_eq_one_iff.2 hx
      rw [h1]
      show Multiplicative.ofAdd (Θ.symm (0 : Additive (SecQuot Sx S₂))) = 1
      rw [map_zero]
      rfl
  · intro m x y hy
    have hyx : y = ⟨(m : G) * x * (m : G)⁻¹, Q.nS m m.2 x x.2⟩ := Subtype.ext hy
    have h1 : Additive.ofMul (secMk Sx S₂ y) = β m • Additive.ofMul (secMk Sx S₂ x) := by
      show Additive.ofMul (secMk Sx S₂ y) = Additive.ofMul (ρ (β m) (secMk Sx S₂ x))
      rw [hconj, hyx]
    rw [hφ, hφ, h1, hΘsymm]
    rfl
  · have h1 : Nat.card ↥Y = Nat.card ↥(secImg Sx S₂ W) :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun a => Iff.rfl))
    rw [h1] at hcard
    let f : ↥W →* SecQuot Sx S₂ := (secMk Sx S₂).comp (Subgroup.inclusion hWSx)
    have hker : f.ker = S₂.subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact secMk_eq_one_iff
    have hrange : f.range = secImg Sx S₂ W := by
      ext z
      rw [MonoidHom.mem_range, mem_secImg]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨Subgroup.inclusion hWSx w, w.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have h2 := Subgroup.card_ker_mul_card_range f
    rw [hker, hrange, hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂W).toEquiv] at h2
    exact h2.symm
  · intro x hx
    constructor
    · intro hux
      have hfixed : ∀ t ∈ Rg F, t • Additive.ofMul (secMk Sx S₂ ⟨x, hx⟩) =
          Additive.ofMul (secMk Sx S₂ ⟨x, hx⟩) := by
        intro t ht
        obtain ⟨i, hiU, rfl⟩ := hRU t ht
        show Additive.ofMul (ρ (β i) (secMk Sx S₂ ⟨x, hx⟩)) = _
        rw [hconj]
        congr 1
        rw [secMk_eq_secMk_iff]
        have hc := hux i hiU
        have h3 := Q.nS₂ (x⁻¹) (inv_mem (Q.Sx_le hx)) (⁅(i : G), x⁆⁻¹) (inv_mem hc)
        have e : ((i : G) * x * (i : G)⁻¹)⁻¹ * x = x⁻¹ * ⁅(i : G), x⁆⁻¹ * x⁻¹⁻¹ := by
          rw [commutatorElement_def]
          group
        show ((i : G) * x * (i : G)⁻¹)⁻¹ * x ∈ S₂
        rw [e]
        exact h3
      obtain ⟨w, hwW, hw⟩ := mem_secImg.1 ((hY _).1 (hC _ hfixed))
      have h4 := secMk_eq_secMk_iff.1 hw
      have e : x = (w : G) * ((w : G)⁻¹ * x) := by group
      rw [e]
      exact mul_mem hwW (hS₂W h4)
    · intro hxW u hu
      exact hfix u hu x hxW

end Main

end CFSG.Quasithin
