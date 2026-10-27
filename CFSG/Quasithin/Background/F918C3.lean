module

public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

universe u

section Defs

variable {G : Type u} [Group G]

@[expose] def HasNoFaithfulFFModulesMod (X C : Subgroup G) : Prop :=
  ∀ (W : Type u) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : ↥X →* MulAut W,
    (∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ C) → ¬ IsFFModule ρ.range

end Defs

section Unsat

noncomputable def invHom {W : Type} [CommGroup W] (τ : MulAut W) (h : τ * τ = 1) :
    Multiplicative (ZMod 2) →* MulAut W :=
  let f : ℤ →+ Additive (MulAut W) := zmultiplesHom _ (Additive.ofMul τ)
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨f, by
    have h2 : (2 : ℤ) • Additive.ofMul τ = Additive.ofMul (τ ^ (2 : ℤ)) := (ofMul_zpow 2 τ).symm
    have h3 : τ ^ (2 : ℤ) = 1 := by rw [zpow_two, h]
    show (2 : ℤ) • Additive.ofMul τ = 0
    rw [h2, h3]
    rfl⟩)

theorem invHom_ofAdd_one {W : Type} [CommGroup W] (τ : MulAut W) (h : τ * τ = 1) :
    invHom τ h (Multiplicative.ofAdd 1) = τ := by
  show Additive.toMul ((ZMod.lift 2 _) ((1 : ℤ) : ZMod 2)) = τ
  rw [ZMod.lift_coe]
  show Additive.toMul ((1 : ℤ) • Additive.ofMul τ) = τ
  rw [one_smul]
  rfl

theorem not_hasNoFFModulesMod_of_module {G : Type} [Group G] {X C : Subgroup G}
    (χ : ↥X →* Multiplicative (ZMod 2)) (hχ : Function.Surjective χ)
    (hC : ∀ x : ↥X, (x : G) ∈ C → χ x = 1) {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W ≤ 4) (τ : MulAut W) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (v : W) (hv1 : v ≠ 1) (hv : τ v = v) : ¬ HasNoFFModulesMod X C := by
  intro hNo
  let ρ : ↥X →* MulAut W := (invHom τ hτ2).comp χ
  have hker : ∀ x : ↥X, (x : G) ∈ C → ρ x = 1 := fun x hx => by
    show invHom τ hτ2 (χ x) = 1
    rw [hC x hx, map_one]
  refine hNo W hsq ρ hker ?_
  have hrange : ∀ a ∈ ρ.range, a = 1 ∨ a = τ := by
    rintro _ ⟨x, rfl⟩
    show invHom τ hτ2 (χ x) = 1 ∨ invHom τ hτ2 (χ x) = τ
    have : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases this (χ x) with h | h
    · left; rw [h, map_one]
    · right; rw [h, invHom_ofAdd_one]
  have hτ : τ ∈ ρ.range := by
    obtain ⟨x, hx⟩ := hχ (Multiplicative.ofAdd 1)
    exact ⟨x, by show invHom τ hτ2 (χ x) = τ; rw [hx, invHom_ofAdd_one]⟩
  refine ⟨ρ.range, le_rfl, fun h => hτ1 (Subgroup.mem_bot.1 (h ▸ hτ)), ⟨?_, ?_⟩, ?_⟩
  · intro a ha b hb
    rcases hrange a ha with rfl | rfl <;> rcases hrange b hb with rfl | rfl <;> simp
  · intro a ha
    rcases hrange a ha with rfl | rfl
    · simp
    · rw [pow_two, hτ2]
  · have hA : 1 < Nat.card ↥ρ.range :=
      Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨1, one_mem _⟩, ⟨τ, hτ⟩, fun h => hτ1 (by
        have := congrArg Subtype.val h
        exact this.symm)⟩⟩
    have hF : 1 < Nat.card ↥(fixV ρ.range) := by
      refine Finite.one_lt_card_iff_nontrivial.2
        ⟨⟨⟨1, one_mem _⟩, ⟨v, fun a ha => ?_⟩, fun h => ?_⟩⟩
      · rcases hrange a ha with rfl | rfl
        · simp
        · exact hv
      · exact hv1 (congrArg Subtype.val h).symm
    nlinarith

@[expose] def tauAdd : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2) where
  toFun v := (v.1 + v.2, v.2)
  invFun v := (v.1 + v.2, v.2)
  left_inv v := by
    have : ∀ b : ZMod 2, b + b = 0 := by decide
    ext
    · simp [add_assoc, this]
    · rfl
  right_inv v := by
    have : ∀ b : ZMod 2, b + b = 0 := by decide
    ext
    · simp [add_assoc, this]
    · rfl
  map_add' v w := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add]
      abel
    · rfl

@[expose] def tauV : MulAut (Multiplicative (ZMod 2 × ZMod 2)) := AddEquiv.toMultiplicative tauAdd

theorem tauV_mul_self : tauV * tauV = 1 := by
  have : ∀ b : ZMod 2, b + b = 0 := by decide
  refine MulEquiv.ext fun w => ?_
  rw [MulAut.mul_apply, MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  show tauAdd (tauAdd (Multiplicative.toAdd w)) = Multiplicative.toAdd w
  ext
  · simp [tauAdd, add_assoc, this]
  · rfl

theorem tauV_ne_one : tauV ≠ 1 := by
  intro h
  have := congrArg (fun f : MulAut (Multiplicative (ZMod 2 × ZMod 2)) =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)))) h
  simp [tauV, tauAdd] at this

theorem not_hasNoFFModulesMod_of_quotient {G : Type} [Group G] {X C : Subgroup G}
    (χ : ↥X →* Multiplicative (ZMod 2)) (hχ : Function.Surjective χ)
    (hC : ∀ x : ↥X, (x : G) ∈ C → χ x = 1) : ¬ HasNoFFModulesMod X C :=
  not_hasNoFFModulesMod_of_module (W := Multiplicative (ZMod 2 × ZMod 2)) χ hχ hC (by decide)
    (by rw [Nat.card_eq_fintype_card]; decide) tauV tauV_mul_self tauV_ne_one
    (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) (by decide) (by decide)

end Unsat

section Faithful

variable {G : Type u} [Group G] [Finite G]

theorem not_hasNoFaithfulFFModulesMod_of_isFFInt {X C F E : Subgroup G}
    (hFN : X ≤ Subgroup.normalizer (F : Set G)) (hEN : X ≤ Subgroup.normalizer (E : Set G))
    (hEF : E ≤ Subgroup.normalizer (F : Set G))
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (F : Set G)) F E))
    (hC : ∀ x ∈ X ⊓ C, ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F)
    (hker : ∀ x ∈ X, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ C)
    (hFF : IsFFInt (secImg (Subgroup.normalizer (F : Set G)) F X)
      (secImg (Subgroup.normalizer (F : Set G)) F E) hE) :
    ¬ HasNoFaithfulFFModulesMod X C := by
  intro hNo
  let S : Subgroup (SecQuot (Subgroup.normalizer (F : Set G)) F) :=
    secImg (Subgroup.normalizer (F : Set G)) F E
  let _ : CommGroup ↥S := commGroupOfElemAbelian hE
  let f : ↥X →* SecQuot (Subgroup.normalizer (F : Set G)) F :=
    (secMk (Subgroup.normalizer (F : Set G)) F).comp (Subgroup.inclusion hFN)
  have hf : ∀ x : ↥X,
      f x ∈ Subgroup.normalizer (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)) :=
    fun x => secMk_mem_normalizer_secImg (X := E) (a := ⟨x, hFN x.2⟩) (hEN x.2)
  let ρ : ↥X →* MulAut ↥S := (conjAct S).comp (f.codRestrict _ hf)
  have hsq : ∀ w : ↥S, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hE.2 w w.2)
  have hρ : ∀ (x : ↥X) (e : G) (he : e ∈ E),
      ((ρ x ⟨secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩,
          secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := E)
            (x := ⟨e, hEF he⟩) he⟩ : ↥S) : SecQuot (Subgroup.normalizer (F : Set G)) F) =
        f x * secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩ * (f x)⁻¹ := fun x e he =>
    conjAct_apply_coe' S ⟨f x, hf x⟩ _
  have hker' : ∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ C := by
    intro x
    constructor
    · intro h1
      refine hker x x.2 fun e he => ?_
      have h2 := congrArg (fun a : ↥S => (a : SecQuot (Subgroup.normalizer (F : Set G)) F))
        (congrArg (fun r : MulAut ↥S => r ⟨secMk (Subgroup.normalizer (F : Set G)) F ⟨e, hEF he⟩,
          secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := E)
            (x := ⟨e, hEF he⟩) he⟩) h1)
      simp only [MulAut.one_apply] at h2
      rw [hρ x e he] at h2
      have h3 := mul_inv_eq_iff_eq_mul.mp h2
      exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (F : Set G)) (B := F)
        (x := ⟨x, hFN x.2⟩) (y := ⟨e, hEF he⟩) h3
    · intro hxC
      refine MulEquiv.ext fun w => ?_
      rw [MulAut.one_apply]
      apply Subtype.ext
      obtain ⟨e, he, hew⟩ := mem_secImg.mp w.2
      have hcomm : secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ *
          secMk (Subgroup.normalizer (F : Set G)) F e =
          secMk (Subgroup.normalizer (F : Set G)) F e *
          secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ :=
        secMk_comm_of_commutator_mem (hC x ⟨x.2, hxC⟩ e he)
      have hw : (w : SecQuot (Subgroup.normalizer (F : Set G)) F) =
          secMk (Subgroup.normalizer (F : Set G)) F e := hew.symm
      have h1 : ((ρ x w : ↥S) : SecQuot (Subgroup.normalizer (F : Set G)) F) =
          f x * (w : SecQuot (Subgroup.normalizer (F : Set G)) F) * (f x)⁻¹ :=
        conjAct_apply_coe' S ⟨f x, hf x⟩ w
      rw [h1, hw]
      change secMk _ F ⟨x, hFN x.2⟩ * secMk _ F e * (secMk _ F ⟨x, hFN x.2⟩)⁻¹ = secMk _ F e
      rw [hcomm]; group
  have hrange : ρ.range = autOn (secImg (Subgroup.normalizer (F : Set G)) F X) S := by
    ext a
    rw [mem_autOn_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hfx : f x = secMk (Subgroup.normalizer (F : Set G)) F ⟨x, hFN x.2⟩ := rfl
      refine ⟨⟨f x, hf x⟩, ?_, rfl⟩
      show f x ∈ secImg (Subgroup.normalizer (F : Set G)) F X
      rw [hfx]
      exact secMk_mem_secImg (A := Subgroup.normalizer (F : Set G)) (B := F) (X := X)
        (x := ⟨(x : G), hFN x.2⟩) x.2
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hys⟩ := mem_secImg.mp (hs : (s : SecQuot (Subgroup.normalizer (F : Set G)) F) ∈
        secImg (Subgroup.normalizer (F : Set G)) F X)
      refine ⟨⟨y, hy⟩, ?_⟩
      have : (⟨f ⟨y, hy⟩, hf ⟨y, hy⟩⟩ : ↥(Subgroup.normalizer
          (S : Set (SecQuot (Subgroup.normalizer (F : Set G)) F)))) = s := Subtype.ext hys
      show (conjAct S) _ = conjAct S s
      rw [← this]
      rfl
  have := hNo ↥S hsq ρ hker'
  rw [hrange] at this
  exact this hFF

namespace HypF918

variable {T V L V₁ Vp H K : Subgroup G}

theorem ker_le_pCoreOf (h : HypF918 T V L V₁ Vp H K) (hH : H = conjClosure K T ⊔ T)
    (hZ : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H)
    {F E : Subgroup G} (hF : conjClosure K T ⊔ T ≤ Subgroup.normalizer (F : Set G))
    (hE : conjClosure K T ⊔ T ≤ Subgroup.normalizer (E : Set G))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) :
    ∀ x ∈ conjClosure K T ⊔ T, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hXH : conjClosure K T ⊔ T ≤ H := h.K₀T_le_H
  have hHX : H ≤ conjClosure K T ⊔ T := hH.le
  have hXn : conjClosure K T ⊔ T ≤ Subgroup.normalizer ((conjClosure K T ⊔ T : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hK₀n : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    K₀T_le_normalizer_K₀ T K
  obtain ⟨Nx, hNxX, hNxn, hNx3, hNx4⟩ : ∃ Nx : Subgroup G, Nx ≤ conjClosure K T ⊔ T ∧
      conjClosure K T ⊔ T ≤ Subgroup.normalizer (Nx : Set G) ∧
      (∀ x ∈ conjClosure K T ⊔ T, (∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) → x ∈ Nx) ∧
      (∀ n ∈ Nx, ∀ e ∈ E, n * e * n⁻¹ * e⁻¹ ∈ F) :=
    ⟨centralizerMod F (conjClosure K T ⊔ T) E, centralizerMod_le_left _ _ _,
      le_normalizer_centralizerMod hF hXn hE, fun x hx h => ⟨hx, hF hx, h⟩,
      fun n hn e he => hn.2.2 e he⟩
  have hDK₀ : ⁅Nx, conjClosure K T⁆ ≤ conjClosure K T :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hNxX.trans hK₀n)
  have hDNx : ⁅Nx, conjClosure K T⁆ ≤ Nx := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hNxn)
  have hDn : conjClosure K T ⊔ T ≤ Subgroup.normalizer ((⁅Nx, conjClosure K T⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le hNxn hK₀n
  have hDQ : ⁅Nx, conjClosure K T⁆ ≤ pCoreOf 2 H := by
    rcases exists_le_or_commutator_le_pCoreOf h.K_cComp h.T_le_H h.K_quasisimple hDK₀
        (le_sup_left.trans hDn) (le_sup_right.trans hDn) with hle | hcomm
    · exact absurd (fun k hk e he => hNx4 _ (hDNx (hle hk)) e he) hnt
    · intro d hd
      exact hZ d (hDK₀ hd) fun k' hk' => hcomm (Subgroup.commutator_mem_commutator hd hk')
  have hNxH : Nx ≤ H := hNxX.trans hXH
  have hYn : H ≤ Subgroup.normalizer ((Nx ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    (le_inf (hHX.trans hNxn) hQn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hYH : Nx ⊔ pCoreOf 2 H ≤ H := sup_le hNxH (pCoreOf_le 2 H)
  have hmul : (Nx : Set G) * (pCoreOf 2 H : Set G) = ↑(Nx ⊔ pCoreOf 2 H) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right Nx (pCoreOf 2 H) (hNxH.trans hQn)).symm
  have hYcomm : ∀ y ∈ Nx ⊔ pCoreOf 2 H, ∀ k ∈ conjClosure K T, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro y hy k hk
    have hy' : y ∈ (Nx : Set G) * (pCoreOf 2 H : Set G) := by rw [hmul]; exact hy
    obtain ⟨n, hn, q, hq, rfl⟩ := hy'
    have hkH : k ∈ H := h.K₀_le_H hk
    have h1 : n * (q * k * q⁻¹ * k⁻¹) * n⁻¹ ∈ pCoreOf 2 H := by
      have h0 : q * k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
        have hq' : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (hQn hkH) q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
        have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 H).mul_mem hq hq'
      exact (Subgroup.mem_normalizer_iff.mp (hQn (hNxH hn)) _).mp h0
    have h2 : n * k * n⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hDQ (Subgroup.commutator_mem_commutator hn hk)
    have e : n * q * k * (n * q)⁻¹ * k⁻¹ =
        (n * (q * k * q⁻¹ * k⁻¹) * n⁻¹) * (n * k * n⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem h1 h2
  have hK₀quot : ∀ y ∈ conjClosure K T ⊔ T, ∃ m : ℕ, y ^ 2 ^ m ∈ conjClosure K T := by
    intro y hy
    have hTn : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
    have hmul' : (T : Set G) * (conjClosure K T : Set G) = ↑(T ⊔ conjClosure K T) :=
      (Subgroup.coe_mul_of_left_le_normalizer_right T (conjClosure K T) hTn).symm
    have hy' : y ∈ (T : Set G) * (conjClosure K T : Set G) := by
      rw [hmul', sup_comm]; exact hy
    obtain ⟨t, ht, a, ha, rfl⟩ := hy'
    obtain ⟨m, hm⟩ := h.sylow_H.2.1 ⟨t, ht⟩
    have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have key : ∀ n : ℕ, ∃ a' ∈ conjClosure K T, (t * a) ^ n = t ^ n * a' := by
      intro n
      induction n with
      | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | succ n ih =>
        obtain ⟨a', ha', h'⟩ := ih
        refine ⟨(t⁻¹ * a' * t) * a, (conjClosure K T).mul_mem
          ((Subgroup.mem_normalizer_iff''.mp (hTn ht) a').mp ha') ha, ?_⟩
        rw [pow_succ, h']
        group
    obtain ⟨a', ha', h'⟩ := key (2 ^ m)
    exact ⟨m, by rw [h', hm', one_mul]; exact ha'⟩
  have hY2 : IsPGroup 2 ↥(Nx ⊔ pCoreOf 2 H) := fun y => by
    obtain ⟨m, hm⟩ := hK₀quot y.1 (hHX (hYH y.2))
    have hz : y.1 ^ 2 ^ m ∈ pCoreOf 2 H :=
      hZ _ hm fun k' hk' => hYcomm _ ((Nx ⊔ pCoreOf 2 H).pow_mem y.2 _) k' hk'
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hz⟩
    refine ⟨m + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hYQ : Nx ⊔ pCoreOf 2 H ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hYH hYn hY2
  intro x hx hxE
  exact hYQ (Subgroup.mem_sup_left (hNx3 x hx hxE))

theorem F918_7' (h : HypF918 T V L V₁ Vp H K) (hH : H = conjClosure K T ⊔ T)
    (hZ : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H)
    {I : Subgroup G} (hI₁ : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hI : IsIrrPlusTilde V₁ (conjClosure K T) I)
    (hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H)) :
    tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have h1 := h.toHypF98.toHypF91
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hUW : conjClosure Vp H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h.toHypF98.F911_3 hIHU
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure Vp H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (h1.commutator_conjClosure_le e he x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hWK := h.tilde_commutator_conjClosure hIU hI
  have hW0 : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
    intro hbot
    have hIV₁ : I ≤ V₁ := by
      intro i hi
      have hiN : i ∈ Subgroup.normalizer (V₁ : Set G) := h1.H_normalizes_V₁ (hUH (hIU hi))
      have : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ ∈
          tildeOf V₁ (conjClosure I H) :=
        secMk_mem_secImg (x := ⟨i, hiN⟩) (le_conjClosure I H hi)
      rw [hbot] at this
      have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨i, hiN⟩ = 1 := this
      exact secMk_eq_one_iff.mp h2
    have hIC : I ≤ centralizerMod V₁ I (conjClosure K T) := by
      intro i hi
      refine ⟨hi, h1.H_normalizes_V₁ (hUH (hIU hi)), fun k hk => ?_⟩
      have h3 : k * i⁻¹ * k⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (h1.H_normalizes_V₁ (h.K₀_le_H hk)) i⁻¹).mp
          (V₁.inv_mem (hIV₁ hi))
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [e]
      exact V₁.mul_mem (hIV₁ hi) h3
    exact (not_le_of_gt hI.2.2.1) hIC
  by_contra hne
  have hnt1 : ¬ ∀ k ∈ conjClosure K T, ∀ w ∈ conjClosure I H, k * w * k⁻¹ * w⁻¹ ∈ V₁ := by
    intro hall
    have hle : ⁅conjClosure I H, conjClosure K T⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun w hw k hk => ?_
      have := V₁.inv_mem (hall k hk w hw)
      have e : (k * w * k⁻¹ * w⁻¹)⁻¹ = w * k * w⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hW0
    rw [← hWK]
    exact tildeOf_eq_bot_of_le hle
  have hnt2 : ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ conjClosure I H := by
    intro hall
    have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure I H := by
      refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
      have := (conjClosure I H).inv_mem (hall k hk u hu)
      have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
      rwa [e] at this
    apply hne
    refine le_antisymm ?_ (secImg_mono hle)
    rw [← hWK]
    exact secImg_mono (Subgroup.commutator_mono hIHU le_rfl)
  have hker1 := ker_le_pCoreOf h hH hZ h.K₀T_le_normalizer_V₁ hIHN hnt1
  have hker2 := ker_le_pCoreOf h hH hZ hIHN h.K₀T_le_normalizer_U hnt2
  have hFF1 : ∀ hFF : IsFFInt (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (conjClosure I H))
      (h.isElemAbelian_tilde_of_le hIHU), False := fun hFF =>
    not_hasNoFaithfulFFModulesMod_of_isFFInt (F := V₁) (E := conjClosure I H)
      h.K₀T_le_normalizer_V₁ hIHN (hIHU.trans (hUH.trans h1.H_normalizes_V₁))
      (h.isElemAbelian_tilde_of_le hIHU) (fun x hx e he => hQV₁ x hx.2 e (hIHU he))
      hker1 hFF hNo
  have hFF2 : ∀ hFF : IsFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure Vp H)) (h.isElemAbelian_quotient (conjClosure I H)), False := fun hFF =>
    not_hasNoFaithfulFFModulesMod_of_isFFInt (F := conjClosure I H) (E := conjClosure Vp H) hIHN
      h.K₀T_le_normalizer_U hUW (h.isElemAbelian_quotient _)
      (fun x hx e he => le_conjClosure I H (hI₁ (hQV₁ x hx.2 e he))) hker2 hFF hNo
  rcases h.F918_6 (le_trans hI₁ (le_conjClosure I H)) hIHU hIHN hW0 hWK with ha | ⟨hb1, hb2⟩ | hc
  · exact hne ha
  · exact (hFF1 hb1).elim
  · rcases hc with hc | hc
    · exact (hFF1 (F9.IsStrongFFInt.isFFInt hc)).elim
    · exact (hFF2 (F9.IsStrongFFInt.isFFInt hc)).elim

end HypF918

end Faithful

end CFSG.Quasithin
