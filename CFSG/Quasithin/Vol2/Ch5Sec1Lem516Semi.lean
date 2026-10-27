module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516TD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Offender

namespace Semi516

section Perm

variable {F : Type*} [Field F] {V' : Type*} [AddCommGroup V'] [Module F V']

theorem exists_isSemilinearWith_of_conj_smul [Finite F] [Nontrivial V'] (b : Equiv.Perm V')
    (hadd : ∀ x y, b (x + y) = b x + b y)
    (hμ : ∀ c : F, ∃ μ : F, ∀ x, b (c • b⁻¹ x) = μ • x) :
    ∃ σ : F ≃+* F, IsSemilinearWith b σ := by
  choose μ hμ using hμ
  have key : ∀ (c : F) (v : V'), b (c • v) = μ c • b v := fun c v => by
    have := hμ c (b v)
    simpa using this
  have hb0 : b 0 = 0 := by
    have := hadd 0 0
    simpa using this
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V')
  have uniq : ∀ s t : F, (∀ v, s • b v = t • b v) → s = t := fun s t h => by
    have h1 := h (b⁻¹ w₀)
    rw [show b (b⁻¹ w₀) = w₀ from Equiv.apply_symm_apply b w₀] at h1
    exact smul_left_injective F hw₀ h1
  let φ : F →+* F :=
    { toFun := μ
      map_one' := uniq _ _ fun v => by rw [← key, one_smul, one_smul]
      map_mul' := fun s t => uniq _ _ fun v => by rw [← key, mul_smul, key, key, mul_smul]
      map_zero' := uniq _ _ fun v => by rw [← key, zero_smul, zero_smul, hb0]
      map_add' := fun s t => uniq _ _ fun v => by rw [← key, add_smul, hadd, key, key, add_smul] }
  exact ⟨RingEquiv.ofBijective φ ⟨φ.injective, Finite.surjective_of_injective φ.injective⟩,
    fun c w => key c w⟩

theorem perm_apply_inv {X : Type*} (p : Equiv.Perm X) (x : X) : p (p⁻¹ x) = x :=
  Equiv.apply_symm_apply p x

theorem eq_one_of_pow_two_pow_eq_one [CharP F 2] {c : F} {k : ℕ} (hc : c ^ 2 ^ k = 1) :
    c = 1 := by
  have h : (c - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, hc, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.mp h)

end Perm

variable {G : Type} [Group G] {F : Type} [Field F] {d : ℕ} {W : Subgroup G}

@[expose] noncomputable def coordPerm (e : ↥W ≃* Multiplicative (Fin d → F)) :
    MulAut ↥W →* Equiv.Perm (Fin d → F) where
  toFun a :=
    { toFun := fun x => Multiplicative.toAdd (e (a (e.symm (Multiplicative.ofAdd x))))
      invFun := fun x => Multiplicative.toAdd (e (a⁻¹ (e.symm (Multiplicative.ofAdd x))))
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp

theorem coordPerm_apply (e : ↥W ≃* Multiplicative (Fin d → F)) (a : MulAut ↥W)
    (x : Fin d → F) :
    coordPerm e a x = Multiplicative.toAdd (e (a (e.symm (Multiplicative.ofAdd x)))) := rfl

theorem coordPerm_add (e : ↥W ≃* Multiplicative (Fin d → F)) (a : MulAut ↥W) (x y : Fin d → F) :
    coordPerm e a (x + y) = coordPerm e a x + coordPerm e a y := by
  simp only [coordPerm_apply, ofAdd_add, map_mul, toAdd_mul]

theorem coordPerm_toAdd (e : ↥W ≃* Multiplicative (Fin d → F)) (a : MulAut ↥W) (w : ↥W) :
    coordPerm e a (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e (a w)) := by
  simp [coordPerm_apply]

theorem coordPerm_injective (e : ↥W ≃* Multiplicative (Fin d → F)) :
    Function.Injective (coordPerm e) := by
  intro a b h
  ext w
  have h1 := congrArg (fun p : Equiv.Perm (Fin d → F) => p (Multiplicative.toAdd (e w))) h
  simp only [coordPerm_toAdd] at h1
  exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h1))

theorem coordPerm_eq_one_iff (e : ↥W ≃* Multiplicative (Fin d → F)) (a : MulAut ↥W) :
    coordPerm e a = 1 ↔ a = 1 :=
  ⟨fun h => coordPerm_injective e (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

@[expose] noncomputable def fixedEquiv (e : ↥W ≃* Multiplicative (Fin d → F)) (a : MulAut ↥W) :
    {w : ↥W // a w = w} ≃ {x : Fin d → F // coordPerm e a x = x} where
  toFun w := ⟨Multiplicative.toAdd (e w.1), by rw [coordPerm_toAdd, w.2]⟩
  invFun x := ⟨e.symm (Multiplicative.ofAdd x.1), by
    apply e.injective
    apply Multiplicative.toAdd.injective
    have := x.2
    rw [coordPerm_apply] at this
    simpa using this⟩
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[expose] noncomputable def act (e : ↥W ≃* Multiplicative (Fin d → F)) (g : G)
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : Equiv.Perm (Fin d → F) :=
  coordPerm e (conjAct W ⟨g, hg⟩)

theorem act_mul (e : ↥W ≃* Multiplicative (Fin d → F)) {g h : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (hh : h ∈ Subgroup.normalizer (W : Set G)) :
    act e (g * h) (Subgroup.mul_mem _ hg hh) = act e g hg * act e h hh := by
  unfold act
  rw [← map_mul, ← map_mul]
  rfl

theorem act_inv (e : ↥W ≃* Multiplicative (Fin d → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    act e g⁻¹ (Subgroup.inv_mem _ hg) = (act e g hg)⁻¹ := by
  unfold act
  rw [← map_inv, ← map_inv]
  rfl

theorem act_pow (e : ↥W ≃* Multiplicative (Fin d → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (k : ℕ) :
    act e (g ^ k) (Subgroup.pow_mem _ hg k) = act e g hg ^ k := by
  unfold act
  rw [← map_pow, ← map_pow]
  rfl

theorem act_add (e : ↥W ≃* Multiplicative (Fin d → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) (x y : Fin d → F) :
    act e g hg (x + y) = act e g hg x + act e g hg y :=
  coordPerm_add e _ x y

theorem act_eq_one_iff (e : ↥W ≃* Multiplicative (Fin d → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    act e g hg = 1 ↔ g ∈ Subgroup.centralizer (W : Set G) := by
  unfold act
  rw [coordPerm_eq_one_iff]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := congrArg (fun a : MulAut ↥W => ((a ⟨w, hw⟩ : ↥W) : G)) h
    simp only [conjAct_apply_coe, MulAut.one_apply] at this
    calc w * g = g * w * g⁻¹ * g := by rw [this]
      _ = g * w := by group
  · intro h
    ext w
    rw [conjAct_apply_coe, MulAut.one_apply]
    show g * (w : G) * g⁻¹ = w
    rw [← Subgroup.mem_centralizer_iff.mp h w w.2, mul_inv_cancel_right]

theorem act_zero (e : ↥W ≃* Multiplicative (Fin d → F)) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : act e g hg 0 = 0 := by
  have h := act_add e hg 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem isSemilinearWith_inv {K : Type*} [Field K] {V' : Type*} [AddCommGroup V'] [Module K V']
    {p : Equiv.Perm V'} {σ : K ≃+* K} (h : IsSemilinearWith p σ) : IsSemilinearWith p⁻¹ σ⁻¹ := by
  intro c w
  apply p.injective
  rw [h]
  show p (p.symm (c • w)) = σ (σ.symm c) • p (p.symm w)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem isElemAbelian_of_equiv [CharP F 2] (e : ↥W ≃* Multiplicative (Fin d → F)) :
    IsElemAbelian 2 W := by
  refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : ↥W) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have := congrArg Subtype.val h1
  simpa using this

section Main

structure Hyp (e : ↥W ≃* Multiplicative (Fin d → F)) (T B D : Subgroup G) : Prop where
  one_le : 1 ≤ d
  isPGroup : IsPGroup 2 T
  odd : Odd (Nat.card D)
  le_T : W ≤ T
  T_le : T ≤ Subgroup.normalizer (W : Set G)
  B_le : B ≤ Subgroup.normalizer (W : Set G)
  T_le_B : T ≤ Subgroup.normalizer (B : Set G)
  D_le : D ≤ B
  decomp : ∀ x ∈ T ⊔ D, ∃ t ∈ T, ∃ δ ∈ D, t * δ = x
  scalar : ∀ (b : G) (hb : b ∈ B), ∃ c : F, ∀ x, act e b (B_le hb) x = c • x
  surj : ∀ c : F, c ≠ 0 → ∃ (δ : G) (hδ : δ ∈ D), ∀ x, act e δ (B_le (D_le hδ)) x = c • x
  linear : ∀ (t : G) (ht : t ∈ T), IsSemilinearWith (act e t (T_le ht)) (1 : F ≃+* F) →
    t ∈ Subgroup.centralizer (W : Set G)
  faithful : D ⊓ Subgroup.centralizer (W : Set G) = ⊥

namespace Hyp

variable {T B D : Subgroup G} {e : ↥W ≃* Multiplicative (Fin d → F)} (h : Hyp e T B D)
include h

theorem nontrivial : Nontrivial (Fin d → F) := by
  have : Nonempty (Fin d) := ⟨⟨0, h.one_le⟩⟩
  infer_instance

theorem D_le_normalizer : D ≤ Subgroup.normalizer (W : Set G) := h.D_le.trans h.B_le

theorem sup_le_normalizer : T ⊔ D ≤ Subgroup.normalizer (W : Set G) :=
  sup_le h.T_le h.D_le_normalizer

theorem linear_D (δ : G) (hδ : δ ∈ D) :
    IsSemilinearWith (act e δ (h.D_le_normalizer hδ)) (1 : F ≃+* F) := by
  obtain ⟨c, hc⟩ := h.scalar δ (h.D_le hδ)
  intro a w
  show act e δ _ (a • w) = a • act e δ _ w
  rw [hc, hc, smul_comm]

theorem semilinear_T [Finite F] (t : G) (ht : t ∈ T) :
    ∃ σ : F ≃+* F, IsSemilinearWith (act e t (h.T_le ht)) σ := by
  have := h.nontrivial
  refine exists_isSemilinearWith_of_conj_smul _ (act_add e _) fun c => ?_
  by_cases hc : c = 0
  · refine ⟨0, fun x => ?_⟩
    rw [hc, zero_smul, zero_smul, act_zero]
  · obtain ⟨δ, hδ, hδc⟩ := h.surj c hc
    have hb : t * δ * t⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (h.T_le_B ht) δ).mp (h.D_le hδ)
    obtain ⟨μ, hμ⟩ := h.scalar _ hb
    refine ⟨μ, fun x => ?_⟩
    have e1 : act e (t * δ * t⁻¹) (h.B_le hb) =
        act e t (h.T_le ht) * act e δ (h.B_le (h.D_le hδ)) * (act e t (h.T_le ht))⁻¹ := by
      rw [← act_inv e (h.T_le ht), ← act_mul e (h.T_le ht) (h.B_le (h.D_le hδ)),
        ← act_mul e (Subgroup.mul_mem _ (h.T_le ht) (h.B_le (h.D_le hδ)))
          (Subgroup.inv_mem _ (h.T_le ht))]
    rw [← hδc, ← hμ x, e1]
    rfl

theorem semilinear_mul {t δ : G} (ht : t ∈ T) (hδ : δ ∈ D) {σ : F ≃+* F}
    (hσ : IsSemilinearWith (act e t (h.T_le ht)) σ) :
    IsSemilinearWith (act e (t * δ) (Subgroup.mul_mem _ (h.T_le ht) (h.D_le_normalizer hδ))) σ := by
  rw [act_mul e (h.T_le ht) (h.D_le_normalizer hδ)]
  have := hσ.mul (h.linear_D δ hδ)
  rwa [mul_one] at this

theorem exists_scalar_of_linear {x : G} (hx : x ∈ T ⊔ D)
    (hlin : IsSemilinearWith (act e x (h.sup_le_normalizer hx)) (1 : F ≃+* F)) :
    ∃ c : F, ∀ y, act e x (h.sup_le_normalizer hx) y = c • y := by
  obtain ⟨t, ht, δ, hδ, rfl⟩ := h.decomp x hx
  obtain ⟨c, hc⟩ := h.scalar δ (h.D_le hδ)
  have hmul := act_mul e (h.T_le ht) (h.D_le_normalizer hδ)
  have htlin : IsSemilinearWith (act e t (h.T_le ht)) (1 : F ≃+* F) := by
    have e1 : act e t (h.T_le ht) =
        act e (t * δ) (Subgroup.mul_mem _ (h.T_le ht) (h.D_le_normalizer hδ)) *
          (act e δ (h.D_le_normalizer hδ))⁻¹ := by
      rw [hmul, mul_inv_cancel_right]
    rw [e1]
    have := hlin.mul (isSemilinearWith_inv (h.linear_D δ hδ))
    rwa [inv_one, mul_one] at this
  have htC := h.linear t ht htlin
  refine ⟨c, fun y => ?_⟩
  have h1 : act e t (h.T_le ht) = 1 := (act_eq_one_iff e (h.T_le ht)).mpr htC
  show act e (t * δ) _ y = c • y
  rw [hmul, h1, one_mul]
  exact hc y

theorem eq_of_smul_eq (a b : F) (hab : ∀ v : Fin d → F, a • v = b • v) : a = b := by
  have := h.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin d → F)
  exact smul_left_injective F hv (hab v)

theorem eq_one_of_pow_smul [CharP F 2] {p : Equiv.Perm (Fin d → F)} {c : F}
    (hp : ∀ v, p v = c • v) {k : ℕ} (hk : p ^ 2 ^ k = 1) : c = 1 := by
  have hpow : ∀ m : ℕ, ∀ v, (p ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, hp, ih, smul_smul, pow_succ]
  have h1 : c ^ 2 ^ k = 1 := h.eq_of_smul_eq _ _ fun v => by
    rw [← hpow, hk, Equiv.Perm.one_apply, one_smul]
  exact eq_one_of_pow_two_pow_eq_one h1

theorem reduced [Finite F] [CharP F 2] : IsTwoReducedIn (T ⊔ D) W := by
  refine ⟨h.le_T.trans le_sup_left, h.sup_le_normalizer, isElemAbelian_of_equiv e,
    fun Dn hDn hnorm h2 => ?_⟩
  intro x hx
  have hxTD := hDn hx
  obtain ⟨t, ht, δ, hδ, rfl⟩ := h.decomp _ hxTD
  obtain ⟨σ, hσ⟩ := h.semilinear_T t ht
  have hσx := h.semilinear_mul ht hδ hσ
  set hxN := Subgroup.mul_mem _ (h.T_le ht) (h.D_le_normalizer hδ) with hxNdef
  have hσ1 : σ = 1 := by
    ext c
    show σ c = c
    by_cases hc : c = 0
    · rw [hc, map_zero]
    obtain ⟨δc, hδc, hδcc⟩ := h.surj c hc
    have hδcN := h.D_le_normalizer hδc
    have hy : t * δ * δc * (t * δ)⁻¹ * δc⁻¹ ∈ Dn := by
      have h1 : δc * (t * δ)⁻¹ * δc⁻¹ ∈ Dn :=
        (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.mem_sup_right hδc)) _).mp
          (Dn.inv_mem hx)
      have := Dn.mul_mem hx h1
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := h2 _ hy
    have hyN : t * δ * δc * (t * δ)⁻¹ * δc⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      h.sup_le_normalizer (hDn hy)
    have hact : ∀ v, act e _ hyN v = (σ c * c⁻¹) • v := by
      intro v
      have e1 : act e _ hyN = act e (t * δ) hxN * act e δc hδcN * (act e (t * δ) hxN)⁻¹ *
          (act e δc hδcN)⁻¹ := by
        rw [← act_inv e hxN, ← act_inv e hδcN, ← act_mul e hxN hδcN,
          ← act_mul e (Subgroup.mul_mem _ hxN hδcN) (Subgroup.inv_mem _ hxN),
          ← act_mul e (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hδcN) (Subgroup.inv_mem _ hxN))
            (Subgroup.inv_mem _ hδcN)]
      have hinv : (act e δc hδcN)⁻¹ v = c⁻¹ • v := by
        apply (act e δc hδcN).injective
        rw [perm_apply_inv, hδcc, smul_smul, mul_inv_cancel₀ hc, one_smul]
      rw [e1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hδcc,
        hσx, perm_apply_inv, smul_smul]
    have hpow : (act e _ hyN) ^ 2 ^ k = 1 := by
      rw [← act_pow e hyN]
      exact (act_eq_one_iff e _).mpr hk
    have h3 := h.eq_one_of_pow_smul hact hpow
    calc σ c = σ c * c⁻¹ * c := by rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
      _ = c := by rw [h3, one_mul]
  rw [hσ1] at hσx
  obtain ⟨c, hc⟩ := h.exists_scalar_of_linear hxTD hσx
  obtain ⟨k, hk⟩ := h2 _ hx
  have hpow : (act e (t * δ) (h.sup_le_normalizer hxTD)) ^ 2 ^ k = 1 := by
    rw [← act_pow e (h.sup_le_normalizer hxTD)]
    exact (act_eq_one_iff e _).mpr hk
  have hc1 := h.eq_one_of_pow_smul hc hpow
  refine (act_eq_one_iff e (h.sup_le_normalizer hxTD)).mp (Equiv.ext fun v => ?_)
  rw [hc, hc1, one_smul, Equiv.Perm.one_apply]

theorem inf_centralizer_le : (T ⊔ D) ⊓ Subgroup.centralizer (W : Set G) ≤ T := by
  intro x hx'
  have hx := Subgroup.mem_inf.mp hx'
  obtain ⟨t, ht, δ, hδ, rfl⟩ := h.decomp _ hx.1
  have hδN := h.D_le_normalizer hδ
  have h1 : act e (t * δ) (Subgroup.mul_mem _ (h.T_le ht) hδN) = 1 :=
    (act_eq_one_iff e _).mpr hx.2
  rw [act_mul e (h.T_le ht) hδN] at h1
  have h2 : act e t (h.T_le ht) = (act e δ hδN)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have htlin : IsSemilinearWith (act e t (h.T_le ht)) (1 : F ≃+* F) := by
    rw [h2]
    have := isSemilinearWith_inv (h.linear_D δ hδ)
    rwa [inv_one] at this
  have htC := h.linear t ht htlin
  have hact1 : act e t (h.T_le ht) = 1 := (act_eq_one_iff e _).mpr htC
  rw [hact1, one_mul] at h1
  have hδC : δ ∈ D ⊓ Subgroup.centralizer (W : Set G) :=
    Subgroup.mem_inf.mpr ⟨hδ, (act_eq_one_iff e hδN).mp h1⟩
  rw [h.faithful, Subgroup.mem_bot] at hδC
  rw [hδC, mul_one]
  exact ht

theorem isSylowTwoOf [Finite G] : IsSylowTwoOf T (T ⊔ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp h.isPGroup
  have hle : Nat.card ↥(T ⊔ D) ≤ Nat.card T * Nat.card D := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective (fun p : ↥T × ↥D => (⟨(p.1 : G) * p.2,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
        ↥(T ⊔ D))) ?_
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, δ, hδ, rfl⟩ := h.decomp x hx
    exact ⟨(⟨t, ht⟩, ⟨δ, hδ⟩), rfl⟩
  have hcop : Nat.Coprime (Nat.card T) (Nat.card D) := by
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr h.odd)
  have hdvd : Nat.card T * Nat.card D ∣ Nat.card ↥(T ⊔ D) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have heq : Nat.card ↥(T ⊔ D) = Nat.card T * Nat.card D :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  refine ⟨le_sup_left, h.isPGroup, ?_⟩
  have hidx := Subgroup.card_mul_index (T.subgroupOf (T ⊔ D))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, heq] at hidx
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have hidx' : (T.subgroupOf (T ⊔ D)).index = Nat.card D :=
    Nat.eq_of_mul_eq_mul_left hT0 hidx
  rw [hidx', Nat.two_dvd_ne_zero]
  exact Nat.odd_iff.mp h.odd

theorem pCoreOf_eq [Finite G] [Finite F] [CharP F 2] :
    pCoreOf 2 (T ⊔ D) = T ⊓ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heq : T ⊓ Subgroup.centralizer (W : Set G) =
      (T ⊔ D) ⊓ Subgroup.centralizer (W : Set G) :=
    le_antisymm (inf_le_inf_right _ le_sup_left) (le_inf h.inf_centralizer_le inf_le_right)
  apply le_antisymm
  · exact le_inf (F7.isSylowTwoOf_pCoreOf_le h.isSylowTwoOf)
      (A4.pCoreOf_le_centralizer_of_isTwoReducedIn h.reduced)
  · rw [heq]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Hyp5_0_1.le_normalizer_inf_centralizer h.sup_le_normalizer)
      (h.isPGroup.to_le h.inf_centralizer_le)

theorem isTDMod [Finite G] [Finite F] [CharP F 2] : IsTDMod T D W := ⟨h.reduced, h.pCoreOf_eq⟩

theorem exists_semilinear_of_mem [Finite F] {a : MulAut ↥W} (ha : a ∈ autOn (T ⊔ D) W) :
    ∃ σ : F ≃+* F, IsSemilinearWith (coordPerm e a) σ := by
  obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff.mp ha
  obtain ⟨t, ht, δ, hδ, hgtd⟩ := h.decomp g hgX
  obtain ⟨σ, hσ⟩ := h.semilinear_T t ht
  refine ⟨σ, ?_⟩
  have hg : g = ⟨t * δ, Subgroup.mul_mem _ (h.T_le ht) (h.D_le_normalizer hδ)⟩ :=
    Subtype.ext hgtd.symm
  rw [hg]
  exact h.semilinear_mul ht hδ hσ

theorem eq_one_of_linear [CharP F 2] {a : MulAut ↥W} (ha : a ∈ autOn (T ⊔ D) W) (ha2 : a ^ 2 = 1)
    (hlin : IsSemilinearWith (coordPerm e a) (1 : F ≃+* F)) : a = 1 := by
  obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff.mp ha
  obtain ⟨c, hc⟩ := h.exists_scalar_of_linear hgX hlin
  have hpow : act e (g : G) (h.sup_le_normalizer hgX) ^ 2 ^ 1 = 1 := by
    show coordPerm e (conjAct W g) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, ha2, map_one]
  have hc1 := h.eq_one_of_pow_smul hc hpow
  apply coordPerm_injective e
  rw [map_one]
  exact Equiv.ext fun v => by
    show act e (g : G) (h.sup_le_normalizer hgX) v = v
    rw [hc, hc1, one_smul]

theorem two_lt_qhatInt [Finite G] [Finite F] [CharP F 2] (hW : IsElemAbelian 2 W)
    (h16 : 16 < Nat.card W) :
    2 < qhatInt (T ⊔ D) W hW := by
  have := h.nontrivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  unfold qhatInt qhatOf
  rw [show (2 : WithTop ℚ) = ((2 : ℚ) : WithTop ℚ) by norm_cast, lt_kq_iff]
  intro A hA _
  obtain ⟨hAX, hA1, -, hA2⟩ := hA
  set A' := A.map (coordPerm e) with hA'
  have hsq : ∀ b ∈ A', b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA2 a ha, map_one]
  have hsemi : ∀ b ∈ A', ∃ σ : F ≃+* F, IsSemilinearWith b σ := by
    rintro _ ⟨a, ha, rfl⟩
    exact h.exists_semilinear_of_mem (hAX ha)
  have hinj : ∀ b ∈ A', IsSemilinearWith b (1 : F ≃+* F) → b = 1 := by
    rintro _ ⟨a, ha, rfl⟩ hlin
    rw [h.eq_one_of_linear (hAX ha) (hA2 a ha) hlin, map_one]
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha₀1' : a₀ ≠ 1 := fun h1 => ha₀1 (Subtype.ext h1)
  obtain ⟨σ₀, hσ₀⟩ := h.exists_semilinear_of_mem (hAX ha₀)
  have hσ₀1 : σ₀ ≠ 1 := by
    rintro rfl
    exact ha₀1' (h.eq_one_of_linear (hAX ha₀) (hA2 a₀ ha₀) hσ₀)
  have hsub := sub_of_inj A' hsq hsemi hinj (Subgroup.mem_map_of_mem _ ha₀) hσ₀ hσ₀1
  have hA01 : ∀ a ∈ A, a = 1 ∨ a = a₀ := by
    intro a ha
    rcases hsub _ (Subgroup.mem_map_of_mem _ ha) with h1 | h1
    · left
      exact coordPerm_injective e (h1.trans (map_one _).symm)
    · right
      exact coordPerm_injective e h1
  have hcardA : Nat.card A = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, A.one_mem⟩, ⟨a₀, ha₀⟩, fun h1 => ha₀1' (congrArg Subtype.val h1).symm, ?_⟩
    ext ⟨b, hb⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases hA01 b hb with rfl | rfl
    · left; rfl
    · right; rfl
  have hfix : ∀ w : ↥W, w ∈ fixV A ↔ a₀ w = w := by
    intro w
    constructor
    · intro hw
      exact hw a₀ ha₀
    · intro hw x hx
      rcases hA01 x hx with rfl | rfl
      · rfl
      · exact hw
  have hcfix : Nat.card ↥(fixV A) = Nat.card {x : Fin d → F // coordPerm e a₀ x = x} :=
    (Nat.card_congr (Equiv.subtypeEquivRight hfix)).trans (Nat.card_congr (fixedEquiv e a₀))
  have hσ₀2 : σ₀ * σ₀ = 1 := sq_eq_one_of_semilinear (hsq _ (Subgroup.mem_map_of_mem _ ha₀)) hσ₀
  have ha₀2 : ∀ x, coordPerm e a₀ (coordPerm e a₀ x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm (Fin d → F) => p x)
      (hsq _ (Subgroup.mem_map_of_mem _ ha₀))
    simpa using this
  have hsqcard := card_eq_sq_fixed (coordPerm e a₀) (coordPerm_add e a₀) ha₀2
    (fun w => neg_eq_self_of_char_two_module F w)
    (fun w hw => semilinear_involution_fixed_image hσ₀ (exists_trace_eq_one σ₀ hσ₀1 hσ₀2) w hw)
  have hWcard : Nat.card ↥W = Nat.card (Fin d → F) :=
    Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd)
  rw [← hcfix, ← hWcard] at hsqcard
  set c := Nat.card ↥(fixV A) with hc
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hW.2 w w.2)⟩
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hW2
  obtain ⟨j, -, hj⟩ : ∃ j ≤ N, c = 2 ^ j :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (hN ▸ Subgroup.card_subgroup_dvd_card (fixV A))
  have hidx : (fixV A).index = c := by
    have h1 := Subgroup.card_mul_index (fixV A)
    rw [hsqcard, ← hc, pow_two] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hj3 : 3 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : c ≤ 4 := by
      rw [hj]
      calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    have : c ^ 2 ≤ 16 := by nlinarith
    omega
  have hrk : rk ↥A = 1 := by
    unfold rk
    rw [hcardA]
    exact padicValNat_self
  have hrkIdx : rkIdx (fixV A) = j := by
    unfold rkIdx
    rw [hidx, hj, padicValNat.prime_pow]
  unfold rAV
  rw [hrk, hrkIdx]
  have : (3 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj3
  rw [Nat.cast_one, div_one]
  linarith

end Hyp

end Main

end Semi516

end CFSG.Quasithin.H13
