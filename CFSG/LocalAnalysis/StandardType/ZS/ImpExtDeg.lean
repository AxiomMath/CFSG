module

import all CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import all CFSG.LocalAnalysis.StandardType.ZS.MonomialDMax
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtH3
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure ImpExtStd (G H : Subgroup (U ≃ₗ[ZMod p] U)) (d : ℕ)
    (e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace H))
    (j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)) (ζ : (ZMod p)ˣ) : Prop
    extends ImpExtSetting G H d where
  ne : j₀ ≠ j₁
  mono : movedGroup H = gmmn p e j₀ j₁ ζ ∨ movedGroup H = g2mmn p e j₀ j₁ ζ

@[expose] noncomputable def basisStab (H : Subgroup (U ≃ₗ[ZMod p] U)) {l : ℕ}
    (e : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)) (i : Fin l) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  H ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U)
    ((e i : HardMathSupport.Kantor79.commutatorSpace H) : U)

@[expose] def ImpExtRowM (H : Subgroup (U ≃ₗ[ZMod p] U)) {l : ℕ}
    (e : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H))
    (j₀ j₁ : Fin l) (ζ : (ZMod p)ˣ) : Prop :=
  l = 3 ∧ (movedGroup H = gmmn p e j₀ j₁ ζ → orderOf ζ = 4) ∧
    (movedGroup H = g2mmn p e j₀ j₁ ζ → orderOf ζ ∣ 2 ∨ orderOf ζ = 4)

structure ImpExtInputs (G H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  splitOfIrred : SplitOfIrred p G (Module.finrank (ZMod p) U - 1)
  lemmaOneSeven : LemmaOneSeven p G H
  centreOrder : CentreOrderBound p G (Module.finrank (ZMod p) U - 1)
  degenerate : DegenerateInput p G (Module.finrank (ZMod p) U - 2)
  primCorank : TFPrimCorank p (Module.finrank (ZMod p) U - 1)
  degenerateExt : TFDegenerateExt p (Module.finrank (ZMod p) U - 1)
  negOfPrim : TFNegOfPrimThree p
  smallThree : TFSmallThree p

private theorem fixReflSubgroup_eq_map_subtype {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (v : HardMathSupport.Kantor79.commutatorSpace X) :
    fixReflSubgroup p X (v : U) = (Subgroup.closure {t : X |
      IsRefl p (t : U ≃ₗ[ZMod p] U) ∧ (t : U ≃ₗ[ZMod p] U) (v : U) = (v : U)}).map
        X.subtype := by
  rw [fixReflSubgroup, MonoidHom.map_closure]
  congr 1
  ext t
  refine ⟨?_, ?_⟩
  · rintro ⟨htX, htr, htv⟩
    exact ⟨⟨t, htX⟩, ⟨htr, htv⟩, rfl⟩
  · rintro ⟨x, hxS, hxt⟩
    rw [← hxt]
    exact ⟨x.2, hxS.1, hxS.2⟩

private theorem map_closure_eq_fixReflSubgroup_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hs : SplitSupport X l) (v : HardMathSupport.Kantor79.commutatorSpace X) :
    (Subgroup.closure {t : X | IsRefl p (t : U ≃ₗ[ZMod p] U) ∧
      (t : U ≃ₗ[ZMod p] U) (v : U) = (v : U)}).map
        (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
          (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)) =
      fixReflSubgroup p (movedGroup X) v := by
  rw [fixReflSubgroup, MonoidHom.map_closure]
  congr 1
  ext t
  constructor
  · rintro ⟨x, ⟨htr, htv⟩, rfl⟩
    refine ⟨⟨x, rfl⟩, isRefl_restrictHom_of_isRefl hs htr, ?_⟩
    apply Subtype.ext
    rw [restrictHom_apply]
    exact htv
  · rintro ⟨ht, htr, htv⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ht
    refine ⟨x, ⟨isRefl_of_isRefl_restrictHom hs (hx.symm ▸ htr), ?_⟩, hx⟩
    have hw := congrArg (fun w : HardMathSupport.Kantor79.commutatorSpace X => (w : U))
      (hx.symm ▸ htv)
    rwa [restrictHom_apply] at hw

private theorem stabilizer_le_fixReflSubgroup_of_movedGroup
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport X l)
    (v : HardMathSupport.Kantor79.commutatorSpace X)
    (h : movedGroup X ⊓ MulAction.stabilizer
        (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X) v ≤
      fixReflSubgroup p (movedGroup X) v) :
    X ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (v : U) ≤
      fixReflSubgroup p X (v : U) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  let S : Set X := {t | IsRefl p (t : U ≃ₗ[ZMod p] U) ∧
    (t : U ≃ₗ[ZMod p] U) (v : U) = (v : U)}
  have hSa : fixReflSubgroup p X (v : U) = (Subgroup.closure S).map X.subtype :=
    fixReflSubgroup_eq_map_subtype v
  have hSb : fixReflSubgroup p (movedGroup X) v = (Subgroup.closure S).map φ :=
    (map_closure_eq_fixReflSubgroup_movedGroup hs v).symm
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgX, hgfix⟩ := hg
  have hgfix' : g (v : U) = (v : U) := by
    simpa [MulAction.mem_stabilizer_iff] using hgfix
  have hmem : φ ⟨g, hgX⟩ ∈ movedGroup X ⊓
      MulAction.stabilizer (V ≃ₗ[ZMod p] V) v := by
    rw [Subgroup.mem_inf]
    refine ⟨⟨⟨g, hgX⟩, rfl⟩, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g ((v : V) : U) = ((v : V) : U)
    exact hgfix'
  have hstab := h hmem
  rw [hSb] at hstab
  obtain ⟨x, hxS, hxφ⟩ := Subgroup.mem_map.mp hstab
  have hxeq : x = ⟨g, hgX⟩ := hinj hxφ
  subst hxeq
  rw [hSa]
  exact ⟨⟨g, hgX⟩, hxS, rfl⟩

private theorem g2mmn_eq_gmmn_of_two {n : ℕ} (hp : p = 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (_hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    g2mmn p f i₀ i₁ ζ = gmmn p f i₀ i₁ ζ := by
  have hsign : (fun i => if i = i₀ then (-1 : (ZMod p)ˣ) else 1) = 1 := by
    funext i
    by_cases hi' : i = i₀
    · rw [if_pos hi']
      exact Units.ext (by
        rw [Units.val_neg, Units.val_one]
        exact (ZMod.neg_one_eq_one_iff (n := p)).mpr (Or.inr hp))
    · rw [if_neg hi']; rfl
  apply le_antisymm
  · rw [g2mmn, Subgroup.closure_le]
    rintro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl hx)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [hsign, diagMap_one]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  · rw [gmmn, Subgroup.closure_le]
    rintro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl hx)
    · exact Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ hx))

section Monomial

variable {l : ℕ}

private theorem zs4d_eq_of_smul_eq (f : Module.Basis (Fin l) (ZMod p) U) {a b : Fin l}
    {c : ZMod p} (hc : c ≠ 0) (h : c • f a = f b) : a = b := by
  by_contra hab
  have h1 := congrArg (fun v => f.repr v a) h
  simp [Ne.symm hab] at h1
  exact hc h1

private theorem zs4d_eq_one_of_smul_eq (f : Module.Basis (Fin l) (ZMod p) U) {a : Fin l}
    {c : ZMod p} (h : c • f a = f a) : c = 1 := by
  have h1 := congrArg (fun v => f.repr v a) h
  simpa using h1

private theorem zs4d_neg_one_ne_one (hp : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  rcases (ZMod.neg_one_eq_one_iff (n := p)).mp h with h1 | h1
  · exact (Fact.out : p.Prime).one_lt.ne' h1
  · exact hp h1

private theorem zs4d_exists_ne_ne (hl : 3 ≤ l) (a b : Fin l) : ∃ k : Fin l, k ≠ a ∧ k ≠ b := by
  by_contra h
  push Not at h
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
  omega

private theorem zs4d_exists_enum {m : ℕ} (hm : l = m + 1) (i : Fin l) :
    ∃ s : Fin m → Fin l, Function.Injective s ∧ Set.range s = {j | j ≠ i} ∧
      ∀ τ : Equiv.Perm (Fin m), ∃ σ : Equiv.Perm (Fin l), σ i = i ∧ ∀ k, s (τ k) = σ (s k) := by
  subst hm
  refine ⟨i.succAbove, Fin.succAbove_right_injective, ?_, fun τ => ?_⟩
  · ext j
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact Fin.succAbove_ne i k
    · exact fun hj => Fin.exists_succAbove_eq hj
  · refine ⟨τ.extendDomain (finSuccAboveEquiv i),
      Equiv.Perm.extendDomain_apply_not_subtype _ _ (fun h => h rfl), fun k => ?_⟩
    have h := Equiv.Perm.extendDomain_apply_image τ (finSuccAboveEquiv i) k
    simp only [finSuccAboveEquiv_apply] at h
    exact h.symm

private theorem zs4d_twist_apply (f : Module.Basis (Fin l) (ZMod p) U) (a b k : Fin l)
    (c : (ZMod p)ˣ) :
    (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) (f k) =
      (pairUnit p a b c (Equiv.swap a b k) : ZMod p) • f (Equiv.swap a b k) := by
  rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]

private theorem zs4d_twist_apply_of_ne (f : Module.Basis (Fin l) (ZMod p) U) {a b k : Fin l}
    (hka : k ≠ a) (hkb : k ≠ b) (c : (ZMod p)ˣ) :
    (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) (f k) = f k := by
  rw [zs4d_twist_apply, Equiv.swap_apply_of_ne_of_ne hka hkb]
  simp [pairUnit, hka, hkb]

private theorem zs4d_sign_apply_of_ne (f : Module.Basis (Fin l) (ZMod p) U) {j k : Fin l}
    (hjk : j ≠ k) :
    diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) (f j) = f j := by
  rw [diagMap_apply_basis, if_neg hjk, Units.val_one, one_smul]

private theorem zs4d_ne_of_swap_eq {a b k : Fin l} (hab : a ≠ b) (h : Equiv.swap a b k = k) :
    k ≠ a ∧ k ≠ b := by
  constructor
  · rintro rfl
    rw [Equiv.swap_apply_left] at h
    exact hab h.symm
  · rintro rfl
    rw [Equiv.swap_apply_right] at h
    exact hab h

private theorem zs4d_twist_fix_ne (f : Module.Basis (Fin l) (ZMod p) U) {a b i : Fin l}
    (hab : a ≠ b) {c : (ZMod p)ˣ}
    (h : (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) (f i) = f i) :
    a ≠ i ∧ b ≠ i := by
  rw [zs4d_twist_apply] at h
  have h1 := zs4d_eq_of_smul_eq f (Units.ne_zero _) h
  exact ⟨fun hai => hab (by subst hai; simpa using h1.symm),
    fun hbi => hab (by subst hbi; simpa using h1)⟩

private theorem zs4d_sign_fix_ne (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U) {k i : Fin l}
    (h : diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) (f i) = f i) : k ≠ i := by
  rintro rfl
  rw [diagMap_apply_basis, if_pos rfl] at h
  have h1 : ((-1 : (ZMod p)ˣ) : ZMod p) = 1 := zs4d_eq_one_of_smul_eq f h
  rw [Units.val_neg, Units.val_one] at h1
  exact zs4d_neg_one_ne_one hp h1

private theorem zs4d_twist_mem_gmmn (f : Module.Basis (Fin l) (ZMod p) U) {j₀ j₁ : Fin l}
    (hi : j₀ ≠ j₁) {ζ c : (ZMod p)ˣ} {a b : Fin l} (hab : a ≠ b) (hc : c ∈ Subgroup.zpowers ζ) :
    diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b) ∈ gmmn p f j₀ j₁ ζ :=
  Subgroup.mul_mem _ (diagMap_pairUnit_mem_gmmn f hi hab hc)
    (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

private theorem zs4d_twist_mem_g2mmn (f : Module.Basis (Fin l) (ZMod p) U) {j₀ j₁ : Fin l}
    (hi : j₀ ≠ j₁) {ζ c : (ZMod p)ˣ} {a b : Fin l} (hab : a ≠ b)
    (hc : c ∈ Subgroup.closure {ζ, -1}) :
    diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b) ∈ g2mmn p f j₀ j₁ ζ :=
  Subgroup.mul_mem _ (diagMap_pairUnit_mem_g2mmn f hi hab hc)
    (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

private theorem zs4d_monomial (f : Module.Basis (Fin l) (ZMod p) U) (d : Fin l → (ZMod p)ˣ)
    (σ : Equiv.Perm (Fin l)) :
    ∃ (σ' : Equiv.Perm (Fin l)) (c : Fin l → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, (diagMap p f d * permMap p f σ) (f i) = c i • f (σ' i) :=
  ⟨σ, fun i => (d (σ i) : ZMod p), fun _ => Units.ne_zero _, fun i => by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]⟩

private theorem zs4d_shape_gmmn (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ gmmn p f j₀ j₁ ζ) (hxr : IsRefl p x) :
    ∃ a b, a ≠ b ∧ ∃ c ∈ Subgroup.zpowers ζ,
      x = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b) := by
  obtain ⟨d, σ, hd, -, rfl⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hx
  rcases eq_sign_or_eq_twist_of_isRefl hp f hxr (zs4d_monomial f d σ) with
    ⟨k, hk⟩ | ⟨a, b, hab, c, hc⟩
  · exact (zsmd_sign_not_mem_gmmn hp f hi k (hk ▸ hx)).elim
  · refine ⟨a, b, hab, c, ?_, hc⟩
    have h1 : c⁻¹ ∈ Subgroup.zpowers ζ := (zsmd_extract_twist f hab hc).2 ▸ hd (σ a)
    simpa using Subgroup.inv_mem _ h1

private theorem zs4d_shape_g2mmn (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ g2mmn p f j₀ j₁ ζ) (hxr : IsRefl p x) :
    (∃ k, x = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ Subgroup.closure {ζ, -1},
        x = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b) := by
  obtain ⟨d, σ, hd, -, rfl⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hx
  rcases eq_sign_or_eq_twist_of_isRefl hp f hxr (zs4d_monomial f d σ) with
    hk | ⟨a, b, hab, c, hc⟩
  · exact Or.inl hk
  · refine Or.inr ⟨a, b, hab, c, ?_, hc⟩
    have h1 : c⁻¹ ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) :=
      (zsmd_extract_twist f hab hc).2 ▸ hd (σ a)
    simpa using Subgroup.inv_mem _ h1

private theorem zs4d_shape (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U) {j₀ j₁ : Fin l}
    (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∨ A = g2mmn p f j₀ j₁ ζ) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ A)
    (hxr : IsRefl p x) :
    (∃ k, x = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ Subgroup.closure {ζ, -1},
        x = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b) := by
  rcases hA with rfl | rfl
  · obtain ⟨a, b, hab, c, hc, rfl⟩ := zs4d_shape_gmmn hp f hi hx hxr
    exact Or.inr ⟨a, b, hab, c,
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hc, rfl⟩
  · exact zs4d_shape_g2mmn hp f hi hx hxr

private theorem zs4d_orderOf_mul_comm {G : Type*} [Group G] (x y : G) :
    orderOf (x * y) = orderOf (y * x) :=
  SemiconjBy.orderOf_eq y (by simp [SemiconjBy, mul_assoc])

private theorem zs4d_pow_mul_comm {G : Type*} [Group G] {x y : G} {m : ℕ}
    (h : (y * x) ^ m = 1) : (x * y) ^ m = 1 := by
  rw [show x * y = x * (y * x) * x⁻¹ by group, conj_pow, h, mul_one, mul_inv_cancel]

private theorem zs4d_pairUnit_mem {C : Subgroup (ZMod p)ˣ} {c : (ZMod p)ˣ} (hc : c ∈ C)
    (a b k : Fin l) : pairUnit p a b c k ∈ C := by
  unfold pairUnit
  split_ifs
  · exact hc
  · exact C.inv_mem hc
  · exact C.one_mem

private theorem zs4d_tw_tw (f : Module.Basis (Fin l) (ZMod p) U) {a b a' b' : Fin l}
    (hab : a ≠ b) (hab' : a' ≠ b') (c c' : (ZMod p)ˣ) :
    orderOf ((diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) *
      (diagMap p f (pairUnit p a' b' c') * permMap p f (Equiv.swap a' b'))) ≤ 3 ∨
    (Equiv.swap a b = Equiv.swap a' b' ∧
      (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) *
        (diagMap p f (pairUnit p a' b' c') * permMap p f (Equiv.swap a' b')) =
      diagMap p f (pairUnit p a b c * (pairUnit p a' b' c' ∘ (Equiv.swap a b).symm))) := by
  by_cases hτ : Equiv.swap a b = Equiv.swap a' b'
  · refine Or.inr ⟨hτ, ?_⟩
    rw [zsmd_mul_diagMap_permMap, ← hτ, Equiv.swap_mul_self, zsmd_permMap_one, mul_one]
  refine Or.inl ?_
  by_cases hcase : a = a' ∨ a = b' ∨ b = a' ∨ b = b'
  · rcases hcase with h | h | h | h
    · subst a'
      have hbb' : b ≠ b' := by rintro rfl; exact hτ rfl
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_canonical_three_pow_three f hab hab' hbb' c c')
    · subst b'
      have hba' : b ≠ a' := by intro h; exact hτ (by rw [h, Equiv.swap_comm])
      rw [zsmd_twist_symm f hab' c']
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_canonical_three_pow_three f hab (Ne.symm hab') hba' c c'⁻¹)
    · subst a'
      have hab'' : a ≠ b' := by intro h; exact hτ (by rw [h, Equiv.swap_comm])
      rw [zsmd_twist_symm f hab c]
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_canonical_three_pow_three f (Ne.symm hab) hab' hab'' c⁻¹ c')
    · subst b'
      have haa' : a ≠ a' := by rintro rfl; exact hτ rfl
      rw [zsmd_twist_symm f hab c, zsmd_twist_symm f hab' c']
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_canonical_three_pow_three f (Ne.symm hab) (Ne.symm hab') haa' c⁻¹ c'⁻¹)
  · push Not at hcase
    obtain ⟨h1, h2, h3, h4⟩ := hcase
    exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
      (zsmd_twist_disjoint_pow_two f a b a' b' hab hab' h1 h2 h3 h4 c c')) (by norm_num)

private theorem zs4d_sg_tw (f : Module.Basis (Fin l) (ZMod p) U) (k : Fin l) {a b : Fin l}
    (hab : a ≠ b) (c : (ZMod p)ˣ) :
    (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b))) ^ 2 = 1 ∨
    ((k = a ∨ k = b) ∧ (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b))) ^ 4 = 1) := by
  by_cases hka : k = a
  · subst hka
    exact Or.inr ⟨Or.inl rfl, zsmd_sign_twist_pow_four_of_mem f hab c⟩
  by_cases hkb : k = b
  · subst hkb
    refine Or.inr ⟨Or.inr rfl, ?_⟩
    rw [zsmd_twist_symm f hab c]
    exact zsmd_sign_twist_pow_four_of_mem f (Ne.symm hab) c⁻¹
  exact Or.inl (zsmd_sign_twist_pow_two_of_notmem f hab hka hkb c)

private theorem zs4d_pair_sign (f : Module.Basis (Fin l) (ZMod p) U) {C : Subgroup (ZMod p)ˣ}
    (k : Fin l) {y : U ≃ₗ[ZMod p] U}
    (hy : (∃ k, y = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ C,
        y = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) :
    orderOf (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) * y) ≤ 3 ∨
      ∃ a b, a ≠ b ∧ (∀ m, m ≠ a → m ≠ b →
        diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) (f m) = f m ∧
          y (f m) = f m) ∧
        (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) * y) ^ 4 = 1 := by
  rcases hy with ⟨k', rfl⟩ | ⟨a, b, hab, c, -, rfl⟩
  · exact Or.inl (le_trans (orderOf_le_of_pow_eq_one (by norm_num)
      (zsmd_sign_sign_pow_two f k k')) (by norm_num))
  rcases zs4d_sg_tw f k hab c with h | ⟨hk, h⟩
  · exact Or.inl (le_trans (orderOf_le_of_pow_eq_one (by norm_num) h) (by norm_num))
  refine Or.inr ⟨a, b, hab, fun m hma hmb => ⟨zs4d_sign_apply_of_ne f ?_,
    zs4d_twist_apply_of_ne f hma hmb c⟩, h⟩
  rcases hk with rfl | rfl
  · exact hma
  · exact hmb

private theorem zs4d_pair (f : Module.Basis (Fin l) (ZMod p) U) {C : Subgroup (ZMod p)ˣ}
    {x y : U ≃ₗ[ZMod p] U}
    (hx : (∃ k, x = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ C,
        x = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b))
    (hy : (∃ k, y = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ C,
        y = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b)) :
    orderOf (x * y) ≤ 3 ∨ ∃ a b, a ≠ b ∧
      (∀ k, k ≠ a → k ≠ b → x (f k) = f k ∧ y (f k) = f k) ∧
      ((∃ k, x = diagMap p f (fun j => if j = k then -1 else 1) ∨
          y = diagMap p f (fun j => if j = k then -1 else 1)) ∧ (x * y) ^ 4 = 1 ∨
        ∃ δ : Fin l → (ZMod p)ˣ, (∀ k, δ k ∈ C) ∧ x * y = diagMap p f δ) := by
  rcases hx with ⟨k, rfl⟩ | ⟨a, b, hab, c, hc, rfl⟩
  · rcases zs4d_pair_sign f k hy with h | ⟨a, b, hab, hfix, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, b, hab, hfix, Or.inl ⟨⟨k, Or.inl rfl⟩, h4⟩⟩
  rcases hy with ⟨k, rfl⟩ | ⟨a', b', hab', c', hc', rfl⟩
  · rcases zs4d_pair_sign f k (Or.inr ⟨a, b, hab, c, hc, rfl⟩) with h | ⟨a₂, b₂, hab₂, hfix, h4⟩
    · exact Or.inl (by rw [zs4d_orderOf_mul_comm]; exact h)
    · exact Or.inr ⟨a₂, b₂, hab₂, fun m hm1 hm2 => (hfix m hm1 hm2).symm,
        Or.inl ⟨⟨k, Or.inr rfl⟩, zs4d_pow_mul_comm h4⟩⟩
  rcases zs4d_tw_tw f hab hab' c c' with h | ⟨hτ, hxy⟩
  · exact Or.inl h
  refine Or.inr ⟨a, b, hab, fun k hka hkb => ⟨zs4d_twist_apply_of_ne f hka hkb c, ?_⟩,
    Or.inr ⟨_, fun k => C.mul_mem (zs4d_pairUnit_mem hc a b k)
      (zs4d_pairUnit_mem hc' a' b' _), hxy⟩⟩
  have hk' : Equiv.swap a' b' k = k := by
    rw [← hτ]
    exact Equiv.swap_apply_of_ne_of_ne hka hkb
  obtain ⟨h1, h2⟩ := zs4d_ne_of_swap_eq hab' hk'
  exact zs4d_twist_apply_of_ne f h1 h2 c'

private theorem zs4d_exists_diag_perm (f : Module.Basis (Fin l) (ZMod p) U) {j₀ j₁ : Fin l}
    (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∨ A = g2mmn p f j₀ j₁ ζ) {b : U ≃ₗ[ZMod p] U} (hb : b ∈ A) :
    ∃ (d : Fin l → (ZMod p)ˣ) (σ : Equiv.Perm (Fin l)), b = diagMap p f d * permMap p f σ := by
  rcases hA with rfl | rfl
  · obtain ⟨d, σ, -, -, h⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hb
    exact ⟨d, σ, h⟩
  · obtain ⟨d, σ, -, -, h⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hb
    exact ⟨d, σ, h⟩

private theorem zs4d_sub_mem_of_basis {ι : Type*} (f : Module.Basis ι (ZMod p) U)
    (b : U ≃ₗ[ZMod p] U) {W : Submodule (ZMod p) U} (h : ∀ j, b (f j) - f j ∈ W) (v : U) :
    b v - v ∈ W := by
  have hle : LinearMap.range ((b : U →ₗ[ZMod p] U) - LinearMap.id) ≤ W := by
    rw [LinearMap.range_eq_map, ← f.span_eq, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact h j
  exact hle ⟨v, rfl⟩

private theorem zs4d_commutatorSpace_stab_le (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∨ A = g2mmn p f j₀ j₁ ζ) (i : Fin l) :
    HardMathSupport.Kantor79.commutatorSpace
        (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) ≤
      Submodule.span (ZMod p) (f '' {j | j ≠ i}) := by
  rw [commutatorSpace_le_iff]
  intro b hb
  obtain ⟨hbA, hbi⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨d, σ, rfl⟩ := zs4d_exists_diag_perm f hi hA hbA
  have hbi' : (diagMap p f d * permMap p f σ) (f i) = f i := hbi
  have happ : ∀ j, (diagMap p f d * permMap p f σ) (f j) = (d (σ j) : ZMod p) • f (σ j) :=
    fun j => by rw [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  have hσ : σ i = i := zs4d_eq_of_smul_eq f (Units.ne_zero _) ((happ i).symm.trans hbi')
  refine zs4d_sub_mem_of_basis f _ fun j => ?_
  by_cases hj : j = i
  · rw [hj, hbi', sub_self]
    exact Submodule.zero_mem _
  · have hσj : σ j ≠ i := fun h => hj (σ.injective (h.trans hσ.symm))
    rw [happ j]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ j, hσj, rfl⟩))
      (Submodule.subset_span ⟨j, hj, rfl⟩)

private theorem zs4d_sep (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U) {j₀ j₁ : Fin l}
    (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ A = g2mmn p f j₀ j₁ ζ) {i a b : Fin l}
    (hab : a ≠ b) (hai : a ≠ i) (hbi : b ≠ i) :
    ∃ u ∈ A, u (f i) = f i ∧ (∀ k, ∃ c : ZMod p, u (f k) = c • f k) ∧
      ∃ c d : ZMod p, c ≠ 1 ∧ c ≠ d ∧ u (f a) = c • f a ∧ u (f b) = d • f b := by
  rcases hA with ⟨rfl, hζ⟩ | rfl
  · refine ⟨diagMap p f (pairUnit p a b ζ),
      diagMap_pairUnit_mem_gmmn f hi hab (Subgroup.mem_zpowers ζ), ?_,
      fun k => ⟨_, diagMap_apply_basis f _ k⟩, ζ, ((ζ⁻¹ : (ZMod p)ˣ) : ZMod p), ?_, ?_, ?_, ?_⟩
    · rw [diagMap_apply_basis]
      simp [pairUnit, Ne.symm hai, Ne.symm hbi]
    · intro h
      exact hζ (by rw [Units.val_eq_one.mp h, one_mul])
    · intro h
      exact hζ (mul_eq_one_iff_eq_inv.mpr (Units.ext h))
    · rw [diagMap_apply_basis]
      simp [pairUnit]
    · rw [diagMap_apply_basis]
      show ((if b = a then ζ else if b = b then ζ⁻¹ else 1 : (ZMod p)ˣ) : ZMod p) • f b = _
      rw [if_neg (Ne.symm hab), if_pos rfl]
  · refine ⟨diagMap p f (fun j => if j = a then (-1 : (ZMod p)ˣ) else 1),
      diagMap_signMap_mem_g2mmn f hi ζ a, zs4d_sign_apply_of_ne f (Ne.symm hai),
      fun k => ⟨_, diagMap_apply_basis f _ k⟩, ((-1 : (ZMod p)ˣ) : ZMod p), 1, ?_, ?_, ?_, ?_⟩
    · rw [Units.val_neg, Units.val_one]
      exact zs4d_neg_one_ne_one hp
    · rw [Units.val_neg, Units.val_one]
      exact zs4d_neg_one_ne_one hp
    · rw [diagMap_apply_basis, if_pos rfl]
    · rw [one_smul]
      exact zs4d_sign_apply_of_ne f (Ne.symm hab)

private theorem zs4d_commutatorSpace_stab (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ A = g2mmn p f j₀ j₁ ζ) (hl : 3 ≤ l) (i : Fin l) :
    HardMathSupport.Kantor79.commutatorSpace
        (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) =
      Submodule.span (ZMod p) (f '' {j | j ≠ i}) := by
  refine le_antisymm (zs4d_commutatorSpace_stab_le f hi (hA.imp And.left id) i) ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨m, hmi, hmj⟩ := zs4d_exists_ne_ne hl i j
  obtain ⟨u, huA, hui, -, c, -, hc1, -, huj, -⟩ := zs4d_sep hp f hi hA (Ne.symm hmj) hj hmi
  have hmem : u (f j) - f j ∈ HardMathSupport.Kantor79.commutatorSpace
      (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) :=
    Submodule.subset_span ⟨u, Subgroup.mem_inf.mpr ⟨huA, hui⟩, f j, rfl⟩
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hfj : f j = (c - 1)⁻¹ • (u (f j) - f j) := by
    rw [huj, show c • f j - f j = (c - 1) • f j by rw [sub_smul, one_smul], smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, hfj]
  exact Submodule.smul_mem _ _ hmem

private theorem zs4d_irred_stab (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ A = g2mmn p f j₀ j₁ ζ) (i : Fin l) :
    IrredOnSection (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) ⊥
      (Submodule.span (ZMod p) (f '' {j | j ≠ i})) := by
  apply irredOnSection_span_of_separating f.linearIndependent
  · intro a ha b hb hab
    obtain ⟨u, huA, hui, hdiag, c, d, -, hcd, hua, hub⟩ := zs4d_sep hp f hi hA hab ha hb
    exact ⟨u, Subgroup.mem_inf.mpr ⟨huA, hui⟩, fun k _ => hdiag k, c, d, hcd, hua, hub⟩
  · intro a ha b hb
    refine ⟨permMap p f (Equiv.swap a b), Subgroup.mem_inf.mpr ⟨?_, ?_⟩, 1, one_ne_zero, ?_⟩
    · rcases hA with ⟨rfl, -⟩ | rfl <;> exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    · show permMap p f (Equiv.swap a b) (f i) = f i
      rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
    · rw [permMap_apply_basis, Equiv.swap_apply_left, one_smul]

private theorem zs4d_stab_eq_fixRefl (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∨ A = g2mmn p f j₀ j₁ ζ) (i : Fin l) :
    A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i) = fixReflSubgroup p A (f i) := by
  refine le_antisymm ?_ fun g hg =>
    Subgroup.mem_inf.mpr ⟨fixReflSubgroup_le A _ hg, fixReflSubgroup_apply_eq hg⟩
  rcases hA with rfl | rfl
  · exact gmmn_inf_stabilizer_le_fixReflSubgroup f hi ζ i
  · exact g2mmn_inf_stabilizer_le_fixReflSubgroup hp f hi ζ i

private theorem zs4d_splitSupport_stab (hp : p ≠ 2) (f : Module.Basis (Fin l) (ZMod p) U)
    {j₀ j₁ : Fin l} (hi : j₀ ≠ j₁) {ζ : (ZMod p)ˣ} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : A = gmmn p f j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ A = g2mmn p f j₀ j₁ ζ) (hl : 3 ≤ l) (i : Fin l) :
    SplitSupport (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) (l - 1) := by
  have hV := zs4d_commutatorSpace_stab hp f hi hA hl i
  have hirr : IrredOnSection (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i))) := by
    rw [hV]
    exact zs4d_irred_stab hp f hi hA i
  have hgen : ReflGen p (A ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f i)) := by
    rw [zs4d_stab_eq_fixRefl hp f hi (hA.imp And.left id) i]
    exact reflGen_fixReflSubgroup A _
  obtain ⟨s, hsinj, hrange, -⟩ := zs4d_exists_enum (m := l - 1) (by omega) i
  refine ⟨⟨disjoint_iff.mpr (commutatorSpace_inf_centralizerSpace_eq_bot hp hgen hirr), ?_⟩, ?_,
    hirr⟩
  · rw [codisjoint_iff, eq_top_iff, ← f.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · refine Submodule.mem_sup_right (mem_centralizerSpace.mpr fun h hh => ?_)
      rw [hj]
      exact (Subgroup.mem_inf.mp hh).2
    · rw [hV]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [hV, show f '' {j | j ≠ i} = Set.range (f ∘ s) by rw [Set.range_comp, hrange],
      finrank_span_eq_card (f.linearIndependent.comp s hsinj), Fintype.card_fin]

private theorem zs4d_pairUnit_left (a b : Fin l) (c : (ZMod p)ˣ) : pairUnit p a b c a = c := by
  unfold pairUnit
  rw [if_pos rfl]

private theorem zs4d_pairUnit_right {a b : Fin l} (hab : a ≠ b) (c : (ZMod p)ˣ) :
    pairUnit p a b c b = c⁻¹ := by
  unfold pairUnit
  rw [if_neg (Ne.symm hab), if_pos rfl]

private theorem zs4d_exists_orderOf_five (f : Module.Basis (Fin l) (ZMod p) U)
    {δ : Fin l → (ZMod p)ˣ} (h : orderOf (diagMap p f δ) = 5) : ∃ k, orderOf (δ k) = 5 := by
  have h5 : diagMap p f (δ ^ 5) = 1 := by rw [← zsmd_diagMap_pow, ← h, pow_orderOf_eq_one]
  by_contra hne
  push Not at hne
  have h1 : ∀ k, δ k = 1 := fun k => by
    have h2 : diagMap p f (δ ^ 5) (f k) = f k := by rw [h5]; rfl
    rw [diagMap_apply_basis] at h2
    have h3 : δ k ^ 5 = 1 := Units.ext (by simpa using zs4d_eq_one_of_smul_eq f h2)
    rcases (Nat.dvd_prime (by norm_num)).mp (orderOf_dvd_of_pow_eq_one h3) with h4 | h4
    · exact orderOf_eq_one_iff.mp h4
    · exact absurd h4 (hne k)
  rw [show δ = 1 from funext h1, diagMap_one, orderOf_one] at h
  omega

private theorem zs4d_exists_lam (f : Module.Basis (Fin l) (ZMod p) U) {C : Subgroup (ZMod p)ˣ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ x ∈ A, IsRefl p x → (∃ k, x = diagMap p f (fun j => if j = k then -1 else 1)) ∨
      ∃ a b, a ≠ b ∧ ∃ c ∈ C, x = diagMap p f (pairUnit p a b c) * permMap p f (Equiv.swap a b))
    (hd : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 5) :
    ∃ lam ∈ C, orderOf lam = 5 := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
  rcases zs4d_pair f (hA x hx hxr) (hA y hy hyr) with
    h | ⟨-, -, -, -, ⟨-, h4⟩ | ⟨δ, hδC, hδ⟩⟩
  · omega
  · have := orderOf_le_of_pow_eq_one (by norm_num) h4
    omega
  · rw [hδ] at hxy
    obtain ⟨k, hk⟩ := zs4d_exists_orderOf_five f hxy
    exact ⟨δ k, hδC k, hk⟩

end Monomial

section Coordinate

variable {X : Subgroup (U ≃ₗ[ZMod p] U)} {l m : ℕ}
  {e : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
  {j₀ j₁ : Fin l} {ζ : (ZMod p)ˣ}

private theorem zs4d_basisStab_eq_movedPullback (i : Fin l) :
    basisStab X e i = movedPullback X (movedGroup X ⊓ MulAction.stabilizer
      (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
        HardMathSupport.Kantor79.commutatorSpace X) (e i)) := by
  ext g
  rw [mem_movedPullback]
  constructor
  · intro hg
    obtain ⟨hgX, hgfix⟩ := Subgroup.mem_inf.mp hg
    refine ⟨hgX, Subgroup.mem_inf.mpr ⟨⟨⟨g, hgX⟩, rfl⟩, MulAction.mem_stabilizer_iff.mpr ?_⟩⟩
    exact Subtype.ext (MulAction.mem_stabilizer_iff.mp hgfix)
  · rintro ⟨hgX, hgB⟩
    refine Subgroup.mem_inf.mpr ⟨hgX, MulAction.mem_stabilizer_iff.mpr ?_⟩
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hgB).2)

private theorem zs4d_basisStab_eq_fixRefl (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) (i : Fin l) :
    basisStab X e i =
      fixReflSubgroup p X ((e i : HardMathSupport.Kantor79.commutatorSpace X) : U) := by
  refine le_antisymm (stabilizer_le_fixReflSubgroup_of_movedGroup hs (e i) ?_) fun g hg =>
    Subgroup.mem_inf.mpr ⟨fixReflSubgroup_le X _ hg, fixReflSubgroup_apply_eq hg⟩
  rcases hA with h | h
  · rw [h]
    exact gmmn_inf_stabilizer_le_fixReflSubgroup e hi ζ i
  · by_cases hp2 : p = 2
    · rw [h, g2mmn_eq_gmmn_of_two hp2 e hi ζ]
      exact gmmn_inf_stabilizer_le_fixReflSubgroup e hi ζ i
    · rw [h]
      exact g2mmn_inf_stabilizer_le_fixReflSubgroup hp2 e hi ζ i

private theorem zs4d_commutatorSpace_basisStab (hp : p ≠ 2) (hs : SplitSupport X l)
    (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ movedGroup X = g2mmn p e j₀ j₁ ζ)
    (hl : 3 ≤ l) {i : Fin l} {s : Fin m → Fin l} (hrange : Set.range s = {j | j ≠ i}) :
    HardMathSupport.Kantor79.commutatorSpace (basisStab X e i) =
      Submodule.span (ZMod p) (Set.range fun k => ((e (s k) : _) : U)) := by
  rw [zs4d_basisStab_eq_movedPullback, commutatorSpace_movedPullback hs inf_le_left,
    zs4d_commutatorSpace_stab hp e hi hA hl i, Submodule.map_span, Set.image_image, ← hrange,
    ← Set.range_comp]
  rfl

private theorem zs4d_exists_basis {W : Submodule (ZMod p) U} {v : Fin m → U}
    (hli : LinearIndependent (ZMod p) v) (h : Submodule.span (ZMod p) (Set.range v) = W) :
    ∃ g : Module.Basis (Fin m) (ZMod p) W, ∀ k, (g k : U) = v k :=
  ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ h), fun k => by
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]⟩

private theorem zs4d_pairUnit_comp {s : Fin m → Fin l} (hs : Function.Injective s)
    (a b : Fin m) (c : (ZMod p)ˣ) : pairUnit p (s a) (s b) c ∘ s = pairUnit p a b c := by
  funext k
  simp only [Function.comp_apply, pairUnit, hs.eq_iff]

private theorem zs4d_sign_comp {s : Fin m → Fin l} (hs : Function.Injective s) (k : Fin m) :
    (fun j => if j = s k then (-1 : (ZMod p)ˣ) else 1) ∘ s = fun j => if j = k then -1 else 1 := by
  funext j
  simp only [Function.comp_apply, hs.eq_iff]

private theorem zs4d_restrict_eq {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) {t : U ≃ₗ[ZMod p] U}
    (ht : t ∈ basisStab X e i) {δ : Fin l → (ZMod p)ˣ} {σ : Equiv.Perm (Fin l)}
    {τ : Equiv.Perm (Fin m)} (hτ : ∀ k, s (τ k) = σ (s k))
    (hr : ∀ k, t (e k : U) = ((diagMap p e δ * permMap p e σ) (e k) : U)) :
    restrictHom (basisStab X e i) (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, ht⟩ =
        diagMap p g (δ ∘ s) * permMap p g τ := by
  refine g.ext' fun k => Subtype.ext ?_
  change t (g k : U) = _
  rw [hg k, hr (s k)]
  simp only [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis,
    Submodule.coe_smul, Function.comp_apply]
  rw [hg (τ k), hτ k]

private theorem zs4d_lift_mem {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) {δ : Fin l → (ZMod p)ˣ}
    {σ : Equiv.Perm (Fin l)} {τ : Equiv.Perm (Fin m)} (hτ : ∀ k, s (τ k) = σ (s k))
    (hδ : δ i = 1) (hσ : σ i = i) (hb : diagMap p e δ * permMap p e σ ∈ movedGroup X) :
    diagMap p g (δ ∘ s) * permMap p g τ ∈ movedGroup (basisStab X e i) := by
  obtain ⟨⟨t, htX⟩, hr⟩ := MonoidHom.mem_range.mp hb
  have hact : ∀ k, t (e k : U) = ((diagMap p e δ * permMap p e σ) (e k) : U) := fun k => by
    rw [← hr]
    rfl
  have hfix : t (e i : U) = e i := by
    rw [hact, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis, hσ, hδ,
      Units.val_one, one_smul]
  have ht : t ∈ basisStab X e i := Subgroup.mem_inf.mpr ⟨htX, hfix⟩
  exact ⟨⟨t, ht⟩, zs4d_restrict_eq hg ht hτ hact⟩

private theorem zs4d_permMap_mem
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U))
    (hext : ∀ τ : Equiv.Perm (Fin m), ∃ σ : Equiv.Perm (Fin l), σ i = i ∧ ∀ k, s (τ k) = σ (s k))
    (τ : Equiv.Perm (Fin m)) : permMap p g τ ∈ movedGroup (basisStab X e i) := by
  obtain ⟨σ, hσi, hσ⟩ := hext τ
  have hb : diagMap p e 1 * permMap p e σ ∈ movedGroup X := by
    rw [diagMap_one, one_mul]
    rcases hA with h | h <;> rw [h] <;> exact Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
  have h := zs4d_lift_mem hg hσ rfl hσi hb
  rwa [Pi.one_comp, diagMap_one, one_mul] at h

private theorem zs4d_diag_mem {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) {δ : Fin l → (ZMod p)ˣ}
    (hδ : δ i = 1) (hb : diagMap p e δ ∈ movedGroup X) :
    diagMap p g (δ ∘ s) ∈ movedGroup (basisStab X e i) := by
  have h := zs4d_lift_mem hg (σ := 1) (τ := 1) (fun _ => rfl) hδ rfl
    (by rwa [zsmd_permMap_one, mul_one])
  rwa [zsmd_permMap_one, mul_one] at h

private theorem zs4d_gmmn_le (hi : j₀ ≠ j₁) (hX : movedGroup X = gmmn p e j₀ j₁ ζ) {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hsi : ∀ k, s k ≠ i)
    (hext : ∀ τ : Equiv.Perm (Fin m), ∃ σ : Equiv.Perm (Fin l), σ i = i ∧ ∀ k, s (τ k) = σ (s k))
    {k₀ k₁ : Fin m} (hk : k₀ ≠ k₁) : gmmn p g k₀ k₁ ζ ≤ movedGroup (basisStab X e i) := by
  rw [gmmn, Subgroup.closure_le]
  rintro _ (⟨τ, rfl⟩ | h)
  · exact zs4d_permMap_mem (Or.inl hX) hg hext τ
  · rw [Set.mem_singleton_iff.mp h, ← zs4d_pairUnit_comp hsinj]
    refine zs4d_diag_mem hg ?_ ?_
    · show (if i = s k₀ then ζ else if i = s k₁ then ζ⁻¹ else 1) = 1
      rw [if_neg (Ne.symm (hsi k₀)), if_neg (Ne.symm (hsi k₁))]
    · rw [hX]
      exact diagMap_pairUnit_mem_gmmn e hi (hsinj.ne hk) (Subgroup.mem_zpowers ζ)

private theorem zs4d_g2mmn_le (hi : j₀ ≠ j₁) (hX : movedGroup X = g2mmn p e j₀ j₁ ζ)
    {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hsi : ∀ k, s k ≠ i)
    (hext : ∀ τ : Equiv.Perm (Fin m), ∃ σ : Equiv.Perm (Fin l), σ i = i ∧ ∀ k, s (τ k) = σ (s k))
    {k₀ k₁ : Fin m} (hk : k₀ ≠ k₁) : g2mmn p g k₀ k₁ ζ ≤ movedGroup (basisStab X e i) := by
  rw [g2mmn, Subgroup.closure_le]
  rintro _ (⟨τ, rfl⟩ | rfl | rfl)
  · exact zs4d_permMap_mem (Or.inr hX) hg hext τ
  · rw [← zs4d_sign_comp hsinj]
    refine zs4d_diag_mem hg (if_neg (Ne.symm (hsi k₀))) ?_
    rw [hX]
    exact diagMap_signMap_mem_g2mmn e hi ζ (s k₀)
  · rw [← zs4d_pairUnit_comp hsinj]
    refine zs4d_diag_mem hg ?_ ?_
    · show (if i = s k₀ then ζ else if i = s k₁ then ζ⁻¹ else 1) = 1
      rw [if_neg (Ne.symm (hsi k₀)), if_neg (Ne.symm (hsi k₁))]
    · rw [hX]
      exact diagMap_pairUnit_mem_g2mmn e hi (hsinj.ne hk)
        (Subgroup.subset_closure (Set.mem_insert _ _))

private theorem zs4d_le_of_refl (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) {i : Fin l}
    {A' : Subgroup (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i) ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    (h : ∀ t ∈ X, IsRefl p t → ∀ ht : t ∈ basisStab X e i,
      restrictHom (basisStab X e i) (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, ht⟩ ∈ A') :
    movedGroup (basisStab X e i) ≤ A' := by
  have key : basisStab X e i ≤ movedPullback (basisStab X e i) A' := by
    refine (zs4d_basisStab_eq_fixRefl hs hi hA i).le.trans ?_
    rw [fixReflSubgroup, Subgroup.closure_le]
    rintro t ⟨htX, htr, hte⟩
    have ht : t ∈ basisStab X e i := Subgroup.mem_inf.mpr ⟨htX, hte⟩
    exact mem_movedPullback.mpr ⟨ht, h t htX htr ht⟩
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨_, h'⟩ := mem_movedPullback.mp (key ht)
  exact h'

private theorem zs4d_restrict_twist {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hrange : Set.range s = {j | j ≠ i}) {t : U ≃ₗ[ZMod p] U} (ht : t ∈ basisStab X e i)
    {a b : Fin l} (hab : a ≠ b) {c : (ZMod p)ˣ}
    (hr : ∀ k, t (e k : U) =
      ((diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b)) (e k) : U)) :
    ∃ a' b', a' ≠ b' ∧
      restrictHom (basisStab X e i) (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, ht⟩ =
          diagMap p g (pairUnit p a' b' c) * permMap p g (Equiv.swap a' b') := by
  have hfix : (diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b)) (e i) = e i :=
    Subtype.ext ((hr i).symm.trans (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp ht).2))
  obtain ⟨hai, hbi⟩ := zs4d_twist_fix_ne e hab hfix
  obtain ⟨a', rfl⟩ : a ∈ Set.range s := by rw [hrange]; exact hai
  obtain ⟨b', rfl⟩ : b ∈ Set.range s := by rw [hrange]; exact hbi
  refine ⟨a', b', fun h => hab (congrArg s h), ?_⟩
  rw [zs4d_restrict_eq hg ht (fun k => hsinj.map_swap a' b' k) hr, zs4d_pairUnit_comp hsinj]

private theorem zs4d_restrict_sign (hp : p ≠ 2) {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hrange : Set.range s = {j | j ≠ i}) {t : U ≃ₗ[ZMod p] U} (ht : t ∈ basisStab X e i)
    {k : Fin l}
    (hr : ∀ j, t (e j : U) = ((diagMap p e (fun j => if j = k then -1 else 1)) (e j) : U)) :
    ∃ k', restrictHom (basisStab X e i)
        (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, ht⟩ =
          diagMap p g (fun j => if j = k' then -1 else 1) := by
  have hfix : diagMap p e (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) (e i) = e i :=
    Subtype.ext ((hr i).symm.trans (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp ht).2))
  obtain ⟨k', rfl⟩ : k ∈ Set.range s := by rw [hrange]; exact zs4d_sign_fix_ne hp e hfix
  refine ⟨k', ?_⟩
  have hr' : ∀ j, t (e j : U) = ((diagMap p e (fun j => if j = s k' then -1 else 1) *
      permMap p e 1) (e j) : U) := fun j => by rw [zsmd_permMap_one, mul_one]; exact hr j
  rw [zs4d_restrict_eq hg ht (τ := 1) (fun _ => rfl) hr', zsmd_permMap_one, mul_one,
    zs4d_sign_comp hsinj]

private theorem zs4d_le_gmmn (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hX : movedGroup X = gmmn p e j₀ j₁ ζ) {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hrange : Set.range s = {j | j ≠ i}) {k₀ k₁ : Fin m} (hk : k₀ ≠ k₁) :
    movedGroup (basisStab X e i) ≤ gmmn p g k₀ k₁ ζ := by
  refine zs4d_le_of_refl hs hi (Or.inl hX) fun t htX htr ht => ?_
  have hmem : restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, htX⟩ ∈ gmmn p e j₀ j₁ ζ := by
    rw [← hX]
    exact ⟨⟨t, htX⟩, rfl⟩
  obtain ⟨a, b, hab, c, hc, hr⟩ :=
    zs4d_shape_gmmn hp e hi hmem (isRefl_restrictHom_of_isRefl hs htr)
  obtain ⟨a', b', hab', hr'⟩ :=
    zs4d_restrict_twist hg hsinj hrange ht hab (fun k => by rw [← hr]; rfl)
  rw [hr']
  exact zs4d_twist_mem_gmmn g hk hab' hc

private theorem zs4d_le_g2mmn (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hX : movedGroup X = g2mmn p e j₀ j₁ ζ) {i : Fin l}
    {g : Module.Basis (Fin m) (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))}
    {s : Fin m → Fin l} (hg : ∀ k, (g k : U) = (e (s k) : U)) (hsinj : Function.Injective s)
    (hrange : Set.range s = {j | j ≠ i}) {k₀ k₁ : Fin m} (hk : k₀ ≠ k₁) :
    movedGroup (basisStab X e i) ≤ g2mmn p g k₀ k₁ ζ := by
  refine zs4d_le_of_refl hs hi (Or.inr hX) fun t htX htr ht => ?_
  have hmem : restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨t, htX⟩ ∈ g2mmn p e j₀ j₁ ζ := by
    rw [← hX]
    exact ⟨⟨t, htX⟩, rfl⟩
  rcases zs4d_shape_g2mmn hp e hi hmem (isRefl_restrictHom_of_isRefl hs htr) with
    ⟨k, hr⟩ | ⟨a, b, hab, c, hc, hr⟩
  · obtain ⟨k', hr'⟩ := zs4d_restrict_sign hp hg hsinj hrange ht (fun j => by rw [← hr]; rfl)
    rw [hr']
    exact diagMap_signMap_mem_g2mmn g hk ζ k'
  · obtain ⟨a', b', hab', hr'⟩ :=
      zs4d_restrict_twist hg hsinj hrange ht hab (fun k => by rw [← hr]; rfl)
    rw [hr']
    exact zs4d_twist_mem_g2mmn g hk hab' hc

private theorem zs4d_basisStab_mono (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ movedGroup X = g2mmn p e j₀ j₁ ζ)
    (hl : 3 ≤ l) (hm : l = m + 1) (i : Fin l) {k₀ k₁ : Fin m} (hk : k₀ ≠ k₁) :
    ∃ (g : Module.Basis (Fin m) (ZMod p)
        (HardMathSupport.Kantor79.commutatorSpace (basisStab X e i))) (s : Fin m → Fin l),
      (∀ k, s k ≠ i) ∧ (∀ k, (g k : U) = (e (s k) : U)) ∧
      (movedGroup X = gmmn p e j₀ j₁ ζ → movedGroup (basisStab X e i) = gmmn p g k₀ k₁ ζ) ∧
      (movedGroup X = g2mmn p e j₀ j₁ ζ → movedGroup (basisStab X e i) = g2mmn p g k₀ k₁ ζ) := by
  obtain ⟨s, hsinj, hrange, hext⟩ := zs4d_exists_enum hm i
  have hsi : ∀ k, s k ≠ i := fun k => by
    have h : s k ∈ Set.range s := ⟨k, rfl⟩
    rw [hrange] at h
    exact h
  have hli : LinearIndependent (ZMod p) fun k => ((e (s k) : _) : U) :=
    (e.linearIndependent.comp s hsinj).map' _ (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ :=
    zs4d_exists_basis hli (zs4d_commutatorSpace_basisStab hp hs hi hA hl hrange).symm
  exact ⟨g, s, hsi, hg, fun hX => le_antisymm (zs4d_le_gmmn hp hs hi hX hg hsinj hrange hk)
      (zs4d_gmmn_le hi hX hg hsinj hsi hext hk),
    fun hX => le_antisymm (zs4d_le_g2mmn hp hs hi hX hg hsinj hrange hk)
      (zs4d_g2mmn_le hi hX hg hsinj hsi hext hk)⟩

private theorem zs4d_splitSupport_basisStab (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ movedGroup X = g2mmn p e j₀ j₁ ζ)
    (hl : 3 ≤ l) (i : Fin l) : SplitSupport (basisStab X e i) (l - 1) := by
  rw [zs4d_basisStab_eq_movedPullback]
  exact splitSupport_movedPullback hs inf_le_left (zs4d_splitSupport_stab hp e hi hA hl i)

private theorem zs4d_exists_perm_lift
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ)
    (σ : Equiv.Perm (Fin l)) : ∃ w ∈ X, ∀ k, w (e k : U) = e (σ k) := by
  have hmem : permMap p e σ ∈ movedGroup X := by
    rcases hA with h | h <;> rw [h] <;> exact Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
  obtain ⟨⟨w, hw⟩, hr⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨w, hw, fun k => ?_⟩
  rw [← permMap_apply_basis, ← hr]
  rfl

private theorem zs4d_exists_fix_pair (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) (hl : 3 ≤ l)
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ X) (hy : y ∈ X) (hxr : IsRefl p x) (hyr : IsRefl p y)
    (h3 : 3 < orderOf (x * y)) : ∃ k, x (e k : U) = e k ∧ y (e k : U) = e k := by
  let φ := restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hord : orderOf (φ ⟨x, hx⟩ * φ ⟨y, hy⟩) = orderOf (x * y) := by
    rw [← map_mul, orderOf_injective φ (restrictHom_injective_of_splitSupport hs)]
    exact (orderOf_injective X.subtype X.subtype_injective (⟨x, hx⟩ * ⟨y, hy⟩)).symm
  have hxm : φ ⟨x, hx⟩ ∈ movedGroup X := ⟨⟨x, hx⟩, rfl⟩
  have hym : φ ⟨y, hy⟩ ∈ movedGroup X := ⟨⟨y, hy⟩, rfl⟩
  rcases zs4d_pair e (zs4d_shape hp e hi hA hxm (isRefl_restrictHom_of_isRefl hs hxr))
      (zs4d_shape hp e hi hA hym (isRefl_restrictHom_of_isRefl hs hyr)) with
    h | ⟨a, b, -, hfix, -⟩
  · omega
  obtain ⟨k, hka, hkb⟩ := zs4d_exists_ne_ne hl a b
  exact ⟨k, congrArg Subtype.val (hfix k hka hkb).1, congrArg Subtype.val (hfix k hka hkb).2⟩

private theorem zs4d_dmax_basisStab (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) (hl : 3 ≤ l)
    {d : ℕ} (hd : DMax p X d) (h3 : 3 < d) (i : Fin l) : DMax p (basisStab X e i) d := by
  refine ⟨fun x hx y hy => hd.1 x (Subgroup.mem_inf.mp hx).1 y (Subgroup.mem_inf.mp hy).1, ?_⟩
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd.2
  obtain ⟨k, hxk, hyk⟩ := zs4d_exists_fix_pair hp hs hi hA hl hx hy hxr hyr (hxy ▸ h3)
  obtain ⟨w, hwX, hw⟩ := zs4d_exists_perm_lift hA (Equiv.swap k i)
  have hwk : w (e k : U) = e i := by rw [hw, Equiv.swap_apply_left]
  have hwi : w⁻¹ (e i : U) = e k := by
    rw [← hwk]
    exact w.symm_apply_apply _
  have hmem : ∀ z ∈ X, z (e k : U) = e k → w * z * w⁻¹ ∈ basisStab X e i := fun z hz hzk =>
    Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hwX hz) (X.inv_mem hwX), by
      show (w * z * w⁻¹) (e i : U) = e i
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hwi, hzk, hwk]⟩
  refine ⟨_, hmem x hx hxk, _, hmem y hy hyk, hxr.conj w, hyr.conj w, ?_⟩
  rw [show w * x * w⁻¹ * (w * y * w⁻¹) = w * (x * y) * w⁻¹ by group, ← hxy]
  exact (SemiconjBy.orderOf_eq w (by simp [SemiconjBy, mul_assoc])).symm

private theorem zs4d_sq_ne_one (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hX : movedGroup X = gmmn p e j₀ j₁ ζ)
    (hd : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) : ζ * ζ ≠ 1 := by
  intro hζ
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := exists_isRefl_pair_movedGroup hs hd
  rw [hX] at hx hy
  obtain ⟨a, b, hab, c, hc, rfl⟩ := zs4d_shape_gmmn hp e hi hx hxr
  obtain ⟨a', b', hab', c', hc', rfl⟩ := zs4d_shape_gmmn hp e hi hy hyr
  have h2 : ∀ u ∈ Subgroup.zpowers ζ, u ^ 2 = 1 := fun u hu =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hu).trans
      (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hζ)))
  rcases zs4d_tw_tw e hab hab' c c' with h | ⟨-, h⟩
  · omega
  · rw [h] at hxy
    have := orderOf_le_of_pow_eq_one (by norm_num) (zsmd_diagMap_pow_eq_one e
      (pairUnit p a b c * (pairUnit p a' b' c' ∘ (Equiv.swap a b).symm)) 2 fun k =>
        h2 _ (Subgroup.mul_mem _ (zs4d_pairUnit_mem hc a b k) (zs4d_pairUnit_mem hc' a' b' _)))
    omega

private theorem zs4d_twist_lift {a b : Fin l} {c : (ZMod p)ˣ} (hab : a ≠ b)
    (hm : diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b) ∈ movedGroup X) :
    ∃ w ∈ X, w (e a : U) = (c : ZMod p)⁻¹ • (e b : U) ∧
      w (e b : U) = (c : ZMod p) • (e a : U) ∧ ∀ k, k ≠ a → k ≠ b → w (e k : U) = e k := by
  obtain ⟨⟨w, hw⟩, hr⟩ := MonoidHom.mem_range.mp hm
  have hwv : ∀ v : HardMathSupport.Kantor79.commutatorSpace X, w (v : U) =
      ((diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b)) v : U) := fun v => by
    rw [← hr]
    rfl
  refine ⟨w, hw, ?_, ?_, fun k hka hkb => ?_⟩
  · rw [hwv, zs4d_twist_apply, Equiv.swap_apply_left, zs4d_pairUnit_right hab,
      Units.val_inv_eq_inv_val, Submodule.coe_smul]
  · rw [hwv, zs4d_twist_apply, Equiv.swap_apply_right, zs4d_pairUnit_left, Submodule.coe_smul]
  · rw [hwv, zs4d_twist_apply_of_ne e hka hkb]

private theorem zs4d_exists_fix (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) (hl : 3 ≤ l)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ X) (hxr : IsRefl p x) : ∃ m, x (e m : U) = e m := by
  let φ := restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hxm : φ ⟨x, hx⟩ ∈ movedGroup X := ⟨⟨x, hx⟩, rfl⟩
  suffices h : ∃ m, φ ⟨x, hx⟩ (e m) = e m by
    obtain ⟨m, hm⟩ := h
    exact ⟨m, congrArg Subtype.val hm⟩
  rcases zs4d_shape hp e hi hA hxm (isRefl_restrictHom_of_isRefl hs hxr) with
    ⟨k, hk⟩ | ⟨a, b, -, c, -, hc⟩
  · obtain ⟨m, hm, -⟩ := zs4d_exists_ne_ne hl k k
    exact ⟨m, by rw [hk]; exact zs4d_sign_apply_of_ne e hm⟩
  · obtain ⟨m, hma, hmb⟩ := zs4d_exists_ne_ne hl a b
    exact ⟨m, by rw [hc]; exact zs4d_twist_apply_of_ne e hma hmb c⟩

private theorem zs4d_mem_of_conj {K : Subgroup (U ≃ₗ[ZMod p] U)} {i m : Fin l}
    (hK : basisStab X e i ≤ K) {w t : U ≃ₗ[ZMod p] U} (hwX : w ∈ X) (hwK : w ∈ K)
    (hw : w (e m : U) = e i) (htX : t ∈ X) (ht : t (e m : U) = e m) : t ∈ K := by
  have hwi : w⁻¹ (e i : U) = e m := by
    rw [← hw]
    exact w.symm_apply_apply _
  have hc : w * t * w⁻¹ ∈ K := hK (Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hwX htX)
    (X.inv_mem hwX), by
      show (w * t * w⁻¹) (e i : U) = e i
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hwi, ht, hw]⟩)
  rw [show t = w⁻¹ * (w * t * w⁻¹) * w by group]
  exact K.mul_mem (K.mul_mem (K.inv_mem hwK) hc) hwK

private theorem zs4d_le_of_fix (hp : p ≠ 2) (hs : SplitSupport X l) (hi : j₀ ≠ j₁)
    (hA : movedGroup X = gmmn p e j₀ j₁ ζ ∨ movedGroup X = g2mmn p e j₀ j₁ ζ) (hl : 3 ≤ l)
    (hX : ReflGen p X) {K : Subgroup (U ≃ₗ[ZMod p] U)} {i : Fin l} (hK : basisStab X e i ≤ K)
    (hw : ∀ m, ∃ w ∈ X, w ∈ K ∧ w (e m : U) = e i) : X ≤ K := by
  rw [hX, Subgroup.closure_le]
  rintro t ⟨htX, htr⟩
  obtain ⟨m, hm⟩ := zs4d_exists_fix hp hs hi hA hl htX htr
  obtain ⟨w, hwX, hwK, hwm⟩ := hw m
  exact zs4d_mem_of_conj hK hwX hwK hwm htX hm

end Coordinate

section Spaces

private theorem zs4d_commutatorSpace_mono {A B : Subgroup (U ≃ₗ[ZMod p] U)} (h : A ≤ B) :
    HardMathSupport.Kantor79.commutatorSpace A ≤ HardMathSupport.Kantor79.commutatorSpace B :=
  commutatorSpace_le_iff.mpr fun g hg v => commutatorSpace_le_iff.mp le_rfl g (h hg) v

private theorem zs4d_commutatorSpace_sup_le {A B : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} (hA : HardMathSupport.Kantor79.commutatorSpace A ≤ W)
    (hB : HardMathSupport.Kantor79.commutatorSpace B ≤ W) :
    HardMathSupport.Kantor79.commutatorSpace (A ⊔ B) ≤ W := by
  let P : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ∀ v, g v - v ∈ W}
      mul_mem' := by
        intro x y hx hy v
        rw [LinearEquiv.mul_apply, ← sub_add_sub_cancel _ (y v)]
        exact W.add_mem (hx (y v)) (hy v)
      one_mem' := by
        intro v
        simp
      inv_mem' := by
        intro x hx v
        have h := W.neg_mem (hx (x⁻¹ v))
        rwa [neg_sub, show x (x⁻¹ v) = v from x.apply_symm_apply v] at h }
  have hAP : A ≤ P := fun g hg v => commutatorSpace_le_iff.mp hA g hg v
  have hBP : B ≤ P := fun g hg v => commutatorSpace_le_iff.mp hB g hg v
  exact commutatorSpace_le_iff.mpr fun g hg v => sup_le hAP hBP hg v

private theorem zs4d_irred_of_le {A B : Subgroup (U ≃ₗ[ZMod p] U)} {W : Submodule (ZMod p) U}
    (hAB : A ≤ B) (h : IrredOnSection A ⊥ W) : IrredOnSection B ⊥ W :=
  fun X h1 h2 h3 => h X h1 h2 fun g hg => h3 g (hAB hg)

private theorem zs4d_reflGen_sup {A B : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ReflGen p A)
    (hB : ReflGen p B) : ReflGen p (A ⊔ B) :=
  le_antisymm (sup_le
      ((Eq.le hA).trans (Subgroup.closure_mono fun _ ht => ⟨Subgroup.mem_sup_left ht.1, ht.2⟩))
      ((Eq.le hB).trans (Subgroup.closure_mono fun _ ht => ⟨Subgroup.mem_sup_right ht.1, ht.2⟩)))
    ((Subgroup.closure_le _).mpr fun _ ht => ht.1)

private theorem zs4d_reflGen_closure {K : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (har : IsRefl p a) (hK : ReflGen p K) :
    ReflGen p (Subgroup.closure (insert a (K : Set (U ≃ₗ[ZMod p] U)))) := by
  refine le_antisymm ((Subgroup.closure_le _).mpr (Set.insert_subset
    (Subgroup.subset_closure ⟨Subgroup.subset_closure (Set.mem_insert _ _), har⟩) ?_))
    ((Subgroup.closure_le _).mpr fun _ ht => ht.1)
  exact (Eq.le hK).trans (Subgroup.closure_mono fun _ ht =>
    ⟨Subgroup.subset_closure (Set.mem_insert_of_mem _ ht.1), ht.2⟩)

private theorem zs4d_finrank_centralizerSpace [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport X l) :
    Module.finrank (ZMod p) (centralizerSpace X) = Module.finrank (ZMod p) U - l := by
  have h := Submodule.finrank_add_eq_of_isCompl hs.1
  have h1 := hs.2.1
  omega

private theorem zs4d_exists_sigma {L : ℕ} (hL : L = 3) (i : Fin L) :
    ∃ σ : Fin 3 ≃ Fin L, σ 2 = i := by
  subst hL
  exact ⟨Equiv.swap 2 i, Equiv.swap_apply_left 2 i⟩

private theorem zs4d_toMatrix_pij01 (f : Module.Basis (Fin 4) (ZMod p) U)
    {w : U ≃ₗ[ZMod p] U} {α : ZMod p} (h0 : w (f 0) = α⁻¹ • f 1) (h1 : w (f 1) = α • f 0)
    (h2 : w (f 2) = f 2) (h3 : w (f 3) = f 3) :
    LinearMap.toMatrix f f w.toLinearMap = pijMat 0 1 α := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [LinearMap.toMatrix_apply, h0, h1, h2, h3, pijMat]

private theorem zs4d_toMatrix_pij12 (f : Module.Basis (Fin 4) (ZMod p) U)
    {w : U ≃ₗ[ZMod p] U} {α : ZMod p} (h0 : w (f 0) = f 0) (h1 : w (f 1) = α⁻¹ • f 2)
    (h2 : w (f 2) = α • f 1) (h3 : w (f 3) = f 3) :
    LinearMap.toMatrix f f w.toLinearMap = pijMat 1 2 α := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [LinearMap.toMatrix_apply, h0, h1, h2, h3, pijMat]

private theorem zs4d_card_gmmn_ne {k n : ℕ} (hn : n = 5)
    (h : k ^ (n - 2 - 1) * (n - 2).factorial = 48) : False := by
  subst hn
  norm_num [Nat.factorial] at h
  have hk : k ≤ 2 := by nlinarith
  interval_cases k <;> norm_num at h

private theorem zs4d_card_g2mmn_lt {L n : ℕ} (hn : n = 5)
    (h : 2 * L ^ (n - 2 - 1) * (n - 2).factorial = 48) :
    2 * L ^ (n - 1 - 1) * (n - 1).factorial < 1152 := by
  subst hn
  norm_num [Nat.factorial] at h ⊢
  have hL : L ≤ 2 := by nlinarith
  interval_cases L <;> revert h <;> norm_num

end Spaces

namespace ImpExtStd

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}
  {e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace H)}
  {j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)} {ζ : (ZMod p)ˣ}

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_sq_ne_one_of_gmmn (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (h : movedGroup H = gmmn p e j₀ j₁ ζ) : ζ * ζ ≠ 1 := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
  exact zs4d_sq_ne_one hp S.splitSupport S.ne h ⟨x, hx, y, hy, hxr, hyr, hxy ▸ S.three_lt⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_mono (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) :
    movedGroup H = gmmn p e j₀ j₁ ζ ∧ ζ * ζ ≠ 1 ∨ movedGroup H = g2mmn p e j₀ j₁ ζ :=
  S.mono.imp (fun h => ⟨h, zs4d_sq_ne_one_of_gmmn hp S h⟩) id

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_closure_le (S : ImpExtStd G H d e j₀ j₁ ζ) {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ G) (i : Fin (Module.finrank (ZMod p) U - 1)) :
    Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
  have hK : basisStab H e i ≤ G := inf_le_left.trans S.H_le
  exact (Subgroup.closure_le _).mpr (Set.insert_subset ha hK)

private theorem zs4d_le_of_commutatorSpace_le (S : ImpExtStd G H d e j₀ j₁ ζ)
    (h14 : SplitOfIrred p G (Module.finrank (ZMod p) U - 1)) {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKG : K ≤ G) (hK : ReflGen p K)
    (hV : HardMathSupport.Kantor79.commutatorSpace K ≤
      HardMathSupport.Kantor79.commutatorSpace H) : K ≤ H := by
  have hFG : K ⊔ H ≤ G := sup_le hKG S.H_le
  have hFr : ReflGen p (K ⊔ H) := zs4d_reflGen_sup hK S.reflGen_H
  have hVF : HardMathSupport.Kantor79.commutatorSpace (K ⊔ H) =
      HardMathSupport.Kantor79.commutatorSpace H :=
    le_antisymm (zs4d_commutatorSpace_sup_le hV le_rfl) (zs4d_commutatorSpace_mono le_sup_right)
  have hirr : IrredOnSection (K ⊔ H) ⊥ (HardMathSupport.Kantor79.commutatorSpace (K ⊔ H)) := by
    rw [hVF]
    exact zs4d_irred_of_le le_sup_right S.splitSupport.2.2
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace (K ⊔ H)) =
      Module.finrank (ZMod p) U - 1 := by
    rw [hVF]
    exact S.splitSupport.2.1
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
  have hFs := h14 _ hFG hFr hirr hfin ⟨x, Subgroup.mem_sup_right hx, y,
    Subgroup.mem_sup_right hy, hxr, hyr, hxy ▸ S.three_lt⟩
  have hcard := S.toImpExtSetting.card_le_of_orderOf hFG hFr hFs
    ⟨x, Subgroup.mem_sup_right hx, y, Subgroup.mem_sup_right hy, hxr, hyr, hxy⟩
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun g : U ≃ₗ[ZMod p] U => (g : U → U)) DFunLike.coe_injective
  exact le_sup_left.trans (Subgroup.eq_of_le_of_card_ge le_sup_right hcard).ge

omit [Module.Finite (ZMod p) U] in
theorem reflGen_basisStab (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) : ReflGen p (basisStab H e i) := by
  rw [zs4d_basisStab_eq_fixRefl S.splitSupport S.ne S.mono i]
  exact reflGen_fixReflSubgroup H _

omit [Module.Finite (ZMod p) U] in
theorem splitSupport_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    SplitSupport (basisStab H e i) (Module.finrank (ZMod p) U - 2) := by
  have h4 := S.four_le_finrank
  have h := zs4d_splitSupport_basisStab hp S.splitSupport S.ne (zs4d_mono hp S) (by omega) i
  rwa [show Module.finrank (ZMod p) U - 1 - 1 = Module.finrank (ZMod p) U - 2 by omega] at h

omit [Module.Finite (ZMod p) U] in
theorem dmax_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) : DMax p (basisStab H e i) d := by
  have h4 := S.four_le_finrank
  exact zs4d_dmax_basisStab hp S.splitSupport S.ne S.mono (by omega) S.dmax_H S.three_lt i

omit [Module.Finite (ZMod p) U] in
theorem exists_basis_basisStab (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ (g : Module.Basis (Fin (Module.finrank (ZMod p) U - 2)) (ZMod p)
        (HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)))
      (k₀ k₁ : Fin (Module.finrank (ZMod p) U - 2)), k₀ ≠ k₁ ∧
      (∀ k, ∃ j, j ≠ i ∧ ((g k : HardMathSupport.Kantor79.commutatorSpace (basisStab H e i)) : U) =
        ((e j : HardMathSupport.Kantor79.commutatorSpace H) : U)) ∧
      (movedGroup H = gmmn p e j₀ j₁ ζ → movedGroup (basisStab H e i) = gmmn p g k₀ k₁ ζ) ∧
      (movedGroup H = g2mmn p e j₀ j₁ ζ → movedGroup (basisStab H e i) = g2mmn p g k₀ k₁ ζ) := by
  have h4 := S.four_le_finrank
  have hk : (⟨0, by omega⟩ : Fin (Module.finrank (ZMod p) U - 2)) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨g, s, hsi, hg, h1, h2⟩ := zs4d_basisStab_mono hp S.splitSupport S.ne (zs4d_mono hp S)
    (by omega) (by omega) i hk
  exact ⟨g, _, _, hk, fun k => ⟨s k, hsi k, hg k⟩, h1, h2⟩

theorem eq_basisStab_of_le (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (h14 : SplitOfIrred p G (Module.finrank (ZMod p) U - 1))
    (i : Fin (Module.finrank (ZMod p) U - 1)) {K : Subgroup (U ≃ₗ[ZMod p] U)} (hKG : K ≤ G)
    (hle : basisStab H e i ≤ K) (hK : ReflGen p K)
    (hKs : SplitSupport K (Module.finrank (ZMod p) U - 2)) : K = basisStab H e i := by
  have hHs := splitSupport_basisStab hp S i
  have hV : HardMathSupport.Kantor79.commutatorSpace K =
      HardMathSupport.Kantor79.commutatorSpace (basisStab H e i) :=
    (Submodule.eq_of_le_of_finrank_eq (zs4d_commutatorSpace_mono hle)
      (hHs.2.1.trans hKs.2.1.symm)).symm
  have hKH := zs4d_le_of_commutatorSpace_le S h14 hKG hK
    (hV.le.trans (zs4d_commutatorSpace_mono (inf_le_left : basisStab H e i ≤ H)))
  have hC : centralizerSpace K = centralizerSpace (basisStab H e i) :=
    Submodule.eq_of_le_of_finrank_eq
      (fun v hv => mem_centralizerSpace.mpr fun h hh => mem_centralizerSpace.mp hv h (hle hh))
      (by rw [zs4d_finrank_centralizerSpace hKs, zs4d_finrank_centralizerSpace hHs])
  have hei : ((e i : HardMathSupport.Kantor79.commutatorSpace H) : U) ∈ centralizerSpace K := by
    rw [hC]
    exact mem_centralizerSpace.mpr fun h hh => (Subgroup.mem_inf.mp hh).2
  exact le_antisymm (fun k hk => Subgroup.mem_inf.mpr ⟨hKH hk, mem_centralizerSpace.mp hei k hk⟩)
    hle

theorem exists_isRefl_not_mem_mul (_hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) :
    ∃ a ∈ G, IsRefl p a ∧
      ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c := by
  by_contra hcon
  have hcon' : ∀ a, a ∈ G → IsRefl p a →
      ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c := by
    intro a haG har
    by_contra hno
    exact hcon ⟨a, haG, har, hno⟩
  have hG_le : G ≤ H ⊔ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) := by
    rw [S.reflGen, Subgroup.closure_le]
    rintro a ⟨haG, har⟩
    obtain ⟨h, hh, c, hc, rfl⟩ := hcon' a haG har
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hc)
  have hN : H ⊔ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) ≤
      Subgroup.normalizer (H : Set (U ≃ₗ[ZMod p] U)) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hInv : ∀ g ∈ G, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      g w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro g hg w hw
    have hgn : g ∈ Subgroup.normalizer (H : Set (U ≃ₗ[ZMod p] U)) := hN (hG_le hg)
    have hmap := map_commutatorSpace_of_mem_normalizer hgn
    rw [← hmap]
    exact ⟨w, hw, rfl⟩
  rcases S.absIrred.1 (HardMathSupport.Kantor79.commutatorSpace H) hInv with hbot | htop
  · have hfr := S.splitSupport.2.1
    rw [hbot, finrank_bot] at hfr
    have h4 := S.four_le_finrank
    omega
  · have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
      S.splitSupport.1.inf_eq_bot
    rw [htop, top_inf_eq] at hinf
    have h1 := ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting
    rw [hinf, finrank_bot] at h1
    exact Nat.zero_ne_one h1

omit [Module.Finite (ZMod p) U] in
theorem lt_of_five_le (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : 5 ≤ p) : d < p := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ :=
    ((dmax_movedGroup_iff S.splitSupport d).mpr S.dmax_H).2
  rcases zs4d_pair e (zs4d_shape hp2 e S.ne S.mono hx hxr) (zs4d_shape hp2 e S.ne S.mono hy hyr)
    with h | ⟨-, -, -, -, ⟨-, h4⟩ | ⟨δ, -, hδ⟩⟩
  · omega
  · have := orderOf_le_of_pow_eq_one (by norm_num) h4
    omega
  · have h1 : (x * y) ^ (p - 1) = 1 := by
      rw [hδ]
      exact zsmd_diagMap_pow_eq_one e δ (p - 1) fun k =>
        ZMod.units_pow_card_sub_one_eq_one p (δ k)
    have := orderOf_le_of_pow_eq_one (by omega) h1
    omega

theorem splitSupport_closure_of_five_le (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : 5 ≤ p)
    (I : ImpExtInputs G H) (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ G) (har : IsRefl p a)
    (hai : ¬ ∃ h ∈ basisStab H e i,
      ∃ c ∈ Subgroup.centralizer (basisStab H e i : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1) := by
  have hp2 : p ≠ 2 := by omega
  have hK : basisStab H e i ≤ G := (inf_le_left).trans S.H_le
  have hFG : Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hzK
    · exact ha
    · exact hK hzK
  have hdK : ∃ x ∈ basisStab H e i, ∃ y ∈ basisStab H e i,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := (dmax_basisStab hp2 S i).2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; exact S.three_lt⟩
  rcases I.degenerate hp2 S.reflGen S.transvectionFree S.absIrred S.primitive
      (by have h4 := S.four_le_finrank; omega)
      (basisStab H e i) hK (reflGen_basisStab S i) (splitSupport_basisStab hp2 S i)
      (fun K' hK'G hle hK' hK's =>
        eq_basisStab_of_le hp2 S I.splitOfIrred i hK'G hle hK' hK's)
      hdK a ha har hai with h | h
  · rwa [show Module.finrank (ZMod p) U - 2 + 1 = Module.finrank (ZMod p) U - 1 from by
      have h4 := S.four_le_finrank; omega] at h
  · obtain ⟨⟨x, hx, y, hy, hxr, hyr, hxy⟩, _⟩ := h
    have hxG : x ∈ G := hFG hx
    have hyG : y ∈ G := hFG hy
    have hle := S.dmax.1 x hxG y hyG hxr hyr
    rw [hxy] at hle
    have hlt := lt_of_five_le S hp
    omega

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_three_g2mmn (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : p = 3) :
    movedGroup H = g2mmn p e j₀ j₁ ζ ∧ orderOf ζ ∣ 2 := by
  have hζ : ζ ^ 2 = 1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p ζ
    rwa [show p - 1 = 2 by omega] at h
  rcases zs4d_mono (by omega) S with ⟨-, h⟩ | h
  · exact (h (by rw [← sq]; exact hζ)).elim
  · exact ⟨h, orderOf_dvd_of_pow_eq_one hζ⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_five_le_of_three (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : p = 3)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) : 5 ≤ Module.finrank (ZMod p) U := by
  have h4 := S.four_le_finrank
  obtain ⟨-, hdvd⟩ := zs4d_three_g2mmn S hp
  have hζ : ζ * ζ = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  by_contra h5
  exact hM ⟨by omega, fun hg => absurd hζ (zs4d_sq_ne_one_of_gmmn (by omega) S hg),
    fun _ => Or.inl hdvd⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_exists_inter (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : p = 3)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) (i : Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ K₁ ≤ basisStab H e i, ReflGen p K₁ ∧ SplitSupport K₁ (Module.finrank (ZMod p) U - 3) ∧
      ∃ x ∈ K₁, ∃ y ∈ K₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, k₀, k₁, hk, -, -, h2⟩ := exists_basis_basisStab hp2 S i
  have hg := h2 (zs4d_three_g2mmn S hp).1
  have hs := splitSupport_basisStab hp2 S i
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ :=
    (zs4d_dmax_basisStab hp2 hs hk (Or.inr hg) (by omega) (dmax_basisStab hp2 S i)
      S.three_lt k₀).2
  refine ⟨basisStab (basisStab H e i) g k₀, inf_le_left, ?_, ?_, x, hx, y, hy, hxr, hyr,
    hxy ▸ S.three_lt⟩
  · rw [zs4d_basisStab_eq_fixRefl hs hk (Or.inr hg) k₀]
    exact reflGen_fixReflSubgroup _ _
  · have h := zs4d_splitSupport_basisStab hp2 hs hk (Or.inr hg) (by omega) k₀
    rwa [show Module.finrank (ZMod p) U - 2 - 1 = Module.finrank (ZMod p) U - 3 by omega] at h

theorem splitSupport_closure_of_three (S : ImpExtStd G H d e j₀ j₁ ζ) (hp : p = 3)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G)
    (har : IsRefl p a)
    (hai : ¬ ∃ h ∈ basisStab H e i,
      ∃ c ∈ Subgroup.centralizer (basisStab H e i : Set (U ≃ₗ[ZMod p] U)), a = h * c) :
    SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1) := by
  have hp2 : p ≠ 2 := by omega
  have h5 := zs4d_five_le_of_three S hp hM
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := (dmax_basisStab hp2 S i).2
  rcases I.degenerate hp2 S.reflGen S.transvectionFree S.absIrred S.primitive (by omega)
      (basisStab H e i) (inf_le_left.trans S.H_le) (reflGen_basisStab S i)
      (splitSupport_basisStab hp2 S i)
      (fun K' hK'G hle hK' hK's => eq_basisStab_of_le hp2 S I.splitOfIrred i hK'G hle hK' hK's)
      ⟨x, hx, y, hy, hxr, hyr, hxy ▸ S.three_lt⟩ a ha har hai with h | ⟨-, h⟩
  · rwa [show Module.finrank (ZMod p) U - 2 + 1 = Module.finrank (ZMod p) U - 1 by omega] at h
  exfalso
  obtain ⟨K₁, hK₁, hK₁r, hK₁s, x₁, hx₁, y₁, hy₁, hxr₁, hyr₁, hxy₁⟩ := zs4d_exists_inter S hp h5 i
  obtain ⟨B, hBG, hBr, hK₁B, hBs, T, hTB, hT1, hT2, hTc, hT3⟩ :=
    h K₁ hK₁ hK₁r (Module.finrank (ZMod p) U - 3) (by omega) hK₁s
      ⟨x₁, hx₁, y₁, hy₁, hxr₁, hyr₁, hxy₁⟩
  have hBs' : SplitSupport B (Module.finrank (ZMod p) U - 1) := by
    rwa [show Module.finrank (ZMod p) U - 3 + 2 = Module.finrank (ZMod p) U - 1 by omega] at hBs
  have hpB : ∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    ⟨x₁, hK₁B hx₁, y₁, hK₁B hy₁, hxr₁, hyr₁, hxy₁⟩
  obtain ⟨hprim, horth⟩ := I.degenerateExt U B hp (by omega) hBr
    (fun g hg => S.transvectionFree g (hBG hg)) hBs' hpB T hTB hT1 hT2
    (by rwa [show Module.finrank (ZMod p) U - 1 - 2 = Module.finrank (ZMod p) U - 3 by omega])
    hT3
  exact S.noOrth B hBG hBr hBs' hprim hpB horth

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_row (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) {m : ℕ} {Y : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : Module.Basis (Fin m) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y)}
    {k₀ k₁ : Fin m}
    (h1 : movedGroup H = gmmn p e j₀ j₁ ζ → movedGroup Y = gmmn p g k₀ k₁ ζ)
    (h2 : movedGroup H = g2mmn p e j₀ j₁ ζ → movedGroup Y = g2mmn p g k₀ k₁ ζ) :
    movedGroup Y = gmmn p g k₀ k₁ ζ ∧ ¬ (Module.finrank (ZMod p) U - 1 = 3 ∧ orderOf ζ = 4) ∨
      movedGroup Y = g2mmn p g k₀ k₁ ζ ∧
        ¬ (Module.finrank (ZMod p) U - 1 = 3 ∧ (orderOf ζ ∣ 2 ∨ orderOf ζ = 4)) := by
  rcases S.mono with h | h
  · exact Or.inl ⟨h1 h, fun ⟨h3, h4⟩ => hM ⟨h3, fun _ => h4, fun _ => Or.inr h4⟩⟩
  · have h4' : orderOf ζ ∣ 2 ∨ orderOf ζ = 4 → movedGroup H = gmmn p e j₀ j₁ ζ →
        orderOf ζ = 4 := fun h4 hg => h4.resolve_left fun hd => zs4d_sq_ne_one_of_gmmn hp S hg
      (by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp hd)
    exact Or.inr ⟨h2 h, fun ⟨h3, h4⟩ => hM ⟨h3, h4' h4, fun _ => h4⟩⟩

theorem primitive_cases (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hM : ¬ ImpExtRowM H e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G)
    (har : IsRefl p a)
    (hF : SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1))
    (hFp : ¬ Quasithin.SimsG4.IsImprimitiveOnV
      (movedGroup (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))))) :
    (Module.finrank (ZMod p) U = 4 ∧ d = 5 ∧
        H3Data p (movedGroup (Subgroup.closure (insert a (basisStab H e i : Set _))))) ∨
      (Module.finrank (ZMod p) U = 5 ∧
        Nat.card (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))) = 1152 ∧
        Nat.card (basisStab H e i) = 48) := by
  have h4 := S.four_le_finrank
  have hKF : basisStab H e i ≤ Subgroup.closure (insert a (basisStab H e i : Set _)) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem _ hh)
  have hFG := zs4d_closure_le S ha i
  have hFr := zs4d_reflGen_closure har (reflGen_basisStab S i)
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := (dmax_basisStab hp S i).2
  have hk : (⟨0, by omega⟩ : Fin (Module.finrank (ZMod p) U - 1 - 1)) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨g, -, -, -, h1, h2⟩ := zs4d_basisStab_mono hp S.splitSupport S.ne (zs4d_mono hp S)
    (by omega) (m := Module.finrank (ZMod p) U - 1 - 1) (by omega) i hk
  rcases I.primCorank U _ (basisStab H e i) d hp (by omega) hFr
      (fun t ht => S.transvectionFree t (hFG ht)) hF hFp
      (S.noOrth _ hFG hFr hF hFp ⟨x, hKF hx, y, hKF hy, hxr, hyr, hxy ▸ S.three_lt⟩)
      (I.centreOrder _ hFG hFr hF)
      ⟨fun x hx y hy hxr hyr => S.dmax.1 x (hFG hx) y (hFG hy) hxr hyr,
        x, hKF hx, y, hKF hy, hxr, hyr, hxy⟩
      S.three_lt hKF (reflGen_basisStab S i)
      (zs4d_splitSupport_basisStab hp S.splitSupport S.ne (zs4d_mono hp S) (by omega) i)
      (dmax_basisStab hp S i) g _ _ ζ hk (zs4d_row hp S hM h1 h2) with
    ⟨h3, hd, hH3⟩ | ⟨h5, -, hcF, hcH⟩
  · exact Or.inl ⟨by omega, hd, hH3⟩
  · exact Or.inr ⟨by omega, hcF, hcH⟩

omit [Module.Finite (ZMod p) U] in
theorem false_of_card_eq_1152 (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G)
    (har : IsRefl p a) (hn : Module.finrank (ZMod p) U = 5)
    (hF : SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1))
    (hcF : Nat.card (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))) = 1152)
    (hcH : Nat.card (basisStab H e i) = 48) : False := by
  have hKF : basisStab H e i ≤ Subgroup.closure (insert a (basisStab H e i : Set _)) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem _ hh)
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := (dmax_basisStab hp S i).2
  have hle := S.toImpExtSetting.card_le_of_orderOf (zs4d_closure_le S ha i)
    (zs4d_reflGen_closure har (reflGen_basisStab S i)) hF ⟨x, hKF hx, y, hKF hy, hxr, hyr, hxy⟩
  rw [hcF, ← card_movedGroup_of_splitSupport S.splitSupport] at hle
  rw [← card_movedGroup_of_splitSupport (splitSupport_basisStab hp S i)] at hcH
  have h4 : 2 ≤ Module.finrank (ZMod p) U - 2 := by omega
  obtain ⟨g, k₀, k₁, hk, -, h1, h2⟩ := exists_basis_basisStab hp S i
  rcases S.mono with h | h
  · rw [h1 h, card_gmmn h4 g hk ζ] at hcH
    exact zs4d_card_gmmn_ne hn hcH
  · rw [h2 h, card_g2mmn hp h4 g hk ζ] at hcH
    rw [h, card_g2mmn hp (by omega) e S.ne ζ] at hle
    exact absurd hle (not_le.mpr (zs4d_card_g2mmn_lt hn hcH))

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_exists_lam_H (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (hd : d = 5) :
    ∃ (C : Subgroup (ZMod p)ˣ) (lam : (ZMod p)ˣ), lam ∈ C ∧ orderOf lam = 5 ∧
      ∀ a b c, a ≠ b → c ∈ C →
        diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b) ∈ movedGroup H := by
  have hpair := ((dmax_movedGroup_iff S.splitSupport d).mpr S.dmax_H).2
  rw [hd] at hpair
  rcases S.mono with h | h
  · obtain ⟨lam, hlC, hl⟩ := zs4d_exists_lam e (C := Subgroup.zpowers ζ) (A := movedGroup H)
      (fun x hx hxr => Or.inr (zs4d_shape_gmmn hp e S.ne (h ▸ hx) hxr)) hpair
    exact ⟨_, lam, hlC, hl, fun a b c hab hc => h ▸ zs4d_twist_mem_gmmn e S.ne hab hc⟩
  · obtain ⟨lam, hlC, hl⟩ := zs4d_exists_lam e (C := Subgroup.closure {ζ, -1})
      (A := movedGroup H) (fun x hx hxr => zs4d_shape_g2mmn hp e S.ne (h ▸ hx) hxr) hpair
    exact ⟨_, lam, hlC, hl, fun a b c hab hc => h ▸ zs4d_twist_mem_g2mmn e S.ne hab hc⟩

private theorem zs4d_exists_basis4 (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) U,
      (∀ t : Fin 3, f t.castSucc = e (σ t)) ∧ f 3 ∈ centralizerSpace H := by
  have hbot : centralizerSpace H ≠ ⊥ := fun h => by
    have h1 := ImpExtSetting.finrank_centralizerSpace S.toImpExtSetting
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hli : LinearIndependent (ZMod p) fun t : Fin 3 => ((e (σ t) : _) : U) :=
    (e.linearIndependent.comp σ σ.injective).map' _ (Submodule.ker_subtype _)
  have hvs : v ∉ Submodule.span (ZMod p) (Set.range fun t : Fin 3 => ((e (σ t) : _) : U)) := by
    intro hvs
    have hvV : v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact (e (σ t)).2) hvs
    have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H := ⟨hvV, hv⟩
    rw [S.splitSupport.1.inf_eq_bot] at hmem
    exact hv0 ((Submodule.mem_bot _).mp hmem)
  have hlin := hli.finSnoc hvs
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hlin (by rw [Fintype.card_fin, hn]),
    fun t => ?_, ?_⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank, Fin.snoc_castSucc]
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank, show (3 : Fin 4) = Fin.last 3 from rfl,
      Fin.snoc_last]
    exact hv

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_lift_f {f : Module.Basis (Fin 4) (ZMod p) U}
    {σ : Fin 3 ≃ Fin (Module.finrank (ZMod p) U - 1)}
    (hf : ∀ t : Fin 3, f t.castSucc = e (σ t)) (hf3 : f 3 ∈ centralizerSpace H)
    {C : Subgroup (ZMod p)ˣ} (hC : ∀ a b c, a ≠ b → c ∈ C →
      diagMap p e (pairUnit p a b c) * permMap p e (Equiv.swap a b) ∈ movedGroup H)
    {a b : Fin 3} (hab : a ≠ b) {c : (ZMod p)ˣ} (hc : c ∈ C) :
    ∃ w ∈ H, w (f a.castSucc) = (c : ZMod p)⁻¹ • f b.castSucc ∧
      w (f b.castSucc) = (c : ZMod p) • f a.castSucc ∧
      (∀ t, t ≠ a → t ≠ b → w (f t.castSucc) = f t.castSucc) ∧ w (f 3) = f 3 := by
  obtain ⟨w, hw, h1, h2, h3⟩ :=
    zs4d_twist_lift (σ.injective.ne hab) (hC _ _ c (σ.injective.ne hab) hc)
  refine ⟨w, hw, ?_, ?_, fun t hta htb => ?_, mem_centralizerSpace.mp hf3 w hw⟩
  · rw [hf, hf, h1]
  · rw [hf, hf, h2]
  · rw [hf, h3 _ (σ.injective.ne hta) (σ.injective.ne htb)]

private theorem zs4d_frame (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ)
    (hn : Module.finrank (ZMod p) U = 4) (hd : d = 5) (i : Fin (Module.finrank (ZMod p) U - 1)) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (lam : (ZMod p)ˣ) (a₁ a₂ a₃ : U ≃ₗ[ZMod p] U),
      orderOf lam = 5 ∧ LinearMap.toMatrix f f a₁.toLinearMap = pijMat 0 1 1 ∧
      LinearMap.toMatrix f f a₂.toLinearMap = pijMat 0 1 (lam : ZMod p) ∧
      LinearMap.toMatrix f f a₃.toLinearMap = pijMat 1 2 1 ∧
      a₁ ∈ basisStab H e i ∧ a₂ ∈ basisStab H e i ∧ a₃ ∈ H ∧
      ∀ K : Subgroup (U ≃ₗ[ZMod p] U), basisStab H e i ≤ K → a₁ ∈ K → a₃ ∈ K → H ≤ K := by
  obtain ⟨σ, hσ⟩ := zs4d_exists_sigma (show Module.finrank (ZMod p) U - 1 = 3 by omega) i
  obtain ⟨f, hf, hf3⟩ := zs4d_exists_basis4 S hn σ
  obtain ⟨C, lam, hlC, hl, hC⟩ := zs4d_exists_lam_H hp S hd
  obtain ⟨a₁, h₁, h₁0, h₁1, h₁t, h₁3⟩ :=
    zs4d_lift_f hf hf3 hC (a := 0) (b := 1) (by decide) C.one_mem
  obtain ⟨a₂, h₂, h₂0, h₂1, h₂t, h₂3⟩ := zs4d_lift_f hf hf3 hC (a := 0) (b := 1) (by decide) hlC
  obtain ⟨a₃, h₃, h₃0, h₃1, h₃t, h₃3⟩ :=
    zs4d_lift_f hf hf3 hC (a := 1) (b := 2) (by decide) C.one_mem
  have hst : ∀ w ∈ H, w (f 2) = f 2 → w ∈ basisStab H e i := fun w hw h2 =>
    Subgroup.mem_inf.mpr ⟨hw, by
      show w (e i : U) = e i
      rw [← hσ, ← hf 2]
      exact h2⟩
  have hm₁ := zs4d_toMatrix_pij01 f h₁0 h₁1 (h₁t 2 (by decide) (by decide)) h₁3
  have hm₃ := zs4d_toMatrix_pij12 f (h₃t 0 (by decide) (by decide)) h₃0 h₃1 h₃3
  rw [Units.val_one] at hm₁ hm₃
  refine ⟨f, lam, a₁, a₂, a₃, hl, hm₁,
    zs4d_toMatrix_pij01 f h₂0 h₂1 (h₂t 2 (by decide) (by decide)) h₂3, hm₃,
    hst a₁ h₁ (h₁t 2 (by decide) (by decide)), hst a₂ h₂ (h₂t 2 (by decide) (by decide)), h₃,
    fun K hK h₁K h₃K => zs4d_le_of_fix hp S.splitSupport S.ne S.mono (by omega) S.reflGen_H hK
      fun m => ?_⟩
  obtain ⟨t, rfl⟩ := σ.surjective m
  rcases (by decide : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2) t with rfl | rfl | rfl
  · refine ⟨a₃ * a₁, H.mul_mem h₃ h₁, K.mul_mem h₃K h₁K, ?_⟩
    rw [← hσ, ← hf, ← hf, LinearEquiv.mul_apply, h₁0, map_smul, h₃0]
    simp
  · refine ⟨a₃, h₃, h₃K, ?_⟩
    rw [← hσ, ← hf, ← hf, h₃0]
    simp
  · exact ⟨1, H.one_mem, K.one_mem, by simp [hσ]⟩

omit [Module.Finite (ZMod p) U] in
private theorem zs4d_K_le (S : ImpExtStd G H d e j₀ j₁ ζ) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G)
    (i : Fin (Module.finrank (ZMod p) U - 1)) {a₁ a₂ a₃ : U ≃ₗ[ZMod p] U}
    (hs₁ : a₁ ∈ basisStab H e i) (hs₂ : a₂ ∈ basisStab H e i) (h₃ : a₃ ∈ H)
    (hle : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), basisStab H e i ≤ K → a₁ ∈ K → a₃ ∈ K → H ≤ K) :
    H ≤ Subgroup.closure {a₁, a₂, a₃} ⊔ Subgroup.closure (insert a (basisStab H e i : Set _)) ∧
      Subgroup.closure {a₁, a₂, a₃} ⊔ Subgroup.closure (insert a (basisStab H e i : Set _)) ≤
        G ∧
      Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) ≤
        Subgroup.closure {a₁, a₂, a₃} ⊔ Subgroup.closure (insert a (basisStab H e i : Set _)) := by
  set F := Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))
  have hKF : basisStab H e i ≤ F := fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem _ hh)
  have hcl : Subgroup.closure {a₁, a₂, a₃} ≤ Subgroup.closure {a₁, a₂, a₃} ⊔ F := le_sup_left
  have hHK : H ≤ Subgroup.closure {a₁, a₂, a₃} ⊔ F := hle _ (hKF.trans le_sup_right)
    (hcl (Subgroup.subset_closure (by simp))) (hcl (Subgroup.subset_closure (by simp)))
  refine ⟨hHK, sup_le ((Subgroup.closure_le _).mpr ?_) (zs4d_closure_le S ha i),
    (Subgroup.closure_le _).mpr (Set.insert_subset
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))) hHK)⟩
  rintro x (rfl | rfl | rfl)
  · exact S.H_le (Subgroup.mem_inf.mp hs₁).1
  · exact S.H_le (Subgroup.mem_inf.mp hs₂).1
  · exact S.H_le h₃

theorem exists_fourThreeData (hp : p ≠ 2) (S : ImpExtStd G H d e j₀ j₁ ζ) (I : ImpExtInputs G H)
    (hn : Module.finrank (ZMod p) U = 4) (hd : d = 5) (i : Fin (Module.finrank (ZMod p) U - 1))
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (har : IsRefl p a)
    (haH : ¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c)
    (hF : SplitSupport (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1))
    (h3 : H3Data p (movedGroup (Subgroup.closure (insert a (basisStab H e i : Set _))))) :
    ∃ (f : Module.Basis (Fin 4) (ZMod p) U) (lam : (ZMod p)ˣ) (a₁ a₂ a₃ : U ≃ₗ[ZMod p] U)
      (K : Subgroup (U ≃ₗ[ZMod p] U)), FourThreeData f lam a₁ a₂ a₃ a K
        (Subgroup.closure (insert a (basisStab H e i : Set (U ≃ₗ[ZMod p] U)))) := by
  obtain ⟨f, lam, a₁, a₂, a₃, hl, hm₁, hm₂, hm₃, hs₁, hs₂, h₃, hle⟩ := zs4d_frame hp S hn hd i
  obtain ⟨hHK, hKG, haK⟩ := zs4d_K_le S ha i hs₁ hs₂ h₃ hle
  have hL : Module.finrank (ZMod p) U - 1 = 3 := by omega
  have hKF : basisStab H e i ≤ Subgroup.closure (insert a (basisStab H e i : Set _)) :=
    fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem _ hh)
  have h14 : SplitOfIrred p G 3 := by
    rw [← hL]
    exact I.splitOfIrred
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := S.dmax_H.2
  subst hd
  exact ⟨f, lam, a₁, a₂, a₃, _,
    { orderOf_lam := hl, toMatrix_a₁ := hm₁, toMatrix_a₂ := hm₂, toMatrix_a₃ := hm₃
      isRefl_a₄ := har, eq_K := rfl
      irred := fun W hW => I.lemmaOneSeven a ha har haH W fun g hg => hW g (haK hg)
      transvectionFree := fun g hg => S.transvectionFree g (hKG hg)
      dmax := ⟨fun x hx y hy hxr hyr => S.dmax.1 x (hKG hx) y (hKG hy) hxr hyr,
        x, hHK hx, y, hHK hy, hxr, hyr, hxy⟩
      a₁_mem := hKF hs₁, a₂_mem := hKF hs₂
      a₄_mem := Subgroup.subset_closure (Set.mem_insert _ _)
      splitSupport_F := ⟨hF.1, hF.2.1.trans hL, hF.2.2⟩, h3 := h3
      splitOfIrred := fun X hX => h14 X (hX.trans hKG)
      noOrth := fun X hX hXr hXs =>
        S.noOrth X (hX.trans hKG) hXr ⟨hXs.1, hXs.2.1.trans hL.symm, hXs.2.2⟩
      negOfPrim := I.negOfPrim }⟩

end ImpExtStd

end CFSG.StandardType.ZS

end
