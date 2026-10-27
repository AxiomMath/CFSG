module

public import CFSG.LieType.RootSystem.Cartan
public import CFSG.LieType.RootSystem.Form
public import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType.CoxTriple

open CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.OfCartan

@[expose] def coxRefl {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) : (coxeterMatrix hC).Group :=
  g * (coxeterMatrix hC).simple i * g⁻¹

@[expose] noncomputable def coxRoot {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) : I → ℤ :=
  weylAction hC g (Pi.single i 1)

@[expose] noncomputable def coxPairing {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (v w : I → ℤ) : ℚ :=
  2 * form hC (toRat v) (toRat w) / form hC (toRat w) (toRat w)

private theorem ct_pr_coxPairing_eq_coroot
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) (v : I → ℤ) :
    ((coroot C i (weylAction hC g⁻¹ v) : ℤ) : ℚ) = coxPairing hC v (coxRoot hC g i) := by
  have hρ : coxRoot hC g i = weylAction hC g (Pi.single i 1) := rfl
  have hBne : form hC (toRat (coxRoot hC g i)) (toRat (coxRoot hC g i)) ≠ 0 :=
    (form_pos hC (toRat_weylAction_single_ne_zero hC g i)).ne'
  have hself : ((coroot C i (weylAction hC g⁻¹ v) : ℤ) : ℚ) *
      form hC (toRat (coxRoot hC g i)) (toRat (coxRoot hC g i)) =
      2 * form hC (toRat v) (toRat (coxRoot hC g i)) := by
    have h := coroot_mul_form_self hC g i v
    rw [hρ]
    rwa [form_comm hC (toRat (weylAction hC g (Pi.single i 1))) (toRat v)] at h
  rw [coxPairing, eq_div_iff hBne]
  exact hself

theorem toRat_weylAction_coxRefl
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) (v : I → ℤ) :
    toRat (weylAction hC (coxRefl hC g i) v) =
      toRat v - coxPairing hC v (coxRoot hC g i) • toRat (coxRoot hC g i) := by
  have hconj := weylAction_conj_simple hC g i v
  have hc := ct_pr_coxPairing_eq_coroot hC g i v
  have h : weylAction hC (g * (coxeterMatrix hC).toCoxeterSystem.simple i * g⁻¹) v =
      v - coroot C i (weylAction hC g⁻¹ v) • coxRoot hC g i := hconj
  change toRat (weylAction hC (g * (coxeterMatrix hC).toCoxeterSystem.simple i * g⁻¹) v) =
    toRat v - coxPairing hC v (coxRoot hC g i) • toRat (coxRoot hC g i)
  rw [h, map_sub, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, hc]

theorem exists_int_coxPairing
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) (v : I → ℤ) :
    ∃ n : ℤ, (n : ℚ) = coxPairing hC v (coxRoot hC g i) :=
  ⟨_, ct_pr_coxPairing_eq_coroot hC g i v⟩

private theorem ct_pr_pairing_mul_eq_zero_or_one_or_two_or_three
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I)
    (hnp : ¬ ∃ q : ℚ, toRat (coxRoot hC h j) = q • toRat (coxRoot hC g i)) :
    ∃ a b : ℤ,
      (a : ℚ) = coxPairing hC (coxRoot hC h j) (coxRoot hC g i) ∧
      (b : ℚ) = coxPairing hC (coxRoot hC g i) (coxRoot hC h j) ∧
      (a * b = 0 ∨ a * b = 1 ∨ a * b = 2 ∨ a * b = 3) := by
  obtain ⟨a, ha⟩ := exists_int_coxPairing hC g i (coxRoot hC h j)
  obtain ⟨b, hb⟩ := exists_int_coxPairing hC h j (coxRoot hC g i)
  set ρ := coxRoot hC g i
  set σ := coxRoot hC h j
  have hρ0 : toRat ρ ≠ 0 := toRat_weylAction_single_ne_zero hC g i
  have hσ0 : toRat σ ≠ 0 := toRat_weylAction_single_ne_zero hC h j
  have hnp' : ∀ t : ℚ, toRat σ ≠ t • toRat ρ := by
    simpa only [not_exists] using hnp
  have hxy : ∀ t : ℚ, toRat ρ ≠ t • toRat σ := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, zero_smul] at ht
      exact (hρ0 ht).elim
    · exact hnp' t⁻¹ (by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul])
  have hBρne : form hC (toRat ρ) (toRat ρ) ≠ 0 := (form_pos hC hρ0).ne'
  have hBσne : form hC (toRat σ) (toRat σ) ≠ 0 := (form_pos hC hσ0).ne'
  have ha' : (a : ℚ) * form hC (toRat ρ) (toRat ρ) = 2 * form hC (toRat ρ) (toRat σ) := by
    rw [ha, coxPairing, div_mul_cancel₀ _ hBρne, form_comm hC (toRat σ) (toRat ρ)]
  have hb' : (b : ℚ) * form hC (toRat σ) (toRat σ) = 2 * form hC (toRat ρ) (toRat σ) := by
    rw [hb, coxPairing, div_mul_cancel₀ _ hBσne]
  have hlt : a * b < 4 := mul_lt_four hC hρ0 hσ0 hxy ha' hb'
  have hge : 0 ≤ a * b := by
    have hfac : (a : ℚ) * form hC (toRat ρ) (toRat ρ) *
          ((b : ℚ) * form hC (toRat σ) (toRat σ)) =
        ((a : ℚ) * b) *
          (form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ)) := by ring
    have hmul : ((a : ℚ) * b) *
          (form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ)) =
        4 * form hC (toRat ρ) (toRat σ) ^ 2 := by
      rw [← hfac, ha', hb']
      ring
    have hpos : 0 < form hC (toRat ρ) (toRat ρ) * form hC (toRat σ) (toRat σ) :=
      mul_pos (form_pos hC hρ0) (form_pos hC hσ0)
    have : 0 ≤ (a : ℚ) * b := by
      nlinarith [hmul, hpos, sq_nonneg (form hC (toRat ρ) (toRat σ))]
    exact_mod_cast this
  have hab : a * b = 0 ∨ a * b = 1 ∨ a * b = 2 ∨ a * b = 3 := by omega
  exact ⟨a, b, ha, hb, hab⟩

theorem coxPairing_mul_cases
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I)
    (hnp : ¬ ∃ q : ℚ, toRat (coxRoot hC h j) = q • toRat (coxRoot hC g i)) :
    coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 0 ∨
    coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 1 ∨
    coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 2 ∨
    coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 3 := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    ct_pr_pairing_mul_eq_zero_or_one_or_two_or_three hC g h i j hnp
  rcases hab with h | h | h | h
  · left
    rw [← ha, ← hb, ← Int.cast_mul, h]
    norm_num
  · right; left
    rw [← ha, ← hb, ← Int.cast_mul, h]
    norm_num
  · right; right; left
    rw [← ha, ← hb, ← Int.cast_mul, h]
    norm_num
  · right; right; right
    rw [← ha, ← hb, ← Int.cast_mul, h]
    norm_num

private theorem ct_pr_pow_sub_mem_span {V : Type*} [AddCommGroup V] [Module ℤ V]
    (F : Module.End ℤ V) (S : Submodule ℤ V)
    (hmaps : ∀ s ∈ S, F s ∈ S) (hsub : ∀ v : V, F v - v ∈ S) (k : ℕ) (v : V) :
    (F ^ k) v - v ∈ S := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (F ^ (k + 1)) v - v = F ((F ^ k) v - v) + (F v - v) := by
      rw [pow_succ']
      simp only [Module.End.mul_apply, map_sub]
      abel
    rw [h]
    exact S.add_mem (hmaps _ ih) (hsub v)

private theorem ct_pr_weylAction_pow_fixes_span
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ρ σ : I → ℤ) (k : ℕ)
    (hfixρ : weylAction hC (t ^ k) ρ = ρ)
    (hfixσ : weylAction hC (t ^ k) σ = σ) :
    ∀ s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)), weylAction hC (t ^ k) s = s := by
  intro s hs
  refine Submodule.span_induction (p := fun x _ => weylAction hC (t ^ k) x = x)
    ?_ ?_ ?_ ?_ hs
  · intro x hx
    rcases hx with rfl | rfl
    · exact hfixρ
    · exact hfixσ
  · simp
  · intro x y hx hy ihx ihy
    rw [map_add, ihx, ihy]
  · intro c x hx ih
    rw [map_smul, ih]

private theorem ct_pr_weylAction_pow_sub_mem_span
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ρ σ : I → ℤ) (k : ℕ)
    (hsub : ∀ v : I → ℤ,
      weylAction hC t v - v ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ))) (v : I → ℤ) :
    weylAction hC (t ^ k) v - v ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)) := by
  have hmaps : ∀ s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)),
      weylAction hC t s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)) := by
    intro s hs
    have h : weylAction hC t s = s + (weylAction hC t s - s) := by abel
    rw [h]
    exact Submodule.add_mem _ hs (hsub s)
  have h := ct_pr_pow_sub_mem_span (weylAction hC t)
    (Submodule.span ℤ ({ρ, σ} : Set (I → ℤ))) hmaps hsub k v
  simpa only [map_pow] using h

private theorem ct_pr_weylAction_pow_orthogonal
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ρ σ : I → ℤ) (k : ℕ)
    (hfix : ∀ s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)),
      weylAction hC (t ^ k) s = s) :
    ∀ v : I → ℤ, ∀ s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)),
      form hC (toRat (weylAction hC (t ^ k) v - v)) (toRat s) = 0 := by
  intro v s hs
  have hinvfix : ∀ s ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)),
      weylAction hC ((t⁻¹) ^ k) s = s := by
    intro s hs
    have h1 : weylAction hC ((t⁻¹) ^ k) (weylAction hC (t ^ k) s) = s := by
      rw [← weylAction_mul_apply, inv_pow, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hfix s hs] at h1
    exact h1
  have hTk_inv_smul : ∀ x : I → ℤ,
      weylAction hC (t ^ k) (weylAction hC ((t⁻¹) ^ k) x) = x := by
    intro x
    rw [← weylAction_mul_apply, inv_pow, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : form hC (toRat (weylAction hC (t ^ k) v)) (toRat s) =
      form hC (toRat v) (toRat (weylAction hC ((t⁻¹) ^ k) s)) := by
    have h3 := form_weylAction hC (t ^ k) v (weylAction hC ((t⁻¹) ^ k) s)
    rwa [hTk_inv_smul s] at h3
  have hsplit : form hC (toRat (weylAction hC (t ^ k) v - v)) (toRat s) =
      form hC (toRat (weylAction hC (t ^ k) v)) (toRat s) -
        form hC (toRat v) (toRat s) := by
    rw [map_sub, map_sub, LinearMap.sub_apply]
  rw [hsplit, h2, hinvfix s hs, sub_self]

private theorem ct_pr_weylAction_pow_eq_one_of_fixes_span {I : Type} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ρ σ : I → ℤ) (k : ℕ)
    (hsub : ∀ v : I → ℤ,
      weylAction hC t v - v ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hfixρ : weylAction hC (t ^ k) ρ = ρ)
    (hfixσ : weylAction hC (t ^ k) σ = σ) :
    weylAction hC (t ^ k) = 1 := by
  have hfix := ct_pr_weylAction_pow_fixes_span hC t ρ σ k hfixρ hfixσ
  have horth := ct_pr_weylAction_pow_orthogonal hC t ρ σ k hfix
  have hfinal : ∀ v : I → ℤ, weylAction hC (t ^ k) v = v := by
    intro v
    have hy := ct_pr_weylAction_pow_sub_mem_span hC t ρ σ k hsub v
    by_contra hv
    have hne : toRat (weylAction hC (t ^ k) v - v) ≠ 0 := fun h =>
      (sub_ne_zero.mpr hv) (toRat_injective (by simpa using h))
    have hpos := form_pos hC hne
    have hzero := horth v _ hy
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℚ)) hpos
  apply LinearMap.ext
  intro v
  exact hfinal v

private theorem ct_pr_coxRefl_apply
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) (x : I → ℤ) :
    weylAction hC (coxRefl hC g i) x =
      x - (coroot C i (weylAction hC g⁻¹ x)) • coxRoot hC g i := by
  simpa only [coxRefl, coxRoot, CoxeterMatrix.toCoxeterSystem_simple] using
    weylAction_conj_simple hC g i x

private theorem ct_pr_coroot_weylAction_inv_coxRoot
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) :
    coroot C i (weylAction hC g⁻¹ (coxRoot hC g i)) = 2 := by
  have h : weylAction hC g⁻¹ (coxRoot hC g i) = Pi.single i 1 := by
    change weylAction hC g⁻¹ (weylAction hC g (Pi.single i 1)) = Pi.single i 1
    rw [weylAction_inv_apply_apply]
  rw [h, coroot_single, hC.apply_self]

private theorem ct_pr_coxRefl_mul_apply_left
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) (a b : ℤ)
    (ha : a = coroot C i (weylAction hC g⁻¹ (coxRoot hC h j)))
    (hb : b = coroot C j (weylAction hC h⁻¹ (coxRoot hC g i))) :
    weylAction hC (coxRefl hC g i * coxRefl hC h j) (coxRoot hC g i) =
      (a * b - 1) • coxRoot hC g i - b • coxRoot hC h j := by
  rw [ha, hb]
  set ρ : I → ℤ := coxRoot hC g i
  set σ : I → ℤ := coxRoot hC h j
  let n1 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C i).comp (weylAction hC g⁻¹)
  let n2 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C j).comp (weylAction hC h⁻¹)
  change weylAction hC (coxRefl hC g i * coxRefl hC h j) ρ =
    (n1 σ * n2 ρ - 1) • ρ - n2 ρ • σ
  have hSρ : ∀ x : I → ℤ, weylAction hC (coxRefl hC g i) x = x - n1 x • ρ := by
    intro x
    rw [ct_pr_coxRefl_apply hC g i x]
    rfl
  have hSσ : ∀ x : I → ℤ, weylAction hC (coxRefl hC h j) x = x - n2 x • σ := by
    intro x
    rw [ct_pr_coxRefl_apply hC h j x]
    rfl
  have hn1ρ : n1 ρ = 2 := ct_pr_coroot_weylAction_inv_coxRoot hC g i
  have hn1σ : n1 σ = coroot C i (weylAction hC g⁻¹ σ) := rfl
  have hn2ρ : n2 ρ = coroot C j (weylAction hC h⁻¹ ρ) := rfl
  rw [weylAction_mul_apply, hSσ, hSρ]
  simp only [map_sub, map_smul, hn1ρ, hn1σ, hn2ρ, smul_eq_mul]
  module

private theorem ct_pr_coxRefl_mul_apply_right
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) (a : ℤ)
    (ha : a = coroot C i (weylAction hC g⁻¹ (coxRoot hC h j))) :
    weylAction hC (coxRefl hC g i * coxRefl hC h j) (coxRoot hC h j) =
      a • coxRoot hC g i - coxRoot hC h j := by
  rw [ha]
  set ρ : I → ℤ := coxRoot hC g i
  set σ : I → ℤ := coxRoot hC h j
  let n1 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C i).comp (weylAction hC g⁻¹)
  let n2 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C j).comp (weylAction hC h⁻¹)
  change weylAction hC (coxRefl hC g i * coxRefl hC h j) σ = n1 σ • ρ - σ
  have hSρ : ∀ x : I → ℤ, weylAction hC (coxRefl hC g i) x = x - n1 x • ρ := by
    intro x
    rw [ct_pr_coxRefl_apply hC g i x]
    rfl
  have hSσ : ∀ x : I → ℤ, weylAction hC (coxRefl hC h j) x = x - n2 x • σ := by
    intro x
    rw [ct_pr_coxRefl_apply hC h j x]
    rfl
  have hn1σ : n1 σ = coroot C i (weylAction hC g⁻¹ σ) := rfl
  have hn2σ : n2 σ = 2 := ct_pr_coroot_weylAction_inv_coxRoot hC h j
  rw [weylAction_mul_apply, hSσ, hSρ]
  simp only [map_sub, map_smul, hn2σ, hn1σ, smul_eq_mul]
  module

private theorem ct_pr_coxRefl_mul_apply_left_two
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) (a b : ℤ)
    (ha : a = coroot C i (weylAction hC g⁻¹ (coxRoot hC h j)))
    (hb : b = coroot C j (weylAction hC h⁻¹ (coxRoot hC g i))) :
    weylAction hC (coxRefl hC g i * coxRefl hC h j)
        (weylAction hC (coxRefl hC g i * coxRefl hC h j) (coxRoot hC g i)) =
      ((a * b - 1) ^ 2 - a * b) • coxRoot hC g i +
        (b * (2 - a * b)) • coxRoot hC h j := by
  rw [ct_pr_coxRefl_mul_apply_left hC g h i j a b ha hb]
  simp only [map_sub, map_smul]
  rw [ct_pr_coxRefl_mul_apply_left hC g h i j a b ha hb,
    ct_pr_coxRefl_mul_apply_right hC g h i j a ha]
  module

private theorem ct_pr_coxRefl_mul_apply_right_two
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) (a b : ℤ)
    (ha : a = coroot C i (weylAction hC g⁻¹ (coxRoot hC h j)))
    (hb : b = coroot C j (weylAction hC h⁻¹ (coxRoot hC g i))) :
    weylAction hC (coxRefl hC g i * coxRefl hC h j)
        (weylAction hC (coxRefl hC g i * coxRefl hC h j) (coxRoot hC h j)) =
      (a * (a * b - 2)) • coxRoot hC g i + (1 - a * b) • coxRoot hC h j := by
  rw [ct_pr_coxRefl_mul_apply_right hC g h i j a ha]
  simp only [map_sub, map_smul]
  rw [ct_pr_coxRefl_mul_apply_left hC g h i j a b ha hb,
    ct_pr_coxRefl_mul_apply_right hC g h i j a ha]
  module

private theorem ct_pr_coxRefl_mul_span
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) :
    ∀ x : I → ℤ,
      weylAction hC (coxRefl hC g i * coxRefl hC h j) x - x ∈
        Submodule.span ℤ ({coxRoot hC g i, coxRoot hC h j} : Set (I → ℤ)) := by
  intro x
  set ρ : I → ℤ := coxRoot hC g i
  set σ : I → ℤ := coxRoot hC h j
  let n1 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C i).comp (weylAction hC g⁻¹)
  let n2 : (I → ℤ) →ₗ[ℤ] ℤ := (coroot C j).comp (weylAction hC h⁻¹)
  have hSρ : ∀ y : I → ℤ, weylAction hC (coxRefl hC g i) y = y - n1 y • ρ := by
    intro y
    rw [ct_pr_coxRefl_apply hC g i y]
    rfl
  have hSσ : ∀ y : I → ℤ, weylAction hC (coxRefl hC h j) y = y - n2 y • σ := by
    intro y
    rw [ct_pr_coxRefl_apply hC h j y]
    rfl
  rw [weylAction_mul_apply]
  have e1 : weylAction hC (coxRefl hC h j) x - x = -(n2 x) • σ := by
    rw [hSσ]; module
  have e2 : weylAction hC (coxRefl hC g i) (weylAction hC (coxRefl hC h j) x) -
        weylAction hC (coxRefl hC h j) x =
      -(n1 (weylAction hC (coxRefl hC h j) x)) • ρ := by
    rw [hSρ]; module
  have e3 : weylAction hC (coxRefl hC g i) (weylAction hC (coxRefl hC h j) x) - x =
      (weylAction hC (coxRefl hC g i) (weylAction hC (coxRefl hC h j) x) -
        weylAction hC (coxRefl hC h j) x) +
      (weylAction hC (coxRefl hC h j) x - x) := by abel
  rw [e3, e2, e1]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem ct_pr_pairing_mul_zero
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (a b : ℤ)
    (hBρne : form hC (toRat ρ) (toRat ρ) ≠ 0)
    (hBσne : form hC (toRat σ) (toRat σ) ≠ 0)
    (ha' : (a : ℚ) * form hC (toRat ρ) (toRat ρ) =
      2 * form hC (toRat ρ) (toRat σ))
    (hb' : (b : ℚ) * form hC (toRat σ) (toRat σ) =
      2 * form hC (toRat ρ) (toRat σ))
    (hab : a * b = 0) :
    form hC (toRat ρ) (toRat σ) = 0 ∧ a = 0 ∧ b = 0 := by
  have hcross : form hC (toRat ρ) (toRat σ) = 0 := by
    have hq : (a : ℚ) * (b : ℚ) = 0 := by
      rw [← Int.cast_mul, hab]; norm_num
    rcases mul_eq_zero.mp hq with ha0 | hb0
    · have := ha'
      rw [ha0] at this
      linarith
    · have := hb'
      rw [hb0] at this
      linarith
  have ha0 : a = 0 := by
    have h : (a : ℚ) = 0 := by
      have h1 : (a : ℚ) * form hC (toRat ρ) (toRat ρ) = 0 := by
        rw [hcross] at ha'
        simpa using ha'
      exact (mul_eq_zero.mp h1).resolve_right hBρne
    exact_mod_cast h
  have hb0 : b = 0 := by
    have h : (b : ℚ) = 0 := by
      have h1 : (b : ℚ) * form hC (toRat σ) (toRat σ) = 0 := by
        rw [hcross] at hb'
        simpa using hb'
      exact (mul_eq_zero.mp h1).resolve_right hBσne
    exact_mod_cast h
  exact ⟨hcross, ha0, hb0⟩

private theorem ct_pr_int_mul_of_pairing_mul
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (a b n : ℤ)
    (ha : (a : ℚ) = coxPairing hC σ ρ)
    (hb : (b : ℚ) = coxPairing hC ρ σ)
    (hp : coxPairing hC σ ρ * coxPairing hC ρ σ = (n : ℚ)) :
    a * b = n := by
  have h : ((a * b : ℤ) : ℚ) = (n : ℚ) := by
    rw [Int.cast_mul, ha, hb, hp]
  exact_mod_cast h

private theorem ct_pr_coxRefl_mul_setup
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I)
    (hnp : ¬ ∃ q : ℚ, toRat (coxRoot hC h j) = q • toRat (coxRoot hC g i)) :
    ∃ (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ),
      ρ = coxRoot hC g i ∧ σ = coxRoot hC h j ∧
      t = coxRefl hC g i * coxRefl hC h j ∧
      (a : ℚ) = coxPairing hC σ ρ ∧ (b : ℚ) = coxPairing hC ρ σ ∧
      weylAction hC t ρ = (a * b - 1) • ρ - b • σ ∧
      weylAction hC t σ = a • ρ - σ ∧
      weylAction hC t (weylAction hC t ρ) =
        ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ ∧
      weylAction hC t (weylAction hC t σ) =
        (a * (a * b - 2)) • ρ + (1 - a * b) • σ ∧
      (∀ x : I → ℤ, weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ))) ∧
      (∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1) ∧
      toRat ρ ≠ 0 ∧ toRat σ ≠ 0 ∧
      (∀ q : ℚ, toRat σ ≠ q • toRat ρ) ∧
      form hC (toRat ρ) (toRat ρ) ≠ 0 ∧
      form hC (toRat σ) (toRat σ) ≠ 0 ∧
      (a : ℚ) * form hC (toRat ρ) (toRat ρ) = 2 * form hC (toRat ρ) (toRat σ) ∧
      (b : ℚ) * form hC (toRat σ) (toRat σ) = 2 * form hC (toRat ρ) (toRat σ) := by
  classical
  let ρ : I → ℤ := coxRoot hC g i
  let σ : I → ℤ := coxRoot hC h j
  let t : (coxeterMatrix hC).Group := coxRefl hC g i * coxRefl hC h j
  let a : ℤ := coroot C i (weylAction hC g⁻¹ σ)
  let b : ℤ := coroot C j (weylAction hC h⁻¹ ρ)
  have ha_def : a = coroot C i (weylAction hC g⁻¹ σ) := rfl
  have hb_def : b = coroot C j (weylAction hC h⁻¹ ρ) := rfl
  have ha : (a : ℚ) = coxPairing hC σ ρ := ct_pr_coxPairing_eq_coroot hC g i σ
  have hb : (b : ℚ) = coxPairing hC ρ σ := ct_pr_coxPairing_eq_coroot hC h j ρ
  have hTmρ : weylAction hC t ρ = (a * b - 1) • ρ - b • σ :=
    ct_pr_coxRefl_mul_apply_left hC g h i j a b ha_def hb_def
  have hTmσ : weylAction hC t σ = a • ρ - σ :=
    ct_pr_coxRefl_mul_apply_right hC g h i j a ha_def
  have hT2ρ : weylAction hC t (weylAction hC t ρ) =
      ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ :=
    ct_pr_coxRefl_mul_apply_left_two hC g h i j a b ha_def hb_def
  have hT2σ : weylAction hC t (weylAction hC t σ) =
      (a * (a * b - 2)) • ρ + (1 - a * b) • σ :=
    ct_pr_coxRefl_mul_apply_right_two hC g h i j a b ha_def hb_def
  have hspan : ∀ x : I → ℤ,
      weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)) :=
    ct_pr_coxRefl_mul_span hC g h i j
  have hcyc : ∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1 := by
    intro k h1
    exact weylAction_injective hC (by simpa only [map_pow, map_one] using h1)
  have hρ0 : toRat ρ ≠ 0 := toRat_weylAction_single_ne_zero hC g i
  have hσ0 : toRat σ ≠ 0 := toRat_weylAction_single_ne_zero hC h j
  have hnp' : ∀ q : ℚ, toRat σ ≠ q • toRat ρ := by
    simpa only [not_exists] using hnp
  have hBρne : form hC (toRat ρ) (toRat ρ) ≠ 0 := (form_pos hC hρ0).ne'
  have hBσne : form hC (toRat σ) (toRat σ) ≠ 0 := (form_pos hC hσ0).ne'
  have ha' : (a : ℚ) * form hC (toRat ρ) (toRat ρ) =
      2 * form hC (toRat ρ) (toRat σ) := by
    rw [ha, coxPairing, div_mul_cancel₀ _ hBρne, form_comm hC (toRat σ) (toRat ρ)]
  have hb' : (b : ℚ) * form hC (toRat σ) (toRat σ) =
      2 * form hC (toRat ρ) (toRat σ) := by
    rw [hb, coxPairing, div_mul_cancel₀ _ hBσne]
  exact ⟨ρ, σ, t, a, b, rfl, rfl, rfl, ha, hb, hTmρ, hTmσ, hT2ρ, hT2σ, hspan,
    hcyc, hρ0, hσ0, hnp', hBρne, hBσne, ha', hb'⟩

private theorem ct_pr_order_two
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ)
    (hab : a * b = 0)
    (hTmρ : weylAction hC t ρ = (a * b - 1) • ρ - b • σ)
    (hT2ρ : weylAction hC t (weylAction hC t ρ) =
      ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ)
    (hT2σ : weylAction hC t (weylAction hC t σ) =
      (a * (a * b - 2)) • ρ + (1 - a * b) • σ)
    (hspan : ∀ x : I → ℤ, weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hcyc : ∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1)
    (hρ0 : toRat ρ ≠ 0)
    (hBρne : form hC (toRat ρ) (toRat ρ) ≠ 0)
    (hBσne : form hC (toRat σ) (toRat σ) ≠ 0)
    (ha' : (a : ℚ) * form hC (toRat ρ) (toRat ρ) =
      2 * form hC (toRat ρ) (toRat σ))
    (hb' : (b : ℚ) * form hC (toRat σ) (toRat σ) =
      2 * form hC (toRat ρ) (toRat σ)) :
    orderOf t = 2 := by
  obtain ⟨_, ha0, hb0⟩ :=
    ct_pr_pairing_mul_zero hC ρ σ a b hBρne hBσne ha' hb' hab
  have hT2ρ' : weylAction hC t (weylAction hC t ρ) = ρ := by
    rw [hT2ρ, hab, hb0]; module
  have hT2σ' : weylAction hC t (weylAction hC t σ) = σ := by
    rw [hT2σ, hab, ha0]; module
  have hfixρ : weylAction hC (t ^ 2) ρ = ρ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 2) ρ = ρ
    rw [pow_two, Module.End.mul_apply, hT2ρ']
  have hfixσ : weylAction hC (t ^ 2) σ = σ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 2) σ = σ
    rw [pow_two, Module.End.mul_apply, hT2σ']
  have h1 : weylAction hC (t ^ 2) = 1 :=
    ct_pr_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 2 hspan hfixρ hfixσ
  have ht2 : t ^ 2 = 1 := hcyc 2 h1
  have htne : t ≠ 1 := by
    intro h1t
    have hρeq : weylAction hC t ρ = ρ := by
      rw [h1t, map_one, Module.End.one_apply]
    rw [hTmρ, hab, hb0] at hρeq
    have hx : -toRat ρ = toRat ρ := by simpa using congrArg toRat hρeq
    have hzero : toRat ρ = 0 := by
      ext k
      exact CharZero.neg_eq_self_iff.mp (congrFun hx k)
    exact hρ0 hzero
  exact orderOf_eq_prime ht2 htne

private theorem ct_pr_order_three
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ)
    (hab : a * b = 1)
    (hTmρ : weylAction hC t ρ = (a * b - 1) • ρ - b • σ)
    (hTmσ : weylAction hC t σ = a • ρ - σ)
    (hT2ρ : weylAction hC t (weylAction hC t ρ) =
      ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ)
    (hT2σ : weylAction hC t (weylAction hC t σ) =
      (a * (a * b - 2)) • ρ + (1 - a * b) • σ)
    (hspan : ∀ x : I → ℤ, weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hcyc : ∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1)
    (hnp' : ∀ q : ℚ, toRat σ ≠ q • toRat ρ) :
    orderOf t = 3 := by
  have hT2ρ' : weylAction hC t (weylAction hC t ρ) = -ρ + b • σ := by
    rw [hT2ρ, hab]; module
  have hT2σ' : weylAction hC t (weylAction hC t σ) = -a • ρ := by
    rw [hT2σ, hab]; module
  have hba : b * a = 1 := by rw [mul_comm, hab]
  have hTmρ1 : weylAction hC t ρ = -b • σ := by rw [hTmρ, hab]; module
  have hT3ρ : weylAction hC t (weylAction hC t (weylAction hC t ρ)) = ρ := by
    rw [hT2ρ', map_add, map_neg, map_smul, hTmρ1, hTmσ]
    simp only [smul_sub, smul_smul, hba]
    module
  have hT3σ : weylAction hC t (weylAction hC t (weylAction hC t σ)) = σ := by
    calc weylAction hC t (weylAction hC t (weylAction hC t σ)) =
        weylAction hC t (-a • ρ) := by rw [hT2σ']
      _ = -a • weylAction hC t ρ := by rw [map_smul]
      _ = -a • (-b • σ) := by rw [hTmρ1]
      _ = (-a * -b) • σ := by rw [smul_smul]
      _ = (a * b) • σ := by rw [show -a * -b = a * b by ring]
      _ = σ := by rw [hab, one_smul]
  have hfixρ : weylAction hC (t ^ 3) ρ = ρ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 3) ρ = ρ
    rw [show ((weylAction hC t) ^ 3) = (weylAction hC t) * (weylAction hC t) *
        (weylAction hC t) by rw [pow_succ, pow_two],
      Module.End.mul_apply, Module.End.mul_apply, hT3ρ]
  have hfixσ : weylAction hC (t ^ 3) σ = σ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 3) σ = σ
    rw [show ((weylAction hC t) ^ 3) = (weylAction hC t) * (weylAction hC t) *
        (weylAction hC t) by rw [pow_succ, pow_two],
      Module.End.mul_apply, Module.End.mul_apply, hT3σ]
  have h1 : weylAction hC (t ^ 3) = 1 :=
    ct_pr_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 3 hspan hfixρ hfixσ
  have ht3 : t ^ 3 = 1 := hcyc 3 h1
  have hb0 : b ≠ 0 := by intro h0; rw [h0, mul_zero] at hab; norm_num at hab
  have htne : t ≠ 1 := by
    intro h1t
    have hρeq : weylAction hC t ρ = ρ := by
      rw [h1t, map_one, Module.End.one_apply]
    rw [hTmρ, hab] at hρeq
    simp only [sub_self, zero_smul, zero_sub] at hρeq
    have hx : (-(b : ℚ)) • toRat σ = toRat ρ := by
      simpa only [map_neg, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, neg_smul] using
        congrArg toRat hρeq
    refine hnp' (-(b : ℚ))⁻¹ ?_
    rw [← hx, smul_smul, inv_mul_cancel₀ ?_, one_smul]
    exact neg_ne_zero.mpr (by exact_mod_cast hb0)
  exact orderOf_eq_prime ht3 htne

private theorem ct_pr_order_four
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ)
    (hab : a * b = 2)
    (hT2ρ : weylAction hC t (weylAction hC t ρ) =
      ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ)
    (hT2σ : weylAction hC t (weylAction hC t σ) =
      (a * (a * b - 2)) • ρ + (1 - a * b) • σ)
    (hspan : ∀ x : I → ℤ, weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hcyc : ∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1)
    (hρ0 : toRat ρ ≠ 0) :
    orderOf t = 4 := by
  have hT2ρ' : weylAction hC t (weylAction hC t ρ) = -ρ := by
    rw [hT2ρ, hab]; module
  have hT2σ' : weylAction hC t (weylAction hC t σ) = -σ := by
    rw [hT2σ, hab]; module
  have hpow2ρ : ((weylAction hC t) ^ 2) ρ = -ρ := by
    rw [pow_two, Module.End.mul_apply]; exact hT2ρ'
  have hpow2σ : ((weylAction hC t) ^ 2) σ = -σ := by
    rw [pow_two, Module.End.mul_apply]; exact hT2σ'
  have hfixρ : weylAction hC (t ^ 4) ρ = ρ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 4) ρ = ρ
    rw [show ((weylAction hC t) ^ 4) = (weylAction hC t) ^ 2 * (weylAction hC t) ^ 2 by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
      Module.End.mul_apply, hpow2ρ, map_neg, hpow2ρ, neg_neg]
  have hfixσ : weylAction hC (t ^ 4) σ = σ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 4) σ = σ
    rw [show ((weylAction hC t) ^ 4) = (weylAction hC t) ^ 2 * (weylAction hC t) ^ 2 by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add],
      Module.End.mul_apply, hpow2σ, map_neg, hpow2σ, neg_neg]
  have h1 : weylAction hC (t ^ 4) = 1 :=
    ct_pr_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 4 hspan hfixρ hfixσ
  have ht4 : t ^ 4 = 1 := hcyc 4 h1
  have ht2ne : t ^ 2 ≠ 1 := by
    intro h2t
    have hw : ((weylAction hC t) ^ 2) = 1 := by rw [← map_pow, h2t, map_one]
    have hρeq : ((weylAction hC t) ^ 2) ρ = ρ := by
      rw [hw, Module.End.one_apply]
    rw [hpow2ρ] at hρeq
    have hx : -toRat ρ = toRat ρ := by simpa using congrArg toRat hρeq
    have hzero : toRat ρ = 0 := by
      ext k
      exact CharZero.neg_eq_self_iff.mp (congrFun hx k)
    exact hρ0 hzero
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 4) (by norm_num) ht4 ?_
  intro p hp hpd
  have hpd2 : p ∣ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hpd
    exact hp.dvd_of_dvd_pow hpd
  have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hpd2
  subst hpe
  norm_num
  exact ht2ne

private theorem ct_pr_pow_six_of_pairing_three
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ)
    (hab : a * b = 3)
    (hTmρ : weylAction hC t ρ = (a * b - 1) • ρ - b • σ)
    (hTmσ : weylAction hC t σ = a • ρ - σ)
    (hT2ρ : weylAction hC t (weylAction hC t ρ) =
      ((a * b - 1) ^ 2 - a * b) • ρ + (b * (2 - a * b)) • σ)
    (hT2σ : weylAction hC t (weylAction hC t σ) =
      (a * (a * b - 2)) • ρ + (1 - a * b) • σ)
    (hspan : ∀ x : I → ℤ, weylAction hC t x - x ∈ Submodule.span ℤ ({ρ, σ} : Set (I → ℤ)))
    (hcyc : ∀ k : ℕ, weylAction hC (t ^ k) = 1 → t ^ k = 1) :
    t ^ 6 = 1 ∧
      ((weylAction hC t) ^ 2) ρ = ρ - b • σ ∧
      ((weylAction hC t) ^ 3) ρ = -ρ ∧
      ((weylAction hC t) ^ 3) σ = -σ := by
  have hT2ρ' : weylAction hC t (weylAction hC t ρ) = ρ - b • σ := by
    rw [hT2ρ, hab]; module
  have hT2σ' : weylAction hC t (weylAction hC t σ) = a • ρ - 2 • σ := by
    rw [hT2σ, hab]; module
  have hba : b * a = 3 := by rw [mul_comm, hab]
  have hTmρ3 : weylAction hC t ρ = 2 • ρ - b • σ := by rw [hTmρ, hab]; module
  have hT3ρ' : weylAction hC t (weylAction hC t (weylAction hC t ρ)) = -ρ := by
    rw [hT2ρ', map_sub, map_smul, hTmρ3, hTmσ]
    simp only [smul_sub, smul_smul, hba]
    module
  have hT3σ' : weylAction hC t (weylAction hC t (weylAction hC t σ)) = -σ := by
    rw [hT2σ', map_sub, map_smul, map_nsmul, hTmρ3, hTmσ]
    simp only [smul_sub, smul_smul, hab]
    module
  have hpow2ρ : ((weylAction hC t) ^ 2) ρ = ρ - b • σ := by
    rw [pow_two, Module.End.mul_apply]; exact hT2ρ'
  have hpow3ρ : ((weylAction hC t) ^ 3) ρ = -ρ := by
    rw [show ((weylAction hC t) ^ 3) =
        (weylAction hC t) * (weylAction hC t) * (weylAction hC t) by
      rw [pow_succ, pow_two],
      Module.End.mul_apply, Module.End.mul_apply]
    exact hT3ρ'
  have hpow3σ : ((weylAction hC t) ^ 3) σ = -σ := by
    rw [show ((weylAction hC t) ^ 3) =
        (weylAction hC t) * (weylAction hC t) * (weylAction hC t) by
      rw [pow_succ, pow_two],
      Module.End.mul_apply, Module.End.mul_apply]
    exact hT3σ'
  have hfixρ : weylAction hC (t ^ 6) ρ = ρ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 6) ρ = ρ
    rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, Module.End.mul_apply,
      hpow3ρ, map_neg, hpow3ρ, neg_neg]
  have hfixσ : weylAction hC (t ^ 6) σ = σ := by
    rw [map_pow]
    show ((weylAction hC t) ^ 6) σ = σ
    rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, Module.End.mul_apply,
      hpow3σ, map_neg, hpow3σ, neg_neg]
  have h1 : weylAction hC (t ^ 6) = 1 :=
    ct_pr_weylAction_pow_eq_one_of_fixes_span hC t ρ σ 6 hspan hfixρ hfixσ
  have ht6 : t ^ 6 = 1 := hcyc 6 h1
  exact ⟨ht6, hpow2ρ, hpow3ρ, hpow3σ⟩

private theorem ct_pr_order_six_of_pairing_three
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (ρ σ : I → ℤ) (t : (coxeterMatrix hC).Group) (a b : ℤ)
    (hab : a * b = 3)
    (hpow2ρ : ((weylAction hC t) ^ 2) ρ = ρ - b • σ)
    (hpow3ρ : ((weylAction hC t) ^ 3) ρ = -ρ)
    (ht6 : t ^ 6 = 1)
    (hρ0 : toRat ρ ≠ 0)
    (hσ0 : toRat σ ≠ 0) :
    orderOf t = 6 := by
  have hb0 : b ≠ 0 := by intro h0; rw [h0, mul_zero] at hab; norm_num at hab
  have ht3ne : t ^ 3 ≠ 1 := by
    intro h3t
    have hw : ((weylAction hC t) ^ 3) = 1 := by rw [← map_pow, h3t, map_one]
    have hρeq : ((weylAction hC t) ^ 3) ρ = ρ := by
      rw [hw, Module.End.one_apply]
    rw [hpow3ρ] at hρeq
    have hx : -toRat ρ = toRat ρ := by simpa using congrArg toRat hρeq
    have hzero : toRat ρ = 0 := by
      ext k
      exact CharZero.neg_eq_self_iff.mp (congrFun hx k)
    exact hρ0 hzero
  have ht2ne : t ^ 2 ≠ 1 := by
    intro h2t
    have hw : ((weylAction hC t) ^ 2) = 1 := by rw [← map_pow, h2t, map_one]
    have hρeq : ((weylAction hC t) ^ 2) ρ = ρ := by
      rw [hw, Module.End.one_apply]
    rw [hpow2ρ] at hρeq
    have hx : toRat ρ - (b : ℚ) • toRat σ = toRat ρ := by
      simpa only [map_sub, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] using congrArg toRat hρeq
    have hbσ : (b : ℚ) • toRat σ = 0 := by
      have h' : toRat ρ = toRat ρ + (b : ℚ) • toRat σ := sub_eq_iff_eq_add.mp hx
      exact add_left_cancel (by rw [add_zero]; exact h'.symm)
    have hbq : (b : ℚ) = 0 := by
      rcases smul_eq_zero.mp hbσ with h | h
      · exact h
      · exact (hσ0 h).elim
    exact hb0 (by exact_mod_cast hbq)
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 6) (by norm_num) ht6 ?_
  intro p hp hpd
  have hpd23 : p ∣ 2 * 3 := by norm_num at hpd ⊢; exact hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd23 with hpd2 | hpd3
  · have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hpd2
    subst hpe
    norm_num
    exact ht3ne
  · have hpe : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hpd3
    subst hpe
    norm_num
    exact ht2ne

theorem orderOf_coxRefl_mul
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I)
    (hnp : ¬ ∃ q : ℚ, toRat (coxRoot hC h j) = q • toRat (coxRoot hC g i)) :
    (coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 0 →
      orderOf (coxRefl hC g i * coxRefl hC h j) = 2) ∧
    (coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 1 →
      orderOf (coxRefl hC g i * coxRefl hC h j) = 3) ∧
    (coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 2 →
      orderOf (coxRefl hC g i * coxRefl hC h j) = 4) ∧
    (coxPairing hC (coxRoot hC h j) (coxRoot hC g i) *
        coxPairing hC (coxRoot hC g i) (coxRoot hC h j) = 3 →
      orderOf (coxRefl hC g i * coxRefl hC h j) = 6) := by
  classical
  obtain ⟨ρ, σ, t, a, b, hρ, hσ, ht, ha, hb, hTmρ, hTmσ, hT2ρ, hT2σ,
    hspan, hcyc, hρ0, hσ0, hnp', hBρne, hBσne, ha', hb'⟩ :=
    ct_pr_coxRefl_mul_setup hC g h i j hnp
  rw [← hρ, ← hσ, ← ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp
    exact ct_pr_order_two hC ρ σ t a b
      (ct_pr_int_mul_of_pairing_mul hC ρ σ a b 0 ha hb hp)
      hTmρ hT2ρ hT2σ hspan hcyc hρ0 hBρne hBσne ha' hb'
  · intro hp
    exact ct_pr_order_three hC ρ σ t a b
      (ct_pr_int_mul_of_pairing_mul hC ρ σ a b 1 ha hb hp)
      hTmρ hTmσ hT2ρ hT2σ hspan hcyc hnp'
  · intro hp
    exact ct_pr_order_four hC ρ σ t a b
      (ct_pr_int_mul_of_pairing_mul hC ρ σ a b 2 ha hb hp)
      hT2ρ hT2σ hspan hcyc hρ0
  · intro hp
    have hab : a * b = 3 := ct_pr_int_mul_of_pairing_mul hC ρ σ a b 3 ha hb hp
    obtain ⟨ht6, hpow2ρ, hpow3ρ, -⟩ :=
      ct_pr_pow_six_of_pairing_three hC ρ σ t a b hab hTmρ hTmσ hT2ρ hT2σ hspan hcyc
    exact ct_pr_order_six_of_pairing_three hC ρ σ t a b hab hpow2ρ hpow3ρ ht6 hρ0 hσ0

private theorem ct_pr_coxPairing_reflect
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : (coxeterMatrix hC).Group) (i : I) (v w : I → ℤ) :
    coxPairing hC (weylAction hC (coxRefl hC g i) v) w =
      coxPairing hC v w - coxPairing hC v (coxRoot hC g i) * coxPairing hC (coxRoot hC g i) w := by
  have h := toRat_weylAction_coxRefl hC g i v
  simp only [coxPairing]
  rw [h]
  simp only [coxPairing, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem commute_coxRefl_of_form_eq_zero
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I)
    (h0 : form hC (toRat (coxRoot hC g i)) (toRat (coxRoot hC h j)) = 0) :
    Commute (coxRefl hC g i) (coxRefl hC h j) := by
  classical
  let u := coxRefl hC g i
  let v := coxRefl hC h j
  let ρ := coxRoot hC g i
  let σ := coxRoot hC h j
  have hρσ : coxPairing hC ρ σ = 0 := by
    rw [coxPairing, h0]
    simp
  have hσρ : coxPairing hC σ ρ = 0 := by
    rw [coxPairing]
    have h : form hC (toRat σ) (toRat ρ) = 0 := by
      rw [form_comm hC (toRat σ) (toRat ρ)]
      exact h0
    rw [h]
    simp
  have hcx1 : ∀ x : I → ℤ, coxPairing hC (weylAction hC v x) ρ = coxPairing hC x ρ := by
    intro x
    rw [ct_pr_coxPairing_reflect hC h j x ρ, hσρ, mul_zero, sub_zero]
  have hcx2 : ∀ x : I → ℤ, coxPairing hC (weylAction hC u x) σ = coxPairing hC x σ := by
    intro x
    rw [ct_pr_coxPairing_reflect hC g i x σ, hρσ, mul_zero, sub_zero]
  apply weylAction_injective hC
  apply LinearMap.ext
  intro x
  apply toRat_injective
  have hleft : toRat (weylAction hC (u * v) x) =
      toRat x - coxPairing hC x σ • toRat σ - coxPairing hC x ρ • toRat ρ := by
    rw [weylAction_mul_apply, toRat_weylAction_coxRefl hC g i (weylAction hC v x), hcx1,
      toRat_weylAction_coxRefl hC h j x]
  have hright : toRat (weylAction hC (v * u) x) =
      toRat x - coxPairing hC x σ • toRat σ - coxPairing hC x ρ • toRat ρ := by
    rw [weylAction_mul_apply, toRat_weylAction_coxRefl hC h j (weylAction hC u x), hcx2,
      toRat_weylAction_coxRefl hC g i x]
    simp only [ρ, σ]
    abel
  exact hleft.trans hright.symm

theorem coxRefl_eq_of_proportional
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g h : (coxeterMatrix hC).Group) (i j : I) (q : ℚ)
    (hq : toRat (coxRoot hC h j) = q • toRat (coxRoot hC g i)) :
    coxRefl hC h j = coxRefl hC g i := by
  classical
  let ρ := coxRoot hC g i
  let σ := coxRoot hC h j
  have hq0 : q ≠ 0 := by
    intro h0
    apply toRat_weylAction_single_ne_zero hC h j
    change toRat σ = 0
    rw [show toRat σ = q • toRat ρ from hq, h0, zero_smul]
  have hBρ0 : toRat ρ ≠ 0 := toRat_weylAction_single_ne_zero hC g i
  have hBρne : form hC (toRat ρ) (toRat ρ) ≠ 0 := (form_pos hC hBρ0).ne'
  apply weylAction_injective hC
  apply LinearMap.ext
  intro v
  have hqB : q * coxPairing hC v σ = coxPairing hC v ρ := by
    rw [coxPairing, coxPairing]
    rw [show toRat σ = q • toRat ρ from hq]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp [hq0, hBρne]
  have hcoeff : coxPairing hC v σ • toRat σ = coxPairing hC v ρ • toRat ρ := by
    rw [show toRat σ = q • toRat ρ from hq]
    rw [smul_smul, mul_comm (coxPairing hC v σ) q, hqB]
  apply toRat_injective
  rw [toRat_weylAction_coxRefl hC h j v, toRat_weylAction_coxRefl hC g i v, hcoeff]

end CFSG.StandardType.CoxTriple

end
