module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CorePermsAux
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem ggQ2s08k4_monoEven_one
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    GGQ2S08MonoEven f 1 :=
  ⟨1, fun _ => 1, fun _ => one_ne_zero, by simp,
    fun i => by simp⟩

private theorem ggQ2s08k4_monoEven_mul
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {g h : V ≃ₗ[ZMod 3] V} (hg : GGQ2S08MonoEven f g) (hh : GGQ2S08MonoEven f h) :
    GGQ2S08MonoEven f (g * h) := by
  obtain ⟨σ, ε, hε, hεp, hgε⟩ := hg
  obtain ⟨τ, δ, hδ, hδp, hhδ⟩ := hh
  refine ⟨σ * τ, fun i => δ i * ε (τ i),
    fun i => mul_ne_zero (hδ i) (hε (τ i)), ?_, ?_⟩
  · rw [Finset.prod_mul_distrib, hδp, one_mul, Equiv.prod_comp τ ε]
    exact hεp
  · intro i
    rw [LinearEquiv.mul_apply, hhδ i, map_smul, hgε (τ i), smul_smul, Equiv.Perm.mul_apply]

private theorem ggQ2s08k4_monoEven_inv
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} (hg : GGQ2S08MonoEven f g) :
    GGQ2S08MonoEven f g⁻¹ := by
  obtain ⟨σ, ε, hε, hεp, hgε⟩ := hg
  refine ⟨σ.symm, fun i => (ε (σ.symm i))⁻¹, fun i => inv_ne_zero (hε _), ?_, ?_⟩
  · rw [Finset.prod_inv_distrib]
    have hreindex : ∏ x, ε (σ.symm x) = ∏ x, ε x :=
      Fintype.prod_equiv σ.symm (fun x => ε (σ.symm x)) ε (fun x => rfl)
    rw [hreindex, hεp, inv_one]
  · intro i
    have h3 : f (σ.symm i) = ε (σ.symm i) • g⁻¹ (f i) := by
      calc f (σ.symm i) = g⁻¹ (g (f (σ.symm i))) := (LinearEquiv.symm_apply_apply g _).symm
        _ = g⁻¹ (ε (σ.symm i) • f i) := by rw [hgε (σ.symm i), Equiv.apply_symm_apply]
        _ = ε (σ.symm i) • g⁻¹ (f i) := by rw [map_smul]
    rw [h3, smul_smul, inv_mul_cancel₀ (hε _), one_smul]

private noncomputable def ggQ2s08k4_monoEvenSub
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {g | GGQ2S08MonoEven f g}
  one_mem' := ggQ2s08k4_monoEven_one f
  mul_mem' := fun hg hh => ggQ2s08k4_monoEven_mul f hg hh
  inv_mem' := fun hg => ggQ2s08k4_monoEven_inv f hg

private theorem ggQ2s08k4_mono_const_of_stab
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {a : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)} {ε : Fin N → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) (ha : ∀ i, a (f i) = ε i • f (σ i)) {c : ZMod 3}
    (hax : a (∑ i, f i) = c • ∑ i, f i) :
    ∀ i, ε i = c := by
  intro i
  have hx : a (∑ j, f j) = ∑ j, ε j • f (σ j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => ha j)
  have h1 : f.repr (a (∑ j, f j)) (σ i) = ε i := by
    rw [hx, map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
      simp
    · intro j _ hj
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
      have hne : σ j ≠ σ i := fun h => hj (σ.injective h)
      simp [hne]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hone : f.repr (∑ j, f j) (σ i) = 1 := by
    rw [map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single (σ i)]
    · rw [Module.Basis.repr_self_apply]; simp
    · intro j _ hj
      rw [Module.Basis.repr_self_apply]
      simp [hj]
    · intro h; exact absurd (Finset.mem_univ (σ i)) h
  have h2 : f.repr (a (∑ j, f j)) (σ i) = c := by
    rw [hax, map_smul, Finsupp.smul_apply, hone, smul_eq_mul, mul_one]
  rw [h1] at h2
  exact h2

private theorem ggQ2s08k4_monoEven_of_mono_const
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {a : V ≃ₗ[ZMod 3] V} (hmono : GGQ2S08Mono f a) {c : ZMod 3} (hc : c ≠ 0)
    (hax : a (∑ i, f i) = c • ∑ i, f i) (hEven : Even N) :
    GGQ2S08MonoEven f a := by
  obtain ⟨σ, ε, hε, haε⟩ := hmono
  have hconst : ∀ i, ε i = c := ggQ2s08k4_mono_const_of_stab f hε haε hax
  refine ⟨σ, ε, hε, ?_, haε⟩
  have hprod : ∏ i, ε i = c ^ N := by
    rw [show (fun i => ε i) = fun _ => c from funext hconst]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  rcases ggQ2s08k4_zmod3_eq_one_or_neg_one c hc with h | h
  · rw [h, one_pow]
  · rw [h, show (-1 : ZMod 3) ^ N = 1 from Even.neg_one_pow hEven]

private theorem ggQ2s08k4_conj_sgn
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {r : V ≃ₗ[ZMod 3] V} {i0 : Fin N}
    (hrd : ∀ k, r (f k) = (if k = i0 then (-1 : ZMod 3) else 1) • f k) (a : Fin N) :
    ggQ2s08k4_sgn f a =
      ggQ2s08k4_permM f (Equiv.swap i0 a) * r *
        (ggQ2s08k4_permM f (Equiv.swap i0 a)).symm := by
  apply ggQ2s08k4_eq_of_basis
  intro k
  change ggQ2s08k4_sgn f a (f k) = _
  rw [ggQ2s08k4_sgn_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ggQ2s08k4_permM_symm, ggQ2s08k4_permM_apply, hrd, map_smul, ggQ2s08k4_permM_apply,
    Equiv.apply_symm_apply]
  congr 1
  have hiff : ((Equiv.swap i0 a).symm k = i0) ↔ (k = a) := by
    rw [Equiv.symm_apply_eq, Equiv.swap_apply_left]
  by_cases hk : k = a
  · rw [if_pos hk, if_pos (hiff.mpr hk)]
  · rw [if_neg hk, if_neg (fun h => hk (hiff.mp h))]

private theorem ggQ2s08k4_twist_eq
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {r : V ≃ₗ[ZMod 3] V} {i0 j0 : Fin N} (hij : i0 ≠ j0)
    (hrd : ∀ k, r (f k) = (if k = i0 then (-1 : ZMod 3) else if k = j0 then -1 else 1) •
      f (Equiv.swap i0 j0 k)) :
    r = ggQ2s08k4_pairDiag f i0 j0 * ggQ2s08k4_permM f (Equiv.swap i0 j0) := by
  apply ggQ2s08k4_eq_of_basis
  intro k
  change r (f k) = _
  rw [hrd k, LinearEquiv.mul_apply, ggQ2s08k4_permM_apply, ggQ2s08k4_pairDiag_apply]
  congr 1
  rcases eq_or_ne k i0 with h1 | h1
  · rw [h1]; simp [Equiv.swap_apply_left, hij]
  · rcases eq_or_ne k j0 with h2 | h2
    · rw [h2]; simp [Equiv.swap_apply_right, hij]
    · have hsw : Equiv.swap i0 j0 k = k := Equiv.swap_apply_of_ne_of_ne h1 h2
      rw [if_neg h1, if_neg h2, hsw, if_neg h1, if_neg h2]

private theorem ggQ2s08k4_conj_pairDiag
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 j0 : Fin N) (τ : Equiv.Perm (Fin N)) :
    ggQ2s08k4_permM f τ * ggQ2s08k4_pairDiag f i0 j0 *
        (ggQ2s08k4_permM f τ).symm = ggQ2s08k4_pairDiag f (τ i0) (τ j0) := by
  apply ggQ2s08k4_eq_of_basis
  intro k
  change (ggQ2s08k4_permM f τ * ggQ2s08k4_pairDiag f i0 j0 *
      (ggQ2s08k4_permM f τ).symm) (f k) = _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2s08k4_permM_symm,
    ggQ2s08k4_permM_apply, ggQ2s08k4_pairDiag_apply, map_smul, ggQ2s08k4_permM_apply,
    ggQ2s08k4_pairDiag_apply, Equiv.apply_symm_apply]
  congr 1
  have hiff1 : (τ.symm k = i0) ↔ (k = τ i0) := by rw [Equiv.symm_apply_eq]
  have hiff2 : (τ.symm k = j0) ↔ (k = τ j0) := by rw [Equiv.symm_apply_eq]
  rw [if_congr hiff1 rfl rfl, if_congr hiff2 rfl rfl]

private noncomputable def ggQ2s08k4_neg
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    V ≃ₗ[ZMod 3] V :=
  ggQ2s08k4_diag f (fun _ => (-1 : ZMod 3)) (fun _ => by decide)

private theorem ggQ2s08k4_neg_apply_basis
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) (i : Fin N) :
    ggQ2s08k4_neg f (f i) = (-1 : ZMod 3) • f i :=
  ggQ2s08k4_diag_apply f _ _ i

private theorem ggQ2s08k4_neg_mul_self
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    ggQ2s08k4_neg f * ggQ2s08k4_neg f = 1 := by
  apply ggQ2s08k4_eq_of_basis
  intro i
  change (ggQ2s08k4_neg f * ggQ2s08k4_neg f) (f i) = _
  rw [LinearEquiv.mul_apply, ggQ2s08k4_neg_apply_basis, map_smul, ggQ2s08k4_neg_apply_basis,
    smul_smul, show (-1 : ZMod 3) * -1 = 1 from by decide, one_smul]
  rfl

private theorem ggQ2s08k4_neg_sum
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    ggQ2s08k4_neg f (∑ i, f i) = (-1 : ZMod 3) • ∑ i, f i := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i _ => ggQ2s08k4_neg_apply_basis f i)]
  rw [← Finset.smul_sum]

private theorem ggQ2s08k4_prod_eq_one_or_neg_one
    {N : ℕ}
    (ε : Fin N → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∏ i, ε i = 1 ∨ ∏ i, ε i = (-1 : ZMod 3) := by
  have hsq : (∏ i, ε i) ^ 2 = 1 := by
    rw [sq, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε i) (hε i) with h | h <;> rw [h] <;> decide
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem ggQ2s08k4_neg_mul_monoEven
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {a : V ≃ₗ[ZMod 3] V} (hmono : GGQ2S08Mono f a) (hodd : Odd N)
    (hne : ¬ GGQ2S08MonoEven f a) :
    GGQ2S08MonoEven f (ggQ2s08k4_neg f * a) := by
  obtain ⟨σ, ε, hε, haε⟩ := hmono
  have hprod_ne : ∏ i, ε i ≠ 1 := fun hp => hne ⟨σ, ε, hε, hp, haε⟩
  have hprod : ∏ i, ε i = (-1 : ZMod 3) := by
    rcases ggQ2s08k4_prod_eq_one_or_neg_one ε hε with h | h
    · exact absurd h hprod_ne
    · exact h
  refine ⟨σ, fun i => (-1 : ZMod 3) * ε i,
    fun i => mul_ne_zero (by decide) (hε i), ?_, ?_⟩
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (-1 : ZMod 3) ^ N = -1 from Odd.neg_one_pow hodd, hprod]
    decide
  · intro i
    rw [LinearEquiv.mul_apply, haε i, map_smul, ggQ2s08k4_neg_apply_basis, smul_smul]
    congr 1
    ring

private theorem ggQ2s08k4_neg_one_ne_zero
    : (-1 : ZMod 3) ≠ 0 := by decide

theorem ggQ2s08core_all_perms {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (hN : 4 ≤ N)
    (f : Module.Basis (Fin N) (ZMod 3) V) (R W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hR : (∀ a, a ∈ R ↔ GGQ2S08Mono f a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven f a))
    (hW : ∀ a, a ∈ W ↔ ∃ σ : Equiv.Perm (Fin N), ∀ i, a (f i) = f (σ i))
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r)
    (hrx : ¬ ∃ c : ZMod 3, r (∑ i, f i) = c • ∑ i, f i) :
    GGQ2S08M0 R W r (∑ i, f i) = R ∨
      (Even N ∧ (∀ a, a ∈ R ↔ GGQ2S08Mono f a) ∧
        ∀ a, a ∈ GGQ2S08M0 R W r (∑ i, f i) ↔ GGQ2S08MonoEven f a) := by
  classical
  set H := GGQ2S08M0 R W r (∑ i, f i)
  have hrmono : GGQ2S08Mono f r := by
    rcases hR with h | h
    · exact (h r).mp hrR
    · exact ggQ2s08k4_mono_of_monoEven f ((h r).mp hrR)
  obtain ⟨σ, c, hc, hrc⟩ := hrmono
  have hshape := ggRC_monomial_refl_shape (p := 3) (by norm_num) f r hr σ c hc hrc
  have hWleR : W ≤ R := by
    intro a ha
    rcases (hW a).mp ha with ⟨ρ, hρ⟩
    rcases hR with h | h
    · exact (h a).mpr ⟨ρ, fun _ => 1, fun _ => one_ne_zero, fun i => by rw [hρ i]; simp⟩
    · exact (h a).mpr ⟨ρ, fun _ => 1, fun _ => one_ne_zero, by simp, fun i => by rw [hρ i]; simp⟩
  have hpermW : ∀ ρ, ggQ2s08k4_permM f ρ ∈ W :=
    fun ρ => (hW _).mpr ⟨ρ, fun i => ggQ2s08k4_permM_apply f ρ i⟩
  have hWleH : W ≤ H := fun a ha => Subgroup.subset_closure (Or.inl (Or.inl ha))
  have hHleR : H ≤ R := by
    change Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r} ∪
      GGQ2S08LineStab R (∑ i, f i)) ≤ R
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with (haW | har) | haL
    · exact hWleR haW
    · rw [Set.mem_singleton_iff] at har; rw [har]; exact hrR
    · exact haL.1
  have hrH : r ∈ H := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hstabH : GGQ2S08LineStab R (∑ i, f i) ⊆ H :=
    fun a ha => Subgroup.subset_closure (Or.inr ha)
  have hpermH : ∀ ρ, ggQ2s08k4_permM f ρ ∈ H := fun ρ => hWleH (hpermW ρ)
  rcases hshape with ⟨i0, hσ1, hci0, hcj⟩ | ⟨i0, j0, hij, hσswap, hcij, hck⟩
  · have hrd : ∀ k, r (f k) = (if k = i0 then (-1 : ZMod 3) else 1) • f k := by
      intro k
      rw [hrc k, hσ1]
      by_cases hk : k = i0
      · rw [hk, hci0, if_pos rfl]
        rfl
      · rw [hcj k hk]; simp [hk]
    have hRmono : ∀ a, a ∈ R ↔ GGQ2S08Mono f a := by
      rcases hR with h | h
      · exact h
      · exfalso
        have hmE : GGQ2S08MonoEven f r := (h r).mp hrR
        obtain ⟨σ', ε', hε', hεp', hr'⟩ := hmE
        have hdata := ggQ2s08k4_mono_data_eq f hc hε' hrc hr'
        have hpc : ∏ i, c i = (-1 : ZMod 3) := ggQ2s08k4_prod_sign_single c i0 hci0 hcj
        rw [hdata.2] at hpc
        rw [hεp'] at hpc
        exact absurd hpc (by decide)
    left
    apply le_antisymm hHleR
    intro a ha
    exact ggQ2s08k4_mono_mem f H hpermH (fun b => by
      rw [ggQ2s08k4_conj_sgn f hrd b]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hpermH (Equiv.swap i0 b)) hrH)
        (Subgroup.inv_mem _ (hpermH (Equiv.swap i0 b)))) a ((hRmono a).mp ha)
  · have hcneg : c i0 = (-1 : ZMod 3) ∧ c j0 = -1 := by
      rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (c i0) (hc i0) with h1 | h1 <;>
        rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (c j0) (hc j0) with h2 | h2
      · exfalso
        have hc1 : ∀ k, c k = 1 := by
          intro k
          by_cases hki : k = i0
          · rw [hki]; exact h1
          · by_cases hkj : k = j0
            · rw [hkj]; exact h2
            · exact hck k hki hkj
        apply hrx
        refine ⟨1, ?_⟩
        have hr_eq : r = ggQ2s08k4_permM f (Equiv.swap i0 j0) := by
          apply ggQ2s08k4_eq_of_basis; intro k
          rw [hrc k, hσswap, hc1 k, one_smul, ggQ2s08k4_permM_apply]
        have hsum : ∑ k, ggQ2s08k4_permM f (Equiv.swap i0 j0) (f k) = ∑ k, f k := by
          rw [Finset.sum_congr rfl (fun k _ => ggQ2s08k4_permM_apply f _ k)]
          exact Equiv.sum_comp (Equiv.swap i0 j0) f
        rw [hr_eq, map_sum, hsum, one_smul]
      · rw [h1, h2] at hcij; exact absurd hcij (by decide)
      · rw [h1, h2] at hcij; exact absurd hcij (by decide)
      · exact ⟨h1, h2⟩
    have hrd : ∀ k, r (f k) =
        (if k = i0 then (-1 : ZMod 3) else if k = j0 then -1 else 1) •
          f (Equiv.swap i0 j0 k) := by
      intro k
      rw [hrc k, hσswap]
      by_cases h1 : k = i0
      · rw [h1, if_pos rfl, hcneg.1]
      · by_cases h2 : k = j0
        · rw [h2, if_neg hij.symm, if_pos rfl, hcneg.2]
        · rw [if_neg h1, if_neg h2, hck k h1 h2]
    have hTwist : r = ggQ2s08k4_pairDiag f i0 j0 * ggQ2s08k4_permM f (Equiv.swap i0 j0) :=
      ggQ2s08k4_twist_eq f hij hrd
    have hpp : (ggQ2s08k4_permM f (Equiv.swap i0 j0)) *
        (ggQ2s08k4_permM f (Equiv.swap i0 j0)).symm = 1 := by
      apply ggQ2s08k4_eq_of_basis
      intro i
      change ((ggQ2s08k4_permM f (Equiv.swap i0 j0)) *
        (ggQ2s08k4_permM f (Equiv.swap i0 j0)).symm) (f i) = _
      rw [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      rfl
    have hD_eq : ggQ2s08k4_pairDiag f i0 j0 =
        r * (ggQ2s08k4_permM f (Equiv.swap i0 j0)).symm := by
      rw [hTwist, mul_assoc, hpp, mul_one]
    have hDmem : ggQ2s08k4_pairDiag f i0 j0 ∈ H := by
      rw [hD_eq]
      exact Subgroup.mul_mem _ hrH (Subgroup.inv_mem _ (hpermH (Equiv.swap i0 j0)))
    have hpairH : ∀ j, j ≠ i0 → ggQ2s08k4_pairDiag f i0 j ∈ H := by
      intro j hji
      have hτi0 : Equiv.swap j0 j i0 = i0 :=
        Equiv.swap_apply_of_ne_of_ne hij hji.symm
      have hτj0 : Equiv.swap j0 j j0 = j := Equiv.swap_apply_left j0 j
      have hconj := ggQ2s08k4_conj_pairDiag f i0 j0 (Equiv.swap j0 j)
      rw [hτi0, hτj0] at hconj
      rw [← hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hpermH (Equiv.swap j0 j)) hDmem)
        (Subgroup.inv_mem _ (hpermH (Equiv.swap j0 j)))
    rcases hR with hRm | hRmE
    · by_cases hEven : Even N
      · right
        refine ⟨hEven, hRm, ?_⟩
        intro a
        constructor
        · intro ha
          have hHleE : H ≤ ggQ2s08k4_monoEvenSub f := by
            change Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r} ∪
              GGQ2S08LineStab R (∑ i, f i)) ≤ ggQ2s08k4_monoEvenSub f
            rw [Subgroup.closure_le]
            intro b hb
            rcases hb with (hbW | hbr) | hbL
            · rcases (hW b).mp hbW with ⟨ρ, hρ⟩
              exact ⟨ρ, fun _ => 1, fun _ => one_ne_zero, by simp, fun i => by rw [hρ i]; simp⟩
            · rw [Set.mem_singleton_iff] at hbr; rw [hbr]
              exact ⟨Equiv.swap i0 j0,
                fun k => if k = i0 then (-1 : ZMod 3) else if k = j0 then -1 else 1,
                fun k => by simp only []; split_ifs <;> decide,
                ggQ2s08k4_prod_sign_pair _ i0 j0 hij (by simp) (by simp [hij.symm])
                  (fun k h1 h2 => by simp [h1, h2]), hrd⟩
            · obtain ⟨hbR, c', hc', hbx⟩ := hbL
              exact ggQ2s08k4_monoEven_of_mono_const f ((hRm b).mp hbR) hc' hbx hEven
          exact hHleE ha
        · intro ha
          exact ggQ2s08k4_monoEven_mem f H hpermH i0 hpairH a ha
      · left
        apply le_antisymm hHleR
        intro a ha
        have hmono : GGQ2S08Mono f a := (hRm a).mp ha
        by_cases hE : GGQ2S08MonoEven f a
        · exact ggQ2s08k4_monoEven_mem f H hpermH i0 hpairH a hE
        · have hodd : Odd N := Nat.not_even_iff_odd.mp hEven
          have hneg_mono : GGQ2S08MonoEven f (ggQ2s08k4_neg f * a) :=
            ggQ2s08k4_neg_mul_monoEven f hmono hodd hE
          have hnegH : ggQ2s08k4_neg f ∈ H := by
            apply hstabH
            refine ⟨?_, ⟨-1, by decide, ggQ2s08k4_neg_sum f⟩⟩
            rw [hRm]
            exact ⟨1, fun _ => -1, fun _ => ggQ2s08k4_neg_one_ne_zero, fun i => by
              rw [ggQ2s08k4_neg_apply_basis]; simp⟩
          have hbH : ggQ2s08k4_neg f * a ∈ H :=
            ggQ2s08k4_monoEven_mem f H hpermH i0 hpairH _ hneg_mono
          have haeq : a = ggQ2s08k4_neg f * (ggQ2s08k4_neg f * a) := by
            rw [← mul_assoc, ggQ2s08k4_neg_mul_self f, one_mul]
          rw [haeq]
          exact Subgroup.mul_mem _ hnegH hbH
    · left
      apply le_antisymm hHleR
      intro a ha
      exact ggQ2s08k4_monoEven_mem f H hpermH i0 hpairH a ((hRmE a).mp ha)

end CFSG.StandardType

end
