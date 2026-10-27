module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoords

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private lemma ggQ2S08_root_xV (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : M.root i M.xV = 0 := by
  have hxV_fixed : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hmem : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hfix : ggLin (p := 3) M.model (M.simple i) M.xV = M.xV :=
    (mem_ggFixedSubmodule_iff.mp hxV_fixed) (M.simple i) hmem
  rw [M.simple_apply i M.xV] at hfix
  have h0 : (M.root i M.xV) • M.coroot i = 0 := sub_eq_self.mp hfix
  have h2 : (M.root i M.xV) * (M.cartan i i : ZMod 3) = 0 := by
    have := congrArg (fun w => M.root i w) h0
    simpa [map_smul, M.pairing i i, smul_eq_mul, RingHom.id_apply] using this
  have hc2 : (M.cartan i i : ZMod 3) = 2 := by
    rw [M.isCartan.1 i]
    norm_num
  rw [hc2] at h2
  exact (mul_eq_zero.mp h2).resolve_right (by decide : (2 : ZMod 3) ≠ 0)

private lemma ggQ2S08_mem_span_xV (M : GGQ2LDatum 3 Bs L x) (v : M.V)
    (h : ∀ i, M.root i v = 0) : v ∈ Submodule.span (ZMod 3) {M.xV} := by
  have hfix : ∀ i, ggLin (p := 3) M.model (M.simple i) v = v := by
    intro i
    rw [M.simple_apply i v, h i, zero_smul, sub_zero]
  let H : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | ggLin (p := 3) M.model φ v = v}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [map_one]
        rfl
      mul_mem' := by
        intro φ ψ hφ hψ
        simp only [Set.mem_setOf_eq] at hφ hψ ⊢
        rw [map_mul, LinearEquiv.mul_apply, hψ, hφ]
      inv_mem' := by
        intro φ hφ
        simp only [Set.mem_setOf_eq] at hφ ⊢
        apply (ggLin (p := 3) M.model φ).injective
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rw [hφ]
        rfl }
  have hle : Subgroup.closure (Set.range M.simple) ≤ H := by
    rw [Subgroup.closure_le]
    rintro φ ⟨i, rfl⟩
    exact hfix i
  have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    exact hle hφ
  rw [M.fixed_x] at hmem
  exact hmem

private lemma ggQ2S08_root_sum (M : GGQ2LDatum 3 Bs L x) {ℓ : ℕ} (e : Fin ℓ ≃ M.Λ)
    (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (y : Fin ℓ → ZMod 3) (i : Fin ℓ) :
    M.root (e i) (∑ j, y j • M.coroot (e j)) = ∑ j, (C₀ i j : ZMod 3) * y j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, M.pairing, hC, smul_eq_mul, mul_comm]

private lemma ggQ2S08_conj_of_bases (M : GGQ2LDatum 3 Bs L x) {ι : Type} {ℓ n : ℕ}
    (e : Fin ℓ ≃ M.Λ) (bV : Module.Basis ι (ZMod 3) M.V)
    (bM : Module.Basis ι (ZMod 3) (Vn n)) (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n))
    (h : ∀ i k, bV.equiv bM (Equiv.refl ι)
      (ggLin (p := 3) M.model (M.simple (e i)) (bV k)) = S i (bM k)) :
    ∀ i v, bV.equiv bM (Equiv.refl ι) (ggLin (p := 3) M.model (M.simple (e i))
      ((bV.equiv bM (Equiv.refl ι)).symm v)) = S i v := by
  intro i
  let κ := bV.equiv bM (Equiv.refl ι)
  let F : Vn n →ₗ[ZMod 3] Vn n :=
    κ.toLinearMap.comp ((ggLin (p := 3) M.model (M.simple (e i))).toLinearMap.comp
      κ.symm.toLinearMap)
  have hF : F = (S i).toLinearMap := by
    refine bM.ext fun k => ?_
    have hk : κ.symm (bM k) = bV k := by
      rw [LinearEquiv.symm_apply_eq]
      exact (Module.Basis.equiv_apply bV k bM (Equiv.refl ι)).symm
    change κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm (bM k))) = S i (bM k)
    rw [hk]
    exact h i k
  intro v
  exact congrArg (fun T : Vn n →ₗ[ZMod 3] Vn n => T v) hF

private lemma ggQ2S08_linIndep_of_table {ι : Type} [Fintype ι] {n : ℕ} (hcard : Fintype.card ι = n)
    (f : ι → Vn n) (B : Fin n → ι → ZMod 3) (hB : ∀ k, ∑ j, B k j • f j = Pi.single k 1) :
    LinearIndependent (ZMod 3) f ∧ ⊤ ≤ Submodule.span (ZMod 3) (Set.range f) := by
  have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range f) := by
    rintro v -
    have hv : v = ∑ k, v k • (Pi.single k (1 : ZMod 3) : Vn n) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hv]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [← hB k]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan ?_, hspan⟩
  rw [hcard, Module.finrank_fin_fun]

private lemma ggQ2S08_xV_ne_zero (M : GGQ2LDatum 3 Bs L x) {ℓ : ℕ} (e : Fin ℓ ≃ M.Λ)
    (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (c : Fin ℓ → ZMod 3) (hc : ∀ i, ∑ j, (C₀ i j : ZMod 3) * c j = 0)
    (hne : ∑ j, c j • M.coroot (e j) ≠ 0) : M.xV ≠ 0 := by
  intro h0
  have hroot : ∀ i, M.root i (∑ j, c j • M.coroot (e j)) = 0 := by
    intro i
    obtain ⟨i', rfl⟩ := e.surjective i
    rw [ggQ2S08_root_sum M e C₀ hC c i', hc i']
  have hmem := ggQ2S08_mem_span_xV M _ hroot
  rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hmem
  exact hne hmem

private lemma ggQ2S08_smul_pm {n : ℕ} (μ : ZMod 3) (hμ : μ ≠ 0) (x₀ : Vn n) :
    μ • x₀ = x₀ ∨ μ • x₀ = -x₀ := by
  have : μ = 1 ∨ μ = -1 := by
    revert μ
    decide
  rcases this with rfl | rfl
  · left
    exact one_smul (ZMod 3) x₀
  · right
    exact neg_one_smul (ZMod 3) x₀

theorem ggQ2LDatum_coords_shapeD (M : GGQ2LDatum 3 Bs L x) (hD : M.ShapeD) {ℓ : ℕ}
    (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (h₀ α₀ : Fin ℓ → Vn ℓ) (hpair : ∀ i j, α₀ i ⬝ᵥ h₀ j = (C₀ i j : ZMod 3))
    (B : Fin ℓ → Fin ℓ → ZMod 3) (hB : ∀ k, ∑ j, B k j • h₀ j = Pi.single k 1)
    (S : Fin ℓ → (Vn ℓ ≃ₗ[ZMod 3] Vn ℓ)) (hS : ∀ k v, S k v = v - (α₀ k ⬝ᵥ v) • h₀ k)
    (c : Fin ℓ → ZMod 3) (hc : ∀ i, ∑ j, (C₀ i j : ZMod 3) * c j = 0) (hc0 : c ≠ 0)
    (hker : ∀ y : Fin ℓ → ZMod 3, (∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0) → ∃ μ : ZMod 3, y = μ • c)
    (x₀ : Vn ℓ) (hx₀ : x₀ = ∑ j, c j • h₀ j) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn ℓ, (κ M.xV = x₀ ∨ κ M.xV = -x₀) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v := by
  classical
  obtain ⟨-, hli, htop⟩ := hD
  have hliV : LinearIndependent (ZMod 3) (fun j => M.coroot (e j)) :=
    hli.comp e e.injective
  have hspV : ⊤ ≤ Submodule.span (ZMod 3) (Set.range fun j => M.coroot (e j)) := by
    rw [show (Set.range fun j => M.coroot (e j)) = Set.range M.coroot from
      e.surjective.range_comp M.coroot]
    exact htop.symm.le
  let bV : Module.Basis (Fin ℓ) (ZMod 3) M.V := Module.Basis.mk hliV hspV
  obtain ⟨hliM, hspM⟩ := ggQ2S08_linIndep_of_table (Fintype.card_fin ℓ) h₀ B hB
  let bM : Module.Basis (Fin ℓ) (ZMod 3) (Vn ℓ) := Module.Basis.mk hliM hspM
  have hbV : ∀ j, bV j = M.coroot (e j) := fun j => Module.Basis.mk_apply hliV hspV j
  have hbM : ∀ j, bM j = h₀ j := fun j => Module.Basis.mk_apply hliM hspM j
  let κ : M.V ≃ₗ[ZMod 3] Vn ℓ := bV.equiv bM (Equiv.refl _)
  have hκh : ∀ j, κ (M.coroot (e j)) = h₀ j := by
    intro j
    rw [← hbV j, ← hbM j]
    exact Module.Basis.equiv_apply bV j bM (Equiv.refl _)
  refine ⟨κ, ?_, ggQ2S08_conj_of_bases M e bV bM S fun i k => ?_⟩
  ·
    let y : Fin ℓ → ZMod 3 := bV.equivFun M.xV
    have hxV : M.xV = ∑ j, y j • M.coroot (e j) := by
      rw [← bV.sum_equivFun M.xV]
      exact Finset.sum_congr rfl fun j _ => by rw [hbV j]
    have hy : ∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0 := by
      intro i
      rw [← ggQ2S08_root_sum M e C₀ hC y i, ← hxV]
      exact ggQ2S08_root_xV M (e i)
    obtain ⟨μ, hμ⟩ := hker y hy
    have hne : ∑ j, c j • M.coroot (e j) ≠ 0 := by
      intro h0
      exact hc0 (funext fun j => (Fintype.linearIndependent_iff.mp hliV) c h0 j)
    have hxV0 := ggQ2S08_xV_ne_zero M e C₀ hC c hc hne
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply hxV0
      rw [hxV, hμ]
      simp
    have hκx : κ M.xV = μ • x₀ := by
      rw [hxV, map_sum, hx₀, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hκh j, hμ, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hκx]
    exact ggQ2S08_smul_pm μ hμ0 x₀
  · rw [hbV k, hbM k, M.simple_apply, M.pairing, hC, map_sub, map_smul, hκh, hκh, hS, hpair]


theorem ggQ2LDatum_coords_shapeB (M : GGQ2LDatum 3 Bs L x) (hB' : M.ShapeB) {ℓ : ℕ}
    (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (h₀ α₀ : Fin ℓ → Vn ℓ) (hpair : ∀ i j, α₀ i ⬝ᵥ h₀ j = (C₀ i j : ZMod 3))
    (x₀ : Vn ℓ) (hαx : ∀ i, α₀ i ⬝ᵥ x₀ = 0) (m : Fin ℓ) (c : Fin ℓ → ZMod 3)
    (hc : ∀ i, ∑ j, (C₀ i j : ZMod 3) * c j = 0) (hcm : c m ≠ 0)
    (hker : ∀ y : Fin ℓ → ZMod 3, (∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0) → ∃ μ : ZMod 3, y = μ • c)
    (hrel : ∑ j, c j • h₀ j = 0)
    (B : Fin ℓ → Fin ℓ → ZMod 3)
    (hB : ∀ k, ∑ j, B k j • (if j = m then x₀ else h₀ j) = Pi.single k 1)
    (S : Fin ℓ → (Vn ℓ ≃ₗ[ZMod 3] Vn ℓ)) (hS : ∀ k v, S k v = v - (α₀ k ⬝ᵥ v) • h₀ k) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn ℓ, κ M.xV = x₀ ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v := by
  classical
  obtain ⟨-, -, hxH, htop⟩ := hB'
  have hrelV : ∑ j, c j • M.coroot (e j) = 0 := by
    have hroot : ∀ i, M.root i (∑ j, c j • M.coroot (e j)) = 0 := by
      intro i
      obtain ⟨i', rfl⟩ := e.surjective i
      rw [ggQ2S08_root_sum M e C₀ hC c i', hc i']
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (ggQ2S08_mem_span_xV M _ hroot)
    have hmemH : ∑ j, c j • M.coroot (e j) ∈ M.coSpan :=
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (e j)))
    by_cases ha0 : a = 0
    · rw [← ha, ha0, zero_smul]
    · exfalso
      apply hxH
      have : M.xV = a⁻¹ • ∑ j, c j • M.coroot (e j) := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [this]
      exact M.coSpan.smul_mem _ hmemH
  let fV : Fin ℓ → M.V := fun j => if j = m then M.xV else M.coroot (e j)
  let fM : Fin ℓ → Vn ℓ := fun j => if j = m then x₀ else h₀ j
  have hcorootH : ∀ (y : Fin ℓ → ZMod 3), ∑ j, y j • M.coroot (e j) ∈ M.coSpan := fun y =>
    Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (e j)))
  have hliV : LinearIndependent (ZMod 3) fV := by
    rw [Fintype.linearIndependent_iff]
    intro y hy
    let y' : Fin ℓ → ZMod 3 := fun j => if j = m then 0 else y j
    have hsplit : ∑ j, y j • fV j = y m • M.xV + ∑ j, y' j • M.coroot (e j) := by
      have hterm : ∀ j, y j • fV j =
          (if j = m then y m • M.xV else 0) + y' j • M.coroot (e j) := by
        intro j
        by_cases hj : j = m
        · rw [hj]
          simp only [fV, y', ↓reduceIte, zero_smul, add_zero]
        · simp only [fV, y', if_neg hj, zero_add]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsplit] at hy
    have hym : y m = 0 := by
      by_contra hym
      apply hxH
      have hx' : M.xV = (y m)⁻¹ • -(∑ j, y' j • M.coroot (e j)) := by
        rw [← eq_neg_of_add_eq_zero_left hy, smul_smul, inv_mul_cancel₀ hym, one_smul]
      rw [hx']
      exact M.coSpan.smul_mem _ (M.coSpan.neg_mem (hcorootH y'))
    rw [hym, zero_smul, zero_add] at hy
    have hroots : ∀ i, ∑ j, (C₀ i j : ZMod 3) * y' j = 0 := by
      intro i
      rw [← ggQ2S08_root_sum M e C₀ hC y' i, hy, map_zero]
    obtain ⟨μ, hμ⟩ := hker y' hroots
    have hμ0 : μ = 0 := by
      have h1 := congrFun hμ m
      simp only [y', if_pos rfl, Pi.smul_apply, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hcm
    intro j
    by_cases hj : j = m
    · rw [hj, hym]
    · have h1 := congrFun hμ j
      simp only [y', if_neg hj, Pi.smul_apply, smul_eq_mul, hμ0, zero_mul] at h1
      exact h1
  have hspV : ⊤ ≤ Submodule.span (ZMod 3) (Set.range fV) := by
    have hfV : ∀ j, j ≠ m → M.coroot (e j) ∈ Submodule.span (ZMod 3) (Set.range fV) := by
      intro j hj
      have : fV j = M.coroot (e j) := if_neg hj
      rw [← this]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hm : M.coroot (e m) ∈ Submodule.span (ZMod 3) (Set.range fV) := by
      have hsum := hrelV
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase m, c j • M.coroot (e j) ∈
          Submodule.span (ZMod 3) (Set.range fV) :=
        Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hfV j (Finset.ne_of_mem_erase hj))
      have hcm' : M.coroot (e m) =
          (c m)⁻¹ • -(∑ j ∈ Finset.univ.erase m, c j • M.coroot (e j)) := by
        rw [← eq_neg_of_add_eq_zero_left hsum, smul_smul, inv_mul_cancel₀ hcm, one_smul]
      rw [hcm']
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hrest)
    have hH : M.coSpan ≤ Submodule.span (ZMod 3) (Set.range fV) := by
      rw [GGQ2LDatum.coSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      by_cases hj : j = m
      · rw [hj]
        exact hm
      · exact hfV j hj
    have hx : Submodule.span (ZMod 3) {M.xV} ≤ Submodule.span (ZMod 3) (Set.range fV) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have : fV m = M.xV := if_pos rfl
      rw [← this]
      exact Submodule.subset_span (Set.mem_range_self m)
    rw [← htop]
    exact sup_le hH hx
  let bV : Module.Basis (Fin ℓ) (ZMod 3) M.V := Module.Basis.mk hliV hspV
  obtain ⟨hliM, hspM⟩ := ggQ2S08_linIndep_of_table (Fintype.card_fin ℓ) fM B hB
  let bM : Module.Basis (Fin ℓ) (ZMod 3) (Vn ℓ) := Module.Basis.mk hliM hspM
  let κ : M.V ≃ₗ[ZMod 3] Vn ℓ := bV.equiv bM (Equiv.refl _)
  have hκf : ∀ j, κ (fV j) = fM j := by
    intro j
    rw [← Module.Basis.mk_apply hliV hspV j, ← Module.Basis.mk_apply hliM hspM j]
    exact Module.Basis.equiv_apply bV j bM (Equiv.refl _)
  have hκx : κ M.xV = x₀ := by
    have h1 := hκf m
    simp only [fV, fM, if_pos rfl] at h1
    exact h1
  have hκh : ∀ j, κ (M.coroot (e j)) = h₀ j := by
    have hne : ∀ j, j ≠ m → κ (M.coroot (e j)) = h₀ j := by
      intro j hj
      have h1 := hκf j
      simp only [fV, fM, if_neg hj] at h1
      exact h1
    intro j
    by_cases hj : j ≠ m
    · exact hne j hj
    · rw [not_not] at hj
      subst hj
      apply smul_right_injective (Vn ℓ) hcm
      have hsum := hrelV
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
      have hsumM := hrel
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsumM
      have h2 := congrArg κ hsum
      rw [map_add, map_smul, map_zero, map_sum] at h2
      rw [Finset.sum_congr rfl fun i hi => by
        rw [map_smul, hne i (Finset.ne_of_mem_erase hi)]] at h2
      change c j • κ (M.coroot (e j)) = c j • h₀ j
      rw [eq_neg_of_add_eq_zero_left h2, eq_neg_of_add_eq_zero_left hsumM]
  refine ⟨κ, hκx, ggQ2S08_conj_of_bases M e bV bM S fun i k => ?_⟩
  rw [Module.Basis.mk_apply hliV hspV k, Module.Basis.mk_apply hliM hspM k]
  by_cases hk : k = m
  · simp only [fV, fM, if_pos hk]
    rw [M.simple_apply, ggQ2S08_root_xV, zero_smul, sub_zero, hκx, hS, hαx, zero_smul, sub_zero]
  · simp only [fV, fM, if_neg hk]
    rw [M.simple_apply, M.pairing, hC, map_sub, map_smul, hκh, hκh, hS, hpair]

theorem ggQ2LDatum_coords_shapeA (M : GGQ2LDatum 3 Bs L x) (hA : M.ShapeA) {ℓ n : ℕ}
    (hn : n = ℓ + 1) (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (h₀ α₀ : Fin ℓ → Vn n) (hpair : ∀ i j, α₀ i ⬝ᵥ h₀ j = (C₀ i j : ZMod 3))
    (m : Fin ℓ) (v₀' : Vn n) (hv₀' : ∀ i, α₀ i ⬝ᵥ v₀' = if i = m then 1 else 0)
    (d : Fin ℓ → ZMod 3) (hd : ∀ j, ∑ i, d i * (C₀ i j : ZMod 3) = 0) (hdm : d m ≠ 0)
    (c : Fin ℓ → ZMod 3) (hc : ∀ i, ∑ j, (C₀ i j : ZMod 3) * c j = 0) (hc0 : c ≠ 0)
    (hker : ∀ y : Fin ℓ → ZMod 3, (∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0) → ∃ μ : ZMod 3, y = μ • c)
    (x₀ : Vn n) (hx₀ : x₀ = ∑ j, c j • h₀ j)
    (B : Fin n → Option (Fin ℓ) → ZMod 3)
    (hB : ∀ k, ∑ o, B k o • (Option.elim o v₀' h₀) = Pi.single k 1)
    (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n)) (hS : ∀ k v, S k v = v - (α₀ k ⬝ᵥ v) • h₀ k) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn n, (κ M.xV = x₀ ∨ κ M.xV = -x₀) ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v := by
  classical
  obtain ⟨-, hli, hxH, hdim, hsurj⟩ := hA
  obtain ⟨v₀, hv₀⟩ := hsurj (Pi.single (e m) 1)
  have hv₀root : ∀ i, M.root (e i) v₀ = if i = m then 1 else 0 := by
    intro i
    have h := congrFun hv₀ (e i)
    simpa [GGQ2LDatum.rootMap, LinearMap.pi_apply, Pi.single_apply, e.injective.eq_iff] using h
  have hliC : LinearIndependent (ZMod 3) (fun j => M.coroot (e j)) := hli.comp e e.injective
  let fV : Option (Fin ℓ) → M.V := fun o => Option.elim o v₀ fun j => M.coroot (e j)
  let fM : Option (Fin ℓ) → Vn n := fun o => Option.elim o v₀' h₀
  have hliV : LinearIndependent (ZMod 3) fV := by
    rw [Fintype.linearIndependent_iff]
    intro y hy
    rw [Fintype.sum_option] at hy
    have hroots : ∀ i, y none * (if i = m then 1 else 0) +
        ∑ j, (C₀ i j : ZMod 3) * y (some j) = 0 := by
      intro i
      have h1 := congrArg (M.root (e i)) hy
      rw [map_add, map_smul, map_zero, smul_eq_mul] at h1
      rw [← ggQ2S08_root_sum M e C₀ hC (fun j => y (some j)) i, ← hv₀root i]
      exact h1
    have hkey : d m * y none = 0 := by
      have h3 : ∑ i, d i * (y none * (if i = m then 1 else 0) +
          ∑ j, (C₀ i j : ZMod 3) * y (some j)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hroots i, mul_zero]
      have h4 : ∑ i, d i * (y none * (if i = m then 1 else 0) +
          ∑ j, (C₀ i j : ZMod 3) * y (some j)) =
          d m * y none + ∑ j, (∑ i, d i * (C₀ i j : ZMod 3)) * y (some j) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single m (fun i _ hi => by rw [if_neg hi, mul_zero, mul_zero])
            (fun h => absurd (Finset.mem_univ m) h), if_pos rfl, mul_one]
        · simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      rw [h4] at h3
      simpa [hd] using h3
    have hnone : y none = 0 := (mul_eq_zero.mp hkey).resolve_left hdm
    simp only [fV, hnone, zero_smul, zero_add, Option.elim] at hy
    have hsome : ∀ j, y (some j) = 0 := fun j =>
      (Fintype.linearIndependent_iff.mp hliC) (fun j => y (some j)) hy j
    intro o
    cases o with
    | none => exact hnone
    | some j => exact hsome j
  have hcardV : Fintype.card (Option (Fin ℓ)) = Module.finrank (ZMod 3) M.V := by
    rw [hdim, Fintype.card_option, Fintype.card_fin, Fintype.card_congr e.symm, Fintype.card_fin]
  let bV : Module.Basis (Option (Fin ℓ)) (ZMod 3) M.V :=
    basisOfLinearIndependentOfCardEqFinrank hliV hcardV
  have hbV : ∀ o, bV o = fV o := fun o =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hliV hcardV) o
  have hcardM : Fintype.card (Option (Fin ℓ)) = n := by
    rw [Fintype.card_option, Fintype.card_fin, hn]
  obtain ⟨hliM, hspM⟩ := ggQ2S08_linIndep_of_table hcardM fM B hB
  let bM : Module.Basis (Option (Fin ℓ)) (ZMod 3) (Vn n) := Module.Basis.mk hliM hspM
  have hbM : ∀ o, bM o = fM o := fun o => Module.Basis.mk_apply hliM hspM o
  let κ : M.V ≃ₗ[ZMod 3] Vn n := bV.equiv bM (Equiv.refl _)
  have hκf : ∀ o, κ (fV o) = fM o := by
    intro o
    rw [← hbV o, ← hbM o]
    exact Module.Basis.equiv_apply bV o bM (Equiv.refl _)
  have hκh : ∀ j, κ (M.coroot (e j)) = h₀ j := fun j => hκf (some j)
  have hκv : κ v₀ = v₀' := hκf none
  refine ⟨κ, ?_, ggQ2S08_conj_of_bases M e bV bM S fun i o => ?_⟩
  ·
    obtain ⟨y₀, hy₀⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hxH
    let y : Fin ℓ → ZMod 3 := fun j => y₀ (e j)
    have hxV : M.xV = ∑ j, y j • M.coroot (e j) := by
      rw [← hy₀]
      exact (Equiv.sum_comp e fun i => y₀ i • M.coroot i).symm
    have hy : ∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0 := by
      intro i
      rw [← ggQ2S08_root_sum M e C₀ hC y i, ← hxV]
      exact ggQ2S08_root_xV M (e i)
    obtain ⟨μ, hμ⟩ := hker y hy
    have hne : ∑ j, c j • M.coroot (e j) ≠ 0 := by
      intro h0
      exact hc0 (funext fun j => (Fintype.linearIndependent_iff.mp hliC) c h0 j)
    have hxV0 := ggQ2S08_xV_ne_zero M e C₀ hC c hc hne
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply hxV0
      rw [hxV, hμ]
      simp
    have hκx : κ M.xV = μ • x₀ := by
      rw [hxV, map_sum, hx₀, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hκh j, hμ, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hκx]
    exact ggQ2S08_smul_pm μ hμ0 x₀
  · rw [hbV o, hbM o]
    cases o with
    | none =>
        simp only [fV, fM, Option.elim]
        rw [M.simple_apply, hv₀root, map_sub, map_smul, hκv, hκh, hS, hv₀']
    | some j =>
        simp only [fV, fM, Option.elim]
        rw [M.simple_apply, M.pairing, hC, map_sub, map_smul, hκh, hκh, hS, hpair]

private def ggQ2S08DotL {n : ℕ} (a : Vn n) : Vn n →ₗ[ZMod 3] ZMod 3 where
  toFun v := a ⬝ᵥ v
  map_add' u v := dotProduct_add a u v
  map_smul' c v := by
    rw [dotProduct_smul, RingHom.id_apply]

theorem ggQ2LDatum_coords_shapeC (M : GGQ2LDatum 3 Bs L x) (hSc : M.ShapeC) {ℓ n : ℕ}
    (e : Fin ℓ ≃ M.Λ) (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j)
    (α₀ v' h₀ : Fin ℓ → Vn n) (ξ₀ x₀ : Vn n)
    (hαv : ∀ i k, α₀ i ⬝ᵥ v' k = if i = k then 1 else 0) (hξv : ∀ k, ξ₀ ⬝ᵥ v' k = 0)
    (hαx : ∀ i, α₀ i ⬝ᵥ x₀ = 0) (hξx : ξ₀ ⬝ᵥ x₀ = 1)
    (hspan : ∀ a : Fin n, ∑ k, (α₀ k ⬝ᵥ Pi.single a 1) • v' k +
      (ξ₀ ⬝ᵥ Pi.single a 1) • x₀ = Pi.single a 1)
    (hh : ∀ k, h₀ k = ∑ j, (C₀ j k : ZMod 3) • v' j)
    (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n)) (hS : ∀ k v, S k v = v - (α₀ k ⬝ᵥ v) • h₀ k) :
    ∃ κ : M.V ≃ₗ[ZMod 3] Vn n, κ M.xV = x₀ ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v := by
  classical
  obtain ⟨-, -, hxH, -, hsurj⟩ := hSc
  let Q : Vn n →ₗ[ZMod 3] (Option (Fin ℓ) → ZMod 3) :=
    LinearMap.pi fun o => Option.rec (ggQ2S08DotL ξ₀) (fun k => ggQ2S08DotL (α₀ k)) o
  have hQ_none : ∀ v, Q v none = ξ₀ ⬝ᵥ v := fun v => rfl
  have hQ_some : ∀ v k, Q v (some k) = α₀ k ⬝ᵥ v := fun v k => rfl
  let Plin : (Option (Fin ℓ) → ZMod 3) →ₗ[ZMod 3] Vn n :=
    (LinearMap.lsum (ZMod 3) (fun _ : Fin ℓ => ZMod 3) (ZMod 3)
      fun k => LinearMap.smulRight LinearMap.id (v' k)).comp
        (LinearMap.funLeft (ZMod 3) (ZMod 3) some) +
      LinearMap.smulRight (coord (ι := Option (Fin ℓ)) none) x₀
  have hPlin : ∀ y, Plin y = ∑ k, y (some k) • v' k + y none • x₀ := by
    intro y
    simp [Plin, LinearMap.lsum_apply, LinearMap.funLeft_apply]
  have hQh : ∀ k, Q (h₀ k) none = 0 ∧ ∀ i, Q (h₀ k) (some i) = (C₀ i k : ZMod 3) := by
    intro k
    refine ⟨?_, fun i => ?_⟩
    · rw [hQ_none, hh k, dotProduct_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [dotProduct_smul, hξv, smul_zero]
    · rw [hQ_some, hh k, dotProduct_sum, Finset.sum_eq_single i]
      · rw [dotProduct_smul, hαv, if_pos rfl, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [dotProduct_smul, hαv, if_neg (Ne.symm hj), smul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
  have hQP : ∀ y, Q (Plin y) = y := by
    intro y
    funext o
    rw [hPlin]
    cases o with
    | none =>
        rw [hQ_none, dotProduct_add, dotProduct_sum, dotProduct_smul, hξx, smul_eq_mul, mul_one]
        rw [Finset.sum_eq_zero fun k _ => by rw [dotProduct_smul, hξv, smul_zero], zero_add]
    | some i =>
        rw [hQ_some, dotProduct_add, dotProduct_sum, dotProduct_smul, hαx, smul_zero, add_zero,
          Finset.sum_eq_single i]
        · rw [dotProduct_smul, hαv, if_pos rfl, smul_eq_mul, mul_one]
        · intro j _ hj
          rw [dotProduct_smul, hαv, if_neg (Ne.symm hj), smul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
  have hPQ : ∀ v, Plin (Q v) = v :=
    rightInverse_of_basis fun a => by
      rw [hPlin]
      exact hspan a
  have hQx : Q x₀ = Pi.single none 1 := by
    funext o
    cases o with
    | none => rw [hQ_none, hξx]; rfl
    | some i => rw [hQ_some, hαx]; rfl
  have hQS : ∀ k, Q.comp (S k).toLinearMap = (rootCoordReflLin C₀ k).comp Q := by
    intro k
    refine LinearMap.ext fun v => funext fun o => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hS, map_sub, map_smul]
    cases o with
    | none =>
        rw [Pi.sub_apply, Pi.smul_apply, (hQh k).1, smul_zero, sub_zero]
        rfl
    | some i =>
        rw [Pi.sub_apply, Pi.smul_apply, (hQh k).2 i, smul_eq_mul, ← hQ_some v k]
        rfl
  obtain ⟨P, hPx, hPS⟩ := coordsData Q Plin x₀ S C₀ hQP hPQ hQx hQS
  exact ggQ2LDatum_coords_of_root M hsurj hxH e C₀ hC P x₀ S hPx hPS

theorem ggQ2S08_ker_of_cert {ℓ : ℕ} (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (c : Fin ℓ → ZMod 3)
    (m : Fin ℓ) (u : ZMod 3) (P : Fin ℓ → Fin ℓ → ZMod 3)
    (hP : ∀ i j, ∑ k, P i k * (C₀ k j : ZMod 3) =
      (if i = j then 1 else 0) - c i * u * (if j = m then 1 else 0)) :
    ∀ y : Fin ℓ → ZMod 3, (∀ i, ∑ j, (C₀ i j : ZMod 3) * y j = 0) → ∃ μ : ZMod 3, y = μ • c := by
  intro y hy
  refine ⟨y m * u, funext fun i => ?_⟩
  have h1 : ∑ k, P i k * ∑ j, (C₀ k j : ZMod 3) * y j = 0 := by
    simp only [hy, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ k, P i k * ∑ j, (C₀ k j : ZMod 3) * y j =
      ∑ j, (∑ k, P i k * (C₀ k j : ZMod 3)) * y j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h2] at h1
  have h3 : ∑ j, (∑ k, P i k * (C₀ k j : ZMod 3)) * y j = y i - c i * u * y m := by
    simp only [hP, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, one_mul]
    · rw [Finset.sum_eq_single m (fun j _ hj => by rw [if_neg hj, mul_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ m) h), if_pos rfl, mul_one]
  rw [h3] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h1

end CFSG.StandardType

end
