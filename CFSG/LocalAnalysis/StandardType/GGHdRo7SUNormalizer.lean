module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SUNormAux_coord_equiv {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ : Equiv.Perm (Fin m)) (w : V) (j : Fin m) :
    b.coord j ((b.equiv b σ) w) = b.coord (σ.symm j) w := by
  have h : (b.coord j).comp ((b.equiv b σ).toLinearMap) = b.coord (σ.symm j) := by
    refine b.ext (fun i => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hij : σ i = j
    · have hji : i = σ.symm j := by
        rw [← hij, Equiv.symm_apply_apply]
      simp [hij, hji]
    · have hji : i ≠ σ.symm j := by
        intro h'
        exact hij (by rw [h', Equiv.apply_symm_apply])
      simp [hij, hji]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    congrArg (fun φ : V →ₗ[ZMod p] (ZMod p) => φ w) h

private theorem hdRo7SUNormAux_equiv_mul {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ τ : Equiv.Perm (Fin m)) :
    b.equiv b σ * b.equiv b τ = b.equiv b (σ * τ) := by
  have h : ((b.equiv b σ * b.equiv b τ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
      ((b.equiv b (σ * τ) : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) := by
    refine b.ext (fun i => ?_)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.Perm.mul_apply]
  exact LinearEquiv.toLinearMap_injective h

private theorem hdRo7SUNormAux_equiv_injective {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    Function.Injective (fun σ : Equiv.Perm (Fin m) => b.equiv b σ) := by
  intro σ τ h
  refine Equiv.ext (fun i => ?_)
  have h2 : b (σ i) = b (τ i) := by
    have := congrArg (fun (e : V ≃ₗ[ZMod p] V) => e (b i)) h
    simpa only [Module.Basis.equiv_apply] using this
  exact b.injective h2

private theorem hdRo7SUNormAux_equiv_ones {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (σ : Equiv.Perm (Fin m)) :
    (b.equiv b σ) (SUOnes p b) = SUOnes p b := by
  unfold SUOnes
  rw [map_sum]
  simp_rw [Module.Basis.equiv_apply]
  exact Equiv.sum_comp σ (fun i => b i)


private theorem hdRo7SUNormAux_coord_ones {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k : Fin m) :
    b.coord k (SUOnes p b) = 1 := by
  unfold SUOnes
  rw [map_sum]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  simp

private theorem hdRo7SUNormAux_repr_ones {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (k : Fin m) :
    (b.repr (SUOnes p b)) k = 1 := by
  rw [← Module.Basis.coord_apply, hdRo7SUNormAux_coord_ones]

private theorem hdRo7SUNormAux_centralizer {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (f : V ≃ₗ[ZMod p] V)
    (i0 k0 : Fin m) (hk0 : k0 ≠ i0)
    (hf : ∀ (σ : Equiv.Perm (Fin m)) (v : V), f ((b.equiv b σ) v) = (b.equiv b σ) (f v)) :
    ∃ α β : ZMod p, ∀ i : Fin m, f (b i) = α • b i + β • SUOnes p b := by
  have hcoord := fun (σ : Equiv.Perm (Fin m)) (w : V) (j : Fin m) =>
    hdRo7SUNormAux_coord_equiv b σ w j
  have hoff : ∀ k l : Fin m, k ≠ i0 → l ≠ i0 →
      b.coord k (f (b i0)) = b.coord l (f (b i0)) := by
    intro k l hk hl
    have hfix : (Equiv.swap k l) i0 = i0 :=
      Equiv.swap_apply_of_ne_of_ne (fun h => hk h.symm) (fun h => hl h.symm)
    have h1 : f (b i0) = (b.equiv b (Equiv.swap k l)) (f (b i0)) := by
      calc f (b i0) = f ((b.equiv b (Equiv.swap k l)) (b i0)) := by
                rw [Module.Basis.equiv_apply, hfix]
        _ = (b.equiv b (Equiv.swap k l)) (f (b i0)) := hf _ _
    have hsymm : (Equiv.swap k l).symm k = l :=
      calc (Equiv.swap k l).symm k
          = (Equiv.swap k l).symm ((Equiv.swap k l) l) := by rw [Equiv.swap_apply_right]
        _ = l := Equiv.symm_apply_apply _ _
    calc b.coord k (f (b i0))
        = b.coord k ((b.equiv b (Equiv.swap k l)) (f (b i0))) := by
            conv_lhs => rw [h1]
      _ = b.coord ((Equiv.swap k l).symm k) (f (b i0)) := hcoord _ _ _
      _ = b.coord l (f (b i0)) := by rw [hsymm]
  have hdiag : ∀ i : Fin m, b.coord i (f (b i)) = b.coord i0 (f (b i0)) := by
    intro i
    have hfix : (Equiv.swap i0 i) i0 = i := Equiv.swap_apply_left i0 i
    have h1 : f (b i) = (b.equiv b (Equiv.swap i0 i)) (f (b i0)) := by
      calc f (b i) = f ((b.equiv b (Equiv.swap i0 i)) (b i0)) := by
                rw [Module.Basis.equiv_apply, hfix]
        _ = (b.equiv b (Equiv.swap i0 i)) (f (b i0)) := hf _ _
    have hsymm : (Equiv.swap i0 i).symm i = i0 :=
      calc (Equiv.swap i0 i).symm i
          = (Equiv.swap i0 i).symm ((Equiv.swap i0 i) i0) := by rw [hfix]
        _ = i0 := Equiv.symm_apply_apply _ _
    calc b.coord i (f (b i))
        = b.coord i ((b.equiv b (Equiv.swap i0 i)) (f (b i0))) := by
            conv_lhs => rw [h1]
      _ = b.coord ((Equiv.swap i0 i).symm i) (f (b i0)) := hcoord _ _ _
      _ = b.coord i0 (f (b i0)) := by rw [hsymm]
  have hoffi : ∀ i j : Fin m, j ≠ i →
      b.coord j (f (b i)) = b.coord k0 (f (b i0)) := by
    intro i j hji
    have hfix : (Equiv.swap i0 i) i0 = i := Equiv.swap_apply_left i0 i
    have h1 : f (b i) = (b.equiv b (Equiv.swap i0 i)) (f (b i0)) := by
      calc f (b i) = f ((b.equiv b (Equiv.swap i0 i)) (b i0)) := by
                rw [Module.Basis.equiv_apply, hfix]
        _ = (b.equiv b (Equiv.swap i0 i)) (f (b i0)) := hf _ _
    have hsymm_ne : (Equiv.swap i0 i).symm j ≠ i0 := by
      intro h
      apply hji
      rw [← Equiv.apply_symm_apply (Equiv.swap i0 i) j, h, hfix]
    calc b.coord j (f (b i))
        = b.coord j ((b.equiv b (Equiv.swap i0 i)) (f (b i0))) := by
            conv_lhs => rw [h1]
      _ = b.coord ((Equiv.swap i0 i).symm j) (f (b i0)) := hcoord _ _ _
      _ = b.coord k0 (f (b i0)) := hoff _ _ hsymm_ne hk0
  refine ⟨b.coord i0 (f (b i0)) - b.coord k0 (f (b i0)), b.coord k0 (f (b i0)), fun i => ?_⟩
  apply b.ext_elem
  intro k
  simp only [← Module.Basis.coord_apply]
  have hdi := hdiag i
  have hoi := hoffi i k
  change b.coord k (f (b i)) =
    b.coord k ((b.coord i0 (f (b i0)) - b.coord k0 (f (b i0))) • b i +
      b.coord k0 (f (b i0)) • SUOnes p b)
  by_cases hki : k = i
  · rw [hki, hdi]
    simp only [map_add, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      hdRo7SUNormAux_repr_ones]
    simp
  · rw [hoi hki]
    simp only [map_add, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      hdRo7SUNormAux_repr_ones]
    rw [if_neg (fun h : i = k => hki h.symm)]
    ring_nf


private theorem hdRo7SUNormAux_inner {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (hm : 7 ≤ m) (b : Module.Basis (Fin m) (ZMod p) V)
    (a : V ≃ₗ[ZMod p] V)
    (hnorm : ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹)) :
    ∃ π : Equiv.Perm (Fin m), ∀ σ : Equiv.Perm (Fin m),
      b.equiv b (π * σ * π⁻¹) = a * (b.equiv b σ) * a⁻¹ := by
  have hSUP : ∀ σ : Equiv.Perm (Fin m), SUPerm p b (b.equiv b σ) := fun σ =>
    ⟨σ, fun i => by rw [Module.Basis.equiv_apply]⟩
  have hchoice : ∀ σ : Equiv.Perm (Fin m), ∃ τ, b.equiv b τ = a * (b.equiv b σ) * a⁻¹ := by
    intro σ
    obtain ⟨τ, hτ⟩ := hnorm (b.equiv b σ) (hSUP σ)
    refine ⟨τ, ?_⟩
    have h : ((b.equiv b τ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
        ((a * (b.equiv b σ) * a⁻¹ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) := by
      refine b.ext (fun i => ?_)
      simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      exact (hτ i).symm
    exact LinearEquiv.toLinearMap_injective h
  let τ : Equiv.Perm (Fin m) → Equiv.Perm (Fin m) := fun σ => Classical.choose (hchoice σ)
  have hτ : ∀ σ, b.equiv b (τ σ) = a * (b.equiv b σ) * a⁻¹ := fun σ =>
    Classical.choose_spec (hchoice σ)
  have hone : b.equiv b (1 : Equiv.Perm (Fin m)) = 1 := by
    rw [show (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) from rfl,
      Module.Basis.equiv_refl]
    exact LinearEquiv.one_eq_refl.symm
  have hτ_one : τ 1 = 1 := by
    apply hdRo7SUNormAux_equiv_injective b
    change b.equiv b (τ 1) = b.equiv b 1
    rw [hτ 1, hone]
    group
  have hmul : ∀ σ τ', b.equiv b (σ * τ') = b.equiv b σ * b.equiv b τ' := fun σ τ' =>
    (hdRo7SUNormAux_equiv_mul b σ τ').symm
  have hτ_mul : ∀ σ τ' : Equiv.Perm (Fin m), τ (σ * τ') = τ σ * τ τ' := by
    intro σ τ'
    apply hdRo7SUNormAux_equiv_injective b
    change b.equiv b (τ (σ * τ')) = b.equiv b (τ σ * τ τ')
    rw [hτ (σ * τ'), hmul σ τ', hmul (τ σ) (τ τ'), hτ σ, hτ τ']
    group
  have hτ_inj : Function.Injective τ := by
    intro σ τ' h
    have h2 : a * b.equiv b σ * a⁻¹ = a * b.equiv b τ' * a⁻¹ := by
      rw [← hτ σ, ← hτ τ', h]
    exact hdRo7SUNormAux_equiv_injective b (mul_left_cancel (mul_right_cancel h2))
  let αhom : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) :=
    { toFun := τ, map_one' := hτ_one, map_mul' := hτ_mul }
  have hbij : Function.Bijective τ :=
    ⟨hτ_inj, (Finite.injective_iff_surjective.mp hτ_inj)⟩
  let αe : MulAut (Equiv.Perm (Fin m)) := MulEquiv.ofBijective αhom hbij
  obtain ⟨π, hπ⟩ := CFSG.EvenSmallLie.OddTranspAlt.perm_aut_inner hm αe
  refine ⟨π, fun σ => ?_⟩
  have h := hτ σ
  change b.equiv b (π * σ * π⁻¹) = a * (b.equiv b σ) * a⁻¹
  rw [← hπ σ]
  change b.equiv b (τ σ) = a * (b.equiv b σ) * a⁻¹
  exact h


private noncomputable def hdRo7SUNormAux_Phom {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V) where
  toFun σ := b.equiv b σ
  map_one' := by
    show b.equiv b 1 = 1
    rw [show (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) from rfl,
      Module.Basis.equiv_refl]
    exact LinearEquiv.one_eq_refl.symm
  map_mul' σ τ := (hdRo7SUNormAux_equiv_mul b σ τ).symm


theorem su_normalizer_holds : SUNormalizerLeaf := by
  unfold SUNormalizerLeaf
  intro p hpFact hp m hm h3 V instV instM b a hnorm hfix
  subst hp
  let P : Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod 3] V) := hdRo7SUNormAux_Phom b
  obtain ⟨π, hπ⟩ := hdRo7SUNormAux_inner (p := 3) hm b a hnorm
  have hπP : ∀ σ : Equiv.Perm (Fin m), P (π * σ * π⁻¹) = a * P σ * a⁻¹ := by
    intro σ
    change b.equiv b (π * σ * π⁻¹) = a * b.equiv b σ * a⁻¹
    exact hπ σ
  let a' : V ≃ₗ[ZMod 3] V := P π⁻¹ * a
  have ha_eq : P π * a' = a := by
    have hππ : P π * P π⁻¹ = 1 := by
      rw [← map_mul P, mul_inv_cancel, map_one P]
    simp only [a']
    rw [← mul_assoc, hππ, one_mul]
  have hcomm : ∀ σ, a' * P σ * a'⁻¹ = P σ := by
    intro σ
    have h1 : a' * P σ * a'⁻¹ = P π⁻¹ * (a * P σ * a⁻¹) * (P π⁻¹)⁻¹ := by
      simp only [a']; group
    rw [h1, ← hπP σ, ← map_inv P, ← map_mul P, ← map_mul P]
    congr 1
    group
  have hcomm' : ∀ σ v, a' ((b.equiv b σ) v) = (b.equiv b σ) (a' v) := by
    intro σ v
    have hmul : a' * P σ = P σ * a' := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e * a') (hcomm σ)
      simpa [mul_assoc] using h
    have h2 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hmul
    change a' (P σ v) = P σ (a' v)
    simpa only [LinearEquiv.mul_apply] using h2
  have hxfix : a' (SUOnes 3 b) = SUOnes 3 b := by
    have h : (P π⁻¹) (SUOnes 3 b) = SUOnes 3 b := by
      change (b.equiv b π⁻¹) (SUOnes 3 b) = SUOnes 3 b
      exact hdRo7SUNormAux_equiv_ones b π⁻¹
    simpa only [a', LinearEquiv.mul_apply, hfix] using h
  let i0 : Fin m := ⟨0, by omega⟩
  let k0 : Fin m := ⟨1, by omega⟩
  have hk0 : k0 ≠ i0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i0, k0] at hv
    omega
  obtain ⟨α₀, β₀, hcent⟩ :=
    hdRo7SUNormAux_centralizer (p := 3) b a' i0 k0 hk0 hcomm'
  have hm_ne : (m : ZMod 3) ≠ 0 := by
    intro h
    exact h3 ((CharP.cast_eq_zero_iff (ZMod 3) 3 m).mp h)
  have hscalar : α₀ + (m : ZMod 3) * β₀ = 1 := by
    have hxval : a' (SUOnes 3 b) = (α₀ + (m : ZMod 3) * β₀) • SUOnes 3 b := by
      calc a' (SUOnes 3 b)
          = ∑ i : Fin m, a' (b i) := by rw [SUOnes, map_sum]
        _ = ∑ i : Fin m, (α₀ • b i + β₀ • SUOnes 3 b) := by simp only [hcent]
        _ = α₀ • SUOnes 3 b + m • (β₀ • SUOnes 3 b) := by
              rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← SUOnes, Finset.sum_const,
                Finset.card_univ, Fintype.card_fin]
        _ = (α₀ + (m : ZMod 3) * β₀) • SUOnes 3 b := by
              rw [← Nat.cast_smul_eq_nsmul (ZMod 3) m (β₀ • SUOnes 3 b), smul_smul,
                ← add_smul]
    have h1 := congrArg (b.coord i0) (hxval.symm.trans hxfix)
    simp only [map_smul, hdRo7SUNormAux_coord_ones, mul_one] at h1
    simpa using h1
  have hα_ne : α₀ ≠ 0 := by
    intro h0
    have h1 : a' (b i0) = a' (b k0) := by
      rw [hcent i0, hcent k0, h0]
      simp
    have h2 : b i0 = b k0 := a'.injective h1
    exact hk0 (b.injective h2).symm
  have hαcases : α₀ = 1 ∨ α₀ = -1 := by
    fin_cases α₀
    · exact absurd rfl hα_ne
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hαcases with hα | hα
  · left
    have hβ : β₀ = 0 := by
      have h := hscalar
      rw [hα] at h
      have hmul : (m : ZMod 3) * β₀ = 0 := by
        apply add_left_cancel (a := (1 : ZMod 3))
        rw [h]
        simp
      exact (mul_eq_zero.mp hmul).resolve_left hm_ne
    refine ⟨π, fun i => ?_⟩
    have hai : a' (b i) = b i := by
      rw [hcent i, hα, hβ]
      simp
    rw [← ha_eq, LinearEquiv.mul_apply, hai]
    change (b.equiv b π) (b i) = b (π i)
    rw [Module.Basis.equiv_apply]
  · right
    have hβ : β₀ = 2 / (m : ZMod 3) := by
      have h := hscalar
      rw [hα] at h
      have hmul : (m : ZMod 3) * β₀ = 2 := by
        have h' := congrArg (fun x : ZMod 3 => x + 1) h
        simp only [add_assoc, add_comm (-1), add_left_comm] at h'
        norm_num at h'
        exact h'
      rw [eq_div_iff hm_ne, mul_comm]
      exact hmul
    refine ⟨π, fun i => ?_⟩
    have hai : a' (b i) = -b i + (2 / (m : ZMod 3)) • SUOnes 3 b := by
      have hneg : (-1 : ZMod 3) • b i = -b i := neg_one_smul (ZMod 3) (b i)
      rw [hcent i, hα, hβ, hneg]
    rw [← ha_eq, LinearEquiv.mul_apply, hai]
    change (b.equiv b π) (-b i + (2 / (m : ZMod 3)) • SUOnes 3 b) =
      -b (π i) + (2 / (m : ZMod 3)) • SUOnes 3 b
    rw [map_add, map_neg, map_smul, Module.Basis.equiv_apply,
      hdRo7SUNormAux_equiv_ones]


end CFSG.StandardType.HdRo7SU
