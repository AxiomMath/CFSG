module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpMono
public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
public import CFSG.LieType.Steinberg.CentralExt.SpTorus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisWeights
public import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras CFSG.StandardType CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
open TauCeti.GLSymplecticFin

@[expose] noncomputable def spTorusChar {K k : Type} [Field K] [Field k] (ι : K →+* k) {n : ℕ}
    (e : Fin n → ℤ) : (Fin n → Kˣ) →* kˣ where
  toFun t := Units.map ι.toMonoidHom (CFSG.LieType.Steinberg.CentralExt.SpTorus.chi e t)
  map_one' := by simp [CFSG.LieType.Steinberg.CentralExt.SpTorus.chi]
  map_mul' t t' := by
    simp [CFSG.LieType.Steinberg.CentralExt.SpTorus.chi, mul_zpow, Finset.prod_mul_distrib]

private theorem spTW_spTorusChar_eq_prod {K k : Type} [Field K] [Field k] (ι : K →+* k)
    {n : ℕ} (e : Fin n → ℤ) (t : Fin n → Kˣ) :
    spTorusChar ι e t = ∏ a, Units.map ι.toMonoidHom (t a) ^ e a := by
  show Units.map ι.toMonoidHom (CFSG.LieType.Steinberg.CentralExt.SpTorus.chi e t) =
    ∏ a, Units.map ι.toMonoidHom (t a) ^ e a
  rw [CFSG.LieType.Steinberg.CentralExt.SpTorus.chi]
  simp only [map_prod, map_zpow]

theorem spTorusChar_apply {K k : Type} [Field K] [Field k] (ι : K →+* k) {n : ℕ}
    (e : Fin n → ℤ) (t : Fin n → Kˣ) :
    ((spTorusChar ι e t : kˣ) : k) = ∏ a, ι (t a : K) ^ e a := by
  rw [congrArg (fun u : kˣ => (u : k)) (spTW_spTorusChar_eq_prod (K := K) ι e t)]
  rw [show ((∏ a, Units.map ι.toMonoidHom (t a) ^ e a : kˣ) : k) =
      (Units.coeHom k) (∏ a, Units.map ι.toMonoidHom (t a) ^ e a) from rfl]
  rw [map_prod (Units.coeHom k) (fun a => Units.map ι.toMonoidHom (t a) ^ e a) Finset.univ]
  apply Finset.prod_congr rfl
  intro a _
  change ((Units.map ι.toMonoidHom (t a) ^ e a : kˣ) : k) = ι (t a : K) ^ e a
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map]
  rfl

theorem spTorusChar_ne_of_not_dvd {K k : Type} [Field K] [Finite K] [Field k] (ι : K →+* k)
    {n : ℕ} {e e' : Fin n → ℤ} {a : Fin n} (h : ¬ ((Nat.card K : ℤ) - 1) ∣ e a - e' a) :
    spTorusChar ι e ≠ spTorusChar ι e' := by
  intro hEq
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  let t : Fin n → Kˣ := Function.update 1 a ζ
  have hval := congrArg (fun f : (Fin n → Kˣ) →* kˣ => (f t : k)) hEq
  rw [spTorusChar_apply, spTorusChar_apply] at hval
  have hL : ∏ b, ι (t b : K) ^ e b = ι (ζ : K) ^ e a := by
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb
      simp [t, Function.update_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ a) hmem
  have hR : ∏ b, ι (t b : K) ^ e' b = ι (ζ : K) ^ e' a := by
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb
      simp [t, Function.update_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ a) hmem
  rw [hL, hR] at hval
  have hy : (ι (ζ : K)) ≠ 0 := fun h0 => Units.ne_zero ζ (ι.injective (by rw [h0, map_zero]))
  have hsub : (ι (ζ : K)) ^ (e a - e' a) = 1 := by
    rw [zpow_sub₀ hy, hval, div_self (zpow_ne_zero _ hy)]
  have hpowK : (ζ : K) ^ (e a - e' a) = 1 := by
    apply ι.injective
    rw [map_zpow₀, hsub, map_one]
  have hpowU : (ζ : Kˣ) ^ (e a - e' a) = 1 := by
    apply Units.ext
    rw [Units.val_zpow_eq_zpow_val, hpowK, Units.val_one]
  have horder : orderOf ζ = Nat.card K - 1 := by
    rw [hζ, Nat.card_units]
  have hdvd : (orderOf ζ : ℤ) ∣ e a - e' a :=
    (orderOf_dvd_iff_zpow_eq_one).mpr hpowU
  rw [horder] at hdvd
  refine h ?_
  have h1 : 1 ≤ Nat.card K := le_of_lt (Finite.one_lt_card (α := K))
  rwa [Nat.cast_sub h1] at hdvd

private noncomputable def spTW_torusTheta {K : Type} [Field K] {n : ℕ}
    (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) : (Fin n → Kˣ) →* (Fin n → Kˣ) where
  toFun t := fun a => t (π a) ^ s a
  map_one' := by funext a; simp
  map_mul' t t' := by
    funext a
    simp only [Pi.mul_apply]
    rw [mul_zpow]

private theorem spTW_torusChar_comp_theta {K k : Type} [Field K] [Field k] (ι : K →+* k)
    {n : ℕ} (e : Fin n → ℤ) (π : Equiv.Perm (Fin n)) (s : Fin n → ℤ) :
    (spTorusChar ι e).comp (spTW_torusTheta (K := K) π s) =
      spTorusChar ι (spAct π s e) := by
  apply MonoidHom.ext
  intro t
  rw [MonoidHom.comp_apply, spTW_spTorusChar_eq_prod, spTW_spTorusChar_eq_prod]
  have hL : (∏ a, Units.map ι.toMonoidHom (spTW_torusTheta (K := K) π s t a) ^ e a) =
      ∏ a, Units.map ι.toMonoidHom (t (π a)) ^ (s a * e a) := by
    apply Finset.prod_congr rfl
    intro a _
    rw [show spTW_torusTheta (K := K) π s t a = t (π a) ^ s a from rfl, map_zpow,
      ← zpow_mul]
  rw [hL]
  rw [show (∏ a, Units.map ι.toMonoidHom (t (π a)) ^ (s a * e a)) =
      ∏ a, Units.map ι.toMonoidHom (t a) ^ (s (π.symm a) * e (π.symm a)) from by
    rw [show (∏ a, Units.map ι.toMonoidHom (t (π a)) ^ (s a * e a)) =
        ∏ a, (fun b => Units.map ι.toMonoidHom (t b) ^
          (s (π.symm b) * e (π.symm b))) (π a) from by
      apply Finset.prod_congr rfl
      intro a _
      simp only [Equiv.symm_apply_apply]]
    exact Equiv.prod_comp π (fun b => Units.map ι.toMonoidHom (t b) ^
      (s (π.symm b) * e (π.symm b)))]
  simp only [spAct]

theorem spTorusChar_mul_character_pow {K k : Type} [Field K] [Field k] (ι : K →+* k) {n : ℕ}
    (e : Fin n → ℤ) (r : RootSubgroupIndex n) (j : ℕ) :
    spTorusChar ι e * ((Units.map ι.toMonoidHom).comp r.character) ^ j =
      spTorusChar ι (e + (j : ℤ) • stdVec r) := by
  apply MonoidHom.ext
  intro t
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply,
    spTW_spTorusChar_eq_prod, spTW_spTorusChar_eq_prod]
  have hchar : Units.map ι.toMonoidHom (r.character t) =
      ∏ a, Units.map ι.toMonoidHom (t a) ^ stdVec r a := by
    rw [character_eq_prod]
    simp only [map_prod, map_zpow]
  rw [hchar, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private noncomputable def spTW_prefixVec {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ)
    (i : Fin n) : Kˣ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), t j

private theorem spTW_prefixVec_succ {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ)
    {b : Fin n} (hb : 0 < b.val) :
    spTW_prefixVec t b = t b * spTW_prefixVec t (⟨b.val - 1, by omega⟩ : Fin n) := by
  have hIio : Finset.Iio b = Finset.Iic (⟨b.val - 1, by omega⟩ : Fin n) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
    omega
  change (∏ a ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ b.val), t a) =
    t b * ∏ a ∈ Finset.univ.filter
      (fun a : Fin n => a.val ≤ (⟨b.val - 1, by omega⟩ : Fin n).val), t a
  have hb' : Finset.univ.filter (fun a : Fin n => a.val ≤ b.val) = Finset.Iic b := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
  have hb'' : Finset.univ.filter
      (fun a : Fin n => a.val ≤ (⟨b.val - 1, by omega⟩ : Fin n).val) =
      Finset.Iic (⟨b.val - 1, by omega⟩ : Fin n) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
  rw [hb', hb'', ← Finset.Iio_insert b, Finset.prod_insert (by simp), hIio]

private theorem spTW_prefixVec_eq_of_val_eq_zero {K : Type} [Field K] {n : ℕ}
    {t : Fin n → Kˣ} {b : Fin n} (hb : b.val = 0) : spTW_prefixVec t b = t b := by
  change (∏ a ∈ Finset.univ.filter (fun a : Fin n => a.val ≤ b.val), t a) = t b
  refine Finset.prod_eq_single b ?_ ?_
  · intro c _ hc
    exfalso
    apply hc
    apply Fin.ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    omega
  · intro h
    exact absurd (by simp) h

private theorem spTW_prod_corootVec_shift {K : Type} [Field K] {n : ℕ}
    (d : Fin n → Kˣ) (b : Fin n) :
    (∏ i, ((if h : i.val + 1 < n then
        Pi.mulSingle ⟨i.val + 1, h⟩ (d i)⁻¹ else 1 : Fin n → Kˣ) b)) =
      if hb : 0 < b.val then (d ⟨b.val - 1, by omega⟩)⁻¹ else 1 := by
  by_cases hb : 0 < b.val
  · rw [dif_pos hb]
    let i0 : Fin n := ⟨b.val - 1, by omega⟩
    have hi0 : i0.val + 1 = b.val := by
      simp only [i0]
      omega
    rw [Finset.prod_eq_single (s := Finset.univ) (f := fun i : Fin n =>
      ((if h : i.val + 1 < n then Pi.mulSingle ⟨i.val + 1, h⟩ (d i)⁻¹ else 1 :
        Fin n → Kˣ) b)) i0 ?_ ?_]
    · have hi0lt : i0.val + 1 < n := by omega
      rw [dif_pos hi0lt]
      have hbi : b = (⟨i0.val + 1, hi0lt⟩ : Fin n) := by
        apply Fin.ext
        show b.val = i0.val + 1
        omega
      rw [Pi.mulSingle_apply, if_pos hbi]
    · intro i _ hi
      have hne : i.val + 1 ≠ b.val := by
        intro h
        apply hi
        apply Fin.ext
        simp only [i0]
        omega
      by_cases h : i.val + 1 < n
      · rw [dif_pos h, Pi.mulSingle_apply, if_neg]
        intro hb_eq
        exact hne (congrArg Fin.val hb_eq).symm
      · rw [dif_neg h]
        rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · rw [dif_neg hb]
    apply Finset.prod_eq_one
    intro i _
    have hne : i.val + 1 ≠ b.val := by omega
    by_cases h : i.val + 1 < n
    · rw [dif_pos h, Pi.mulSingle_apply, if_neg]
      intro hb_eq
      exact hne (congrArg Fin.val hb_eq).symm
    · rw [dif_neg h]
      rfl

private theorem spTW_prod_corootVec_prefixVec {K : Type} [Field K] {n : ℕ}
    (t : Fin n → Kˣ) : ∏ i, corootVec n K i (spTW_prefixVec t i) = t := by
  rw [show (∏ i, corootVec n K i (spTW_prefixVec t i)) =
      ∏ i, (Pi.mulSingle i (spTW_prefixVec t i) *
        (if h : i.val + 1 < n then
          Pi.mulSingle ⟨i.val + 1, h⟩ (spTW_prefixVec t i)⁻¹ else 1)) from
    Finset.prod_congr rfl (fun i _ => corootVec_eq_mul i (spTW_prefixVec t i))]
  rw [Finset.prod_mul_distrib]
  funext b
  rw [Pi.mul_apply, Finset.prod_apply, Finset.prod_apply, Fintype.prod_pi_mulSingle,
    spTW_prod_corootVec_shift]
  by_cases hb : 0 < b.val
  · rw [dif_pos hb, spTW_prefixVec_succ t hb]
    group
  · rw [dif_neg hb, mul_one]
    exact spTW_prefixVec_eq_of_val_eq_zero (by omega)

private theorem spTW_prefixVec_eq_prefixProd {K : Type} [Field K] {n : ℕ}
    (t : Fin n → Kˣ) (i : Fin n) : spTW_prefixVec t i = prefixProd i t := by
  have hprod : prefixProd i t =
      ∏ j, prefixProd i (corootVec n K j (spTW_prefixVec t j)) := by
    conv_lhs => rw [← spTW_prod_corootVec_prefixVec (K := K) t]
    rw [map_prod]
  rw [hprod]
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [prefixProd_corootVec, if_neg hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [prefixProd_corootVec, if_pos rfl]

theorem prod_corootVec_prefixProd {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ) :
    ∏ i, corootVec n K i (prefixProd i t) = t := by
  rw [show (∏ i, corootVec n K i (prefixProd i t)) =
      ∏ i, corootVec n K i (spTW_prefixVec t i) from
    Finset.prod_congr rfl (fun i _ => by rw [← spTW_prefixVec_eq_prefixProd])]
  exact spTW_prod_corootVec_prefixVec t

theorem diagHom_mem_spCurtisDatum_H {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (t : Fin n → Kˣ) : diagHom n K t ∈ (spCurtisDatum n K).H := by
  rw [← prod_corootVec_prefixProd (K := K) t, Fin.prod_univ_def, map_list_prod]
  refine Subgroup.list_prod_mem (spCurtisDatum n K).H (fun x hx => ?_)
  obtain ⟨y, hy, hi⟩ := List.mem_map.mp hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  rw [← hi]
  exact diagHom_corootVec_mem_H i (prefixProd i t)

theorem sum_pow_smul_mem_weightSpace {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] (ι : K →+* k) {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (StatedSp n K) V) (r : RootSubgroupIndex n) {e : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι e)) {j : ℕ}
    (hj : j < Nat.card K) :
    (∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (elt r c) z) ∈
      weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι (e + (j : ℤ) • stdVec r)) := by
  have hx : ∀ t : Fin n → Kˣ, ∀ c : K,
      diagHom n K t * elt r c * (diagHom n K t)⁻¹ =
        elt r ((r.character t : K) * c) := by
    intro t c
    rw [diagHom_conj_elt, character_eq_prod]
  have hmem := sum_pow_smul_mem_weightSpace_of_conj (ρ := ρ) (τ := diagHom n K)
    (x := fun c => elt r c) (α := r.character) (fun t c => hx t c) ι hz hj
  rwa [spTorusChar_mul_character_pow] at hmem

private theorem spTW_permMatrix_diagonal_conj {K : Type} [Field K] {n : ℕ}
    (σ : Equiv.Perm (Fin n ⊕ Fin n)) (d : Fin n ⊕ Fin n → K) :
    σ.permMatrix K * Matrix.diagonal d * (σ.permMatrix K)⁻¹ = Matrix.diagonal (d ∘ σ) := by
  have hQ : σ.permMatrix K * (σ⁻¹).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul (σ := σ⁻¹) (τ := σ)]
    simp
  rw [Matrix.inv_eq_right_inv hQ]
  rw [show σ.permMatrix K = σ.toPEquiv.toMatrix from rfl,
    show (σ⁻¹).permMatrix K = (σ⁻¹).toPEquiv.toMatrix from rfl]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  change ((Matrix.diagonal d).submatrix σ id).submatrix id σ = Matrix.diagonal (d ∘ σ)
  ext i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_apply]

private theorem spTW_nW_inv_conj_diagHom {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hw : SpRealizes n w π s) (hs : SpIsSign s) (t : Fin n → Kˣ) :
    ((spCurtisDatum n K).nW w)⁻¹ * diagHom n K t * (spCurtisDatum n K).nW w =
      diagHom n K (spTW_torusTheta (K := K) π s t) := by
  apply mat_injective
  have hQ : (spMonoPerm π s).permMatrix K * ((spMonoPerm π s)⁻¹).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul (σ := (spMonoPerm π s)⁻¹) (τ := spMonoPerm π s)]
    simp
  have hy : mat n K ((spCurtisDatum n K).nW w) = ((spMonoPerm π s).permMatrix K)⁻¹ := by
    rw [mat_nW_spCurtisDatum hw hs]
    exact (Matrix.inv_eq_right_inv hQ).symm
  have hinv : mat n K ((spCurtisDatum n K).nW w)⁻¹ =
      (mat n K ((spCurtisDatum n K).nW w))⁻¹ :=
    (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])).symm
  have hDt : mat n K (diagHom n K t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => ((t i)⁻¹ : K))) := by
    rw [show diagHom n K t = equivStatedSp n K (TauCeti.GLSymplecticFin.diagonal t) from rfl,
      mat_equiv_diagonal]
    simp
  have hDθ : mat n K (diagHom n K (spTW_torusTheta (K := K) π s t)) =
      Matrix.diagonal (Sum.elim (fun i => ((spTW_torusTheta (K := K) π s t) i : K))
        (fun i => (((spTW_torusTheta (K := K) π s t) i)⁻¹ : K))) := by
    rw [show diagHom n K (spTW_torusTheta (K := K) π s t) =
      equivStatedSp n K (TauCeti.GLSymplecticFin.diagonal
        (spTW_torusTheta (K := K) π s t)) from rfl, mat_equiv_diagonal]
    simp
  have hdet : IsUnit (((spMonoPerm π s).permMatrix K).det) := by
    rw [Matrix.det_permutation]
    exact IsUnit.map (Int.castRingHom K) (Equiv.Perm.sign (spMonoPerm π s)).isUnit
  rw [map_mul, map_mul, hinv, hy, hDt, hDθ]
  rw [show ((spMonoPerm π s).permMatrix K)⁻¹⁻¹ = (spMonoPerm π s).permMatrix K from
    Matrix.nonsing_inv_nonsing_inv (A := (spMonoPerm π s).permMatrix K) hdet,
    spTW_permMatrix_diagonal_conj]
  congr 1
  funext x
  rcases x with b | b <;> rcases hs b with h | h <;>
    simp [Function.comp, spTW_torusTheta, spMonoPerm_inl, spMonoPerm_inr, h]

theorem nW_mem_weightSpace {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type}
    [Field k] (ι : K →+* k) {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (StatedSp n K) V)
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hw : SpRealizes n w π s) (hs : SpIsSign s) {e : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι e)) :
    ρ ((spCurtisDatum n K).nW w) v ∈
      weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι (spAct π s e)) := by
  have hmem := mem_weightSpace_of_inv_mul_mul (ρ := ρ) (τ := diagHom n K)
    (y := (spCurtisDatum n K).nW w) (θ := spTW_torusTheta (K := K) π s)
    (fun t => spTW_nW_inv_conj_diagHom hw hs t) hv
  rwa [spTW_torusChar_comp_theta ι e π s] at hmem

end CFSG.LocalAnalysis.WeakClosure81
