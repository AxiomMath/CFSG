module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Submodule
open Module

private def s16t3_c0 : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private theorem s16t3_c0_det : s16t3_c0.det = 1 := by
  decide +kernel

private def s16t3_C : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨s16t3_c0, s16t3_c0_det⟩

private theorem s16t3_C_pow_seven : s16t3_C ^ 7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem s16t3_C_ne_one : s16t3_C ≠ 1 := by
  intro h
  have h00 : (s16t3_C : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := by
    rw [h]
    rfl
  revert h00
  decide +kernel

private theorem s16t3_C_order : orderOf s16t3_C = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime s16t3_C_pow_seven s16t3_C_ne_one

private noncomputable def s16t3_c : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  Matrix.SpecialLinearGroup.toLin' s16t3_C

private theorem s16t3_c_order : orderOf s16t3_c = 7 := by
  have h := orderOf_injective (Matrix.SpecialLinearGroup.toLin' (n := Fin 3) (R := ZMod 2))
    Matrix.SpecialLinearGroup.toLin'_injective s16t3_C
  simpa [s16t3_c] using h.trans s16t3_C_order

private theorem s16t3_c_ne_one : s16t3_c ≠ 1 := by
  intro h
  have h' : Matrix.SpecialLinearGroup.toLin' s16t3_C = 1 := by
    simpa [s16t3_c] using h
  exact s16t3_C_ne_one (Matrix.SpecialLinearGroup.toLin'_injective (by simpa using h'))

private noncomputable def s16t3_M (n : ℕ) :
    ((Fin 3 ⊕ Fin (n - 3)) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin 3 ⊕ Fin (n - 3)) → ZMod 2) where
  toFun f := Sum.elim (fun a => s16t3_c (fun b => f (Sum.inl b)) a)
    (fun b => f (Sum.inr b))
  invFun f := Sum.elim (fun a => s16t3_c.symm (fun b => f (Sum.inl b)) a)
    (fun b => f (Sum.inr b))
  left_inv f := by
    ext a
    rcases a with a | b <;> simp
  right_inv f := by
    ext a
    rcases a with a | b <;> simp
  map_add' f g := by
    ext a
    rcases a with a | b
    · change s16t3_c ((fun b => f (Sum.inl b)) + (fun b => g (Sum.inl b))) a =
        s16t3_c (fun b => f (Sum.inl b)) a + s16t3_c (fun b => g (Sum.inl b)) a
      rw [map_add]
      rfl
    · rfl
  map_smul' r f := by
    ext a
    rcases a with a | b
    · change s16t3_c (r • (fun b => f (Sum.inl b))) a =
        r • s16t3_c (fun b => f (Sum.inl b)) a
      rw [map_smul]
      rfl
    · rfl

private theorem s16t3_M_apply_inl (n : ℕ) (f : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2) (a : Fin 3) :
    s16t3_M n f (Sum.inl a) = s16t3_c (fun b => f (Sum.inl b)) a := rfl

private theorem s16t3_M_apply_inr (n : ℕ) (f : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2)
    (b : Fin (n - 3)) : s16t3_M n f (Sum.inr b) = f (Sum.inr b) := rfl

private theorem s16t3_M_pow_inl (n k : ℕ) (f : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2) :
    (fun a : Fin 3 => (s16t3_M n ^ k) f (Sum.inl a)) =
      (s16t3_c ^ k) (fun b => f (Sum.inl b)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply]
      ext a
      rw [s16t3_M_apply_inl, ih, pow_succ', LinearEquiv.mul_apply]

private theorem s16t3_M_pow_inr (n k : ℕ) (f : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2) :
    (fun b : Fin (n - 3) => (s16t3_M n ^ k) f (Sum.inr b)) = fun b => f (Sum.inr b) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply]
      ext b
      rw [s16t3_M_apply_inr]
      exact congrFun ih b

private theorem s16t3_M_pow_seven (n : ℕ) : s16t3_M n ^ 7 = 1 := by
  ext f a
  rcases a with a | b
  · rw [show (s16t3_M n ^ 7) f (Sum.inl a) =
        (s16t3_c ^ 7) (fun b => f (Sum.inl b)) a from congrFun (s16t3_M_pow_inl n 7 f) a]
    have h : s16t3_c ^ 7 = 1 := by
      rw [← s16t3_c_order, pow_orderOf_eq_one]
    rw [h]
    rfl
  · rw [show (s16t3_M n ^ 7) f (Sum.inr b) = f (Sum.inr b) from
      congrFun (s16t3_M_pow_inr n 7 f) b]
    rfl

private theorem s16t3_M_ne_one (n : ℕ) : s16t3_M n ≠ 1 := by
  intro h
  have hc : s16t3_c = 1 := by
    ext x a
    let f : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2 := Sum.elim x 0
    have h1 : s16t3_M n f = f := by rw [h]; rfl
    have h2 := congrArg (fun g => g (Sum.inl a)) h1
    rw [s16t3_M_apply_inl] at h2
    simpa [f] using h2
  exact s16t3_c_ne_one hc

private theorem s16t3_M_fix_of_inr_zero (n : ℕ) (g : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2)
    (hg : ∀ a : Fin 3, g (Sum.inl a) = 0) : s16t3_M n g = g := by
  ext a
  rcases a with a | b
  · rw [s16t3_M_apply_inl]
    have hzero : (fun b => g (Sum.inl b)) = 0 := funext hg
    rw [hzero, map_zero]
    exact (hg a).symm
  · rw [s16t3_M_apply_inr]

private theorem s16t3_M_sub_inr_zero (n : ℕ) (g : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2)
    (b : Fin (n - 3)) : (s16t3_M n g - g) (Sum.inr b) = 0 := by
  rw [Pi.sub_apply, s16t3_M_apply_inr, sub_self]

attribute [irreducible] s16t3_M

theorem s16t3_model_exists_fix_seven {n : ℕ} (hn : n = 6 ∨ n = 7)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → Fin n → ZMod 2) (f : κ → Fin n → ZMod 2)
    (hcard : Fintype.card ι + Fintype.card κ ≤ 3) :
    ∃ s : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2),
      orderOf s = 7 ∧ (∀ i, s (v i) = v i) ∧
        (∀ j u, (f j) ⬝ᵥ (s u) = (f j) ⬝ᵥ u) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : NeZero n := by
    rcases hn with rfl | rfl <;> exact ⟨by norm_num⟩
  let V := Fin n → ZMod 2
  let X : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range v)
  let F : V →ₗ[ZMod 2] (κ → ZMod 2) :=
    LinearMap.pi fun j => (dotProductBilin (R := ZMod 2) (S := ZMod 2))
      (f j)
  let H : Submodule (ZMod 2) V := LinearMap.ker F
  let Y : Submodule (ZMod 2) V := X ⊓ H
  have hF_apply : ∀ (u : V) (j : κ), F u j = f j ⬝ᵥ u := fun u j => rfl
  have hH_mem : ∀ u : V, u ∈ H ↔ ∀ j, f j ⬝ᵥ u = 0 := by
    intro u
    change F u = 0 ↔ ∀ j, f j ⬝ᵥ u = 0
    constructor
    · intro h j
      have := congrFun h j
      simpa [hF_apply] using this
    · intro h
      ext j
      simpa [hF_apply] using h j
  have hfrV : Module.finrank (ZMod 2) V = n := by
    simp [V, Module.finrank_fintype_fun_eq_card (R := ZMod 2)]
  have hfr_range : Module.finrank (ZMod 2) (LinearMap.range F) ≤ Fintype.card κ := by
    calc Module.finrank (ZMod 2) (LinearMap.range F)
        ≤ Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (κ → ZMod 2)) :=
          Submodule.finrank_mono le_top
      _ = Module.finrank (ZMod 2) (κ → ZMod 2) := finrank_top _ _
      _ = Fintype.card κ := Module.finrank_fintype_fun_eq_card (R := ZMod 2)
  have hfrH : n - Fintype.card κ ≤ Module.finrank (ZMod 2) H := by
    have h := LinearMap.finrank_range_add_finrank_ker F
    have hker : Module.finrank (ZMod 2) (LinearMap.ker F) =
        Module.finrank (ZMod 2) H := rfl
    omega
  have hfrX : Module.finrank (ZMod 2) X ≤ Fintype.card ι := by
    calc Module.finrank (ZMod 2) X
        ≤ (Set.range v).toFinset.card := finrank_span_le_card _
      _ = Fintype.card (Set.range v) := Set.toFinset_card _
      _ ≤ Fintype.card ι := Fintype.card_range_le v
  have hfrY : Module.finrank (ZMod 2) Y ≤ Fintype.card ι :=
    le_trans (Submodule.finrank_mono inf_le_left) hfrX
  have hHge : 3 + Module.finrank (ZMod 2) Y ≤ Module.finrank (ZMod 2) H := by
    have hn6 : 6 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    omega
  let Yh : Submodule (ZMod 2) H := Y.comap H.subtype
  obtain ⟨Ch, hCh⟩ := Submodule.exists_isCompl Yh
  let C1 : Submodule (ZMod 2) V := Ch.map H.subtype
  have hC1leH : C1 ≤ H := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hYhfin : Module.finrank (ZMod 2) Yh = Module.finrank (ZMod 2) Y :=
    (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  have hChfin : Module.finrank (ZMod 2) C1 = Module.finrank (ZMod 2) Ch :=
    Submodule.finrank_map_subtype_eq H Ch
  have hHY : Module.finrank (ZMod 2) H =
      Module.finrank (ZMod 2) Y + Module.finrank (ZMod 2) C1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hCh
    rw [hYhfin, ← hChfin] at h
    exact h.symm
  have hYdisj : Y ⊓ C1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := hx.1
    have hxC : x ∈ C1 := hx.2
    obtain ⟨c, hc, hcx⟩ := Submodule.mem_map.mp hxC
    have hcY : c ∈ Yh := by
      change H.subtype c ∈ Y
      rw [hcx]
      exact hxY
    have hcbot : c ∈ (⊥ : Submodule (ZMod 2) H) := by
      rw [← hCh.disjoint.eq_bot]
      exact ⟨hcY, hc⟩
    rw [Submodule.mem_bot] at hcbot
    rw [← hcx, hcbot]
    change (0 : V) ∈ (⊥ : Submodule (ZMod 2) V)
    exact Submodule.zero_mem _
  have hC1ge : 3 ≤ Module.finrank (ZMod 2) C1 := by omega
  obtain ⟨t, ht⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := C1) hC1ge
  let T : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range fun i : Fin 3 => (t i : V))
  have htV : LinearIndependent (ZMod 2) fun i : Fin 3 => (t i : V) :=
    ht.map' C1.subtype (by simp)
  have hTfin : Module.finrank (ZMod 2) T = 3 := by
    change Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range fun i : Fin 3 => (t i : V))) = 3
    rw [finrank_span_eq_card htV]
    simp
  have hTleC1 : T ≤ C1 := by
    change Submodule.span (ZMod 2) (Set.range fun i : Fin 3 => (t i : V)) ≤ C1
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (t i).2
  have hTleH : T ≤ H := le_trans hTleC1 hC1leH
  have hTX : T ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := ⟨hx.2, hTleH hx.1⟩
    have hxbot : x ∈ Y ⊓ C1 := ⟨hxY, hTleC1 hx.1⟩
    rwa [hYdisj, Submodule.mem_bot] at hxbot
  let Z₀ : Submodule (ZMod 2) V := X ⊔ T
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Z₀
  let C : Submodule (ZMod 2) V := X ⊔ D
  have hTC : IsCompl T C := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxT : x ∈ T := hx.1
      have hxC : x ∈ C := hx.2
      obtain ⟨a, ha, d, hd, had⟩ := Submodule.mem_sup.mp hxC
      have hxd : x - a = d := by rw [← had]; abel
      have hdZ : d ∈ Z₀ := by
        rw [← hxd]
        exact Z₀.sub_mem (Submodule.mem_sup_right hxT) (Submodule.mem_sup_left ha)
      have hdD : d ∈ D := hd
      have hd0 : d = 0 := by
        have : d ∈ Z₀ ⊓ D := ⟨hdZ, hdD⟩
        rw [hD.disjoint.eq_bot] at this
        exact this
      have hxX : x ∈ X := by
        rw [← had, hd0, add_zero]
        exact ha
      have : x ∈ T ⊓ X := ⟨hxT, hxX⟩
      rw [hTX] at this
      exact this
    · rw [codisjoint_iff]
      calc T ⊔ C = T ⊔ (X ⊔ D) := rfl
        _ = (T ⊔ X) ⊔ D := by rw [sup_assoc]
        _ = (X ⊔ T) ⊔ D := by rw [sup_comm T X]
        _ = Z₀ ⊔ D := rfl
        _ = ⊤ := hD.codisjoint.eq_top
  have hXC : X ≤ C := le_sup_left
  have hCfin : Module.finrank (ZMod 2) C = n - 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hTC
    rw [hTfin, hfrV] at h
    omega
  let eT : T ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hTfin]; simp)
  let eC : C ≃ₗ[ZMod 2] (Fin (n - 3) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hCfin]; simp)
  let bT : Basis (Fin 3) (ZMod 2) T := (Pi.basisFun (ZMod 2) (Fin 3)).map eT.symm
  let bC : Basis (Fin (n - 3)) (ZMod 2) C := (Pi.basisFun (ZMod 2) (Fin (n - 3))).map eC.symm
  let b : Basis (Fin 3 ⊕ Fin (n - 3)) (ZMod 2) V :=
    (bT.prod bC).map (Submodule.prodEquivOfIsCompl T C hTC)
  let φ : V ≃ₗ[ZMod 2] ((Fin 3 ⊕ Fin (n - 3)) → ZMod 2) := b.equivFun
  let s : V ≃ₗ[ZMod 2] V := (φ.trans (s16t3_M n)).trans φ.symm
  have hb_inl_mem : ∀ a : Fin 3, b (Sum.inl a) ∈ T := by
    intro a
    have h1 : b (Sum.inl a) =
        (Submodule.prodEquivOfIsCompl T C hTC) ((bT.prod bC) (Sum.inl a)) := rfl
    rw [h1, Basis.prod_apply]
    simp only [Sum.elim_inl, Submodule.prodEquivOfIsCompl, LinearEquiv.coe_mk,
      Submodule.coe_subtype, Submodule.coe_add, Submodule.coe_zero]
    exact T.add_mem (bT a).2 T.zero_mem
  have hφ_mem_C : ∀ x ∈ C, ∀ a : Fin 3, φ x (Sum.inl a) = 0 := by
    intro x hx a
    have h1 : φ x = (bT.prod bC).equivFun
        ((Submodule.prodEquivOfIsCompl T C hTC).symm (⟨x, hx⟩ : C)) := rfl
    rw [h1, Submodule.prodEquivOfIsCompl_symm_apply_right T C]
    rw [Basis.equivFun_apply, Basis.prod_repr_inl]
    simp
  have hφ_symm_mem_T : ∀ g : (Fin 3 ⊕ Fin (n - 3)) → ZMod 2,
      (∀ c : Fin (n - 3), g (Sum.inr c) = 0) → φ.symm g ∈ T := by
    intro g hg
    rw [show φ.symm = b.equivFun.symm from rfl, Basis.equivFun_symm_apply]
    rw [Fintype.sum_sum_type]
    have hzero : ∑ c : Fin (n - 3), g (Sum.inr c) • b (Sum.inr c) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [hg c, zero_smul]
    rw [hzero, add_zero]
    exact Submodule.sum_mem T fun (i : Fin 3) _ => T.smul_mem _ (hb_inl_mem i)
  have hfixC : ∀ x ∈ C, s x = x := by
    intro x hx
    have h1 : s x = φ.symm (s16t3_M n (φ x)) := rfl
    rw [h1, s16t3_M_fix_of_inr_zero n (φ x) (hφ_mem_C x hx)]
    exact φ.symm_apply_apply x
  have hsubT : ∀ u : V, s u - u ∈ T := by
    intro u
    have h1 : s u = φ.symm (s16t3_M n (φ u)) := rfl
    have h2 : φ (s u) = s16t3_M n (φ u) := by
      rw [h1, φ.apply_symm_apply]
    have h3 : s u - u = φ.symm (s16t3_M n (φ u) - φ u) := by
      apply φ.injective
      rw [map_sub, h2, φ.apply_symm_apply]
    rw [h3]
    exact hφ_symm_mem_T _ (s16t3_M_sub_inr_zero n (φ u))
  have hs_apply : ∀ y : V, s y = φ.symm ((s16t3_M n) (φ y)) := fun y => rfl
  have hpow : ∀ (k : ℕ) (x : V), (s ^ k) x = φ.symm ((s16t3_M n ^ k) (φ x)) := by
    intro k
    induction k with
    | zero =>
        intro x
        change x = φ.symm (φ x)
        exact (φ.symm_apply_apply x).symm
    | succ k ih =>
        intro x
        rw [pow_succ', LinearEquiv.mul_apply, ih, hs_apply, φ.apply_symm_apply]
        rw [pow_succ', LinearEquiv.mul_apply]
  have hs7 : s ^ 7 = 1 := by
    apply LinearEquiv.ext
    intro x
    rw [hpow 7 x, s16t3_M_pow_seven n]
    change φ.symm (φ x) = x
    exact φ.symm_apply_apply x
  have hsne : s ≠ 1 := by
    intro h
    have hM : s16t3_M n = 1 := by
      apply LinearEquiv.ext
      intro y
      have h1 := congrArg (fun e => e (φ.symm y)) h
      have h2 : s (φ.symm y) = φ.symm ((s16t3_M n) y) := by
        rw [hs_apply, φ.apply_symm_apply]
      rw [h2] at h1
      change φ.symm ((s16t3_M n) y) = φ.symm y at h1
      exact φ.symm.injective h1
    exact s16t3_M_ne_one n hM
  have hsorder : orderOf s = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact orderOf_eq_prime hs7 hsne
  refine ⟨s, hsorder, ?_, ?_⟩
  · intro i
    exact hfixC (v i) (hXC (Submodule.subset_span ⟨i, rfl⟩))
  · intro j u
    have hmem : s u - u ∈ T := hsubT u
    have h0 : (f j) ⬝ᵥ (s u - u) = 0 := by
      have : s u - u ∈ H := hTleH hmem
      rw [hH_mem] at this
      exact this j
    calc (f j) ⬝ᵥ (s u) = (f j) ⬝ᵥ ((s u - u) + u) := by rw [sub_add_cancel]
      _ = (f j) ⬝ᵥ (s u - u) + (f j) ⬝ᵥ u := by rw [dotProduct_add]
      _ = (f j) ⬝ᵥ u := by rw [h0, zero_add]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
