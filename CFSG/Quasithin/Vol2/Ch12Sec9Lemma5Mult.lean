module

public import Mathlib.LinearAlgebra.Center
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.Quasithin.H13.Mult

open Module

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

section Y

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [Module.Finite (ZMod 2) Y]

theorem eq_zero_or_eq_id_of_commute (hd : 2 ≤ finrank (ZMod 2) Y) {φ : Y →ₗ[ZMod 2] Y}
    (hφ : ∀ τ : Y ≃ₗ[ZMod 2] Y, ∀ y, φ (τ y) = τ (φ y)) : φ = 0 ∨ φ = LinearMap.id := by
  let b := Module.finBasis (ZMod 2) Y
  have : Nontrivial (Fin (finrank (ZMod 2) Y)) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨a, ha⟩ := LinearMap.commute_transvections_iff_of_basis b (f := φ) fun i j r hij => by
    have h0 : b.coord i (r • b j) = 0 := by
      rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hij, smul_zero]
    show φ * _ = _ * φ
    refine LinearMap.ext fun y => ?_
    exact hφ (LinearEquiv.transvection h0) y
  rcases zmod_two_eq_zero_or_one (a : ZMod 2) with h | h
  · left
    rw [ha, Subring.smul_def, h, zero_smul]
  · right
    rw [ha, Subring.smul_def, h, one_smul]
    rfl

omit [Module.Finite (ZMod 2) Y] in
theorem exists_linearEquiv_apply_eq {y₀ y : Y} (hy₀ : y₀ ≠ 0) (hy : y ≠ 0) :
    ∃ τ : Y ≃ₗ[ZMod 2] Y, τ y₀ = y := by
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Y y₀ hy₀).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Y y hy)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have h1 := hg ⟨y₀, Submodule.mem_span_singleton_self y₀⟩
  have h2 : f ⟨y₀, Submodule.mem_span_singleton_self y₀⟩ =
      ⟨y, Submodule.mem_span_singleton_self y⟩ := by
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod 2) Y y₀ hy₀, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  rw [← h1, h2]

end Y

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

structure Hyp (Ls : Subgroup (E ≃ₗ[ZMod 2] E)) (Y : Submodule (ZMod 2) E) : Prop where
  mapsTo : ∀ l ∈ Ls, ∀ y ∈ Y, l y ∈ Y
  onto : ∀ τ : Y ≃ₗ[ZMod 2] Y, ∃ l ∈ Ls, ∀ y : Y, l (y : E) = (τ y : E)
  two_le : 2 ≤ finrank (ZMod 2) Y

abbrev Cent (Ls : Subgroup (E ≃ₗ[ZMod 2] E)) : Subgroup (E ≃ₗ[ZMod 2] E) :=
  Subgroup.centralizer (Ls : Set (E ≃ₗ[ZMod 2] E))

variable {Ls : Subgroup (E ≃ₗ[ZMod 2] E)} {Y : Submodule (ZMod 2) E}

theorem comm_apply {c l : E ≃ₗ[ZMod 2] E} (hc : c ∈ Cent Ls)
    (hl : l ∈ Ls) (x : E) : c (l x) = l (c x) := by
  have h1 := LinearEquiv.congr_fun (Subgroup.mem_centralizer_iff.1 hc l hl) x
  simp only [LinearEquiv.mul_apply] at h1
  exact h1.symm

theorem eq_bot_or_le_of_invariant [Module.Finite (ZMod 2) E] (h : Hyp Ls Y)
    {c : E ≃ₗ[ZMod 2] E} (hc : c ∈ Cent Ls)
    {Z : Submodule (ZMod 2) E} (hZ : ∀ l ∈ Ls, ∀ z ∈ Z, l z ∈ Z)
    (hZY : Z ≤ Y.map (c : E →ₗ[ZMod 2] E)) : Z = ⊥ ∨ Y.map (c : E →ₗ[ZMod 2] E) ≤ Z := by
  by_cases hZ0 : Z = ⊥
  · exact Or.inl hZ0
  right
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  obtain ⟨y₀, hy₀, rfl⟩ := hZY hz
  rintro _ ⟨y, hy, rfl⟩
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]
    exact Z.zero_mem
  have hy₀0 : (⟨y₀, hy₀⟩ : Y) ≠ 0 := by
    intro h0
    apply hz0
    have : y₀ = 0 := congrArg Subtype.val h0
    simp [this]
  have hy0' : (⟨y, hy⟩ : Y) ≠ 0 := fun h0 => hy0 (congrArg Subtype.val h0)
  obtain ⟨τ, hτ⟩ := exists_linearEquiv_apply_eq hy₀0 hy0'
  obtain ⟨l, hl, hlτ⟩ := h.onto τ
  have h1 : l y₀ = y := by
    have := hlτ ⟨y₀, hy₀⟩
    rw [hτ] at this
    exact this
  show c y ∈ Z
  rw [← h1, comm_apply hc hl]
  exact hZ l hl _ hz

@[expose] def psi (Y : Submodule (ZMod 2) E) {m : ℕ} (c : Fin m → (E ≃ₗ[ZMod 2] E)) :
    (Fin m → Y) →ₗ[ZMod 2] E where
  toFun f := ∑ j, c j (f j : E)
  map_add' f g := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem psi_apply {m : ℕ} (c : Fin m → (E ≃ₗ[ZMod 2] E)) (f : Fin m → Y) :
    psi Y c f = ∑ j, c j (f j : E) := rfl

theorem apply_psi (h : Hyp Ls Y) {m : ℕ} {c : Fin m → (E ≃ₗ[ZMod 2] E)}
    (hc : ∀ j, c j ∈ Cent Ls) {l : E ≃ₗ[ZMod 2] E} (hl : l ∈ Ls)
    (f : Fin m → Y) :
    l (psi Y c f) = psi Y c (fun j => ⟨l (f j), h.mapsTo l hl _ (f j).2⟩) := by
  simp only [psi_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => (comm_apply (hc j) hl _).symm

theorem exists_bijective_psi [Finite E] (h : Hyp Ls Y)
    (hspan : ∀ e : E, e ∈ ⨆ c ∈ Cent Ls,
      Y.map (c : E →ₗ[ZMod 2] E)) :
    ∃ (m : ℕ) (c : Fin m → (E ≃ₗ[ZMod 2] E)),
      (∀ j, c j ∈ Cent Ls) ∧ Function.Bijective (psi Y c) := by
  classical
  have : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  set Cs := Cent Ls with hCs
  let P : ℕ → Prop := fun k => ∃ c : Fin k → (E ≃ₗ[ZMod 2] E),
    (∀ j, c j ∈ Cs) ∧ Function.Injective (psi Y c)
  have hP0 : P 0 := ⟨Fin.elim0, fun j => j.elim0, fun f g _ => funext fun j => j.elim0⟩
  have hY2 : 2 ≤ Nat.card Y := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y)
    rw [Nat.card_zmod] at h1
    rw [h1]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) Y := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  have hbound : ∀ k, P k → k < Nat.card E := by
    rintro k ⟨c, -, hinj⟩
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fun, Nat.card_fin] at h1
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ Nat.card Y ^ k := Nat.pow_le_pow_left hY2 k
      _ ≤ Nat.card E := h1
  set k₀ := Nat.findGreatest P (Nat.card E) with hk₀def
  have hk₀ : P k₀ := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hk₁ : ¬ P (k₀ + 1) := by
    intro hP1
    have := hbound _ hP1
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k₀) (by omega) hP1
  obtain ⟨c, hcC, hinj⟩ := hk₀
  refine ⟨k₀, c, hcC, hinj, ?_⟩
  by_contra hsurj
  have hR : LinearMap.range (psi Y c) ≠ ⊤ := fun hr => hsurj (LinearMap.range_eq_top.1 hr)
  obtain ⟨c', hc', hc'R⟩ : ∃ c' ∈ Cs,
      ¬ Y.map (c' : E →ₗ[ZMod 2] E) ≤ LinearMap.range (psi Y c) := by
    by_contra hall
    push Not at hall
    apply hR
    rw [eq_top_iff]
    intro e _
    exact (iSup₂_le hall) (hspan e)
  have hZinv : ∀ l ∈ Ls, ∀ z ∈ LinearMap.range (psi Y c) ⊓ Y.map (c' : E →ₗ[ZMod 2] E),
      l z ∈ LinearMap.range (psi Y c) ⊓ Y.map (c' : E →ₗ[ZMod 2] E) := by
    rintro l hl z ⟨⟨f, rfl⟩, ⟨y, hy, hyz⟩⟩
    refine ⟨⟨_, (apply_psi h hcC hl f).symm⟩, ⟨l y, h.mapsTo l hl y hy, ?_⟩⟩
    rw [← hyz]
    exact comm_apply hc' hl y
  rcases eq_bot_or_le_of_invariant h hc' hZinv inf_le_right with hZ | hZ
  · apply hk₁
    refine ⟨Fin.snoc c c', fun j => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]
        exact hc'
      · rw [Fin.snoc_castSucc]
        exact hcC i
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      have hsum : psi Y (Fin.snoc c c' : Fin (k₀ + 1) → (E ≃ₗ[ZMod 2] E)) f =
          psi Y c (fun i => f i.castSucc) + c' (f (Fin.last k₀)) := by
        simp only [psi_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hsum] at hf
      have hmem : c' (f (Fin.last k₀) : E) ∈
          LinearMap.range (psi Y c) ⊓ Y.map (c' : E →ₗ[ZMod 2] E) := by
        refine ⟨⟨-(fun i => f i.castSucc), ?_⟩, ⟨_, (f (Fin.last k₀)).2, rfl⟩⟩
        rw [map_neg, neg_eq_iff_add_eq_zero]
        exact hf
      rw [hZ, Submodule.mem_bot] at hmem
      have hlast : f (Fin.last k₀) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero]
        exact c'.injective (by rw [hmem, map_zero])
      have hrest : (fun i : Fin k₀ => f i.castSucc) = 0 := by
        apply hinj
        rw [map_zero]
        rw [hmem, add_zero] at hf
        exact hf
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact hlast
      · exact congrFun hrest i
  · exact hc'R (hZ.trans inf_le_left)

theorem Hyp.nontrivial (h : Hyp Ls Y) : Nontrivial Y := by
  apply Module.nontrivial_of_finrank_pos (R := ZMod 2)
  have := h.two_le
  omega

section Coef

variable (h : Hyp Ls Y) {m : ℕ} {c : Fin m → (E ≃ₗ[ZMod 2] E)}
  (hc : ∀ j, c j ∈ Cent Ls) (hbij : Function.Bijective (psi Y c))

include h hc hbij

theorem symm_apply_apply_of_mem {l : E ≃ₗ[ZMod 2] E} (hl : l ∈ Ls) (x : E) (i : Fin m) :
    ((LinearEquiv.ofBijective (psi Y c) hbij).symm (l x) i : E) =
      l ((LinearEquiv.ofBijective (psi Y c) hbij).symm x i) := by
  set Ψ := LinearEquiv.ofBijective (psi Y c) hbij
  have h1 : l x = Ψ (fun j => ⟨l (Ψ.symm x j), h.mapsTo l hl _ (Ψ.symm x j).2⟩) := by
    have h2 := apply_psi h hc hl (Ψ.symm x)
    have h3 : psi Y c (Ψ.symm x) = x := Ψ.apply_symm_apply x
    rw [h3] at h2
    exact h2
  rw [h1, LinearEquiv.symm_apply_apply]

@[expose] noncomputable def block (e : E ≃ₗ[ZMod 2] E) (i j : Fin m) : Y →ₗ[ZMod 2] Y :=
  (LinearMap.proj i).comp ((LinearEquiv.ofBijective (psi Y c) hbij).symm.toLinearMap.comp
    ((e : E →ₗ[ZMod 2] E).comp (((c j : E →ₗ[ZMod 2] E)).comp Y.subtype)))

omit h hc in
theorem block_apply (e : E ≃ₗ[ZMod 2] E) (i j : Fin m) (y : Y) :
    block hbij e i j y = (LinearEquiv.ofBijective (psi Y c) hbij).symm (e (c j y)) i := rfl

theorem block_eq_zero_or_eq_id [Finite E] {e : E ≃ₗ[ZMod 2] E}
    (he : e ∈ Cent Ls) (i j : Fin m) :
    block hbij e i j = 0 ∨ block hbij e i j = LinearMap.id := by
  have : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  refine eq_zero_or_eq_id_of_commute h.two_le fun τ y => ?_
  obtain ⟨l, hl, hlτ⟩ := h.onto τ
  apply Subtype.ext
  rw [← hlτ, block_apply, block_apply, ← hlτ, comm_apply (hc j) hl, comm_apply he hl]
  exact symm_apply_apply_of_mem h hc hbij hl _ i

@[expose] noncomputable def coef (e : E ≃ₗ[ZMod 2] E) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => by
    classical
    exact if block hbij e i j = 0 then 0 else 1

omit h hc in
theorem block_eq_smul {e : E ≃ₗ[ZMod 2] E} (i j : Fin m)
    (hb : block hbij e i j = 0 ∨ block hbij e i j = LinearMap.id) :
    block hbij e i j = coef hbij e i j • LinearMap.id := by
  classical
  simp only [coef, Matrix.of_apply]
  rcases hb with hb | hb
  · rw [ite_eq_left hb, zero_smul, hb]
  · by_cases h0 : block hbij e i j = 0
    · rw [ite_eq_left h0, zero_smul, h0]
    · rw [ite_eq_right h0, one_smul, hb]

@[expose] def act (A : Matrix (Fin m) (Fin m) (ZMod 2)) (f : Fin m → Y) : Fin m → Y :=
  fun i => ∑ j, A i j • f j

omit h hc hbij in
theorem act_one (f : Fin m → Y) : act (1 : Matrix (Fin m) (Fin m) (ZMod 2)) f = f := by
  classical
  funext i
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

omit h hc hbij in
theorem act_mul (A B : Matrix (Fin m) (Fin m) (ZMod 2)) (f : Fin m → Y) :
    act (A * B) f = act A (act B f) := by
  funext i
  simp only [act, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

omit h hc hbij in
theorem act_injective [Nontrivial Y] {A B : Matrix (Fin m) (Fin m) (ZMod 2)}
    (hAB : ∀ f : Fin m → Y, act A f = act B f) : A = B := by
  classical
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  ext i j
  have h1 := congrFun (hAB (Pi.single j y)) i
  simp only [act, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h1
  exact smul_left_injective (ZMod 2) hy h1

theorem apply_psi_eq [Finite E] {e : E ≃ₗ[ZMod 2] E} (he : e ∈ Cent Ls)
    (f : Fin m → Y) : e (psi Y c f) = psi Y c (act (coef hbij e) f) := by
  set Ψ := LinearEquiv.ofBijective (psi Y c) hbij
  have key : Ψ.symm (e (psi Y c f)) = act (coef hbij e) f := by
    funext i
    rw [psi_apply, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := LinearMap.congr_fun (block_eq_smul hbij i j
      (block_eq_zero_or_eq_id h hc hbij he i j)) (f j)
    rw [block_apply] at h1
    rw [h1]
    rfl
  have h2 := congrArg Ψ key
  rw [LinearEquiv.apply_symm_apply] at h2
  exact h2

theorem coef_one [Finite E] : coef hbij (1 : E ≃ₗ[ZMod 2] E) = 1 := by
  have := h.nontrivial
  refine act_injective fun f => hbij.1 ?_
  rw [← apply_psi_eq h hc hbij (Subgroup.one_mem _), act_one]
  rfl

theorem coef_mul [Finite E] {e e' : E ≃ₗ[ZMod 2] E} (he : e ∈ Cent Ls) (he' : e' ∈ Cent Ls) :
    coef hbij (e * e') = coef hbij e * coef hbij e' := by
  have := h.nontrivial
  refine act_injective fun f => hbij.1 ?_
  rw [← apply_psi_eq h hc hbij (Subgroup.mul_mem _ he he'), act_mul,
    ← apply_psi_eq h hc hbij he, ← apply_psi_eq h hc hbij he', LinearEquiv.mul_apply]

@[expose] noncomputable def coefHom [Finite E] : ↥(Cent Ls) →* Matrix (Fin m) (Fin m) (ZMod 2) where
  toFun e := coef hbij (e : E ≃ₗ[ZMod 2] E)
  map_one' := coef_one h hc hbij
  map_mul' e e' := coef_mul h hc hbij e.2 e'.2

@[expose] noncomputable def theta [Finite E] :
    ↥(Cent Ls) →* ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) where
  toFun e :=
    { Matrix.mulVecLin (coefHom h hc hbij e) with
      invFun := (coefHom h hc hbij e⁻¹).mulVec
      left_inv := fun x => by
        show (coefHom h hc hbij e⁻¹).mulVec ((coefHom h hc hbij e).mulVec x) = x
        rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
      right_inv := fun x => by
        show (coefHom h hc hbij e).mulVec ((coefHom h hc hbij e⁻¹).mulVec x) = x
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec] }
  map_one' := LinearEquiv.ext fun x => by
    show (coefHom h hc hbij 1).mulVec x = x
    rw [map_one, Matrix.one_mulVec]
  map_mul' e e' := LinearEquiv.ext fun x => by
    show (coefHom h hc hbij (e * e')).mulVec x =
      (coefHom h hc hbij e).mulVec ((coefHom h hc hbij e').mulVec x)
    rw [map_mul, Matrix.mulVec_mulVec]

theorem theta_apply [Finite E] (e : ↥(Cent Ls)) (x : Fin m → ZMod 2) :
    theta h hc hbij e x = (coef hbij (e : E ≃ₗ[ZMod 2] E)).mulVec x := rfl

theorem eq_one_of_theta_eq_one [Finite E] {e : ↥(Cent Ls)} (he : theta h hc hbij e = 1) :
    e = 1 := by
  have h1 : coef hbij (e : E ≃ₗ[ZMod 2] E) = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have := LinearEquiv.congr_fun he x
    rw [theta_apply] at this
    rw [Matrix.toLin'_apply, this, Matrix.toLin'_one]
    rfl
  apply Subtype.ext
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨f, rfl⟩ := hbij.2 x
  rw [apply_psi_eq h hc hbij e.2, h1, act_one]
  rfl

@[expose] noncomputable def coords [Module.Finite (ZMod 2) Y] :
    (Fin m → Y) ≃ (Fin (finrank (ZMod 2) Y) → Fin m → ZMod 2) where
  toFun f l i := (Module.finBasis (ZMod 2) Y).equivFun (f i) l
  invFun F i := (Module.finBasis (ZMod 2) Y).equivFun.symm (fun l => F l i)
  left_inv f := by
    funext i
    simp only [LinearEquiv.symm_apply_apply]
  right_inv F := by
    funext l i
    simp only [LinearEquiv.apply_symm_apply]

omit h hc hbij in
theorem coords_act [Module.Finite (ZMod 2) Y] (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (f : Fin m → Y) (l : Fin (finrank (ZMod 2) Y)) :
    coords (act A f) l = A.mulVec (coords f l) := by
  funext i
  simp only [coords, Equiv.coe_fn_mk, act, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]

theorem card_fix [Finite E] (B : Subgroup ↥(Cent Ls)) :
    Nat.card {x : E // ∀ b ∈ B, (b : E ≃ₗ[ZMod 2] E) x = x} =
      Nat.card {v : Fin m → ZMod 2 // ∀ b ∈ B, theta h hc hbij b v = v} ^
        finrank (ZMod 2) Y := by
  have : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  set Ψ := LinearEquiv.ofBijective (psi Y c) hbij
  have e1 : {x : E // ∀ b ∈ B, (b : E ≃ₗ[ZMod 2] E) x = x} ≃
      {F : Fin (finrank (ZMod 2) Y) → Fin m → ZMod 2 //
        ∀ l, ∀ b ∈ B, (coef hbij (b : E ≃ₗ[ZMod 2] E)).mulVec (F l) = F l} := by
    refine Equiv.subtypeEquiv (Ψ.symm.toEquiv.trans coords) fun x => ?_
    obtain ⟨f, rfl⟩ := hbij.2 x
    have hΨf : Ψ.symm (psi Y c f) = f := Ψ.symm_apply_apply f
    simp only [Equiv.trans_apply, LinearEquiv.coe_toEquiv, hΨf]
    constructor
    · intro hx l b hb
      have h1 := hx b hb
      rw [apply_psi_eq h hc hbij b.2 f] at h1
      have h2 : act (coef hbij (b : E ≃ₗ[ZMod 2] E)) f = f := hbij.1 h1
      rw [← coords_act, h2]
    · intro hF b hb
      rw [apply_psi_eq h hc hbij b.2 f]
      congr 1
      apply coords.injective
      funext l
      rw [coords_act]
      exact hF l b hb
  have e2 := e1.trans (Equiv.subtypePiEquivPi (p := fun _ (v : Fin m → ZMod 2) =>
    ∀ b ∈ B, (coef hbij (b : E ≃ₗ[ZMod 2] E)).mulVec v = v))
  rw [Nat.card_congr e2, Nat.card_fun, Nat.card_fin]
  rfl

omit h hc in
theorem card_eq [Finite E] : Nat.card E = (2 ^ m) ^ finrank (ZMod 2) Y := by
  have : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  set Ψ := LinearEquiv.ofBijective (psi Y c) hbij
  rw [Nat.card_congr (Ψ.symm.toEquiv.trans coords), Nat.card_fun, Nat.card_fun, Nat.card_fin,
    Nat.card_fin, Nat.card_zmod]

end Coef

section Sup

theorem inf_eq_bot [Finite E] (h : Hyp Ls Y)
    (hspan : ∀ e : E, e ∈ ⨆ c ∈ Cent Ls, Y.map (c : E →ₗ[ZMod 2] E)) : Cent Ls ⊓ Ls = ⊥ := by
  have : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  have hY := h.nontrivial
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxL⟩
  set φ : Y →ₗ[ZMod 2] Y := (x : E →ₗ[ZMod 2] E).restrict (h.mapsTo x hxL) with hφ
  have hφτ : ∀ τ : Y ≃ₗ[ZMod 2] Y, ∀ y, φ (τ y) = τ (φ y) := by
    intro τ y
    obtain ⟨l, hl, hlτ⟩ := h.onto τ
    apply Subtype.ext
    show x (τ y : E) = (τ (φ y) : E)
    rw [← hlτ, ← hlτ]
    exact comm_apply hxC hl _
  have hfix : ∀ y ∈ Y, x y = y := by
    rcases eq_zero_or_eq_id_of_commute h.two_le hφτ with h0 | h1
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      have h2 : φ y = 0 := by rw [h0]; rfl
      apply hy
      apply Subtype.ext
      have h3 : x (y : E) = 0 := congrArg Subtype.val h2
      have h4 : x (y : E) = x 0 := by rw [h3, map_zero]
      simpa using x.injective h4
    · intro y hy
      exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨y, hy⟩)
  have hle : (⨆ c ∈ Cent Ls, Y.map (c : E →ₗ[ZMod 2] E)) ≤
      LinearMap.ker ((x : E →ₗ[ZMod 2] E) - LinearMap.id) := by
    refine iSup₂_le fun c hc => ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    show x (c y) = c y
    rw [← comm_apply hc hxL, hfix y hy]
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun e => ?_
  have := hle (hspan e)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  exact this

theorem le_normalizer_cent : Cent Ls ≤ Subgroup.normalizer (Ls : Set (E ≃ₗ[ZMod 2] E)) := by
  intro a ha
  have hconj : ∀ b ∈ Cent Ls, ∀ l ∈ Ls, b * l * b⁻¹ = l := fun b hb l hl => by
    rw [← Subgroup.mem_centralizer_iff.1 hb l hl]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    rw [hconj a ha l hl]
    exact hl
  · intro hl
    have h1 := hconj a⁻¹ (Subgroup.inv_mem _ ha) _ hl
    rw [show a⁻¹ * (a * l * a⁻¹) * a⁻¹⁻¹ = l by group] at h1
    rw [h1]
    exact hl

theorem exists_mul_eq_of_mem_sup {g : E ≃ₗ[ZMod 2] E} (hg : g ∈ Cent Ls ⊔ Ls) :
    ∃ a ∈ Cent Ls, ∃ l ∈ Ls, a * l = g := by
  have h1 : g ∈ ((Cent Ls ⊔ Ls : Subgroup _) : Set (E ≃ₗ[ZMod 2] E)) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ le_normalizer_cent] at h1
  obtain ⟨a, ha, l, hl, hal⟩ := h1
  exact ⟨a, ha, l, hl, hal⟩

theorem eq_of_mul_eq (hinf : Cent Ls ⊓ Ls = ⊥) {a a' l l' : E ≃ₗ[ZMod 2] E}
    (ha : a ∈ Cent Ls) (ha' : a' ∈ Cent Ls) (hl : l ∈ Ls) (hl' : l' ∈ Ls)
    (he : a * l = a' * l') : a = a' := by
  have h1 : a'⁻¹ * a = l' * l⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * l) * l⁻¹ := by group
      _ = a'⁻¹ * (a' * l') * l⁻¹ := by rw [he]
      _ = l' * l⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ Cent Ls ⊓ Ls :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha, h1 ▸ Subgroup.mul_mem _ hl' (inv_mem hl)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  calc a = a' * (a'⁻¹ * a) := by group
    _ = a' := by rw [h2, mul_one]

@[expose] noncomputable def projFun (g : ↥(Cent Ls ⊔ Ls)) : ↥(Cent Ls) :=
  ⟨Classical.choose (exists_mul_eq_of_mem_sup g.2),
    (Classical.choose_spec (exists_mul_eq_of_mem_sup g.2)).1⟩

theorem projFun_spec (g : ↥(Cent Ls ⊔ Ls)) :
    ∃ l ∈ Ls, ((projFun g : ↥(Cent Ls)) : E ≃ₗ[ZMod 2] E) * l = g :=
  (Classical.choose_spec (exists_mul_eq_of_mem_sup g.2)).2

theorem projFun_eq (hinf : Cent Ls ⊓ Ls = ⊥) {g : ↥(Cent Ls ⊔ Ls)} {a l : E ≃ₗ[ZMod 2] E}
    (ha : a ∈ Cent Ls) (hl : l ∈ Ls) (he : a * l = g) : projFun g = ⟨a, ha⟩ := by
  obtain ⟨l', hl', h'⟩ := projFun_spec g
  exact Subtype.ext (eq_of_mul_eq hinf (projFun g).2 ha hl' hl (h'.trans he.symm))

@[expose] noncomputable def proj (hinf : Cent Ls ⊓ Ls = ⊥) : ↥(Cent Ls ⊔ Ls) →* ↥(Cent Ls) where
  toFun := projFun
  map_one' := projFun_eq hinf (Subgroup.one_mem _) (Subgroup.one_mem _) (mul_one 1)
  map_mul' g g' := by
    obtain ⟨l, hl, h1⟩ := projFun_spec g
    obtain ⟨l', hl', h2⟩ := projFun_spec g'
    set a : E ≃ₗ[ZMod 2] E := ((projFun g : ↥(Cent Ls)) : E ≃ₗ[ZMod 2] E) with ha
    set a' : E ≃ₗ[ZMod 2] E := ((projFun g' : ↥(Cent Ls)) : E ≃ₗ[ZMod 2] E) with ha'
    have hcomm : l * a' = a' * l := Subgroup.mem_centralizer_iff.1 (projFun g').2 l hl
    refine (projFun_eq hinf (Subgroup.mul_mem _ (projFun g).2 (projFun g').2)
      (Subgroup.mul_mem _ hl hl') ?_).trans rfl
    show a * a' * (l * l') = (g : E ≃ₗ[ZMod 2] E) * g'
    rw [← h1, ← h2]
    calc a * a' * (l * l') = a * (a' * l) * l' := by group
      _ = a * (l * a') * l' := by rw [hcomm]
      _ = a * l * (a' * l') := by group

theorem proj_of_mem_left (hinf : Cent Ls ⊓ Ls = ⊥) {a : E ≃ₗ[ZMod 2] E} (ha : a ∈ Cent Ls) :
    proj hinf ⟨a, Subgroup.mem_sup_left ha⟩ = ⟨a, ha⟩ :=
  projFun_eq hinf ha (Subgroup.one_mem _) (mul_one a)

theorem proj_of_mem_right (hinf : Cent Ls ⊓ Ls = ⊥) {l : E ≃ₗ[ZMod 2] E} (hl : l ∈ Ls) :
    proj hinf ⟨l, Subgroup.mem_sup_right hl⟩ = 1 :=
  projFun_eq hinf (Subgroup.one_mem _) hl (one_mul l)

end Sup

end CFSG.Quasithin.H13.Mult
