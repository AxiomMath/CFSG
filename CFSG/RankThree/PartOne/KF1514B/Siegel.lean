module

public import CFSG.RankThree.PartOne.KF1514B.Geom

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

noncomputable abbrev e0 (K : Type) [Field K] : Vt K := hypVec K (Fin 2 → K) (Sum.inl 0)

noncomputable abbrev e1 (K : Type) [Field K] : Vt K := hypVec K (Fin 2 → K) (Sum.inl 1)

noncomputable abbrev F2 (K : Type) [Field K] : Submodule K (Vt K) := tailFlag K (Fin 2 → K) 3 2

theorem mem_F2 {v : Vt K} : v ∈ F2 K ↔ (∀ j, v.1 (Sum.inr j) = 0) ∧
    (∀ j : Fin 3, 2 ≤ (j : ℕ) → v.1 (Sum.inl j) = 0) ∧ v.2 = 0 := by
  rw [mem_tailFlag_iff, mem_flag]
  tauto

theorem e0_mem_F2 : e0 K ∈ F2 K := mem_F2.2 ⟨fun j => by simp [hypVec], fun j hj => by
  have : j ≠ 0 := fun h => by subst h; simp at hj
  simp [hypVec, this], rfl⟩

theorem e1_mem_F2 : e1 K ∈ F2 K := mem_F2.2 ⟨fun j => by simp [hypVec], fun j hj => by
  have : j ≠ 1 := fun h => by subst h; simp at hj
  simp [hypVec, this], rfl⟩

theorem eq_of_mem_F2 {v : Vt K} (hv : v ∈ F2 K) :
    v = v.1 (Sum.inl 0) • e0 K + v.1 (Sum.inl 1) • e1 K := by
  obtain ⟨h1, h2, h3⟩ := mem_F2.1 hv
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · fin_cases i
      · simp [hypVec]
      · simp [hypVec]
      · simp [hypVec, h2 2 (by decide)]
    · simp [hypVec, h1 i]
  · simp [hypVec, h3]

section Nmap

variable (b c)

noncomputable abbrev Q0 : QuadraticForm K (Vt K) := quadTail 3 (minusTailForm K b c)

noncomputable def Nmap (a a' v : Vt K) : Vt K :=
  polar (Q0 b c) v a • a' + polar (Q0 b c) v a' • a

variable {b c}

theorem map_Nmap {g : Vt K ≃ₗ[K] Vt K} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q0 b c))
    (a a' v : Vt K) : g (Nmap b c a a' (g.symm v)) = Nmap b c (g a) (g a') v := by
  have h1 := polar_map_of_mem_orth hg (g.symm v) a
  have h2 := polar_map_of_mem_orth hg (g.symm v) a'
  rw [LinearEquiv.apply_symm_apply] at h1 h2
  simp only [Nmap, map_add, map_smul, ← h1, ← h2]

theorem Nmap_comb (a a' v : Vt K) (α γ δ ε : K) :
    Nmap b c (α • a + γ • a') (δ • a + ε • a') v = (α * ε + γ * δ) • Nmap b c a a' v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Nmap, polar_add_right, polar_smul_right_eq]
  have ha : (α * δ * polar (Q0 b c) v a) • ((2 : K) • a) = 0 := by
    rw [h2, zero_smul, smul_zero]
  have hb : (γ * ε * polar (Q0 b c) v a') • ((2 : K) • a') = 0 := by
    rw [h2, zero_smul, smul_zero]
  linear_combination (norm := module) ha + hb

end Nmap

section Siegel

noncomputable def x0U : ↥(U0 b c) := mkE 0 0 1 0 0

noncomputable abbrev x0 (b c : K) [AnisoPair b c] : Vt K ≃ₗ[K] Vt K :=
  ((x0U (b := b) (c := c) : ↥(U0 b c)) : Vt K ≃ₗ[K] Vt K)

theorem x0_apply (v : Vt K) :
    x0 b c v = (Sum.elim (fun i => v.1 (Sum.inl i) + ((Calt (1 : K) 0 0 : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (v.1 ∘ Sum.inr)) i) (v.1 ∘ Sum.inr), v.2) := by
  have hL : (fun i : Fin 3 => (0 : Fin 3 → K) i • (0 : Fin 2 → K)) = 0 := by
    funext i; simp
  have e : (x0 b c : Vt K ≃ₗ[K] Vt K) = dMap (1 : GL (Fin 3) K) 1 *
      uMap (minusTailForm K b c) (fun i => (0 : Fin 3 → K) i • (0 : Fin 2 → K)) (Calt 1 0 0) := rfl
  rw [e, LinearEquiv.mul_apply, dMap_apply, uMap_apply, hL]
  refine Prod.ext (funext fun c' => ?_) ?_
  · rcases c' with i | i
    · simp [uLin_apply_inl, sMat_zero]
    · simp [uLin_apply_inr]
  · simp [uLin_apply_snd]

theorem Calt_mulVec (y : Fin 3 → K) :
    (Calt (1 : K) 0 0 : Matrix (Fin 3) (Fin 3) K) *ᵥ y = ![y 1, y 0, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Calt]

theorem x0_eq (v : Vt K) : x0 b c v = v + Nmap b c (e0 K) (e1 K) v := by
  rw [x0_apply]
  have p0 : polar (Q0 b c) v (e0 K) = v.1 (Sum.inr 0) := by
    rw [polar_hypVec]; rfl
  have p1 : polar (Q0 b c) v (e1 K) = v.1 (Sum.inr 1) := by
    rw [polar_hypVec]; rfl
  rw [Nmap, p0, p1]
  refine Prod.ext (funext fun c' => ?_) ?_
  · rcases c' with i | i
    · rw [Calt_mulVec]
      fin_cases i <;> simp [hypVec]
    · simp [hypVec]
  · simp [hypVec]

theorem commute_x0_of_coeff {g : Vt K ≃ₗ[K] Vt K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q0 b c)) {α γ δ ε : K}
    (h0 : g (e0 K) = α • e0 K + γ • e1 K) (h1 : g (e1 K) = δ • e0 K + ε • e1 K)
    (hdet : α * ε + γ * δ = 1) : g * x0 b c = x0 b c * g := by
  have key : ∀ v, g (x0 b c (g.symm v)) = x0 b c v := by
    intro v
    rw [x0_eq, x0_eq, map_add, LinearEquiv.apply_symm_apply, map_Nmap hg, h0, h1, Nmap_comb, hdet,
      one_smul]
  refine LinearEquiv.ext fun w => ?_
  have := key (g w)
  rw [LinearEquiv.symm_apply_apply] at this
  exact this

theorem x0U_mem_center : (x0U : ↥(U0 b c)) ∈ Subgroup.center ↥(U0 b c) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hL : Lp (x0U (b := b) (c := c)) = 0 := by
    rw [x0U, Lp_mkE]
    funext i
    simp
  refine commute_of_Cp_fixed (Dm_mkE _ _ _ _ _) hL ?_
  have hC : Cp (x0U (b := b) (c := c)) = Calt 1 0 0 := by rw [x0U, Cp_mkE]
  rw [hC, conj_Calt]
  simp

theorem x0U_sq : (x0U : ↥(U0 b c)) * x0U = 1 := (elemAb_Aw (0 : Fin 2 → K)).sq _ (mkE_mem_Aw 0 0 1 0 0)

theorem x0_mem_omegaOneCenterIn : x0 b c ∈ omegaOneCenterIn (U0 b c) := by
  refine Subgroup.subset_closure ⟨⟨x0U, x0U_mem_center, rfl⟩, ?_⟩
  show (x0 b c) ^ 2 = 1
  rw [pow_two]
  have := congrArg (fun z : ↥(U0 b c) => (z : Vt K ≃ₗ[K] Vt K)) (x0U_sq (b := b) (c := c))
  simpa using this

theorem x0_ne_one : x0 b c ≠ 1 := by
  intro h
  have h1 : (x0U : ↥(U0 b c)) = 1 := Subtype.ext h
  have h2 := congrArg (fun z : ↥(U0 b c) => Cp z) h1
  simp only [x0U, Cp_mkE, Cp_one] at h2
  have := congrFun (congrFun h2 0) 1
  simp [Calt] at this

end Siegel

section Stab2

variable (K) in
def Stab2 : Submonoid (Vt K ≃ₗ[K] Vt K) where
  carrier := {g | ∀ w ∈ F2 K, g w ∈ F2 K}
  one_mem' := fun _ h => h
  mul_mem' := fun {g h} hg hh w hw => by
    rw [LinearEquiv.mul_apply]
    exact hg _ (hh w hw)

theorem mem_Stab2 {g : Vt K ≃ₗ[K] Vt K} : g ∈ Stab2 K ↔ ∀ w ∈ F2 K, g w ∈ F2 K := Iff.rfl

noncomputable def coefMat (g : Vt K ≃ₗ[K] Vt K) : Matrix (Fin 2) (Fin 2) K :=
  !![(g (e0 K)).1 (Sum.inl 0), (g (e1 K)).1 (Sum.inl 0);
    (g (e0 K)).1 (Sum.inl 1), (g (e1 K)).1 (Sum.inl 1)]

theorem coord_apply0 (g : Vt K ≃ₗ[K] Vt K) {v : Vt K} (hv : v ∈ F2 K) :
    (g v).1 (Sum.inl 0) = coefMat g 0 0 * v.1 (Sum.inl 0) + coefMat g 0 1 * v.1 (Sum.inl 1) := by
  have hv' := eq_of_mem_F2 hv
  conv_lhs => rw [hv']
  simp only [map_add, map_smul, Prod.fst_add, Pi.add_apply, Prod.smul_fst, Pi.smul_apply,
    smul_eq_mul]
  simp [coefMat, mul_comm]

theorem coord_apply1 (g : Vt K ≃ₗ[K] Vt K) {v : Vt K} (hv : v ∈ F2 K) :
    (g v).1 (Sum.inl 1) = coefMat g 1 0 * v.1 (Sum.inl 0) + coefMat g 1 1 * v.1 (Sum.inl 1) := by
  have hv' := eq_of_mem_F2 hv
  conv_lhs => rw [hv']
  simp only [map_add, map_smul, Prod.fst_add, Pi.add_apply, Prod.smul_fst, Pi.smul_apply,
    smul_eq_mul]
  simp [coefMat, mul_comm]

theorem coefMat_one : coefMat (1 : Vt K ≃ₗ[K] Vt K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coefMat, hypVec]

theorem coefMat_mul {g h : Vt K ≃ₗ[K] Vt K} (hh : h ∈ Stab2 K) :
    coefMat (g * h) = coefMat g * coefMat h := by
  have hmem0 := hh _ e0_mem_F2
  have hmem1 := hh _ e1_mem_F2
  have m00 : coefMat (g * h) 0 0 = (coefMat g * coefMat h) 0 0 := by
    show (g (h (e0 K))).1 (Sum.inl 0) = _
    rw [coord_apply0 g hmem0, Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  have m10 : coefMat (g * h) 1 0 = (coefMat g * coefMat h) 1 0 := by
    show (g (h (e0 K))).1 (Sum.inl 1) = _
    rw [coord_apply1 g hmem0, Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  have m01 : coefMat (g * h) 0 1 = (coefMat g * coefMat h) 0 1 := by
    show (g (h (e1 K))).1 (Sum.inl 0) = _
    rw [coord_apply0 g hmem1, Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  have m11 : coefMat (g * h) 1 1 = (coefMat g * coefMat h) 1 1 := by
    show (g (h (e1 K))).1 (Sum.inl 1) = _
    rw [coord_apply1 g hmem1, Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  ext i j
  fin_cases i <;> fin_cases j
  exacts [m00, m01, m10, m11]

noncomputable def coefMatHom : Stab2 K →* Matrix (Fin 2) (Fin 2) K where
  toFun g := coefMat (g : Vt K ≃ₗ[K] Vt K)
  map_one' := coefMat_one
  map_mul' _ h := coefMat_mul h.2

theorem det_coefMat_eq_one {g : Vt K ≃ₗ[K] Vt K} (hg : g ∈ Stab2 K) {n : ℕ} (hn : 0 < n)
    (hgn : g ^ n = 1) (hcop : Nat.Coprime n (Nat.card K - 1)) : (coefMat g).det = 1 := by
  have hpow : (⟨g, hg⟩ : Stab2 K) ^ n = 1 := Subtype.ext (by simpa using hgn)
  have hM : (coefMat g) ^ n = 1 := by
    have h' : coefMatHom ((⟨g, hg⟩ : Stab2 K) ^ n) = coefMatHom 1 := by rw [hpow]
    rw [map_pow, map_one] at h'
    exact h'
  have h1 : ((coefMat g).det) ^ n = 1 := by
    rw [← Matrix.det_pow, hM, Matrix.det_one]
  have hu : (coefMat g).det ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  have : Fintype K := Fintype.ofFinite K
  have h2 : ((coefMat g).det) ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hu
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop, pow_one] at h3

theorem commute_x0_of_det {g : Vt K ≃ₗ[K] Vt K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q0 b c)) (hs : g ∈ Stab2 K)
    (hdet : (coefMat g).det = 1) : g * x0 b c = x0 b c * g := by
  have hmem0 := hs _ e0_mem_F2
  have hmem1 := hs _ e1_mem_F2
  have e0' := eq_of_mem_F2 hmem0
  have e1' := eq_of_mem_F2 hmem1
  refine commute_x0_of_coeff hg (α := coefMat g 0 0) (γ := coefMat g 1 0) (δ := coefMat g 0 1)
    (ε := coefMat g 1 1) ?_ ?_ ?_
  · rw [e0']; simp [coefMat]
  · rw [e1']; simp [coefMat]
  · rw [Matrix.det_fin_two] at hdet
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hdet + (coefMat g 0 1 * coefMat g 1 0) * h2

end Stab2

end CFSG.RankThree.PartOne.KF1514B
