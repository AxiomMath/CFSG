module

public import CFSG.Quasithin.Recognition.CertU33Model
public import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.Quasithin.Recognition.CertPermAction

public section

open scoped MatrixGroups LinearAlgebra.Projectivization Matrix

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Monster.B.Co2

@[expose] def isoDigits : List (List ℕ) :=
  [[0, 0, 1], [1, 0, 0], [1, 0, 3], [1, 0, 6], [1, 1, 1], [1, 1, 4], [1, 1, 7], [1, 2, 1],
    [1, 2, 4], [1, 2, 7], [1, 3, 1], [1, 3, 4], [1, 3, 7], [1, 4, 2], [1, 4, 5], [1, 4, 8],
    [1, 5, 2], [1, 5, 5], [1, 5, 8], [1, 6, 1], [1, 6, 4], [1, 6, 7], [1, 7, 2], [1, 7, 5],
    [1, 7, 8], [1, 8, 2], [1, 8, 5], [1, 8, 8]]

@[expose] def isoVec (k : Fin 28) : Fin 3 → GF9 :=
  fun j => GF9.ofNat' ((isoDigits.getD k []).getD j 0)

theorem isoVec_ne_zero : ∀ k : Fin 28, isoVec k ≠ 0 := by decide +kernel

theorem isoVec_not_proportional : ∀ i j : Fin 28, i ≠ j → ∀ c : GF9, c ≠ 0 →
    c • isoVec j ≠ isoVec i := by decide +kernel

theorem u33M_isoVec : ∀ (i : Fin 5) (k : Fin 28), ∃ c : GF9, c ≠ 0 ∧
    c • isoVec (u33Img i k) = u33M i *ᵥ isoVec k := by decide +kernel

noncomputable def isoLine (k : Fin 28) : Projectivization GF9 (Fin 3 → GF9) :=
  Projectivization.mk GF9 (isoVec k) (isoVec_ne_zero k)

theorem isoLine_injective : Function.Injective isoLine := by
  intro i j h
  by_contra hij
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff GF9 _ _ (isoVec_ne_zero i)
    (isoVec_ne_zero j)).1 h
  exact isoVec_not_proportional i j hij a a.ne_zero ha

theorem smul_isoLine_gen (i : Fin 5) (k : Fin 28) : u33GL i • isoLine k = isoLine (u33Img i k) := by
  obtain ⟨c, hc, h⟩ := u33M_isoVec i k
  unfold isoLine
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc, h⟩

@[expose] def u33Group9 : Subgroup (GL (Fin 3) GF9) := Subgroup.closure (Set.range u33GL)

theorem exists_isoLine_smul {g : GL (Fin 3) GF9} (hg : g ∈ u33Group9) (k : Fin 28) :
    ∃ j, g • isoLine k = isoLine j := by
  have key : ∀ g : GL (Fin 3) GF9, g ∈ Submonoid.closure (Set.range u33GL) →
      ∀ k : Fin 28, ∃ j, g • isoLine k = isoLine j := by
    intro g hg' k
    induction hg' using Submonoid.closure_induction generalizing k with
    | mem A hA =>
      obtain ⟨i, rfl⟩ := hA
      exact ⟨_, smul_isoLine_gen i k⟩
    | one => exact ⟨k, one_smul _ _⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨j, hj⟩ := ihy k
      obtain ⟨l, hl⟩ := ihx j
      exact ⟨l, by rw [mul_smul, hj, hl]⟩
  refine key g ?_ k
  rw [← Subgroup.closure_toSubmonoid_of_finite]
  exact hg

theorem eq_of_edge_indep {F : Type*} [Field F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    {x y w : Fin n → F} {μ ν d c e : F} (hc : c ≠ 0)
    (hind : ∀ s t : F, s • x + t • y = 0 → s = 0 ∧ t = 0)
    (hx : M *ᵥ x = μ • x) (hy : M *ᵥ y = ν • y) (hw : x + c • y = e • w)
    (hMw : M *ᵥ w = d • w) : μ = ν := by
  have h1 : M *ᵥ (x + c • y) = d • (x + c • y) := by
    rw [hw, Matrix.mulVec_smul, hMw, smul_comm]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy] at h1
  simp only [smul_smul, smul_add] at h1
  have h2 : (μ - d) • x + (c * ν - d * c) • y = 0 := by
    rw [sub_smul, sub_smul]
    rw [← sub_eq_zero] at h1
    rw [← h1]
    abel
  obtain ⟨h3, h4⟩ := hind _ _ h2
  have h5 : μ = d := sub_eq_zero.1 h3
  have h6 : c * (ν - d) = 0 := by rw [mul_sub, mul_comm c d]; exact h4
  have h7 : ν - d = 0 := (mul_eq_zero.1 h6).resolve_left hc
  rw [h5, sub_eq_zero.1 h7]

@[expose] def isoBasis : Matrix (Fin 3) (Fin 3) GF9 := !![0, 1, 1; 0, 0, 1; 1, 0, 1]

@[expose] def isoBasisInv : Matrix (Fin 3) (Fin 3) GF9 := !![0, 2, 1; 1, 2, 0; 0, 1, 0]

theorem isoBasis_mul_inv : isoBasis * isoBasisInv = 1 := by decide +kernel

theorem isoBasis_col : ∀ i : Fin 3, isoBasis i 0 = isoVec 0 i ∧ isoBasis i 1 = isoVec 1 i ∧
    isoBasis i 2 = isoVec 4 i := by decide +kernel

theorem isoVec_indep : (∀ s t : GF9, s • isoVec 0 + t • isoVec 1 = 0 → s = 0 ∧ t = 0) ∧
    (∀ s t : GF9, s • isoVec 0 + t • isoVec 4 = 0 → s = 0 ∧ t = 0) := by decide +kernel

theorem isoVec_edges : isoVec 0 + GF9.ofNat' 3 • isoVec 1 = GF9.ofNat' 3 • isoVec 3 ∧
    isoVec 0 + GF9.ofNat' 3 • isoVec 4 = GF9.ofNat' 3 • isoVec 6 := by decide +kernel

theorem exists_eigen_of_fixed_line3 {F : Type*} [Field F] (g : GL (Fin 3) F) (v : Fin 3 → F)
    (hv : v ≠ 0) (h : g • Projectivization.mk F v hv = Projectivization.mk F v hv) :
    ∃ c : F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v := by
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨(a : F), ha.symm⟩

theorem exists_scalar_of_fixed_lines_u33 (M : Matrix (Fin 3) (Fin 3) GF9)
    (h0 : ∃ c : GF9, M *ᵥ isoVec 0 = c • isoVec 0) (h1 : ∃ c : GF9, M *ᵥ isoVec 1 = c • isoVec 1)
    (h4 : ∃ c : GF9, M *ᵥ isoVec 4 = c • isoVec 4) (h3 : ∃ c : GF9, M *ᵥ isoVec 3 = c • isoVec 3)
    (h6 : ∃ c : GF9, M *ᵥ isoVec 6 = c • isoVec 6) : ∃ c : GF9, M = c • 1 := by
  obtain ⟨c0, hc0⟩ := h0
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c4, hc4⟩ := h4
  obtain ⟨d3, hd3⟩ := h3
  obtain ⟨d6, hd6⟩ := h6
  have hne : GF9.ofNat' 3 ≠ 0 := by decide +kernel
  have e1 : c0 = c1 :=
    eq_of_edge_indep hne isoVec_indep.1 hc0 hc1 isoVec_edges.1 hd3
  have e4 : c0 = c4 :=
    eq_of_edge_indep hne isoVec_indep.2 hc0 hc4 isoVec_edges.2 hd6
  have hMB : M * isoBasis = c0 • isoBasis := by
    ext i k
    have hk : (M * isoBasis) i k = (M *ᵥ fun j => isoBasis j k) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hk]
    fin_cases k
    · have : (fun j => isoBasis j 0) = isoVec 0 := funext fun j => (isoBasis_col j).1
      simp only [Fin.zero_eta, this, hc0]
      simp [(isoBasis_col i).1]
    · have : (fun j => isoBasis j 1) = isoVec 1 := funext fun j => (isoBasis_col j).2.1
      simp only [Fin.mk_one, this, hc1, ← e1]
      simp [(isoBasis_col i).2.1]
    · have : (fun j => isoBasis j 2) = isoVec 4 := funext fun j => (isoBasis_col j).2.2
      simp only [Fin.reduceFinMk, this, hc4, ← e4]
      simp [(isoBasis_col i).2.2]
  refine ⟨c0, ?_⟩
  calc M = M * (isoBasis * isoBasisInv) := by rw [isoBasis_mul_inv, mul_one]
    _ = (M * isoBasis) * isoBasisInv := (Matrix.mul_assoc _ _ _).symm
    _ = (c0 • isoBasis) * isoBasisInv := by rw [hMB]
    _ = c0 • (isoBasis * isoBasisInv) := Matrix.smul_mul _ _ _
    _ = c0 • 1 := by rw [isoBasis_mul_inv]

theorem det_eq_one_of_mem_u33Group9 {g : GL (Fin 3) GF9} (hg : g ∈ u33Group9) :
    (g : Matrix (Fin 3) (Fin 3) GF9).det = 1 := by
  have hle : u33Group9 ≤ (Matrix.GeneralLinearGroup.det (n := Fin 3) (R := GF9)).ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact u33M_det i
  have := hle hg
  rw [MonoidHom.mem_ker] at this
  have h2 := congrArg Units.val this
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2

theorem eq_one_of_fixes_isoLines {g : GL (Fin 3) GF9} (hg : g ∈ u33Group9)
    (h : ∀ k, g • isoLine k = isoLine k) : g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_fixed_lines_u33 (g : Matrix (Fin 3) (Fin 3) GF9)
    (exists_eigen_of_fixed_line3 g _ (isoVec_ne_zero 0) (h 0))
    (exists_eigen_of_fixed_line3 g _ (isoVec_ne_zero 1) (h 1))
    (exists_eigen_of_fixed_line3 g _ (isoVec_ne_zero 4) (h 4))
    (exists_eigen_of_fixed_line3 g _ (isoVec_ne_zero 3) (h 3))
    (exists_eigen_of_fixed_line3 g _ (isoVec_ne_zero 6) (h 6))
  have hdet := det_eq_one_of_mem_u33Group9 hg
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1 : c = 1 := by
    have h3 : ∀ x : GF9, x ^ 3 = 1 → x = 1 := by decide +kernel
    exact h3 c hdet
  apply Units.ext
  rw [hc, hc1, one_smul]
  rfl

theorem card_u33Group9 : Nat.card u33Group9 = 6048 := by
  have hst : ∀ (g : ↥u33Group9) (k : Fin 28), ∃ j, g • isoLine k = isoLine j :=
    fun g k => exists_isoLine_smul g.2 k
  have hfaith : ∀ g : ↥u33Group9, (∀ k, g • isoLine k = isoLine k) → g = 1 :=
    fun g h => Subtype.ext (eq_one_of_fixes_isoLines g.2 h)
  have hS : Subgroup.closure ((↑) ⁻¹' Set.range u33GL : Set ↥u33Group9) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have key := card_eq_card_closure_of_faithful (G := ↥u33Group9) isoLine isoLine_injective hst
    hfaith _ hS {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g}
    (by
      rintro s ⟨i, hi⟩
      obtain ⟨hsz, -⟩ := u33Chain_check
      refine ⟨u33Img i, ⟨i, by rw [hsz]; exact i.2, permOfArr_u33Gens i⟩, fun k => ?_⟩
      have hs : s • isoLine k = u33GL i • isoLine k := by
        rw [hi]
        rfl
      rw [hs, smul_isoLine_gen])
    (by
      rintro τ ⟨k, hk, rfl⟩
      obtain ⟨hsz, -⟩ := u33Chain_check
      rw [hsz] at hk
      refine ⟨⟨u33GL ⟨k, hk⟩, Subgroup.subset_closure ⟨_, rfl⟩⟩, ⟨_, rfl⟩, fun l => ?_⟩
      show u33GL ⟨k, hk⟩ • isoLine l = _
      rw [smul_isoLine_gen, permOfArr_u33Gens ⟨k, hk⟩])
  rw [key, card_u33Perm]

end CFSG.Quasithin
