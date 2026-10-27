module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordLift
public import CFSG.LocalAnalysis.StandardType.GGA8NbrLModel
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.Goldschmidt.Steps.G74Basic
public import CFSG.Goldschmidt.StatementsG2

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix
  CFSG.RankThree.CALinearPlane
open Module
open scoped commutatorElement

namespace CFSG.StandardType.A11

private theorem a11lg_ggDiagConj_diag {n : ℕ} {F : Type} [Field F] (w : Fin n → Fˣ)
    {s : SpecialLinearGroup (Fin n) F} (hs : Matrix.IsDiag (s : Matrix (Fin n) (Fin n) F)) :
    ggDiagConj w s = s := by
  apply Subtype.ext
  rw [coe_ggDiagConj]
  have hsd : (s : Matrix (Fin n) (Fin n) F) =
      diagonal (fun i => (s : Matrix (Fin n) (Fin n) F) i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [hs h]; simp [Matrix.diagonal_apply_ne _ h]
  rw [hsd, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h : (↑(w i) : F) * ↑((w i)⁻¹) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (↑(w i) : F) * (s : Matrix (Fin n) (Fin n) F) i i * ↑((w i)⁻¹)
      = (s : Matrix (Fin n) (Fin n) F) i i * ((↑(w i) : F) * ↑((w i)⁻¹)) := by ring
    _ = (s : Matrix (Fin n) (Fin n) F) i i := by rw [h, mul_one]

private theorem a11lg_diagTorus_pow_seven {s : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hs : s ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) : s ^ 7 = 1 := by
  obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp
    (SpecialLinearGroup.mem_diagonalTorus_iff_toGL_mem.mp hs)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  have hsmat : (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
      diagonal (fun i => (t i : GaloisField 2 3)) := by
    have h := congrArg (fun g : GL (Fin 4) (GaloisField 2 3) =>
      (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) ht
    rw [TauCeti.diagGL_coe] at h
    simpa using h.symm
  rw [hsmat, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact congrArg (fun z : (GaloisField 2 3)ˣ => (z : GaloisField 2 3))
    (ggSL9_units_pow_seven (t i))


private theorem a11lg_diag_mem_Bs {G : Type} [Group G] {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 7 = 1 → g ∈ Bs)
    {φ : SpecialLinearGroup (Fin 4) (GaloisField 2 3) →* G}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b)
    {s : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hs : s ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) : φ s ∈ Bs := by
  apply hSC
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨w, hw⟩ := hdiag b hb
    calc b * φ s = b * φ s * b⁻¹ * b := by group
      _ = φ (ggDiagConj w s) * b := by rw [hw]
      _ = φ s * b := by
        rw [a11lg_ggDiagConj_diag w (SpecialLinearGroup.mem_diagonalTorus_iff.mp hs)]
  · rw [← map_pow, a11lg_diagTorus_pow_seven hs, map_one]


private theorem a11lg_inf_le_diagTorus {G : Type} [Group G] {Bs L : Subgroup G}
    {φ : SpecialLinearGroup (Fin 4) (GaloisField 2 3) →* G} (hφinj : Function.Injective φ)
    (hrange : φ.range = L) (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) {g : G}
    (hg : g ∈ Bs ⊓ L) :
    ∃ s ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4, φ s = g := by
  obtain ⟨hgBs, hgL⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hgL)
  obtain ⟨w, hw⟩ := hdiag (φ s) hgBs
  have hst : ∀ t : SpecialLinearGroup (Fin 4) (GaloisField 2 3),
      s * t * s⁻¹ = ggDiagConj w t := by
    intro t
    apply hφinj
    rw [map_mul, map_mul, map_inv]
    exact hw t
  let D : Matrix (Fin 4) (Fin 4) (GaloisField 2 3) :=
    diagonal (fun i => (w i : GaloisField 2 3))
  let D' : Matrix (Fin 4) (Fin 4) (GaloisField 2 3) :=
    diagonal (fun i => ((w i : GaloisField 2 3))⁻¹)
  have hDD' : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    exact mul_inv_cancel₀ (Units.ne_zero (w i))
  have hD'D : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    exact inv_mul_cancel₀ (Units.ne_zero (w i))
  have hrel : ∀ t : SpecialLinearGroup (Fin 4) (GaloisField 2 3),
      (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
      D * (t : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) * D' *
        (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by
    intro t
    have hst' : s * t = ggDiagConj w t * s := by
      have h := congrArg (fun z : SpecialLinearGroup (Fin 4) (GaloisField 2 3) =>
        z * s) (hst t)
      simpa [mul_assoc] using h
    have h := congrArg (fun z : SpecialLinearGroup (Fin 4) (GaloisField 2 3) =>
      (z : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) hst'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_ggDiagConj] at h
    simpa only [D, D', Units.val_inv_eq_inv_val] using h
  have hscalar : D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) ∈
      Set.range (fun r : GaloisField 2 3 => Matrix.scalar (Fin 4) r) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro τ
    rw [Commute]
    have hτ : (TransvectionStruct.toSpecialLinearGroup τ :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) = τ.toMatrix := by
      cases τ with
      | mk i j hij c =>
        rw [TransvectionStruct.toSpecialLinearGroup_mk, TransvectionStruct.toMatrix_mk,
          SpecialLinearGroup.transvection_coe]
        rfl
    have hrelτ := hrel (TransvectionStruct.toSpecialLinearGroup τ)
    rw [hτ] at hrelτ
    calc τ.toMatrix * (D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))
        = D' * D * τ.toMatrix *
            (D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) := by
          rw [hD'D, one_mul]
      _ = D' * (D * τ.toMatrix * D' *
            (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) := by noncomm_ring
      _ = D' * ((s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) * τ.toMatrix) := by
          rw [← hrelτ]
      _ = D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) * τ.toMatrix := by
          noncomm_ring
  obtain ⟨r, hr⟩ := hscalar
  change Matrix.scalar (Fin 4) r = D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) at hr
  have hsmat : (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
      diagonal (fun i => r * (w i : GaloisField 2 3)) := by
    have h1 : D * (D' * (s : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) =
        D * Matrix.scalar (Fin 4) r := by rw [hr]
    rw [← mul_assoc, hDD', one_mul, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at h1
    rw [h1]
    congr 1; funext i; rw [mul_comm]
  refine ⟨s, SpecialLinearGroup.mem_diagonalTorus_iff.mpr ?_, rfl⟩
  rw [hsmat]
  exact isDiag_diagonal _


private theorem a11lg_conj_mem_closure {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    (hBs : Subgroup.closure (Set.range f) = Bs) {g : G}
    (hg : ∀ i, g * f i * g⁻¹ ∈ Bs) : ∀ b ∈ Bs, g * b * g⁻¹ ∈ Bs := by
  intro b hb
  rw [← hBs] at hb ⊢
  rw [← hBs] at hg
  induction hb using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hg i
  | one => simp
  | mul x y hx hy ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ih

private theorem a11lg_n2_mem_normalizer {G : Type} [Group G] {Bs : Subgroup G} {f n : Fin 4 → G}
    (hfi : ∀ i, f i ∈ Bs) (hBs : Subgroup.closure (Set.range f) = Bs)
    (hnswap : ∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i)) :
    n 2 ∈ Subgroup.normalizer (Bs : Set G) := by
  have hgen : ∀ i, n 2 * f i * (n 2)⁻¹ ∈ Bs := fun i => by
    rw [hnswap 2 i]; exact hfi _
  have hgen' : ∀ i, (n 2)⁻¹ * f i * n 2 ∈ Bs := by
    intro i
    have h := hnswap 2 (Equiv.swap 2 3 i)
    rw [show (Equiv.swap 2 3) ((Equiv.swap 2 3) i) = i from by fin_cases i <;> rfl] at h
    rw [show (n 2)⁻¹ * f i * n 2 = f (Equiv.swap 2 3 i) by rw [← h]; group]
    exact hfi _
  rw [Subgroup.mem_normalizer_iff]
  intro b
  exact ⟨a11lg_conj_mem_closure hBs hgen b,
    fun hb => by
      have h := a11lg_conj_mem_closure (g := (n 2)⁻¹) hBs
        (fun i => by simpa only [inv_inv] using hgen' i) (n 2 * b * (n 2)⁻¹) hb
      rwa [show (n 2)⁻¹ * (n 2 * b * (n 2)⁻¹) * (n 2)⁻¹⁻¹ = b by group] at h⟩


private theorem a11lg_diagGL_decomp (t : Fin 4 → (GaloisField 2 3)ˣ) :
    ∃ (s : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) (c : (GaloisField 2 3)ˣ),
      s ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 ∧
      TauCeti.diagGL t = SpecialLinearGroup.toGL s *
        TauCeti.diagGL (fun _ : Fin 4 => c) := by
  let P : (GaloisField 2 3)ˣ := ∏ i, t i
  let c : (GaloisField 2 3)ˣ := P ^ 2
  let d : Fin 4 → (GaloisField 2 3)ˣ := fun i => t i * c⁻¹
  have hc : c ^ 4 = P := by
    simp only [c]
    rw [← pow_mul]
    norm_num
    rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, pow_one, ggSL9_units_pow_seven P, one_mul]
  have hd : ∏ i, d i = 1 := by
    simp only [d, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    change P * (c⁻¹) ^ 4 = 1
    have hcinv : (c⁻¹) ^ 4 = P⁻¹ := by rw [inv_pow, hc]
    rw [hcinv, mul_inv_cancel]
  have hdet : (Matrix.diagonal (fun i => (d i : GaloisField 2 3))).det = 1 := by
    rw [Matrix.det_diagonal]
    exact congrArg (fun z : (GaloisField 2 3)ˣ => (z : GaloisField 2 3)) hd
  refine ⟨⟨Matrix.diagonal (fun i => (d i : GaloisField 2 3)), hdet⟩, c, ?_, ?_⟩
  · exact SpecialLinearGroup.mem_diagonalTorus_iff.mpr (isDiag_diagonal _)
  have htoGL : SpecialLinearGroup.toGL
      (⟨Matrix.diagonal (fun i => (d i : GaloisField 2 3)), hdet⟩ :
        SpecialLinearGroup (Fin 4) (GaloisField 2 3)) = TauCeti.diagGL d := by
    ext i j
    rw [TauCeti.diagGL_coe]
    rfl
  rw [htoGL, ← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, d]
  rw [mul_assoc, inv_mul_cancel, mul_one]


private theorem a11lg_toGL_conj_mem_diagTorus
    {u : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hu : u ∈ Subgroup.normalizer
      (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 : Set
        (SpecialLinearGroup (Fin 4) (GaloisField 2 3))))
    {g : GL (Fin 4) (GaloisField 2 3)}
    (hg : g ∈ TauCeti.diagonalTorus (GaloisField 2 3) 4) :
    SpecialLinearGroup.toGL u * g * (SpecialLinearGroup.toGL u)⁻¹ ∈
      TauCeti.diagonalTorus (GaloisField 2 3) 4 := by
  obtain ⟨t, rfl⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hg
  obtain ⟨s, c, hsT, hdec⟩ := a11lg_diagGL_decomp t
  have hu_s : u * s * u⁻¹ ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 :=
    (Subgroup.mem_normalizer_iff.mp hu s).mp hsT
  have hDcenter : TauCeti.diagGL (fun _ : Fin 4 => c) ∈
      Subgroup.center (GL (Fin 4) (GaloisField 2 3)) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨c, by rw [TauCeti.diagGL_coe, Matrix.scalar_apply]⟩
  have hc : Commute (TauCeti.diagGL (fun _ : Fin 4 => c)) (SpecialLinearGroup.toGL u) :=
    (Subgroup.mem_center_iff.mp hDcenter (SpecialLinearGroup.toGL u)).symm
  rw [hdec]
  have heq : SpecialLinearGroup.toGL u *
        (SpecialLinearGroup.toGL s * TauCeti.diagGL (fun _ : Fin 4 => c)) *
        (SpecialLinearGroup.toGL u)⁻¹ =
      SpecialLinearGroup.toGL (u * s * u⁻¹) *
        TauCeti.diagGL (fun _ : Fin 4 => c) := by
    rw [map_mul, map_mul, map_inv]
    calc SpecialLinearGroup.toGL u *
          (SpecialLinearGroup.toGL s * TauCeti.diagGL (fun _ : Fin 4 => c)) *
          (SpecialLinearGroup.toGL u)⁻¹
        = SpecialLinearGroup.toGL u * SpecialLinearGroup.toGL s *
            (TauCeti.diagGL (fun _ : Fin 4 => c) * (SpecialLinearGroup.toGL u)⁻¹) := by
          noncomm_ring
      _ = SpecialLinearGroup.toGL u * SpecialLinearGroup.toGL s *
            ((SpecialLinearGroup.toGL u)⁻¹ * TauCeti.diagGL (fun _ : Fin 4 => c)) := by
          rw [hc.inv_right.eq]
      _ = SpecialLinearGroup.toGL u * SpecialLinearGroup.toGL s *
            (SpecialLinearGroup.toGL u)⁻¹ * TauCeti.diagGL (fun _ : Fin 4 => c) := by
          noncomm_ring
  rw [heq]
  refine (TauCeti.diagonalTorus (GaloisField 2 3) 4).mul_mem ?_ ?_
  · rw [← SpecialLinearGroup.mem_diagonalTorus_iff_toGL_mem]; exact hu_s
  · exact TauCeti.mem_diagonalTorus_iff_exists_diagGL.mpr ⟨fun _ => c, rfl⟩

private theorem a11lg_toGL_mem_normalizer
    {m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hmT : m ∈ Subgroup.normalizer
      (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 : Set
        (SpecialLinearGroup (Fin 4) (GaloisField 2 3)))) :
    SpecialLinearGroup.toGL m ∈ Subgroup.normalizer
      (TauCeti.diagonalTorus (GaloisField 2 3) 4 : Set (GL (Fin 4) (GaloisField 2 3))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact a11lg_toGL_conj_mem_diagTorus hmT hg
  · intro hg
    have hmTinv : m⁻¹ ∈ Subgroup.normalizer
        (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 : Set
          (SpecialLinearGroup (Fin 4) (GaloisField 2 3))) := Subgroup.inv_mem _ hmT
    have h := a11lg_toGL_conj_mem_diagTorus (u := m⁻¹) hmTinv hg
    rwa [show SpecialLinearGroup.toGL m⁻¹ * (SpecialLinearGroup.toGL m * g *
        (SpecialLinearGroup.toGL m)⁻¹) * (SpecialLinearGroup.toGL m⁻¹)⁻¹ = g by
      rw [map_inv]; group] at h


private theorem a11lg_center_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at ha
  obtain ⟨r, hr, hrA⟩ := ha
  have hr4 : r ^ 4 = 1 := by simpa using hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 4 ≠ 0)] at hr4
    exact one_ne_zero hr4.symm
  have hr7 : r ^ 7 = 1 := by
    have h := ggSL9_units_pow_seven (Units.mk0 r hr0)
    have h' := congrArg (fun z : (GaloisField 2 3)ˣ => (z : GaloisField 2 3)) h
    simpa [Units.val_pow_eq_pow_val] using h'
  have hr1 : r = 1 := by
    have h := (pow_gcd_eq_one (a := r) (m := 4) (n := 7)).mpr ⟨hr4, hr7⟩
    simpa using h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  have hcoe : (↑a : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 3)) = 1 := by
    rw [← hrA, hr1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  rw [hcoe]

private theorem a11lg_phi_injective {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3))) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  have hc := hker ha
  rw [a11lg_center_eq_bot, Subgroup.mem_bot] at hc
  exact hc


private theorem a11lg_permMatrix_apply (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (σ.permMatrix (GaloisField 2 3)) i j = if σ i = j then 1 else 0 := by
  have h := congrFun (Matrix.vecMul_permMatrix (R := GaloisField 2 3) σ
    (v := Pi.single i (1 : GaloisField 2 3))) j
  rw [Matrix.vecMul_apply_eq_sum, Finset.sum_eq_single i] at h
  · rw [Pi.single_eq_same, one_mul, Function.comp_apply, Pi.single_apply] at h
    rw [h]
    by_cases hσ : σ i = j
    · rw [if_pos hσ, if_pos (by rw [← hσ, Equiv.symm_apply_apply])]
    · rw [if_neg hσ, if_neg (fun hh => hσ (by rw [← hh, Equiv.apply_symm_apply]))]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h


private theorem a11lg_monomial_mul_compIndicator {U : Finset (Fin 4)}
    {d : Fin 4 → (GaloisField 2 3)ˣ} {σ : Equiv.Perm (Fin 4)}
    {m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hm : SpecialLinearGroup.toGL m = TauCeti.diagGL d * TauCeti.permutationGL σ) :
    (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U =
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
        (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by
  have hm_mat : (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
      diagonal (fun i => (d i : GaloisField 2 3)) *
        (Equiv.Perm.permMatrix (GaloisField 2 3) σ⁻¹) := by
    have h := congrArg (fun g : GL (Fin 4) (GaloisField 2 3) =>
      (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) hm
    rw [GeneralLinearGroup.coe_mul, TauCeti.diagGL_coe, TauCeti.permutationGL_coe] at h
    exact h
  ext i j
  rw [CFSG.RankThree.CALinearPlane.mul_compIndicator_apply,
    CFSG.RankThree.CALinearPlane.compIndicator_mul_apply]
  by_cases h : (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) i j = 0
  · rw [h]; split_ifs <;> rfl
  · have hij : σ.symm i = j := by
      by_contra hne
      apply h
      rw [hm_mat, Matrix.diagonal_mul, a11lg_permMatrix_apply (σ⁻¹),
        if_neg (show ¬ (σ⁻¹) i = j from hne), mul_zero]
    have hiff : i ∈ U.image σ ↔ j ∈ U := by
      rw [← hij]
      constructor
      · intro hi
        obtain ⟨u, hu, hσu⟩ := Finset.mem_image.mp hi
        rw [← hσu, Equiv.symm_apply_apply]
        exact hu
      · intro hj
        exact Finset.mem_image.mpr ⟨σ.symm i, hj, by rw [Equiv.apply_symm_apply]⟩
    by_cases hj : j ∈ U
    · rw [if_pos hj, if_pos (hiff.mpr hj)]
    · rw [if_neg hj, if_neg (fun hh => hj (hiff.mp hh))]


private theorem a11lg_monomial_conj_coordBlockSL {U : Finset (Fin 4)}
    {d : Fin 4 → (GaloisField 2 3)ˣ} {σ : Equiv.Perm (Fin 4)}
    {m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)}
    (hm : SpecialLinearGroup.toGL m = TauCeti.diagGL d * TauCeti.permutationGL σ) :
    Subgroup.map (MulAut.conj m).toMonoidHom
        (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) U) =
      CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) (U.image σ) := by
  have hm_CI := a11lg_monomial_mul_compIndicator (U := U) hm
  have hm_inv : (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
      ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)
  have hm_inv' : ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
      (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) = 1 :=
    Matrix.nonsing_inv_mul _
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)
  have hCI' : (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
      ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ =
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := by
    rw [hm_CI, Matrix.mul_assoc, hm_inv, Matrix.mul_one]
  have hCI'_right : CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
      ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ =
      ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := by
    calc CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
          ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹
        = (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by
          rw [hm_inv', Matrix.one_mul]
      _ = ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := by
          rw [hCI']
  have hCI_inv : ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
      (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
      CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := by
    calc ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
          CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
          (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))
        = ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) *
            (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by rw [hCI']
      _ = (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
            (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) := by simp only [Matrix.mul_assoc]
      _ = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := by
          rw [hm_inv', Matrix.one_mul, Matrix.mul_one]
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := hg
    obtain ⟨hA1, hA2⟩ := hA
    have h1 : CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
        ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := by
      calc CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹)
          = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by
              noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by rw [← hm_CI]
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by rw [hA1]
        _ = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := hCI'
    have h2 : ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) *
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := by
      calc (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ)
          = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ)) := by
              noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) := by rw [← hCI'_right]
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              ((A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by rw [hA2]
        _ = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) := hCI'
    have hmul : (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        ((m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hminv : ((m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ :=
      (Matrix.inv_eq_right_inv hmul).symm
    have hcoe : ((m * A * m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hminv]
    change CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
        ((m * A * m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) ∧
      ((m * A * m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ)
    rw [hcoe]
    exact ⟨h1, h2⟩
  · intro g hg
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨m⁻¹ * g * m, ?_, by change m * (m⁻¹ * g * m) * m⁻¹ = g; group⟩
    have h1 : CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
        (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
          (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := by
      calc CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
            (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))
          = (CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹) *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by noncomm_ring
        _ = (((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ)) *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by rw [hCI'_right]
        _ = ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
              (CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by noncomm_ring
        _ = ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by rw [hg1]
        _ = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := hCI_inv
    have h2 : ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
          (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := by
      calc (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))⁻¹ *
            (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
            CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U
          = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))⁻¹ *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U) := by
              noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))⁻¹ *
              (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              (CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))) := by rw [hm_CI]
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))⁻¹ *
              ((g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ)) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by noncomm_ring
        _ = (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3))⁻¹ *
              CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) (U.image σ) *
              (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by rw [hg2]
        _ = CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U := hCI_inv
    have hmul' : ((m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hminv' : ((m⁻¹ : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ :=
      (Matrix.inv_eq_left_inv hmul').symm
    have hcoe : ((m⁻¹ * g * m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        ((m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)))⁻¹ *
          (g : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
          (m : Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hminv']
    change CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U *
        ((m⁻¹ * g * m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U ∧
      ((m⁻¹ * g * m : SpecialLinearGroup (Fin 4) (GaloisField 2 3)) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 3)) *
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U =
        CFSG.RankThree.CALinearPlane.compIndicator (GaloisField 2 3) U
    rw [hcoe]
    exact ⟨h1, h2⟩

private theorem a11lg_commutator_mem {G : Type} [Group G] (K : Subgroup G) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : ⁅a, b⁆ ∈ K := by
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem a11lg_transvection_mem_coordBlockSL {F : Type} [Field F] {U : Finset (Fin 4)}
    {i j : Fin 4} (hij : i ≠ j) (hi : i ∈ U) (hj : j ∈ U) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ coordBlockSL F U := by
  rw [mem_coordBlockSL_iff]
  intro k l hkl
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  rcases hkl with hk | hl
  · have hki : i ≠ k := fun h => hk (h ▸ hi)
    simp [hki]
  · have hlj : j ≠ l := fun h => hl (h ▸ hj)
    simp [hlj]

private theorem a11lg_eq_univ_erase_of_card {U : Finset (Fin 4)} (hU : U.card = 3) :
    ∃ a : Fin 4, a ∉ U ∧ U = Finset.univ.erase a := by
  have h : Uᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin, hU]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have haU : a ∉ U := by
    have : a ∈ Uᶜ := by rw [ha]; exact Finset.mem_singleton_self a
    simpa using this
  refine ⟨a, haU, ?_⟩
  ext x
  rw [Finset.mem_erase]
  constructor
  · intro hx
    exact ⟨fun hxa => haU (hxa ▸ hx), Finset.mem_univ x⟩
  · rintro ⟨hxa, -⟩
    by_contra hxU
    have hxc : x ∈ Uᶜ := by simpa using hxU
    rw [ha] at hxc
    exact hxa (Finset.mem_singleton.mp hxc)

private theorem a11lg_closure_blocks_eq_top {F : Type} [Field F] (U U' : Finset (Fin 4))
    (hU : U.card = 3) (hU' : U'.card = 3) (hne : U ≠ U') :
    Subgroup.closure ((coordBlockSL F U : Set (SpecialLinearGroup (Fin 4) F)) ∪
      (coordBlockSL F U' : Set (SpecialLinearGroup (Fin 4) F))) = ⊤ := by
  classical
  obtain ⟨a, haU, hUeq⟩ := a11lg_eq_univ_erase_of_card hU
  obtain ⟨a', ha'U', hU'eq⟩ := a11lg_eq_univ_erase_of_card hU'
  have haa' : a ≠ a' := by
    intro h
    exact hne (by rw [hUeq, hU'eq, h])
  have key : ∀ x : Fin 4, x ∉ U → x = a := by
    intro x hx
    by_contra hxa
    rw [hUeq] at hx
    exact hx (Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩)
  have key' : ∀ x : Fin 4, x ∉ U' → x = a' := by
    intro x hx
    by_contra hxa
    rw [hU'eq] at hx
    exact hx (Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩)
  have haU' : a ∈ U' := by
    rw [hU'eq, Finset.mem_erase]
    exact ⟨haa', Finset.mem_univ a⟩
  have ha'U : a' ∈ U := by
    rw [hUeq, Finset.mem_erase]
    exact ⟨haa'.symm, Finset.mem_univ a'⟩
  have hkex : ((Finset.univ.erase a).erase a').Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (by rw [Finset.mem_erase]; exact ⟨haa'.symm, Finset.mem_univ a'⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    simp
  obtain ⟨k, hk⟩ := hkex
  rw [Finset.mem_erase, Finset.mem_erase] at hk
  obtain ⟨hka', hka, -⟩ := hk
  have hkU : k ∈ U := by rw [hUeq]; exact Finset.mem_erase.mpr ⟨hka, Finset.mem_univ k⟩
  have hkU' : k ∈ U' := by rw [hU'eq]; exact Finset.mem_erase.mpr ⟨hka', Finset.mem_univ k⟩
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  set K : Subgroup (SpecialLinearGroup (Fin 4) F) :=
    Subgroup.closure ((coordBlockSL F U : Set (SpecialLinearGroup (Fin 4) F)) ∪
      (coordBlockSL F U' : Set (SpecialLinearGroup (Fin 4) F))) with hK
  have hKU : coordBlockSL F U ≤ K := fun x hx =>
    Subgroup.subset_closure (Set.mem_union_left _ hx)
  have hKU' : coordBlockSL F U' ≤ K := fun x hx =>
    Subgroup.subset_closure (Set.mem_union_right _ hx)
  change SpecialLinearGroup.transvection hij c ∈ K
  by_cases h1 : i ∈ U ∧ j ∈ U
  · exact hKU (a11lg_transvection_mem_coordBlockSL hij h1.1 h1.2 c)
  by_cases h2 : i ∈ U' ∧ j ∈ U'
  · exact hKU' (a11lg_transvection_mem_coordBlockSL hij h2.1 h2.2 c)
  have hcross : (i ∉ U ∧ i ∈ U' ∧ j ∈ U ∧ j ∉ U') ∨
      (j ∉ U ∧ j ∈ U' ∧ i ∈ U ∧ i ∉ U') := by
    rcases not_and_or.mp h1 with hiU | hjU
    · have hia : i = a := key i hiU
      have hja : j ≠ a := fun h => hij (hia.trans h.symm)
      have hjU : j ∈ U := by
        by_contra hjU
        exact hja (key j hjU)
      have hjU' : j ∉ U' := by
        intro hjU'
        exact h2 ⟨hia ▸ haU', hjU'⟩
      exact Or.inl ⟨hiU, hia ▸ haU', hjU, hjU'⟩
    · have hja : j = a := key j hjU
      have hia : i ≠ a := fun h => hij (h.trans hja.symm)
      have hiU : i ∈ U := by
        by_contra hiU
        exact hia (key i hiU)
      have hiU' : i ∉ U' := by
        intro hiU'
        exact h2 ⟨hiU', hja ▸ haU'⟩
      exact Or.inr ⟨hjU, hja ▸ haU', hiU, hiU'⟩
  rcases hcross with ⟨hiU, hiU', hjU, hjU'⟩ | ⟨hjU, hjU', hiU, hiU'⟩
  · have hik : i ≠ k := fun h => hiU (h ▸ hkU)
    have hkj : k ≠ j := fun h => hjU' (h ▸ hkU')
    rw [show SpecialLinearGroup.transvection hij c =
        ⁅SpecialLinearGroup.transvection hik c,
          SpecialLinearGroup.transvection hkj (1 : F)⁆ by
      rw [SpecialLinearGroup.commutatorElement_transvection, mul_one]]
    exact a11lg_commutator_mem K
      (hKU' (a11lg_transvection_mem_coordBlockSL hik hiU' hkU' c))
      (hKU (a11lg_transvection_mem_coordBlockSL hkj hkU hjU 1))
  · have hik : i ≠ k := fun h => hiU' (h ▸ hkU')
    have hkj : k ≠ j := fun h => hjU (h ▸ hkU)
    rw [show SpecialLinearGroup.transvection hij c =
        ⁅SpecialLinearGroup.transvection hik c,
          SpecialLinearGroup.transvection hkj (1 : F)⁆ by
      rw [SpecialLinearGroup.commutatorElement_transvection, mul_one]]
    exact a11lg_commutator_mem K
      (hKU (a11lg_transvection_mem_coordBlockSL hik hiU hkU c))
      (hKU' (a11lg_transvection_mem_coordBlockSL hkj hkU' hjU' 1))

private theorem a11lg_lin_not_mem {u : Fin 4 → (Fin 4 → ZMod 7)}
    (hspan : Submodule.span (ZMod 7) (Set.range u) = ⊤) :
    u 2 ∉ Submodule.span (ZMod 7)
      ({u 0 + u 1 + u 2 + u 3, u 3} : Set (Fin 4 → ZMod 7)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let hb : Basis (Fin 4) (ZMod 7) (Fin 4 → ZMod 7) :=
    basisOfTopLeSpanOfCardEqFinrank u (le_of_eq hspan.symm) (by simp)
  have hbi : ∀ i, hb i = u i := by
    intro i
    dsimp only [hb]
    exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank (R := ZMod 7) u _ _) i
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hrepr : ∀ i, hb.repr (u i) = Finsupp.single i (1 : ZMod 7) := by
    intro i
    rw [← hbi i, hb.repr_self]
  have key : hb.repr (u 2) = a • hb.repr (u 0 + u 1 + u 2 + u 3) + b • hb.repr (u 3) := by
    have h := congrArg hb.repr hab
    rw [map_add, map_smul, map_smul] at h
    exact h.symm
  rw [hrepr 2, map_add, map_add, map_add, hrepr 0, hrepr 1, hrepr 2, hrepr 3] at key
  have h0 : a = 0 := by
    have h := congrArg (fun f : Fin 4 →₀ ZMod 7 => f 0) key
    simp at h
    exact h.symm
  have h2 : a = 1 := by
    have h := congrArg (fun f : Fin 4 →₀ ZMod 7 => f 2) key
    simp at h
    exact h.symm
  rw [h0] at h2
  exact (by norm_num : (0 : ZMod 7) ≠ 1) h2

private theorem a11lg_span_range {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    (hfi : ∀ i, f i ∈ Bs) (hgen : Subgroup.closure (Set.range f) = Bs) :
    Submodule.span (ZMod 7) (Set.range (fun i => ι (Additive.ofMul (⟨f i, hfi i⟩ : ↥Bs)))) =
      ⊤ := by
  let u : Fin 4 → (Fin 4 → ZMod 7) := fun i => ι (Additive.ofMul (⟨f i, hfi i⟩ : ↥Bs))
  let K : AddSubgroup (Additive ↥Bs) :=
    AddSubgroup.closure (Set.range (fun i => Additive.ofMul (⟨f i, hfi i⟩ : ↥Bs)))
  have hsub : ∀ x (hx : x ∈ Subgroup.closure (Set.range f)),
      Additive.ofMul (⟨x, hgen ▸ hx⟩ : ↥Bs) ∈ K := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact AddSubgroup.subset_closure (Set.mem_range_self i)
    | one => exact K.zero_mem
    | mul y z hy hz ihy ihz =>
        have h : Additive.ofMul (⟨y * z, hgen ▸ (Subgroup.mul_mem _ hy hz)⟩ : ↥Bs) =
            Additive.ofMul (⟨y, hgen ▸ hy⟩ : ↥Bs) +
              Additive.ofMul (⟨z, hgen ▸ hz⟩ : ↥Bs) := rfl
        rw [h]; exact K.add_mem ihy ihz
    | inv y hy ihy =>
        have h : Additive.ofMul (⟨y⁻¹, hgen ▸ (Subgroup.inv_mem _ hy)⟩ : ↥Bs) =
            -Additive.ofMul (⟨y, hgen ▸ hy⟩ : ↥Bs) := rfl
        rw [h]; exact K.neg_mem ihy
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro b _
    have hmem : (((Additive.toMul b : ↥Bs) : G)) ∈ Subgroup.closure (Set.range f) := by
      rw [hgen]; exact (Additive.toMul b).2
    have h := hsub (((Additive.toMul b : ↥Bs) : G)) hmem
    simpa using h
  have hιK : ∀ y, y ∈ K → ι y ∈ Submodule.span (ZMod 7) (Set.range u) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simpa using Submodule.zero_mem _
    | add p q hp hq ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
    | neg p hp ihp => rw [map_neg]; exact Submodule.neg_mem _ ihp
  rw [Submodule.eq_top_iff']
  intro w
  have hw : ι.symm w ∈ K := by rw [hKtop]; trivial
  have := hιK (ι.symm w) hw
  simpa using this


private theorem a11lg_f2_not_mem {G : Type} [Group G] {Bs : Subgroup G} {f : Fin 4 → G}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} {x : G}
    (hfi : ∀ i, f i ∈ Bs) (hgen : Subgroup.closure (Set.range f) = Bs)
    (hx : x = f 0 * f 1 * f 2 * f 3) (hxBs : x ∈ Bs)
    (hxι : ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) = fun _ => 1) :
    f 2 ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers (f 3) := by
  intro hmem
  let u : Fin 4 → (Fin 4 → ZMod 7) := fun i => ι (Additive.ofMul (⟨f i, hfi i⟩ : ↥Bs))
  have hspan : Submodule.span (ZMod 7) (Set.range u) = ⊤ := a11lg_span_range hfi hgen
  have hnot := a11lg_lin_not_mem hspan
  have hux : u 0 + u 1 + u 2 + u 3 = fun _ => 1 := by
    have h : ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) = u 0 + u 1 + u 2 + u 3 := by
      have hxsub : (⟨x, hxBs⟩ : ↥Bs) =
          ⟨f 0 * f 1 * f 2 * f 3, Bs.mul_mem
            (Bs.mul_mem (Bs.mul_mem (hfi 0) (hfi 1)) (hfi 2)) (hfi 3)⟩ := Subtype.ext hx
      rw [hxsub]
      change ι (Additive.ofMul (⟨f 0, hfi 0⟩ : ↥Bs) +
        Additive.ofMul (⟨f 1, hfi 1⟩ : ↥Bs) +
        Additive.ofMul (⟨f 2, hfi 2⟩ : ↥Bs) +
        Additive.ofMul (⟨f 3, hfi 3⟩ : ↥Bs)) = u 0 + u 1 + u 2 + u 3
      simp only [map_add]
      rfl
    rw [← h, hxι]
  have hle : Subgroup.closure ({x, f 3} : Set G) ≤ Bs := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxBs
    · exact hfi 3
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers (f 3) =
      Subgroup.closure ({x, f 3} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  have hmem' : f 2 ∈ Subgroup.closure ({x, f 3} : Set G) := by rw [← hsup]; exact hmem
  have hP : ∀ y (hy : y ∈ Subgroup.closure ({x, f 3} : Set G)),
      ι (Additive.ofMul (⟨y, hle hy⟩ : ↥Bs)) ∈
        Submodule.span (ZMod 7) ({fun _ => (1 : ZMod 7), u 3} : Set (Fin 4 → ZMod 7)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with rfl | rfl
        · rw [hxι]; exact Submodule.subset_span (by simp)
        · exact Submodule.subset_span (by simp [u])
    | one =>
        have hz : Additive.ofMul (⟨1, hle (Subgroup.one_mem _)⟩ : ↥Bs) = 0 := rfl
        rw [hz, map_zero]
        exact Submodule.zero_mem _
    | mul a b ha hb iha ihb =>
        have h : Additive.ofMul (⟨a * b, hle (Subgroup.mul_mem _ ha hb)⟩ : ↥Bs) =
            Additive.ofMul (⟨a, hle ha⟩ : ↥Bs) + Additive.ofMul (⟨b, hle hb⟩ : ↥Bs) := rfl
        rw [h, map_add]; exact Submodule.add_mem _ iha ihb
    | inv a ha iha =>
        have h : Additive.ofMul (⟨a⁻¹, hle (Subgroup.inv_mem _ ha)⟩ : ↥Bs) =
            -Additive.ofMul (⟨a, hle ha⟩ : ↥Bs) := rfl
        rw [h, map_neg]; exact Submodule.neg_mem _ iha
  have hfin := hP (f 2) hmem'
  have hmem2 : u 2 ∈ Submodule.span (ZMod 7)
      ({u 0 + u 1 + u 2 + u 3, u 3} : Set (Fin 4 → ZMod 7)) := by
    rw [hux]
    simpa [u] using hfin
  exact hnot hmem2


theorem a11LGenInput_holds
    : A11LGenInput := by
  intro hMp hLB G _ _ B Bs x L D J hR hA y K f n hnb hBs hfcomm hford hfcard hx hy hD hnL hnswap
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcfg : GGConfig 7 B Bs x L D J := hR.1
  have hInnL : GGInnerDiagOn Bs L := hR.2.2.1.1
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := hA.2.1
  have hfi : ∀ i, f i ∈ Bs := fun i => by
    rw [← hBs]; exact Subgroup.subset_closure (Set.mem_range_self i)
  have hxBs : x ∈ Bs := by
    rw [hx]
    exact Bs.mul_mem (Bs.mul_mem (Bs.mul_mem (hfi 0) (hfi 1)) (hfi 2)) (hfi 3)
  have hx1 : x ≠ 1 := by
    intro h
    have h7 := hcfg.orderOf_x
    rw [h, orderOf_one] at h7
    omega
  obtain ⟨φ, hrange, hker, hdiag, hJ⟩ := ggA8Nbr_exists_lift_L hMp hcfg hInnL hmodL hnb
  obtain ⟨ιL, hιLx, hιLL, hιLJ⟩ :=
    A8Coord.ggA8Nbr_lModel hcfg.2.1.2.1 hcfg.2.1.2.2.2 (GGConfig.bstar_inf_centralizer_L hcfg)
      hx1 hxBs φ hrange hker hdiag hJ
  have hφinj : Function.Injective φ := a11lg_phi_injective φ hker
  have hmap : Subgroup.map φ (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) =
      Bs ⊓ L := by
    apply le_antisymm
    · rintro g ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨a11lg_diag_mem_Bs hcfg.2.1.2.2.2 hdiag hs,
        by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨s, rfl⟩⟩
    · intro g hg
      obtain ⟨s, hs, rfl⟩ := a11lg_inf_le_diagTorus hφinj hrange hdiag hg
      exact ⟨s, hs, rfl⟩
  have hn2Bs : n 2 ∈ Subgroup.normalizer (Bs : Set G) := a11lg_n2_mem_normalizer hfi hBs hnswap
  have hn2L : n 2 ∈ L := hnL 2
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hn2L)
  have hmTle : Subgroup.map (MulAut.conj m).toMonoidHom
      (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) ≤
      SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have hmem : n 2 * φ t₀ * (n 2)⁻¹ ∈ Bs ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hn2Bs (φ t₀)).mp
          (a11lg_diag_mem_Bs hcfg.2.1.2.2.2 hdiag ht₀)
      · exact L.mul_mem (L.mul_mem hn2L (hrange ▸ MonoidHom.mem_range.mpr ⟨t₀, rfl⟩))
          (L.inv_mem hn2L)
    rw [← hmap] at hmem
    obtain ⟨t', ht', ht'eq⟩ := hmem
    have hconj : m * t₀ * m⁻¹ = t' := by
      apply hφinj
      rw [map_mul, map_mul, map_inv, hm, ht'eq]
    change m * t₀ * m⁻¹ ∈ SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4
    rwa [hconj]
  have hmT : Subgroup.map (MulAut.conj m).toMonoidHom
      (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) =
      SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 :=
    Subgroup.eq_of_le_of_card_ge hmTle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  have hmN : m ∈ Subgroup.normalizer
      (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4 : Set
        (SpecialLinearGroup (Fin 4) (GaloisField 2 3))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have : MulAut.conj m t ∈ Subgroup.map (MulAut.conj m).toMonoidHom
          (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) := ⟨t, ht, rfl⟩
      rwa [hmT] at this
    · intro ht
      have hmem : m * t * m⁻¹ ∈ Subgroup.map (MulAut.conj m).toMonoidHom
          (SpecialLinearGroup.diagonalTorus (GaloisField 2 3) 4) := by rwa [hmT]
      obtain ⟨t', ht', ht'eq⟩ := hmem
      have hteq : t' = t := by
        apply (MulAut.conj m).injective
        change (MulEquiv.toMonoidHom (MulAut.conj m)) t' =
          (MulEquiv.toMonoidHom (MulAut.conj m)) t
        rw [ht'eq]
        rfl
      rwa [hteq] at ht'
  haveI : Nontrivial (GaloisField 2 3)ˣ :=
    ⟨1, ggSL9Zeta, by
      intro h
      have h2 := orderOf_ggSL9Zeta
      rw [← h, orderOf_one] at h2
      omega⟩
  obtain ⟨d, σ, hdσ⟩ := TauCeti.mem_normalizer_diagonalTorus_iff_exists.mp
    (a11lg_toGL_mem_normalizer hmN)
  let U : Finset (Fin 4) := {1, 2, 3}
  have hKrange : (slLowerBlockHom 3 (GaloisField 2 3)).range =
      CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) U := by
    rw [show U = ({1, 2, 3} : Finset (Fin 4)) from rfl]
    apply le_antisymm
    · rintro g ⟨A, rfl⟩
      rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff]
      intro i j hij
      rw [coe_slLowerBlockHom]
      obtain ⟨p, rfl⟩ := (slLowerBlockEquiv 3).surjective i
      obtain ⟨q, rfl⟩ := (slLowerBlockEquiv 3).surjective j
      rw [slLowerBlockMat_apply]
      rcases p with p | p <;> rcases q with q | q
      · obtain rfl : p = 0 := Subsingleton.elim _ _
        obtain rfl : q = 0 := Subsingleton.elim _ _
        rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq, slLowerBlockEquiv_inl, if_pos rfl]
      · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, slLowerBlockEquiv_inl,
          slLowerBlockEquiv_inr, if_neg (fun h => Fin.succ_ne_zero q h.symm)]
      · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, slLowerBlockEquiv_inl,
          slLowerBlockEquiv_inr, if_neg (fun h => Fin.succ_ne_zero p h)]
      · exfalso
        rcases hij with h | h
        · exact h (by fin_cases p <;> decide)
        · exact h (by fin_cases q <;> decide)
    · refine le_trans (coordBlockSL_le_closure (F := GaloisField 2 3) U) ?_
      rw [Subgroup.closure_le]
      rintro g ⟨i, j, hij, hi, hj, c, rfl⟩
      have hi' : i ≠ 0 := fun h => by subst h; simp only [U] at hi; exact absurd hi (by decide)
      have hj' : j ≠ 0 := fun h => by subst h; simp only [U] at hj; exact absurd hj (by decide)
      obtain ⟨i', rfl⟩ : ∃ i' : Fin 3, i'.succ = i :=
        ⟨⟨i.val - 1, by have := i.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin 3, j'.succ = j :=
        ⟨⟨j.val - 1, by have := j.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      refine ⟨SpecialLinearGroup.transvection (fun h => hij (congrArg Fin.succ h)) c, ?_⟩
      rw [slLowerBlockHom_transvection]
  have hJeq : J = Subgroup.map φ
      (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) U) := by
    rw [← hJ, MonoidHom.range_comp, hKrange]
  have hJ2eq : J.map (MulAut.conj (n 2)).toMonoidHom = Subgroup.map φ
      (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) (U.image σ)) := by
    rw [hJeq, ← hm, Subgroup.map_map]
    rw [show (MulAut.conj (φ m)).toMonoidHom.comp φ = φ.comp (MulAut.conj m).toMonoidHom from by
      ext A
      change MulAut.conj (φ m) (φ A) = φ (MulAut.conj m A)
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]]
    rw [← Subgroup.map_map, a11lg_monomial_conj_coordBlockSL (U := U) hdσ]
  have hDdef : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hDJ : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
    apply le_antisymm (ggA8Nbr_bstar_inf_centralizer_J_le hMp hcfg hInnL hmodL hnb)
    rw [hDdef]
    exact inf_le_inf_right _ hcfg.2.1.1
  have hJ2ne : J.map (MulAut.conj (n 2)).toMonoidHom ≠ J := by
    intro heq
    have hf3D : f 3 ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := by
      rw [hDJ, hD]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hf2CJ : f 2 ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : (n 2)⁻¹ * j * n 2 ∈ J := by
        have hjmap : j ∈ J.map (MulAut.conj (n 2)).toMonoidHom := by rw [heq]; exact hj
        obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hjmap
        change n 2 * k * (n 2)⁻¹ = j at hk_eq
        have : k = (n 2)⁻¹ * j * n 2 := by rw [← hk_eq]; group
        rwa [this] at hk
      have hf3comm : f 3 * ((n 2)⁻¹ * j * n 2) = ((n 2)⁻¹ * j * n 2) * f 3 :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hf3D).2 _ hj').symm
      have hf23 : f 2 = n 2 * f 3 * (n 2)⁻¹ := by
        have h2 : (2 : Fin 4) = (Equiv.swap (2 : Fin 4) 3) 3 := by decide
        rw [show f 2 = f ((Equiv.swap 2 3) 3) from congrArg f h2]
        rw [← hnswap 2 3]
      calc j * f 2 = j * (n 2 * f 3 * (n 2)⁻¹) := by rw [hf23]
        _ = n 2 * (((n 2)⁻¹ * j * n 2) * f 3) * (n 2)⁻¹ := by group
        _ = n 2 * (f 3 * ((n 2)⁻¹ * j * n 2)) * (n 2)⁻¹ := by rw [← hf3comm]
        _ = n 2 * f 3 * (n 2)⁻¹ * j := by group
        _ = f 2 * j := by rw [hf23]
    have hf2D : f 2 ∈ D := by
      rw [← hDJ]
      exact Subgroup.mem_inf.mpr ⟨hfi 2, hf2CJ⟩
    have hf2D' : f 2 ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers (f 3) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
      rw [hD] at hf2D
      simpa [Set.pair_comm] using hf2D
    exact a11lg_f2_not_mem hfi hBs hx hxBs hιLx hf2D'
  have hUne : U.image σ ≠ U := by
    intro hU
    apply hJ2ne
    rw [hJ2eq, hJeq, hU]
  have hgen := a11lg_closure_blocks_eq_top (F := GaloisField 2 3) U (U.image σ)
    (by decide) (by rw [Finset.card_image_of_injective (s := U) (f := ⇑σ) σ.injective]; decide) (fun h => hUne h.symm)
  have hmap2 : Subgroup.map φ (Subgroup.closure
      ((CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) U : Set
          (SpecialLinearGroup (Fin 4) (GaloisField 2 3))) ∪
        (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) (U.image σ) : Set
          (SpecialLinearGroup (Fin 4) (GaloisField 2 3))))) =
      Subgroup.closure ((J : Set G) ∪ (J.map (MulAut.conj (n 2)).toMonoidHom : Set G)) := by
    rw [MonoidHom.map_closure, Set.image_union]
    rw [show φ '' (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) U) = (J : Set G)
        from by rw [← Subgroup.coe_map, hJeq]]
    rw [show φ '' (CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 3) (U.image σ)) =
        (J.map (MulAut.conj (n 2)).toMonoidHom : Set G) from by
      rw [← Subgroup.coe_map, hJ2eq]]
  rw [hgen] at hmap2
  rw [← hrange]
  simpa only [MonoidHom.range_eq_map, hgen] using hmap2.le

end CFSG.StandardType.A11

end
