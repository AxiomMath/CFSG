module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux5

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA_permSU_one {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} :
    ggPermSU (K := K) (f := f) (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((1 : Equiv.Perm (Fin n)).permMatrix K) = (1 : Matrix (Fin n) (Fin n) K)
  simp

theorem ggNSPosPA_ggConjAut_mul {G : Type} [Group G] {Bs : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hh : h ∈ Subgroup.normalizer (Bs : Set G)) :
    ggConjAut Bs hg * ggConjAut Bs hh = ggConjAut Bs (Subgroup.mul_mem _ hg hh) := by
  ext b
  rw [MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
  group

theorem ggNSPosPA_ggConjAut_congr {G : Type} [Group G] {Bs : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hh : h ∈ Subgroup.normalizer (Bs : Set G))
    (heq : g = h) : ggConjAut Bs hg = ggConjAut Bs hh := by
  subst heq
  exact congrArg (fun p => ggConjAut Bs p) (Subsingleton.elim hg hh)

noncomputable def ggNSPosPA_permAutHom {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    Equiv.Perm (Fin n) →* ↥(ggAutomizer ψ.range Bs) where
  toFun σ :=
    ⟨ggConjAut Bs (ggNSPosPA_permSU_mem_normalizer h hd σ⁻¹),
      ggConjAut_mem_ggAutomizer
        (H := ψ.range) (g := ψ (ggPermSU (K := K) (f := f) σ⁻¹))
        (by exact ⟨ggPermSU (K := K) (f := f) σ⁻¹, rfl⟩)
        (ggNSPosPA_permSU_mem_normalizer h hd σ⁻¹)⟩
  map_one' := by
    apply Subtype.ext
    ext b
    rw [ggConjAut_apply]
    simp [ggNSPosPA_permSU_one]
  map_mul' σ τ := by
    apply Subtype.ext
    ext b
    have hperm : ggPermSU (K := K) (f := f) (σ * τ)⁻¹ =
        ggPermSU (K := K) (f := f) σ⁻¹ * ggPermSU (K := K) (f := f) τ⁻¹ := by
      rw [_root_.mul_inv_rev, ggNSPosPA_permSU_mul_anti']
    rw [Subgroup.coe_mul, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply,
      hperm, map_mul]
    group

theorem ggNSPosPA_permAutHom_apply {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (σ : Equiv.Perm (Fin n)) (b : ↥Bs) :
    ((((ggNSPosPA_permAutHom h hd σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) b : ↥Bs) : G) =
      ψ (ggPermSU (K := K) (f := f) σ⁻¹) * (b : G) *
        (ψ (ggPermSU (K := K) (f := f) σ⁻¹))⁻¹ := by
  rw [show ((ggNSPosPA_permAutHom h hd σ : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) =
      ggConjAut Bs (ggNSPosPA_permSU_mem_normalizer h hd σ⁻¹) from rfl]
  exact ggConjAut_apply Bs _ b

theorem ggNSPosPA_permutationGL_eq_permSU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    (TauCeti.permutationGL σ : GL (Fin n) K) = (ggPermSU (K := K) (f := f) σ⁻¹ : GL (Fin n) K) := by
  apply Units.ext
  rw [TauCeti.permutationGL_coe]
  rfl

theorem ggNSPosPA_diag_centralizes {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {u : Su K 2 f n} (hu : ∃ d : Fin n → Kˣ, (u : GL (Fin n) K) = TauCeti.diagGL d)
    {b : G} (hb : b ∈ Bs) : ψ u * b = b * ψ u := by
  obtain ⟨d, hd_eq⟩ := hu
  obtain ⟨g, hgdiag, hgind⟩ := hd b hb
  obtain ⟨db, hdb_eq⟩ := hgdiag
  obtain ⟨y, hy, hby⟩ := hgind.2 u
  have hu_mat : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (d i : K)) := by
    rw [hd_eq]; exact ggNSPosPA_coe_diagGL d
  have hcomm_mat : (g : Matrix (Fin n) (Fin n) K) *
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) := by
    rw [hdb_eq, hu_mat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hcomm : g * (u : GL (Fin n) K) = (u : GL (Fin n) K) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hcomm_mat
  have hyu : y = u := Subtype.ext (by
    rw [hy]
    rw [hcomm]
    group)
  rw [hyu] at hby
  have : b * ψ u = ψ u * b := by
    have h' := congrArg (fun z => z * b) hby
    simpa [mul_assoc] using h'
  exact this.symm

theorem ggNSPosPA_permAutHom_surjective {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    Function.Surjective (ggNSPosPA_permAutHom h hd) := by
  intro φ
  have hmem : (φ : MulAut ↥Bs) ∈ ggInduced ψ.range Bs := by
    have h2 : (φ : MulAut ↥Bs) ∈ ggInducedSubgroup ψ.range Bs := by
      rw [← ggAutomizer_eq]
      exact φ.2
    exact h2
  obtain ⟨g, hgH, hgN, hφ⟩ := hmem
  obtain ⟨x, rfl⟩ := hgH
  obtain ⟨d, σ, hx⟩ := ggNSPosPA_monomial_of_mem_normalizer h hd hgN
  let P : Su K 2 f n := ggPermSU (K := K) (f := f) σ⁻¹
  let u : Su K 2 f n := x * P⁻¹
  have hu : (u : GL (Fin n) K) = TauCeti.diagGL d := by
    show (x : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹ = TauCeti.diagGL d
    rw [show (P : GL (Fin n) K) = (ggPermSU (K := K) (f := f) σ⁻¹ : GL (Fin n) K) from rfl,
      ← ggNSPosPA_permutationGL_eq_permSU σ, hx]
    group
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  ext b
  rw [ggNSPosPA_permAutHom_apply]
  have hx_eq : (ψ x : G) = ψ u * ψ P := by
    have hxu : x = u * P := by
      apply Subtype.ext
      show (x : GL (Fin n) K) = (x : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹ * (P : GL (Fin n) K)
      group
    rw [hxu, map_mul]
  have hPmem : ψ P * (b : G) * (ψ P)⁻¹ ∈ Bs := ggNSPosPA_permSU_conj_mem h hd σ⁻¹ b.2
  have hcommP : ψ u * (ψ P * (b : G) * (ψ P)⁻¹) =
      (ψ P * (b : G) * (ψ P)⁻¹) * ψ u :=
    ggNSPosPA_diag_centralizes h hd ⟨d, hu⟩ hPmem
  rw [hφ b, hx_eq, _root_.mul_inv_rev]
  change ψ P * (b : G) * (ψ P)⁻¹ = ψ u * ψ P * (b : G) * ((ψ P)⁻¹ * (ψ u)⁻¹)
  rw [show ψ u * ψ P * (b : G) * ((ψ P)⁻¹ * (ψ u)⁻¹) =
      ψ u * (ψ P * (b : G) * (ψ P)⁻¹) * (ψ u)⁻¹ by group]
  rw [hcommP]
  group

end CFSG.StandardType

end
