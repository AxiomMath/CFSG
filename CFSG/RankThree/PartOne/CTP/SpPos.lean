module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.RankThree.PartOne.CTP.SpGeom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

variable {K : Type} [Field K]

section Split

theorem le_iSup_inf_eig {g : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hg : g ^ p = 1) {S : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hS : ∀ v ∈ S, mat 2 K g *ᵥ v ∈ S) : S ≤ ⨆ l, S ⊓ eig g l := by
  classical
  let f : Module.End K (Fin 2 ⊕ Fin 2 → K) := Matrix.mulVecLin (mat 2 K g)
  have hfS : ∀ x ∈ S, f x ∈ S := hS
  have hfp : f ^ p = 1 := by
    have h := congrArg (actHom K) hg
    rwa [map_pow, map_one] at h
  have hf'p : f.restrict hfS ^ p = 1 :=
    LinearMap.ext fun x => Subtype.ext (by
      rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, hfp]
      rfl)
  have htop := CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ hf'p
  intro x hx
  have hx' : (⟨x, hx⟩ : S) ∈ (⊤ : Submodule K S) := Submodule.mem_top
  rw [← htop] at hx'
  have hmap := Submodule.mem_map_of_mem (f := S.subtype) hx'
  rw [Submodule.map_iSup] at hmap
  have hle : (⨆ l, Submodule.map S.subtype (Module.End.eigenspace (f.restrict hfS) l)) ≤
      ⨆ l, S ⊓ eig g l := by
    refine iSup_mono fun l => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    show S.subtype y ∈ eig g l
    rw [mem_eig]
    have := Module.End.mem_eigenspace_iff.mp hy
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  exact hle hmap

end Split

section Levi

theorem perfect_hom_eq_one {H : Type*} [Group H] [Group.IsPerfect H] (χ : H →* K) :
    ∀ h, χ h = 1 := by
  intro g
  have hsub : Subsingleton χ.toHomUnits.range := by
    have : Group.IsPerfect χ.toHomUnits.range := Group.IsPerfect.range χ.toHomUnits
    infer_instance
  have h1 : (⟨χ.toHomUnits g, ⟨g, rfl⟩⟩ : χ.toHomUnits.range) = 1 := Subsingleton.elim _ _
  have h2 : χ.toHomUnits g = 1 := congrArg Subtype.val h1
  have h3 := congrArg Units.val h2
  simpa using h3

theorem blockMat_zero_one (M : Matrix (Fin 2) (Fin 2) K) :
    blockMat (0 : Fin 2) 1 M = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem mem_range_shortBlock_of_block {x : StatedSp 2 K}
    (h21 : ∀ i j, mat 2 K x (Sum.inr i) (Sum.inl j) = 0)
    (h12 : ∀ i j, mat 2 K x (Sum.inl i) (Sum.inr j) = 0)
    (hdet : (Matrix.of fun i j : Fin 2 => mat 2 K x (Sum.inl i) (Sum.inl j)).det = 1) :
    x ∈ (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  set P : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j : Fin 2 => mat 2 K x (Sum.inl i) (Sum.inl j)
    with hP
  set Q : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j : Fin 2 => mat 2 K x (Sum.inr i) (Sum.inr j)
    with hQ
  let A : SL(2, K) := ⟨P, hdet⟩
  refine ⟨A, mat_injective ?_⟩
  rw [mat_shortBlock, blockMat_zero_one, blockMat_zero_one]
  have hPQ : Pᵀ * Q = 1 := by
    ext i j
    have hs := congrFun (congrFun (mat_transpose_mul_gram_mul x) (Sum.inl i)) (Sum.inr j)
    rw [transpose_mul_gram_mul_apply,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, Fintype.sum_sum_type] at hs
    simp only [par_inl, par_inr, sgn_inl, sgn_inr, h21, zero_mul, Finset.sum_const_zero, add_zero,
      one_mul] at hs
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply] at hs ⊢
    simpa [hP, hQ, eq_comm] using hs
  have hR : P * ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    change ((A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * _ = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hQR : Q = ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    have h1 : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * Pᵀ = 1 := by
      rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
    calc Q = (((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * Pᵀ) * Q := by rw [h1, one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hPQ, Matrix.mul_one]
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · rw [Matrix.fromBlocks_apply₁₁]
    rfl
  · simp [h12]
  · simp [h21]
  · rw [Matrix.fromBlocks_apply₂₂, ← hQR]
    rfl

end Levi

section Conj

variable [Finite K]

omit [Finite K] in
private theorem inl_coord_eq_zero {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ Submodule.span K {(Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K),
      Pi.single (Sum.inr 1) 1}) (i : Fin 2) : v (Sum.inl i) = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp

omit [Finite K] in
private theorem inr_coord_eq_zero {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ Submodule.span K {(Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K),
      Pi.single (Sum.inl 1) 1}) (i : Fin 2) : v (Sum.inr i) = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp

theorem eq_shortBlock_conj_of_stab {c : StatedSp 2 K} (H : Subgroup (StatedSp 2 K))
    [Group.IsPerfect H] (hcard : Nat.card H = Nat.card SL(2, K))
    (hE : ∀ h ∈ H, ∀ v ∈ Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inl 0) 1),
      mat 2 K c *ᵥ (Pi.single (Sum.inl 1) 1)}, mat 2 K h *ᵥ v ∈ Submodule.span K
        {mat 2 K c *ᵥ (Pi.single (Sum.inl 0) 1), mat 2 K c *ᵥ (Pi.single (Sum.inl 1) 1)})
    (hF : ∀ h ∈ H, ∀ v ∈ Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inr 0) 1),
      mat 2 K c *ᵥ (Pi.single (Sum.inr 1) 1)}, mat 2 K h *ᵥ v ∈ Submodule.span K
        {mat 2 K c *ᵥ (Pi.single (Sum.inr 0) 1), mat 2 K c *ᵥ (Pi.single (Sum.inr 1) 1)}) :
    H = (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (MulAut.conj c).toMonoidHom := by
  have hmatc : ∀ h : StatedSp 2 K, ∀ v, mat 2 K (c⁻¹ * h * c) *ᵥ v =
      mat 2 K c⁻¹ *ᵥ (mat 2 K h *ᵥ (mat 2 K c *ᵥ v)) := by
    intro h v
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hent : ∀ (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (r j : Fin 2 ⊕ Fin 2),
      M r j = (M *ᵥ Pi.single j 1) r := fun M r j => (mulVec_single_one_apply M j r).symm
  have h21 : ∀ h ∈ H, ∀ i j, mat 2 K (c⁻¹ * h * c) (Sum.inr i) (Sum.inl j) = 0 := by
    intro h hh i j
    rw [hent (mat 2 K (c⁻¹ * h * c)) (Sum.inr i) (Sum.inl j), hmatc]
    have hmem : mat 2 K c *ᵥ (Pi.single (Sum.inl j) 1 : Fin 2 ⊕ Fin 2 → K) ∈
        Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K),
          mat 2 K c *ᵥ (Pi.single (Sum.inl 1) 1)} := by
      fin_cases j
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    have h1 := (mem_span_pair_conj c _ _ _).mp (hE h hh _ hmem)
    exact inr_coord_eq_zero h1 i
  have h12 : ∀ h ∈ H, ∀ i j, mat 2 K (c⁻¹ * h * c) (Sum.inl i) (Sum.inr j) = 0 := by
    intro h hh i j
    rw [hent (mat 2 K (c⁻¹ * h * c)) (Sum.inl i) (Sum.inr j), hmatc]
    have hmem : mat 2 K c *ᵥ (Pi.single (Sum.inr j) 1 : Fin 2 ⊕ Fin 2 → K) ∈
        Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K),
          mat 2 K c *ᵥ (Pi.single (Sum.inr 1) 1)} := by
      fin_cases j
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    have h1 := (mem_span_pair_conj c _ _ _).mp (hF h hh _ hmem)
    exact inl_coord_eq_zero h1 i
  let Pm : StatedSp 2 K → Matrix (Fin 2) (Fin 2) K := fun h =>
    Matrix.of fun i j : Fin 2 => mat 2 K (c⁻¹ * h * c) (Sum.inl i) (Sum.inl j)
  have hPmul : ∀ h₁ ∈ H, ∀ h₂ : StatedSp 2 K, Pm (h₁ * h₂) = Pm h₁ * Pm h₂ := by
    intro h₁ hh₁ h₂
    ext i j
    have hmul : mat 2 K (c⁻¹ * (h₁ * h₂) * c) =
        mat 2 K (c⁻¹ * h₁ * c) * mat 2 K (c⁻¹ * h₂ * c) := by
      rw [← map_mul]
      congr 1
      group
    simp only [Pm, Matrix.of_apply, Matrix.mul_apply, hmul, Fintype.sum_sum_type]
    simp [h12 h₁ hh₁]
  let χ : H →* K :=
    { toFun := fun h => (Pm (h : StatedSp 2 K)).det
      map_one' := by
        have h1 : Pm ((1 : H) : StatedSp 2 K) = 1 := by
          have hm1 : mat 2 K (c⁻¹ * ((1 : H) : StatedSp 2 K) * c) = 1 := by
            rw [Subgroup.coe_one, mul_one, inv_mul_cancel, map_one]
          ext i j
          show mat 2 K (c⁻¹ * ((1 : H) : StatedSp 2 K) * c) (Sum.inl i) (Sum.inl j) =
            (1 : Matrix (Fin 2) (Fin 2) K) i j
          rw [hm1]
          simp [Matrix.one_apply]
        show (Pm ((1 : H) : StatedSp 2 K)).det = 1
        rw [h1, Matrix.det_one]
      map_mul' := fun h₁ h₂ => by
        simp only [Subgroup.coe_mul]
        rw [hPmul h₁ h₁.2, Matrix.det_mul] }
  have hdet : ∀ h ∈ H, (Pm h).det = 1 := fun h hh => perfect_hom_eq_one χ ⟨h, hh⟩
  have hle : H.map (MulAut.conj c⁻¹).toMonoidHom ≤
      (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
    rintro _ ⟨h, hh, rfl⟩
    have e : (MulAut.conj c⁻¹).toMonoidHom h = c⁻¹ * h * c := by simp
    rw [e]
    exact mem_range_shortBlock_of_block (h21 h hh) (h12 h hh) (hdet h hh)
  have hcard' : Nat.card (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range =
      Nat.card (H.map (MulAut.conj c⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (shortBlock_injective (K := K) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1))).toEquiv).symm
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard'.le
  have hH : H = (H.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨(MulAut.conj c⁻¹) x, ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hh
  rw [hH, heq]

end Conj

end CFSG.RankThree.PartOne.CTP
