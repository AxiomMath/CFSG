module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

section SL2

variable (K : Type) [Field K]

@[expose] def uHom : Multiplicative K →* SL(2, K) where
  toFun a := ⟨!![1, Multiplicative.toAdd a; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    simp [Matrix.one_fin_two]
  map_mul' a b := by
    apply Subtype.ext
    show !![1, Multiplicative.toAdd (a * b); 0, 1] =
      !![1, Multiplicative.toAdd a; 0, 1] * !![1, Multiplicative.toAdd b; 0, 1]
    simp [Matrix.mul_fin_two, toAdd_mul, add_comm]

@[expose] def uTri : Subgroup SL(2, K) := (uHom K).range

variable {K}

private theorem mem_uTri_iff {g : SL(2, K)} :
    g ∈ uTri K ↔ ∃ a : Multiplicative K, uHom K a = g := by
  simp only [uTri, MonoidHom.mem_range]

private theorem uTri_sq_eq_one [CharP K 2] {g : SL(2, K)} (hg : g ∈ uTri K) : g ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := mem_uTri_iff.mp hg
  have ha2 : a ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one, CharTwo.two_nsmul]
  rw [← ha, ← map_pow, ha2, map_one]

private theorem coe_uHom (a : Multiplicative K) :
    (uHom K a : Matrix (Fin 2) (Fin 2) K) = !![1, Multiplicative.toAdd a; 0, 1] :=
  rfl

theorem card_uTri : Nat.card (uTri K) = Nat.card K := by
  have hinj : Function.Injective (uHom K) := by
    intro a b h
    have h01 : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      have h' := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 1) h
      rw [coe_uHom a, coe_uHom b] at h'
      simpa using h'
    exact Multiplicative.toAdd.injective h01
  calc Nat.card (uTri K) = Nat.card ((uHom K).range) := rfl
    _ = Nat.card (Multiplicative K) := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

private theorem diag2_pow_seven {s : K} (hs : s ≠ 0) (hs7 : s ^ 7 = 1) :
    (Matrix.SpecialLinearGroup.diag2 s hs) ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    Matrix.SpecialLinearGroup.diag2_coe, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.pow_apply, hs7, inv_pow]

private theorem diag2_ne_one {s : K} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    Matrix.SpecialLinearGroup.diag2 s hs ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : SL(2, K) => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have hs_eq : s = 1 := by
    simpa [Matrix.SpecialLinearGroup.diag2_coe'] using h00
  exact hs1 hs_eq

private theorem diag2_mul_uHom_mul_diag2_inv {s : K} (hs : s ≠ 0) (a : Multiplicative K) :
    Matrix.SpecialLinearGroup.diag2 s hs * uHom K a *
        (Matrix.SpecialLinearGroup.diag2 s hs)⁻¹ =
      uHom K (Multiplicative.ofAdd (s ^ 2 * Multiplicative.toAdd a)) := by
  have hinv : (((Matrix.SpecialLinearGroup.diag2 s hs)⁻¹ : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) = !![s⁻¹, 0; 0, s] := by
    rw [Matrix.SpecialLinearGroup.diag2_inv, Matrix.SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv,
    Matrix.SpecialLinearGroup.diag2_coe']
  simp only [coe_uHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem exists_orderOf_eq_seven_mem_normalizer_uTri (hK : Nat.card K = 8) :
    ∃ d : SL(2, K), orderOf d = 7 ∧ d ∈ Subgroup.normalizer (uTri K : Set SL(2, K)) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by simpa [Nat.card_eq_fintype_card] using hK
  have hs : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
    have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
      have h2 : ({0, 1} : Finset K).card ≤ 2 := by
        calc ({0, 1} : Finset K).card ≤ ({1} : Finset K).card + 1 :=
              Finset.card_insert_le 0 {1}
          _ = 2 := by simp
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨s, -, hs'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs'
    exact ⟨s, hs'.1, hs'.2⟩
  obtain ⟨s, hs0, hs1⟩ := hs
  have hs7 : s ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one s hs0
    simpa [hcard] using this
  let d : SL(2, K) := Matrix.SpecialLinearGroup.diag2 s hs0
  have hd7 : d ^ 7 = 1 := diag2_pow_seven hs0 hs7
  have hd_ne : d ≠ 1 := diag2_ne_one hs0 hs1
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨d, orderOf_eq_prime hd7 hd_ne, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨a, ha⟩ := mem_uTri_iff.mp hh
    rw [mem_uTri_iff]
    refine ⟨Multiplicative.ofAdd (s ^ 2 * Multiplicative.toAdd a), ?_⟩
    rw [← ha]
    show uHom K (Multiplicative.ofAdd (s ^ 2 * Multiplicative.toAdd a)) =
      Matrix.SpecialLinearGroup.diag2 s hs0 * uHom K a *
        (Matrix.SpecialLinearGroup.diag2 s hs0)⁻¹
    exact (diag2_mul_uHom_mul_diag2_inv hs0 a).symm
  · intro hh
    obtain ⟨b, hb⟩ := mem_uTri_iff.mp hh
    rw [mem_uTri_iff]
    refine ⟨Multiplicative.ofAdd ((s⁻¹) ^ 2 * Multiplicative.toAdd b), ?_⟩
    have hdi : Matrix.SpecialLinearGroup.diag2 s⁻¹ (inv_ne_zero hs0) = d⁻¹ := by
      dsimp only [d]
      rw [Matrix.SpecialLinearGroup.diag2_inv]
    have hconj := diag2_mul_uHom_mul_diag2_inv (inv_ne_zero hs0) b
    rw [hdi] at hconj
    rw [← hconj, hb]
    group

end SL2

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def u0Sub : Subgroup (MulAut W) := ((uTri S.K).prod (uTri S.K)).map S.jHom

theorem u0Sub_le_omega0 : u0Sub S ≤ S.omega0 := by
  simpa only [u0Sub, OmegaModel.omega0] using
    Subgroup.map_le_range S.jHom ((uTri S.K).prod (uTri S.K))

theorem card_u0Sub (hK : Nat.card S.K = 8) : Nat.card (u0Sub S) = 64 := by
  rw [u0Sub, Subgroup.card_map_of_injective S.jHom_injective,
    Nat.card_congr (Subgroup.prodEquiv (uTri S.K) (uTri S.K)).toEquiv, Nat.card_prod,
    card_uTri, hK]

private theorem u0Sub_sq_eq_one {x : MulAut W} (hx : x ∈ u0Sub S) : x ^ 2 = 1 := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (by simpa only [u0Sub] using hx)
  have hy' := Subgroup.mem_prod.mp hy
  have h1 : y ^ 2 = 1 := by
    refine Prod.ext ?_ ?_
    · simpa using uTri_sq_eq_one hy'.1
    · simpa using uTri_sq_eq_one hy'.2
  rw [← map_pow, h1, map_one]

theorem isPGroup_two_u0Sub : IsPGroup 2 (u0Sub S) := by
  intro x
  refine ⟨1, ?_⟩
  have h : x ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact u0Sub_sq_eq_one S x.2
  simpa using h

theorem exists_diag_mem_normalizer_u0Sub (hK : Nat.card S.K = 8) :
    ∃ d : SL(2, S.K), orderOf (S.jHom (d, d)) = 7 ∧
      S.jHom (d, d) ∈ Subgroup.normalizer (u0Sub S : Set (MulAut W)) := by
  obtain ⟨d, hd7, hd⟩ := exists_orderOf_eq_seven_mem_normalizer_uTri hK
  refine ⟨d, ?_, ?_⟩
  · rw [orderOf_injective S.jHom S.jHom_injective (d, d)]
    simp only [Prod.orderOf_mk, hd7, Nat.lcm_self]
  · have hdd : (d, d) ∈ Subgroup.normalizer
        (((uTri S.K).prod (uTri S.K) : Subgroup (SL(2, S.K) × SL(2, S.K))) :
          Set (SL(2, S.K) × SL(2, S.K))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro p
      rw [Subgroup.mem_prod, Subgroup.mem_prod]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hd p.1).mp h1,
          (Subgroup.mem_normalizer_iff.mp hd p.2).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hd p.1).mpr h1,
          (Subgroup.mem_normalizer_iff.mp hd p.2).mpr h2⟩
    have hmap := Subgroup.le_normalizer_map (H := (uTri S.K).prod (uTri S.K)) S.jHom
      (Subgroup.mem_map.mpr ⟨(d, d), hdd, rfl⟩)
    simpa only [u0Sub] using hmap

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
