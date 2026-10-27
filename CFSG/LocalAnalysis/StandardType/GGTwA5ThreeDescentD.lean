module

import all CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentB
import all CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentC
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem twd_c2 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    A ≤ twd_T hker hAle w₁ := by
  have hw₁' := hw₁
  obtain ⟨-, h2, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro a ha
  refine (twd_mem_T hker hAle w₁).mpr ⟨hAle ha, ?_⟩
  exact h2 ⟨⟨a, ha⟩, rfl⟩

private theorem twd_c3 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ (k : Fin N) (ζ : Multiplicative (ZMod 3)), MulAut.conj (twd_cor hker hAle w₁ k ζ) ∈ twd_T hker
        hAle w₁ := by
  have hw₁' := hw₁
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro k ζ
  refine (twd_mem_T hker hAle w₁).mpr ⟨(U63TB.conjP (U63TB.twoSub ψ.ker hker) _).2, ?_⟩
  show U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_cor hker
      hAle w₁ k ζ)) ∈ w₁.T
  rw [U63TB.redHom_conjP, twd_cor_mk]
  exact h3 k ζ

private theorem twd_c4 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ (j : Fin N), ∀ x ∈ twd_T hker hAle w₁, ∀ y ∈ twd_T hker hAle w₁,
      twd_alpha hker hAle w₁ j (x * y) = twd_alpha hker hAle w₁ j x * twd_alpha hker hAle w₁ j
          y := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro j x hx y hy
  obtain ⟨hxP, hxT⟩ := (twd_mem_T hker hAle w₁).mp hx
  obtain ⟨hyP, hyT⟩ := (twd_mem_T hker hAle w₁).mp hy
  have hxyP : x * y ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker) := (U63TB.presZ (U63TB.twoSub ψ.ker
      hker)).mul_mem hxP hyP
  rw [twd_alpha_of_mem hker hAle w₁ j hxyP, twd_alpha_of_mem hker hAle w₁ j hxP,
    twd_alpha_of_mem hker hAle w₁ j hyP]
  have hm : U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x * y, hxyP⟩ =
      U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩ * U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨y,
          hyP⟩ := by
    ext c
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
    calc U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x * y, hxyP⟩ (l : L' ⧸ U63TB.twoSub ψ.ker hker)
        = (((x * y) l : L') : L' ⧸ U63TB.twoSub ψ.ker hker) := U63TB.redHom_mk (U63TB.twoSub ψ.ker
            hker) ⟨x * y, hxyP⟩ l
      _ = ((x (y l) : L') : L' ⧸ U63TB.twoSub ψ.ker hker) := by rw [MulAut.mul_apply]
      _ = U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩ ((y l : L') : L' ⧸ U63TB.twoSub ψ.ker
          hker) :=
        (U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩ (y l)).symm
      _ = U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩ (U63TB.redHom (U63TB.twoSub ψ.ker hker)
          ⟨y, hyP⟩ (l : L' ⧸ U63TB.twoSub ψ.ker hker)) := by
        rw [U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨y, hyP⟩ l]
      _ = (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩ * U63TB.redHom (U63TB.twoSub ψ.ker hker)
          ⟨y, hyP⟩) (l : L' ⧸ U63TB.twoSub ψ.ker hker) :=
        by rw [MulAut.mul_apply]
  rw [hm]
  exact h4 j _ hxT _ hyT

private theorem twd_c5 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ k : Fin N, Function.Injective (twd_cor hker hAle w₁ k) := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, h5, -, -, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro k ζ ξ h
  apply h5 k
  rw [← twd_cor_mk hker hAle w₁ k ζ, ← twd_cor_mk hker hAle w₁ k ξ, h]

private theorem twd_c6 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ (j k : Fin N) (ζ ξ : Multiplicative (ZMod 3)), Commute (twd_cor hker hAle w₁ j ζ) (twd_cor
        hker hAle w₁ k ξ) := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  have hcube : ∀ (i : Fin N) (θ : Multiplicative (ZMod 3)), (twd_cor hker hAle w₁ i θ) ^ 3 = 1 :=
      fun i θ => by
    rw [← map_pow, twd_mu3_cube, map_one]
  intro j k ζ ξ
  have hmk : ((twd_cor hker hAle w₁ k ξ * twd_cor hker hAle w₁ j ζ * (twd_cor hker hAle w₁ k ξ)⁻¹ :
      L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
      ((twd_cor hker hAle w₁ j ζ : L') : L' ⧸ U63TB.twoSub ψ.ker hker) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, twd_cor_mk]
    rw [(h6 k j ξ ζ).eq]
    group
  have hcb : (twd_cor hker hAle w₁ k ξ * twd_cor hker hAle w₁ j ζ * (twd_cor hker hAle w₁ k ξ)⁻¹) ^
      3 = 1 := by
    rw [conj_pow, hcube, mul_one, mul_inv_cancel]
  have heq := twd_eq_of_mk_eq hker hmk hcb (hcube j ζ)
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

private theorem twd_c7 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ τ ∈ twd_T hker hAle w₁, ∀ (k : Fin N) (ζ : Multiplicative (ZMod 3)), τ (twd_cor hker hAle w₁ k
        ζ) = twd_cor hker hAle w₁ k ζ := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  have hcube : ∀ (i : Fin N) (θ : Multiplicative (ZMod 3)), (twd_cor hker hAle w₁ i θ) ^ 3 = 1 :=
      fun i θ => by
    rw [← map_pow, twd_mu3_cube, map_one]
  intro τ hτ k ζ
  obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
  refine twd_eq_of_mk_eq hker ?_ ?_ (hcube k ζ)
  · rw [← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ (twd_cor hker hAle w₁ k ζ), twd_cor_mk]
    exact h7 _ hτT k ζ
  · rw [← map_pow, hcube k ζ, map_one]

private theorem twd_c8 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ (i j : Fin N) (ζ : Multiplicative (ZMod 3)),
      twd_alpha hker hAle w₁ i (MulAut.conj (twd_cor hker hAle w₁ j ζ)) = ζ ^ C i j := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro i j ζ
  have hP : MulAut.conj (twd_cor hker hAle w₁ j ζ) ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker) :=
      (U63TB.conjP (U63TB.twoSub ψ.ker hker) _).2
  rw [twd_alpha_of_mem hker hAle w₁ i hP]
  have hm : U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨MulAut.conj (twd_cor hker hAle w₁ j ζ), hP⟩ =
      MulAut.conj (w₁.cor j ζ) := by
    show U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_cor hker
        hAle w₁ j ζ)) = _
    rw [U63TB.redHom_conjP, twd_cor_mk]
  rw [hm]
  exact h8 i j ζ

private theorem twd_c9 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ k : Fin N, ∀ τ ∈ twd_T hker hAle w₁, MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) *
        τ * (MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹ =
      τ * (MulAut.conj (twd_cor hker hAle w₁ k (twd_alpha hker hAle w₁ k τ)))⁻¹ := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  have hinj := U63TB.redHom_injective (U63TB.twoSub ψ.ker hker) (U63TB.twoSub_le_center hker) hperf
  intro k τ hτ
  obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
  have e1 : U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_n (L'
      := L') hker hperf hAle w₁ hw₁ k)) = MulAut.conj (w₁.n k) := by
    rw [U63TB.redHom_conjP, twd_n_mk]
  have e2 : U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_cor
      hker hAle w₁ k (twd_alpha hker hAle w₁ k τ))) =
      MulAut.conj (w₁.cor k (w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩))) := by
    rw [U63TB.redHom_conjP, twd_cor_mk, twd_alpha_of_mem hker hAle w₁ k hτP]
  have key : U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * ⟨τ,
      hτP⟩ * (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹ =
      ⟨τ, hτP⟩ * (U63TB.conjP (U63TB.twoSub ψ.ker hker) (twd_cor hker hAle w₁ k (twd_alpha hker hAle
          w₁ k τ)))⁻¹ := by
    apply hinj
    simp only [map_mul, map_inv, e1, e2]
    exact h9 k _ hτT
  exact congrArg Subtype.val key

private theorem twd_c10 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ k : Fin N, ∀ τ ∈ twd_T hker hAle w₁, twd_n (L' := L') hker hperf hAle w₁ hw₁ k * (τ (twd_n (L'
        := L') hker hperf hAle w₁ hw₁ k))⁻¹ = (twd_cor hker hAle w₁ k (twd_alpha hker hAle w₁ k
        τ))⁻¹ := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro k τ hτ
  obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
  refine twd_eq_of_mk_eq hker ?_ (twd_n_cube hker hperf hAle w₁ hw₁ k hτ) ?_
  · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [twd_cor_mk, twd_alpha_of_mem hker hAle w₁ k hτP,
      ← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ (twd_n (L' := L') hker hperf hAle w₁ hw₁
          k), twd_n_mk]
    exact h10 k _ hτT
  · rw [inv_pow, ← map_pow, twd_mu3_cube, map_one, inv_one]

private theorem twd_c11 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ τ ∈ twd_T hker hAle w₁, (∀ k : Fin N, twd_alpha hker hAle w₁ k τ = 1) → τ = 1 := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  have hinj := U63TB.redHom_injective (U63TB.twoSub ψ.ker hker) (U63TB.twoSub_le_center hker) hperf
  intro τ hτ hα
  obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
  have h1 : U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ = 1 :=
    h11 _ hτT fun k => by rw [← twd_alpha_of_mem hker hAle w₁ k hτP]; exact hα k
  have h2 : (⟨τ, hτP⟩ : U63TB.presZ (U63TB.twoSub ψ.ker hker)) = 1 := hinj (h1.trans (map_one
      _).symm)
  have h3 := congrArg Subtype.val h2
  simpa using h3

private theorem twd_c12 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ k : Fin N, ∃ a ∈ A, twd_alpha hker hAle w₁ k a ≠ 1 := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  intro k
  obtain ⟨a₁, ⟨a, rfl⟩, hα⟩ := h12 k
  refine ⟨a.1, a.2, ?_⟩
  rw [twd_alpha_of_mem hker hAle w₁ k (hAle a.2)]
  exact hα

private theorem twd_map_join {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) :
    (⨆ k, (twd_cor hker hAle w₁ k).range).map (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)) = ⨆ k,
        (w₁.cor k).range := by
  rw [Subgroup.map_iSup]
  refine iSup_congr fun k => ?_
  have hcomp : (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).comp (twd_cor hker hAle w₁ k) = w₁.cor
      k :=
    MonoidHom.ext fun ζ => twd_cor_mk hker hAle w₁ k ζ
  rw [MonoidHom.map_range, hcomp]

private theorem twd_join_comm {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ x ∈ ⨆ k, (twd_cor hker hAle w₁ k).range, ∀ y ∈ ⨆ k, (twd_cor hker hAle w₁ k).range, Commute x
        y := by
  intro x hx y hy
  refine Subgroup.iSup_induction (fun k => (twd_cor hker hAle w₁ k).range)
    (C := fun x => ∀ y ∈ ⨆ k, (twd_cor hker hAle w₁ k).range, Commute x y) hx ?_ ?_ ?_ y hy
  · rintro i _ ⟨θ, rfl⟩ y hy
    refine Subgroup.iSup_induction (fun k => (twd_cor hker hAle w₁ k).range)
      (C := fun y => Commute (twd_cor hker hAle w₁ i θ) y) hy ?_ ?_ ?_
    · rintro j _ ⟨ζ, rfl⟩
      exact twd_c6 hker hAle w₁ hw₁ i j θ ζ
    · exact Commute.one_right _
    · intro a b ha hb
      exact ha.mul_right hb
  · intro y _
    exact Commute.one_left _
  · intro a b ha hb y hy
    exact (ha y hy).mul_left (hb y hy)

private theorem twd_join_cube {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M)
    {s : L'} (hs : s ∈ ⨆ k, (twd_cor hker hAle w₁ k).range) : s ^ 3 = 1 := by
  have hcomm := twd_join_comm hker hAle w₁ hw₁
  have h := Subgroup.iSup_induction (fun k => (twd_cor hker hAle w₁ k).range)
    (C := fun s => s ^ 3 = 1 ∧ s ∈ ⨆ k, (twd_cor hker hAle w₁ k).range) hs ?_ ?_ ?_
  · exact h.1
  · rintro i _ ⟨θ, rfl⟩
    exact ⟨by rw [← map_pow, twd_mu3_cube, map_one], Subgroup.mem_iSup_of_mem i ⟨θ, rfl⟩⟩
  · exact ⟨one_pow 3, Subgroup.one_mem _⟩
  · rintro a b ⟨ha3, haJ⟩ ⟨hb3, hbJ⟩
    refine ⟨?_, Subgroup.mul_mem _ haJ hbJ⟩
    rw [(hcomm a haJ b hbJ).mul_pow, ha3, hb3, one_mul]

private theorem twd_center_of_mk {L' R : Type} [Group L'] [Finite L'] [Group R]
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {c' : L'}
    (hc : (c' : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ Subgroup.center (L' ⧸ U63TB.twoSub ψ.ker hker)) :
    c' ∈ Subgroup.center L' := by
  have h : ∀ l : L', l⁻¹ * (MulAut.conj c') l ∈ U63TB.twoSub ψ.ker hker := by
    intro l
    apply QuotientGroup.eq.mp
    rw [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hl := Subgroup.mem_center_iff.mp hc (l : L' ⧸ U63TB.twoSub ψ.ker hker)
    rw [← hl]
    group
  have h1 := U63TB.aut_eq_one_of_central (U63TB.twoSub_le_center hker) hperf h
  rw [Subgroup.mem_center_iff]
  intro l
  have h2 := congrArg (fun f : MulAut L' => f l) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

private theorem twd_c13 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range →
      ∃ t ∈ ⨆ k, (twd_cor hker hAle w₁ k).range, a = MulAut.conj t := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -, ⟨-, -, -⟩, -, -⟩ := hw₁'
  have hinj := U63TB.redHom_injective (U63TB.twoSub ψ.ker hker) (U63TB.twoSub_le_center hker) hperf
  rintro a haA ⟨g, hg⟩
  have hainP : a ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker) := hAle haA
  have hRa : U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨a, hainP⟩ = MulAut.conj (g : L' ⧸ U63TB.twoSub
      ψ.ker hker) := by
    have hm : (⟨a, hainP⟩ : U63TB.presZ (U63TB.twoSub ψ.ker hker)) = U63TB.conjP (U63TB.twoSub ψ.ker
        hker) g := Subtype.ext hg.symm
    rw [hm, U63TB.redHom_conjP]
  obtain ⟨t₁, ht₁, hct⟩ := h13 (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨a, hainP⟩) ⟨⟨a, haA⟩, rfl⟩
    ⟨(g : L' ⧸ U63TB.twoSub ψ.ker hker), hRa.symm⟩
  have ht₁' : t₁ ∈ (⨆ k, (twd_cor hker hAle w₁ k).range).map (QuotientGroup.mk' (U63TB.twoSub ψ.ker
      hker)) := by
    rw [twd_map_join hker hAle w₁]
    exact ht₁
  obtain ⟨t, htmem, htmk⟩ := Subgroup.mem_map.mp ht₁'
  refine ⟨t, htmem, ?_⟩
  have hconj : U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker) t) =
      U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨a, hainP⟩ := by
    rw [U63TB.redHom_conjP, hct]
    exact congrArg (fun x => MulAut.conj x) htmk
  exact (congrArg Subtype.val (hinj hconj)).symm

private theorem twd_c14 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ twd_Tsc hker hAle w₁ := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, ⟨-, h15b, -⟩, -, -⟩ := hw₁'
  have h2 : IsPGroup 2 (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).ker := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.isPGroup_twoSub hker
  have hc : (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.twoSub_le_center hker
  intro z hz hodd
  have hzc : (z : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ Subgroup.center (L' ⧸ U63TB.twoSub ψ.ker
      hker) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz g]
  have hzT : (z : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ w₁.Tsc :=
    h14 _ hzc (Odd.of_dvd_nat hodd (orderOf_map_dvd (QuotientGroup.mk' (U63TB.twoSub ψ.ker
        hker)) z))
  refine (twd_mem_Tsc hker hAle w₁).mpr ⟨hzT, fun τ hτ => ?_⟩
  obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
  refine eq_of_map_eq_of_pow_odd (f := QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)) hc h2 hodd ?_ ?_
    (pow_orderOf_eq_one z)
  · show ((τ z : L') : L' ⧸ U63TB.twoSub ψ.ker hker) = ((z : L') : L' ⧸ U63TB.twoSub ψ.ker hker)
    rw [← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ z]
    exact h15b _ hτT _ hzT
  · rw [← map_pow, pow_orderOf_eq_one, map_one]

private theorem twd_c15a {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ g : L', (∀ a ∈ A, MulAut.conj g * a = a * MulAut.conj g) →
      g ∈ twd_Tsc hker hAle w₁ ⊔ Subgroup.center L' := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h15a, -, -⟩, -, -⟩ := hw₁'
  intro g hg
  have hg₁ : ∀ a₁ ∈ (U63TB.redSub hker hAle).range,
      MulAut.conj (g : L' ⧸ U63TB.twoSub ψ.ker hker) * a₁ = a₁ * MulAut.conj (g : L' ⧸ U63TB.twoSub
          ψ.ker hker) := by
    rintro _ ⟨a, rfl⟩
    have hkey : U63TB.conjP (U63TB.twoSub ψ.ker hker) g * ⟨a.1, hAle a.2⟩ = ⟨a.1, hAle a.2⟩ *
        U63TB.conjP (U63TB.twoSub ψ.ker hker) g :=
      Subtype.ext (hg a.1 a.2)
    have h1 := congrArg (U63TB.redHom (U63TB.twoSub ψ.ker hker)) hkey
    rw [map_mul, map_mul, U63TB.redHom_conjP] at h1
    exact h1
  obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup_of_normal_right.mp (h15a _ hg₁)
  obtain ⟨t, htT, htmk⟩ := twd_lift_Tsc hker hperf hAle w₁ hw₁ hs
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective c
  have hc'c : c' ∈ Subgroup.center L' := twd_center_of_mk hker hperf (by rw [hc']; exact hc)
  have hu : (t * c')⁻¹ * g ∈ U63TB.twoSub ψ.ker hker := by
    apply QuotientGroup.eq.mp
    rw [QuotientGroup.mk_mul, htmk, hc']
    exact hsc
  have hg' : g = t * (c' * ((t * c')⁻¹ * g)) := by group
  rw [hg']
  exact (twd_Tsc hker hAle w₁ ⊔ Subgroup.center L').mul_mem (Subgroup.mem_sup_left htT)
    (Subgroup.mem_sup_right ((Subgroup.center L').mul_mem hc'c
      (U63TB.twoSub_le_center hker hu)))

private theorem twd_c15b {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) :
    ∀ τ ∈ twd_T hker hAle w₁, ∀ t ∈ twd_Tsc hker hAle w₁, τ t = t :=
  fun τ hτ t ht => ((twd_mem_Tsc hker hAle w₁).mp ht).2 τ hτ

private theorem twd_c15c {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ t ∈ twd_Tsc hker hAle w₁, t ^ 3 = 1 → t ∈ ⨆ k, (twd_cor hker hAle w₁ k).range := by
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, h15c⟩, -, -⟩ := hw₁'
  intro t ht ht3
  have hts := ((twd_mem_Tsc hker hAle w₁).mp ht).1
  have h3' : (t : L' ⧸ U63TB.twoSub ψ.ker hker) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ht3, QuotientGroup.mk_one]
  have hmem' : (t : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ (⨆ k, (twd_cor hker hAle w₁ k).range).map
      (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)) := by
    rw [twd_map_join hker hAle w₁]
    exact h15c _ hts h3'
  obtain ⟨s, hsmem, hsmk⟩ := Subgroup.mem_map.mp hmem'
  have hs3 := twd_join_cube hker hAle w₁ hw₁ hsmem
  have hts' := twd_eq_of_mk_eq hker hsmk.symm ht3 hs3
  rw [hts']
  exact hsmem

private theorem twd_holds {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    (twd_w hker hperf hAle w₁ hw₁).Holds C M :=
  ⟨twd_T_comm hker hperf hAle w₁ hw₁, twd_c2 hker hAle w₁ hw₁, twd_c3 hker hAle w₁ hw₁,
    twd_c4 hker hAle w₁ hw₁, twd_c5 hker hAle w₁ hw₁, twd_c6 hker hAle w₁ hw₁,
    twd_c7 hker hAle w₁ hw₁, twd_c8 hker hAle w₁ hw₁, twd_c9 hker hperf hAle w₁ hw₁,
    twd_c10 hker hperf hAle w₁ hw₁, twd_c11 hker hperf hAle w₁ hw₁, twd_c12 hker hAle w₁ hw₁,
    twd_c13 hker hperf hAle w₁ hw₁, twd_c14 hker hAle w₁ hw₁,
    ⟨twd_c15a hker hperf hAle w₁ hw₁, twd_c15b hker hAle w₁, twd_c15c hker hAle w₁ hw₁⟩,
    (twd_clause16 hker hperf hAle w₁ hw₁ (twd_n (L' := L') hker hperf hAle w₁ hw₁) (twd_n_mk (L' :=
        L') hker hperf hAle w₁ hw₁)
    (fun k => (twd_w hker hperf hAle w₁ hw₁).hn k)).1,
    (twd_clause16 hker hperf hAle w₁ hw₁ (twd_n (L' := L') hker hperf hAle w₁ hw₁) (twd_n_mk (L' :=
        L') hker hperf hAle w₁ hw₁)
    (fun k => (twd_w hker hperf hAle w₁ hw₁).hn k)).2⟩

end CFSG.StandardType

end

