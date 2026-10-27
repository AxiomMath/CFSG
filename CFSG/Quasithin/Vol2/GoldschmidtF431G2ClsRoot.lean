module

public import CFSG.LieType.Chevalley.WeylRootTransport

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

@[expose] def iA : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def iR : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem isRoot_of_reflect {i : Fin Tag.G2.rank} {γ δ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (h : reflect .G2 i γ = δ) : IsRoot .G2 δ :=
  h ▸ IsRoot.reflect i hγ

theorem isRoot_a : IsRoot .G2 ![1, 0] := by
  have h : (![1, 0] : Fin 2 → ℤ) = Pi.single iA 1 := List.ofFn_injective (by decide +kernel)
  rw [h]
  exact IsRoot.basis iA

theorem isRoot_r : IsRoot .G2 ![0, 1] := by
  have h : (![0, 1] : Fin 2 → ℤ) = Pi.single iR 1 := List.ofFn_injective (by decide +kernel)
  rw [h]
  exact IsRoot.basis iR

theorem reflect_a_r : reflect .G2 iA ![0, 1] = ![1, 1] := List.ofFn_injective (by decide +kernel)

theorem reflect_r_u : reflect .G2 iR ![1, 1] = ![1, 2] := List.ofFn_injective (by decide +kernel)

theorem reflect_r_a : reflect .G2 iR ![1, 0] = ![1, 3] := List.ofFn_injective (by decide +kernel)

theorem reflect_a_b : reflect .G2 iA ![1, 3] = ![2, 3] := List.ofFn_injective (by decide +kernel)

theorem reflect_a_a : reflect .G2 iA ![1, 0] = ![-1, 0] := List.ofFn_injective (by decide +kernel)

theorem reflect_r_r : reflect .G2 iR ![0, 1] = ![0, -1] := List.ofFn_injective (by decide +kernel)

theorem reflect_r_na : reflect .G2 iR ![-1, 0] = ![-1, -3] :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_a_nb : reflect .G2 iA ![-1, -3] = ![-2, -3] :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_a_nr : reflect .G2 iA ![0, -1] = ![-1, -1] :=
  List.ofFn_injective (by decide +kernel)

theorem reflect_r_nu : reflect .G2 iR ![-1, -1] = ![-1, -2] :=
  List.ofFn_injective (by decide +kernel)

theorem isRoot_u : IsRoot .G2 ![1, 1] := isRoot_of_reflect isRoot_r reflect_a_r

theorem isRoot_v : IsRoot .G2 ![1, 2] := isRoot_of_reflect isRoot_u reflect_r_u

theorem isRoot_b : IsRoot .G2 ![1, 3] := isRoot_of_reflect isRoot_a reflect_r_a

theorem isRoot_c : IsRoot .G2 ![2, 3] := isRoot_of_reflect isRoot_b reflect_a_b

theorem isRoot_na : IsRoot .G2 ![-1, 0] := isRoot_of_reflect isRoot_a reflect_a_a

theorem isRoot_nr : IsRoot .G2 ![0, -1] := isRoot_of_reflect isRoot_r reflect_r_r

theorem isRoot_nb : IsRoot .G2 ![-1, -3] := isRoot_of_reflect isRoot_na reflect_r_na

theorem isRoot_nu : IsRoot .G2 ![-1, -1] := isRoot_of_reflect isRoot_nr reflect_a_nr

@[expose] def IsLong (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  γ = ![1, 0] ∨ γ = ![1, 3] ∨ γ = ![2, 3] ∨ γ = ![-1, 0] ∨ γ = ![-1, -3] ∨ γ = ![-2, -3]

@[expose] def IsShort (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  γ = ![0, 1] ∨ γ = ![1, 1] ∨ γ = ![1, 2] ∨ γ = ![0, -1] ∨ γ = ![-1, -1] ∨ γ = ![-1, -2]

theorem eq_one_of_mul_self_eq_one {K : Type} [Field K] [CharP K 2] {ε : K} (h : ε * ε = 1) :
    ε = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (ε - 1) * (ε - 1) = 0 := by linear_combination h + (1 - ε) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

variable {K : Type} [Field K]

theorem weylElt_conj_pinnedX [CharP K 2] (i : Fin Tag.G2.rank) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (s : K) :
    weylElt Tag.G2 K i 1 * pinnedX Tag.G2 K γ s * (weylElt Tag.G2 K i 1)⁻¹ =
      pinnedX Tag.G2 K (reflect Tag.G2 i γ) s := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hγ
  rw [h s, eq_one_of_mul_self_eq_one hε, one_mul]

theorem torusElt_conj_pinnedX_c (t : Kˣ) (s : K) :
    torusElt Tag.G2 K iA t * pinnedX Tag.G2 K ![2, 3] s * (torusElt Tag.G2 K iA t)⁻¹ =
      pinnedX Tag.G2 K ![2, 3] ((t : K) * s) := by
  rw [root_torus_conjugation iA isRoot_c t s,
    show (∑ j, Tag.G2.cartan iA j * (![2, 3] : Fin Tag.G2.rank → ℤ) j) = 1 by decide, zpow_one]

theorem torusElt_conj_pinnedX_v (t : Kˣ) (s : K) :
    torusElt Tag.G2 K iR t * pinnedX Tag.G2 K ![1, 2] s * (torusElt Tag.G2 K iR t)⁻¹ =
      pinnedX Tag.G2 K ![1, 2] ((t : K) * s) := by
  rw [root_torus_conjugation iR isRoot_v t s,
    show (∑ j, Tag.G2.cartan iR j * (![1, 2] : Fin Tag.G2.rank → ℤ) j) = 1 by decide, zpow_one]

variable (K) in
@[expose] def rootC (γ : Fin Tag.G2.rank → ℤ) (s : K) : ↥(adjointGroup Tag.G2 K) :=
  ⟨pinnedX Tag.G2 K γ s, pinnedX_mem_adjointGroup γ s⟩

@[expose] def zC (K : Type) [Field K] : ↥(adjointGroup Tag.G2 K) := rootC K ![2, 3] 1

@[expose] def tC (K : Type) [Field K] : ↥(adjointGroup Tag.G2 K) := rootC K ![1, 2] 1

theorem isConj_rootC_reflect [CharP K 2] (i : Fin Tag.G2.rank) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (s : K) : IsConj (rootC K γ s) (rootC K (reflect Tag.G2 i γ) s) :=
  isConj_iff.mpr ⟨⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩,
    Subtype.ext (weylElt_conj_pinnedX i hγ s)⟩

theorem isConj_rootC_c {s : K} (hs : s ≠ 0) : IsConj (rootC K ![2, 3] 1) (rootC K ![2, 3] s) :=
  isConj_iff.mpr ⟨⟨torusElt Tag.G2 K iA (Units.mk0 s hs),
    torusElt_mem_adjointGroup iA (Units.mk0 s hs)⟩,
    Subtype.ext (by
      have := torusElt_conj_pinnedX_c (K := K) (Units.mk0 s hs) 1
      rwa [Units.val_mk0, mul_one] at this)⟩

theorem isConj_rootC_v {s : K} (hs : s ≠ 0) : IsConj (rootC K ![1, 2] 1) (rootC K ![1, 2] s) :=
  isConj_iff.mpr ⟨⟨torusElt Tag.G2 K iR (Units.mk0 s hs),
    torusElt_mem_adjointGroup iR (Units.mk0 s hs)⟩,
    Subtype.ext (by
      have := torusElt_conj_pinnedX_v (K := K) (Units.mk0 s hs) 1
      rwa [Units.val_mk0, mul_one] at this)⟩

section Chains

variable [CharP K 2] (s : K)

theorem isConj_b_c : IsConj (rootC K ![1, 3] s) (rootC K ![2, 3] s) := by
  have := isConj_rootC_reflect iA isRoot_b s
  rwa [reflect_a_b] at this

theorem isConj_a_b : IsConj (rootC K ![1, 0] s) (rootC K ![1, 3] s) := by
  have := isConj_rootC_reflect iR isRoot_a s
  rwa [reflect_r_a] at this

theorem isConj_a_na : IsConj (rootC K ![1, 0] s) (rootC K ![-1, 0] s) := by
  have := isConj_rootC_reflect iA isRoot_a s
  rwa [reflect_a_a] at this

theorem isConj_na_nb : IsConj (rootC K ![-1, 0] s) (rootC K ![-1, -3] s) := by
  have := isConj_rootC_reflect iR isRoot_na s
  rwa [reflect_r_na] at this

theorem isConj_nb_nc : IsConj (rootC K ![-1, -3] s) (rootC K ![-2, -3] s) := by
  have := isConj_rootC_reflect iA isRoot_nb s
  rwa [reflect_a_nb] at this

theorem isConj_r_u : IsConj (rootC K ![0, 1] s) (rootC K ![1, 1] s) := by
  have := isConj_rootC_reflect iA isRoot_r s
  rwa [reflect_a_r] at this

theorem isConj_u_v : IsConj (rootC K ![1, 1] s) (rootC K ![1, 2] s) := by
  have := isConj_rootC_reflect iR isRoot_u s
  rwa [reflect_r_u] at this

theorem isConj_r_nr : IsConj (rootC K ![0, 1] s) (rootC K ![0, -1] s) := by
  have := isConj_rootC_reflect iR isRoot_r s
  rwa [reflect_r_r] at this

theorem isConj_nr_nu : IsConj (rootC K ![0, -1] s) (rootC K ![-1, -1] s) := by
  have := isConj_rootC_reflect iA isRoot_nr s
  rwa [reflect_a_nr] at this

theorem isConj_nu_nv : IsConj (rootC K ![-1, -1] s) (rootC K ![-1, -2] s) := by
  have := isConj_rootC_reflect iR isRoot_nu s
  rwa [reflect_r_nu] at this

theorem isConj_long_c {γ : Fin Tag.G2.rank → ℤ} (hγ : IsLong γ) :
    IsConj (rootC K γ s) (rootC K ![2, 3] s) := by
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (isConj_a_b s).trans (isConj_b_c s)
  · exact isConj_b_c s
  · exact IsConj.refl _
  · exact ((isConj_a_na s).symm.trans (isConj_a_b s)).trans (isConj_b_c s)
  · exact (((isConj_na_nb s).symm.trans (isConj_a_na s).symm).trans (isConj_a_b s)).trans
      (isConj_b_c s)
  · exact ((((isConj_nb_nc s).symm.trans (isConj_na_nb s).symm).trans
      (isConj_a_na s).symm).trans (isConj_a_b s)).trans (isConj_b_c s)

theorem isConj_short_v {γ : Fin Tag.G2.rank → ℤ} (hγ : IsShort γ) :
    IsConj (rootC K γ s) (rootC K ![1, 2] s) := by
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (isConj_r_u s).trans (isConj_u_v s)
  · exact isConj_u_v s
  · exact IsConj.refl _
  · exact ((isConj_r_nr s).symm.trans (isConj_r_u s)).trans (isConj_u_v s)
  · exact (((isConj_nr_nu s).symm.trans (isConj_r_nr s).symm).trans (isConj_r_u s)).trans
      (isConj_u_v s)
  · exact ((((isConj_nu_nv s).symm.trans (isConj_nr_nu s).symm).trans
      (isConj_r_nr s).symm).trans (isConj_r_u s)).trans (isConj_u_v s)

end Chains

theorem isConj_z_of_long [CharP K 2] {γ : Fin Tag.G2.rank → ℤ} (hγ : IsLong γ) {s : K}
    (hs : s ≠ 0) : IsConj (zC K) (rootC K γ s) :=
  (isConj_rootC_c hs).trans (isConj_long_c s hγ).symm

theorem isConj_t_of_short [CharP K 2] {γ : Fin Tag.G2.rank → ℤ} (hγ : IsShort γ) {s : K}
    (hs : s ≠ 0) : IsConj (tC K) (rootC K γ s) :=
  (isConj_rootC_v hs).trans (isConj_short_v s hγ).symm

end CFSG.Quasithin.H13.F431.G2.Cls
