module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {J : HermitianForm 3 K}

section Product

variable {C : Subgroup J.specialSubgroup} [C.Normal]

theorem sublineL_subtype_commute [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (x : sublineL J C hJ) (y : torusL J C hJ) :
    Commute ((sublineL J C hJ).subtype x) ((torusL J C hJ).subtype y) := by
  show (x : J.specialSubgroup ⧸ C) * y = y * x
  exact sublineL_commute_torusL (C := C) hJ (x : J.specialSubgroup ⧸ C) x.2
    (y : J.specialSubgroup ⧸ C) y.2

@[expose] def sublineTorusMul [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    sublineL J C hJ × torusL J C hJ →* J.specialSubgroup ⧸ C :=
  MonoidHom.noncommCoprod (sublineL J C hJ).subtype (torusL J C hJ).subtype
    (sublineL_subtype_commute hJ)

theorem sublineTorusMul_injective [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : Function.Injective (sublineTorusMul (C := C) hJ) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨Subtype.val_injective, Subtype.val_injective, disjoint_iff.mpr (by
      rw [Subgroup.range_subtype, Subgroup.range_subtype]
      exact sublineL_inf_torusL hJ hC)⟩

theorem range_sublineTorusMul [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (sublineTorusMul (C := C) hJ).range = sublineL J C hJ ⊔ torusL J C hJ := by
  have h := MonoidHom.noncommCoprod_range (sublineL J C hJ).subtype (torusL J C hJ).subtype
    (sublineL_subtype_commute hJ)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at h
  exact h

@[expose] def sublineTorusProdEquiv [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    sublineL J C hJ × torusL J C hJ ≃* (sublineL J C hJ ⊔ torusL J C hJ : Subgroup _) :=
  (MonoidHom.ofInjective (sublineTorusMul_injective hJ hC)).trans
    (MulEquiv.subgroupCongr (range_sublineTorusMul hJ))

theorem coe_sublineTorusProdEquiv [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (p : sublineL J C hJ × torusL J C hJ) :
    (sublineTorusProdEquiv hJ hC p : J.specialSubgroup ⧸ C) = (p.1 : J.specialSubgroup ⧸ C) * p.2 :=
  rfl

end Product

theorem unitary_central_cover_subline_torus_centralizer [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (C : Subgroup J.specialSubgroup) [C.Normal] (hC : C ≤ scalarCenter J) :
    let q := 2 ^ f
    let L := J.specialSubgroup ⧸ C
    let π : J.specialSubgroup →* L := QuotientGroup.mk' C
    let J₀ := sublineL J C hJ
    let Q₀ := upperRootL J C hJ
    let A₀ := torusL J C hJ
    (∀ c : K, J.conj c = c ^ q) ∧
    (∀ g : J.specialSubgroup, g ∈ scalarCenter J ↔ ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c ∧
        c ^ (q + 1) = 1 ∧ c ^ 3 = 1) ∧
    (∀ c : Kˣ, c ∈ normOne J ↔ (c : K) ^ (q + 1) = 1) ∧
    Nat.card (unitaryCoverFixedField J) = q ∧
    Function.Injective (π.comp (sublineHom J hJ)) ∧
    Nonempty (J₀ ≃* SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) ∧
    J₀ = Q₀ ⊔ lowerRootL J C hJ ∧
    IsCyclic A₀ ∧ Nat.card A₀ = (q + 1) / Nat.card C ∧
    ⁅J₀, A₀⁆ = ⊥ ∧ J₀ ⊓ A₀ = ⊥ ∧
    pairStabilizerL J C hJ hC ⊓ Subgroup.centralizer (Q₀ : Set L) = A₀ ∧
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ q + 1 ∧
      ∃ A : Subgroup L, A ≤ A₀ ∧ IsCyclic A ∧ IsPGroup p A ∧ A ≠ ⊥ ∧
        ∃ c : normOne J, ((c : Kˣ) : K) ^ 3 ≠ 1 ∧ π (torusHom J hJ c) ∈ A) ∧
    (∀ A : Subgroup L, A ≤ A₀ →
      (∃ c : normOne J, ((c : Kˣ) : K) ^ 3 ≠ 1 ∧ π (torusHom J hJ c) ∈ A) →
        Subgroup.centralizer (A : Set L) = J₀ ⊔ A₀ ∧
          (∃ e : J₀ × A₀ ≃* Subgroup.centralizer (A : Set L), ∀ p, (e p : L) = p.1 * p.2) ∧
          ∀ x ∈ Subgroup.centralizer (A : Set L), x ^ 2 = 1 → x ∈ J₀) ∧
    Nat.card (sublineOrbit J C hJ hC) = q + 1 ∧
    Nat.card Q₀ = q := by
  intro q L π J₀ Q₀ A₀
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hq4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hM : Nat.card (normOne J) = q + 1 := card_normOne Nat.prime_two hq hcard hfixed
  have hk0 : Nat.card (unitaryCoverFixedField J) = q := card_unitaryCoverFixedField hfixed
  have hqeven : Even q := (Nat.even_pow' (by omega)).mpr even_two
  have hodd : Odd (Nat.card (normOne J)) := by
    rw [hM]
    exact hqeven.add_one
  have hA₀card : Nat.card A₀ * Nat.card C = q + 1 := by
    rw [← hM]
    exact card_torusL_mul_card hJ hC
  have hCpos : 0 < Nat.card C := Nat.card_pos
  refine ⟨huppert_II_10_4_conj_eq_frobenius J q hcard hfixed,
    mem_scalarCenter_iff_pow hcard hfixed, mem_normOne_iff_pow hcard hfixed, hk0,
    sublineL_injective hJ hC, ⟨(sublineEquiv hJ hC).symm⟩, sublineL_eq_sup hJ,
    isCyclic_of_surjective ((QuotientGroup.mk' C).comp (torusHom J hJ)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _), ?_,
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (sublineL_le_centralizer_torusL hJ),
    sublineL_inf_torusL hJ hC, pairStabilizerL_inf_centralizer hJ hC, ?_, ?_, ?_, ?_⟩
  · rw [← hA₀card, Nat.mul_div_cancel _ hCpos]
  · obtain ⟨p, hp, hpodd, hpM, hA⟩ := exists_pSubgroup_torusL hJ hC hodd (by omega)
    exact ⟨p, hp, hpodd, hM ▸ hpM, hA⟩
  · rintro A hA ⟨c, hc3, hcA⟩
    have hcen := centralizer_eq_sublineL_sup_torusL hJ hC hA hc3 hcA
    refine ⟨hcen, ⟨(sublineTorusProdEquiv hJ hC).trans (MulEquiv.subgroupCongr hcen.symm),
      fun p => rfl⟩, fun x hx hx2 => ?_⟩
    exact mem_sublineL_of_sq_eq_one hJ hC hodd hc3
      (Subgroup.mem_centralizer_iff.mp hx _ hcA).symm hx2
  · rw [card_sublineOrbit hJ hC, hk0]
  · rw [card_upperRootL hJ hC, hk0]

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
