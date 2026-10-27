module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem fam_rootChar_zpow {τ : Tag} {L : Type} [Field L] {ζ : Lˣ}
    (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) (ha : ∀ j, a j = ζ ^ v j)
    (γ : Fin τ.rank → ℤ) : rootChar a γ = ζ ^ (∑ j, γ j * v j) := by
  rw [rootChar, ← prod_zpow_eq_zpow_finset_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [ha j, ← zpow_mul, mul_comm]

theorem fam_eqvGen_iff {α : Type*} (R : α → α → Prop) (P : α → Prop)
    (hR : ∀ x y, R x y → (P x ↔ P y)) {x y : α} (h : Relation.EqvGen R x y) : P x ↔ P y := by
  induction h with
  | rel x y hxy => exact hR x y hxy
  | refl => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

open Matrix in
theorem fam_rel_iff {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (X : Set (Fin Tag.E6.rank → ℤ))
    (hdich : ∀ γ ∈ kernelRoots χ, γ ∈ X ∨ ∀ m ∈ X, iform γ m = 0)
    (x y : kernelRoots χ)
    (hxy : (x : Fin Tag.E6.rank → ℤ) ⬝ᵥ
      (Tag.symmetrizedCartan Tag.E6 *ᵥ (y : Fin Tag.E6.rank → ℤ)) ≠ 0) :
    (x : Fin Tag.E6.rank → ℤ) ∈ X ↔ (y : Fin Tag.E6.rank → ℤ) ∈ X := by
  have hi : iform (x : Fin Tag.E6.rank → ℤ) (y : Fin Tag.E6.rank → ℤ) ≠ 0 := by
    rwa [dotProduct_mulVec_eq_iform] at hxy
  have hi' : iform (y : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ℤ) ≠ 0 := by
    rw [iform_comm_E6]
    exact hi
  constructor
  · intro hx
    rcases hdich _ y.2 with hy | hy
    · exact hy
    · exact absurd (hy _ hx) hi'
  · intro hy
    rcases hdich _ x.2 with hx | hx
    · exact hx
    · exact absurd (hx _ hy) hi

theorem family_vectors
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p : ℕ}
    (S : LangSetup .E6 Lf p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    (Dg : Subgroup (ModGL .E6 Lf)) (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 Lf) = rootDiagUnit .E6 (a u))
    (hap : ∀ u j, a u j ^ p = 1) (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus) :
    ∃ v : ↥Dg → (Fin Tag.E6.rank → ℤ),
      (∀ u u' : ↥Dg, ∀ j, (p : ℤ) ∣ v (u * u') j - v u j - v u' j) ∧
      (∀ u : ↥Dg, (∀ j, (p : ℤ) ∣ v u j) → u = 1) ∧
      (∀ u γ, IsRoot .E6 γ → (rootChar (a u) γ = 1 ↔ (p : ℤ) ∣ ∑ j, γ j * v u j)) ∧
      (∀ u γ, IsRoot .E6 γ →
        (p : ℤ) ∣ (∑ j, (S.ρ γ) j * v u j) - (S.D.q : ℤ) * ∑ j, γ j * v u j) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcast : ((p : ℕ) : Lf) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff Lf 2 p).1 h)).symm
  haveI : NeZero ((p : ℕ) : Lf) := ⟨hcast⟩
  obtain ⟨ε, hε⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Lf p
  have hu0 : IsUnit ε := hε.isUnit hp.ne_zero
  obtain ⟨ζ, hζε⟩ : ∃ ζ : Lfˣ, (ζ : Lf) = ε := ⟨hu0.unit, hu0.unit_spec⟩
  have hζ : IsPrimitiveRoot ζ p := by
    refine IsPrimitiveRoot.of_map_of_injective (f := Units.coeHom Lf) ?_
      (fun x y h => Units.ext h)
    show IsPrimitiveRoot (ζ : Lf) p
    rw [hζε]
    exact hε
  have hex : ∀ u j, ∃ n : ℕ, ζ ^ n = a u j := by
    intro u j
    have hx : ((a u j : Lfˣ) : Lf) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap u j, Units.val_one]
    obtain ⟨i, -, hi⟩ := hε.eq_pow_of_pow_eq_one hx
    exact ⟨i, Units.ext (by rw [Units.val_pow_eq_pow_val, hζε]; exact hi)⟩
  choose k hk using hex
  obtain ⟨v, hav⟩ : ∃ v : ↥Dg → Fin Tag.E6.rank → ℤ, ∀ u j, a u j = ζ ^ v u j :=
    ⟨fun u j => ((k u j : ℕ) : ℤ), fun u j => by
      show a u j = ζ ^ ((k u j : ℕ) : ℤ)
      rw [zpow_natCast, hk u j]⟩
  have hmul : ∀ u u' : ↥Dg, a (u * u') = a u * a u' := by
    intro u u'
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [← ha (u * u'), Subgroup.coe_mul, ha u, ha u', CFSG.LieType.Chevalley.rootDiagUnit_mul]
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro u u' j
    have hmj : a (u * u') j = a u j * a u' j := congrFun (hmul u u') j
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub, zpow_sub, ← hav (u * u') j, ← hav u j,
      ← hav u' j, hmj, mul_comm (a u j) (a u' j)]
    group
  · intro u hu
    have hfun : a u = 1 :=
      funext fun j => (hav u j).trans ((hζ.zpow_eq_one_iff_dvd _).2 (hu j))
    apply Subtype.ext
    rw [ha u, hfun, CFSG.LieType.Chevalley.rootDiagUnit_one]
    rfl
  · intro u γ _
    exact rootChar_eq_one_iff_dvd_pairing hζ (a u) (v u) (hav u) γ
  · intro u γ hγ
    have h1 := S.frob.rootChar_eq (a u) (hT u) γ hγ
    rw [fam_rootChar_zpow (a u) (v u) (hav u) (S.ρ γ),
      fam_rootChar_zpow (a u) (v u) (hav u) γ, ← zpow_natCast, ← zpow_mul] at h1
    have h2 : ζ ^ ((∑ j, (S.ρ γ) j * v u j) - (∑ j, γ j * v u j) * (S.D.q : ℤ)) = 1 := by
      rw [zpow_sub, h1]
      simp
    have e : (∑ j, γ j * v u j) * (S.D.q : ℤ) = (S.D.q : ℤ) * ∑ j, γ j * v u j :=
      mul_comm _ _
    rw [e] at h2
    exact (hζ.zpow_eq_one_iff_dvd _).1 h2

theorem componentRoots_subset_or {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M) (X : Set (Fin Tag.E6.rank → ℤ))
    (hdich : ∀ γ ∈ kernelRoots χ, γ ∈ X ∨ ∀ m ∈ X, iform γ m = 0)
    (i : KernelComponent χ) :
    componentRoots χ i ⊆ X ∨ ∀ γ ∈ componentRoots χ i, ∀ m ∈ X, iform γ m = 0 := by
  by_cases hex : ∃ γ₀ ∈ componentRoots χ i, γ₀ ∈ X
  · left
    obtain ⟨γ₀, ⟨h₀, hi₀⟩, hγ₀X⟩ := hex
    intro α hα
    obtain ⟨h, hi⟩ := hα
    have hq : (⟦⟨α, h⟩⟧ : KernelComponent χ) = ⟦⟨γ₀, h₀⟩⟧ := hi.trans hi₀.symm
    exact (fam_eqvGen_iff _ (fun x : kernelRoots χ => (x : Fin Tag.E6.rank → ℤ) ∈ X)
      (fun x y hxy => fam_rel_iff X hdich x y hxy) (Quotient.exact hq)).2 hγ₀X
  · right
    intro γ hγ m hm
    have hγ' := hγ
    obtain ⟨hk, -⟩ := hγ'
    rcases hdich γ hk with hγX | hγX
    · exact (hex ⟨γ, hγ, hγX⟩).elim
    · exact hγX m hm

end CFSG.StandardType.TableCRes

end
