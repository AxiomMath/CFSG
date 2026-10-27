module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel
public import Mathlib.GroupTheory.SemidirectProduct

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Pointwise

universe u

variable {f : ℕ} {K : Type u} [Field K]

theorem unitary_root_norm_automorphisms_and_field_involution_cosets
    (h : UnitaryFieldData 2 f K) :
    Nat.card (heisenbergRoot h) = (2 ^ f) ^ 3 ∧
      (∀ x : heisenbergRoot h, x ∈ heisenbergRootCenter h ↔
        ∃ b ∈ h.fixedField,
          ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h 0 b) ∧
      heisenbergRootCenter h = Subgroup.center (heisenbergRoot h) ∧
      heisenbergRootCenter h = frattini (heisenbergRoot h) ∧
      Nat.card (heisenbergRootCenter h) = 2 ^ f ∧
      (∃ e : heisenbergRoot h ⧸ heisenbergRootCenter h ≃* Multiplicative K,
        ∀ x : heisenbergRoot h,
          e x = Multiplicative.ofAdd (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2)) ∧
      (∀ a b : K, heisenbergMatrix h a b ^ 2 = heisenbergMatrix h 0 (h.norm a)) ∧
      (∀ ψ : MulAut (heisenbergRoot h), (∀ x ∈ heisenbergRootCenter h, ψ x = x) →
        ∃ c : K, h.norm c = 1 ∧
          ((∀ x : heisenbergRoot h,
              ((ψ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
                c * ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2) ∨
            ∀ x : heisenbergRoot h,
              ((ψ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
                c * h.bar (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2))) ∧
      (∀ (θ : MulAut (heisenbergRoot h)) (μ : K), h.norm μ = 1 → μ ≠ 1 →
        (∀ x : heisenbergRoot h,
          ((θ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
            μ * ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2) →
        ∀ P : Subgroup (MulAut (heisenbergRoot h)), IsPGroup 2 P →
          (∀ ψ ∈ P, ∀ x ∈ heisenbergRootCenter h, ψ x = x) → (∀ ψ ∈ P, ψ * θ = θ * ψ) →
          ∀ ψ ∈ P, ∀ x : heisenbergRoot h,
            ((ψ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
              ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2) ∧
      (∀ (x : heisenbergRoot h) (a b : K),
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix h a b →
          ((heisenbergRootBar h x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            heisenbergMatrix h (h.bar a) (h.bar b)) ∧
      orderOf (heisenbergRootBar h) = 2 ∧
      let G := heisenbergRoot h ⋊[(Subgroup.zpowers (heisenbergRootBar h)).subtype]
        Subgroup.zpowers (heisenbergRootBar h)
      let t : G := SemidirectProduct.inr ⟨heisenbergRootBar h, Subgroup.mem_zpowers _⟩
      let E : Subgroup G := (heisenbergRootCenter h).map SemidirectProduct.inl
      let Γ : Set G := t • (E : Set G)
      let U : Subgroup (heisenbergRoot h) := (Subgroup.normalizer Γ).comap SemidirectProduct.inl
      let W : Subgroup G := U.map SemidirectProduct.inl ⊔ Subgroup.zpowers t
      let C : Set (Set G) := {S | ∃ x ∈ U, S = (t * SemidirectProduct.inl x) • (E : Set G)}
      (∀ x : heisenbergRoot h,
        x ∈ U ↔ ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 ∈ h.fixedField) ∧
      Nat.card U = (2 ^ f) ^ 2 ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ Monoid.exponent U = 4 ∧
      {x : heisenbergRoot h | ∃ y ∈ U, y ^ 2 = x} = heisenbergRootCenter h ∧
      (∀ x ∈ U, orderOf x = 2 ↔ x ∈ heisenbergRootCenter h ∧ x ≠ 1) ∧
      (∀ x ∈ U, heisenbergRootBar h x = x⁻¹) ∧
      Nat.card W = 2 * (2 ^ f) ^ 2 ∧ frattini W = E.subgroupOf W ∧ W.Normal ∧
      C.ncard = 2 ^ f ∧
      {S | ∃ v : heisenbergRoot h, S = MulAut.conj (SemidirectProduct.inl v : G) '' Γ} = C ∧
      (∀ S ∈ C, ∀ S' ∈ C, ∃ v : heisenbergRoot h,
        MulAut.conj (SemidirectProduct.inl v : G) '' S = S') ∧
      ∀ S ∈ C, ∃ v : heisenbergRoot h, MulAut.conj (SemidirectProduct.inl v : G) '' S ≠ S := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have hcard : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hfixed := card_fixed_fieldDataHermitianForm h
  set J := fieldDataHermitianForm h
  set φ := heisenbergRootEquiv h
  have hconj : ∀ x : K, J.conj x = h.bar x := fun _ => rfl
  have ha : ∀ x : heisenbergRoot h,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = h.bar (φ.symm x).1.1 := fun x => by
    rw [entry_one_two, CharTwo.neg_eq]
  obtain ⟨hV, hZ, hΦ, hE, hsurj, -⟩ := root_structure J φ (2 ^ f) hcard hfixed
  refine ⟨hV, mem_heisenbergRootCenter h, hZ, hΦ, hE, ?_, ?_, ?_, ?_, fun x a b hx =>
    coe_heisenbergRootBar h hx, ?_, ?_⟩
  · let e : Multiplicative K ≃* Multiplicative K := AddEquiv.toMultiplicative J.conj.toAddEquiv
    refine ⟨(QuotientGroup.quotientKerEquivOfSurjective (rootFst J φ) hsurj).trans e, fun x => ?_⟩
    rw [ha]
    rfl
  · intro a b
    simp only [pow_two, heisenbergMatrix_mul, CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq,
      UnitaryFieldData.norm, mul_comm (h.bar a)]
  · intro ψ hψ
    obtain ⟨c, hc, hσ⟩ := root_aut_fst_eq J φ (2 ^ f) hcard hfixed ψ hψ
    refine ⟨h.bar c, ?_, hσ.imp (fun hσ x => ?_) fun hσ x => ?_⟩
    · rw [UnitaryFieldData.norm, h.bar_bar, mul_comm]
      exact hc
    · rw [ha, ha, hσ, map_mul]
    · rw [ha, ha, hσ, map_mul, hconj, h.bar_bar]
  · intro θ μ hμ hμ1 hθ P hP hPE hPθ ψ hψ x
    have hθ' : ∀ x, (φ.symm (θ x)).1.1 = h.bar μ * (φ.symm x).1.1 := fun x => by
      have := congrArg h.bar (hθ x)
      rwa [ha, ha, map_mul, h.bar_bar, h.bar_bar] at this
    have key := root_two_subgroup_fst_eq J φ (2 ^ f) hcard hfixed θ (μ := h.bar μ)
      (by rw [hconj, h.bar_bar, mul_comm]; exact hμ)
      (fun h1 => hμ1 (by rw [← h.bar_bar μ, h1, map_one])) hθ' P hP hPE hPθ ψ hψ x
    rw [ha, ha, key]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact fieldInvolution_mul_self J φ, ?_⟩
    intro h1
    obtain ⟨ξ, hξ⟩ := exists_conj_ne J (2 ^ f) hcard hfixed
    obtain ⟨z, hz⟩ := exists_fst_eq J (2 ^ f) hcard hfixed ξ
    have h2 := congrArg (fun ψ : MulAut (heisenbergRoot h) => (φ.symm (ψ (φ z))).1.1) h1
    simp only [MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
    change (φ.symm (fieldInvolution J φ (φ z))).1.1 = z.1.1 at h2
    rw [symm_fieldInvolution_apply, MulEquiv.symm_apply_apply, fst_rootTau, hz] at h2
    exact hξ h2
  · intro G t E Γ U W C
    have hι : Function.Injective (SemidirectProduct.inl : heisenbergRoot h →* G) :=
      SemidirectProduct.inl_injective
    have ht : t ^ 2 = 1 := by
      rw [← map_pow]
      refine (congrArg SemidirectProduct.inr (Subtype.ext ?_)).trans (map_one _)
      rw [Subgroup.coe_pow, pow_two]
      exact fieldInvolution_mul_self J φ
    have htι : ∀ v, t * SemidirectProduct.inl v * t⁻¹ =
        SemidirectProduct.inl (fieldInvolution J φ v) := fun v => by
      rw [← map_inv]
      exact (SemidirectProduct.inl_aut _ v).symm
    have htop : (SemidirectProduct.inl : heisenbergRoot h →* G).range ⊔ Subgroup.zpowers t = ⊤ := by
      refine eq_top_iff.mpr fun g _ => ?_
      rw [← SemidirectProduct.inl_left_mul_inr_right g]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g.left, rfl⟩) (Subgroup.mem_sup_right ?_)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.right.2
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← map_zpow]
      exact congrArg _ (Subtype.ext (by rw [Subgroup.coe_zpow, hk]))
    refine ⟨fun x => ?_, card_involutionCosetNormalizer hι ht htι _ hcard hfixed,
      fun x hx y hy => involutionCosetNormalizer_mul_comm hι ht htι hx hy,
      exponent_involutionCosetNormalizer hι ht htι _ hcard hfixed,
      sq_involutionCosetNormalizer hι ht htι _ hcard hfixed,
      fun x _ => orderOf_eq_two_iff_mem_rootCenter φ x,
      fun x hx => fieldInvolution_eq_inv hι ht htι hx,
      card_involutionCosetHull hι ht htι _ hcard hfixed,
      frattini_involutionCosetHull hι ht htι _ hcard hfixed, ?_,
      ncard_involutionCosets hι ht htι _ hcard hfixed,
      conj_orbit_eq_involutionCosets hι ht htι _ hcard hfixed,
      involutionCosets_conj_transitive hι ht htι _ hcard hfixed,
      involutionCosets_not_fixed hι ht htι _ hcard hfixed⟩
    · refine (mem_involutionCosetNormalizer hι ht htι x).trans ?_
      rw [ha, UnitaryFieldData.mem_fixedField, h.bar_bar, hconj, eq_comm]
    · rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact le_normalizer_involutionCosetHull hι ht htι

theorem unitaryCoverRoot_norm_automorphisms [Finite K] [CharP K 2] (J : HermitianForm 3 K)
    (q : ℕ) (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (unitaryCoverRoot J hJ) = q ^ 3 ∧
      rootCenter J (unitaryCoverRootEquiv J hJ) = Subgroup.center (unitaryCoverRoot J hJ) ∧
      rootCenter J (unitaryCoverRootEquiv J hJ) = frattini (unitaryCoverRoot J hJ) ∧
      Nat.card (rootCenter J (unitaryCoverRootEquiv J hJ)) = q ∧
      (∀ r : unitaryCoverRoot J hJ, ((unitaryCoverRootEquiv J hJ).symm (r ^ 2)).1 =
        (0, ((unitaryCoverRootEquiv J hJ).symm r).1.1 *
          J.conj ((unitaryCoverRootEquiv J hJ).symm r).1.1)) ∧
      ∀ ψ : MulAut (unitaryCoverRoot J hJ),
        (∀ r ∈ rootCenter J (unitaryCoverRootEquiv J hJ), ψ r = r) →
        ∃ c : K, c * J.conj c = 1 ∧
          ((∀ r, ((unitaryCoverRootEquiv J hJ).symm (ψ r)).1.1 =
              c * ((unitaryCoverRootEquiv J hJ).symm r).1.1) ∨
            ∀ r, ((unitaryCoverRootEquiv J hJ).symm (ψ r)).1.1 =
              c * J.conj ((unitaryCoverRootEquiv J hJ).symm r).1.1) := by
  obtain ⟨h₁, h₂, h₃, h₄, -, h₅⟩ := root_structure J (unitaryCoverRootEquiv J hJ) q hcard hfixed
  exact ⟨h₁, h₂, h₃, h₄, h₅, root_aut_fst_eq J _ q hcard hfixed⟩

end CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
