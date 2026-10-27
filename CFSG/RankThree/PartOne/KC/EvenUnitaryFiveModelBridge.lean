module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCyclicField
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LinearGroups
  CFSG.ComponentClassification.OutcomeLocal

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Transport

variable {r ε : ℕ} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem transportGL_mul (hR : IsHypTransport h R) (g₁ g₂ : GL (HypIndex r ε) K) :
    transportGL hR (g₁ * g₂) = transportGL hR g₁ * transportGL hR g₂ :=
  Units.ext (transport_mul_mul hR _ _).symm

theorem transportGL_one (hR : IsHypTransport h R) :
    transportGL hR (1 : GL (HypIndex r ε) K) = 1 :=
  Units.ext (transport_one hR)

theorem transportGL_transportGLInv (hR : IsHypTransport h R) (g : GL (Fin (2 * r + ε)) K) :
    transportGL hR (transportGLInv hR g) = g :=
  Units.ext (transport_transportInv hR _)

@[expose] noncomputable def transportGLHom (hR : IsHypTransport h R) :
    GL (HypIndex r ε) K →* GL (Fin (2 * r + ε)) K where
  toFun := transportGL hR
  map_one' := transportGL_one h hR
  map_mul' := transportGL_mul h hR

theorem transportGLInv_mem_linearSimilitudes (hR : IsHypTransport h R)
    {x : GL (Fin (2 * r + ε)) K}
    (hx : x ∈ primeFormUnitary h ((1 : GL (Fin (2 * r + ε)) K) : Matrix _ _ K)) :
    transportGLInv hR x ∈ linearSimilitudes h r ε := by
  refine mem_linearSimilitudes.mpr ⟨1, one_ne_zero, map_one _, ?_⟩
  rw [one_smul]
  refine (gramForm_isometry_iff h (hypGram r ε K) _).mp (fun u v => ?_)
  have hRA : R * ((transportGLInv hR x : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        ((x : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R := by
    rw [coe_transportGLInv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R, mul_transportInv hR, Matrix.one_mul]
  have hx' : ∀ u v : Fin (2 * r + ε) → K,
      gramForm h (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) (x *ᵥ u) (x *ᵥ v) =
        gramForm h (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) u v := by
    refine (gramForm_isometry_iff h 1 _).mpr ?_
    have := mem_primeFormUnitary.mp hx
    simpa using this
  have h1 : gramForm h (hypGram r ε K) (((transportGLInv hR x : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u)
      (((transportGLInv hR x : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) =
      stdHermForm h (2 * r + ε) (R *ᵥ (((transportGLInv hR x : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u))
        (R *ᵥ (((transportGLInv hR x : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)) :=
    (stdHermForm_transport hR _ _).symm
  have h3 := stdHermForm_transport hR u v
  rw [stdHermForm_eq_gramForm] at h3
  rw [h1, mulVec_mulVec, mulVec_mulVec, hRA, ← mulVec_mulVec, ← mulVec_mulVec,
    stdHermForm_eq_gramForm, hx']
  exact h3

end Transport

section Iso

variable {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K}

@[expose] noncomputable def hypToPrimeForm (hR : IsHypTransport h R) :
    hypPSU h 2 1 ≃* primeFormP h (idGram K 5) :=
  (hypProjTransport h hR).trans (primeFormOneEquiv h 5).symm

theorem transportGL_mem_gramSU (hR : IsHypTransport h R) (g : hypSU h 2 1) :
    transportGL hR (g : GL (HypIndex 2 1) K) ∈ gramSU h (idGram K 5) := by
  have := transportGL_mem hR g
  rw [unitarySU_eq_gramSU h] at this
  exact this

theorem hypToPrimeForm_hypProj (hR : IsHypTransport h R) (g : hypSU h 2 1) :
    hypToPrimeForm h hR (hypProj h 2 1 g) =
      ((⟨transportGL hR (g : GL (HypIndex 2 1) K), transportGL_mem_gramSU h hR g⟩ :
        gramSU h (idGram K 5)) : primeFormP h (idGram K 5)) := by
  rw [hypToPrimeForm, MulEquiv.trans_apply, hypProjTransport_hypProj, MulEquiv.symm_apply_eq]
  exact (primeFormOneEquiv_mk h ⟨transportGL hR (g : GL (HypIndex 2 1) K),
    transportGL_mem_gramSU h hR g⟩ (hypTransport h hR g) rfl).symm

@[expose] noncomputable def toSimilitude (hR : IsHypTransport h R)
    (x : primeFormUnitary h (idGram K 5)) : linearSimilitudes h 2 1 :=
  ⟨transportGLInv hR (x : GL (Fin 5) K), transportGLInv_mem_linearSimilitudes h hR x.2⟩

theorem conj_hypToPrimeForm (hR : IsHypTransport h R) (x : primeFormUnitary h (idGram K 5))
    (y : hypPSU h 2 1) :
    primeFormConjHom h (idGram K 5) x (hypToPrimeForm h hR y) =
      hypToPrimeForm h hR
        (linearSimAut h (by norm_num : 1 ≤ 2) le_rfl (toSimilitude h hR x) y) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 y
  rw [linearSimAut_apply, hypToPrimeForm_hypProj, hypToPrimeForm_hypProj, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  have hA : transportGL hR (transportGLInv hR (x : GL (Fin 5) K)) = x :=
    transportGL_transportGLInv h hR _
  have e1 : transportGLHom h hR (((toSimilitude h hR x : linearSimilitudes h 2 1) :
      GL (HypIndex 2 1) K) * (g : GL (HypIndex 2 1) K) *
        ((toSimilitude h hR x : linearSimilitudes h 2 1) : GL (HypIndex 2 1) K)⁻¹) =
      (x : GL (Fin 5) K) * transportGL hR (g : GL (HypIndex 2 1) K) * (x : GL (Fin 5) K)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change transportGL hR (transportGLInv hR (x : GL (Fin 5) K)) * _ *
      (transportGL hR (transportGLInv hR (x : GL (Fin 5) K)))⁻¹ = _
    rw [hA]
    rfl
  exact e1.symm

theorem mulAut_congr_conj_eq (hR : IsHypTransport h R) (x : primeFormUnitary h (idGram K 5)) :
    MulAut.congr (hypToPrimeForm h hR).symm (primeFormConjHom h (idGram K 5) x) =
      linearSimAut h (by norm_num : 1 ≤ 2) le_rfl (toSimilitude h hR x) := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.congr_apply, MulEquiv.symm_symm]
  simp only [MulEquiv.trans_apply]
  rw [MulEquiv.symm_apply_eq]
  exact conj_hypToPrimeForm h hR x y

end Iso

section Odd

theorem map_centralizer_subgroup_mulEquiv {M M' : Type*} [Group M] [Group M'] (φ : M ≃* M')
    (S : Subgroup M) :
    (Subgroup.centralizer (S : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup M') : Set M') := by
  ext y
  rw [Subgroup.mem_map_equiv]
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hc d hd
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hd
    have h2 := congrArg φ (hc s hs)
    simpa using h2
  · intro hc s hs
    have := hc (φ s) (Subgroup.mem_map_of_mem _ hs)
    apply φ.injective
    simpa using this

theorem odd_card_centralizer_of_nonabelian_lift (h5 : 5 ∣ 2 ^ f + 1)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAD : A ≤ primeFormD h (idGram K 5))
    (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hna : ¬ ∀ x y : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
        x * y = y * x) :
    Odd (Nat.card (Subgroup.centralizer (A : Set (MulAut (primeFormP h (idGram K 5)))))) := by
  classical
  have hfin := h.finite
  have hq : ¬(2 * 2 + 1 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have ha : 1 ≤ 2 := by norm_num
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  set Ξ := MulAut.congr (hypToPrimeForm h hR).symm with hΞ
  set D' : Subgroup (MulAut (hypPSU h 2 1)) := A.map Ξ.toMonoidHom with hD'
  have hΞρ : ∀ x, Ξ (primeFormConjHom h (idGram K 5) x) =
      linearSimAut h ha le_rfl (toSimilitude h hR x) := fun x => mulAut_congr_conj_eq h hR x
  have hDI : D' ≤ linearSimAutGroup h ha le_rfl := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨x, rfl⟩ := hAD hα
    exact ⟨toSimilitude h hR x, (hΞρ x).symm⟩
  have hDab : ∀ a ∈ D', ∀ b ∈ D', a * b = b * a := by
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    have h1 : (⟨α, hα⟩ : A) * ⟨β, hβ⟩ = ⟨β, hβ⟩ * ⟨α, hα⟩ :=
      hAel.toIsMulCommutative.is_comm.comm _ _
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    change Ξ α * Ξ β = Ξ β * Ξ α
    rw [← map_mul, ← map_mul, h2]
  have hDp : ∀ a ∈ D', a ^ 5 = 1 := by
    rintro _ ⟨α, hα, rfl⟩
    change (Ξ α) ^ 5 = 1
    have := hAel
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian α hα, map_one]
  have hcard : Nat.card D' = 5 ^ 2 := by
    rw [hD', Subgroup.card_map_of_injective Ξ.injective, hAcard]
  have hna' : ¬ ∀ X ∈ D'.comap (linearSimAut h ha le_rfl),
      ∀ Y ∈ D'.comap (linearSimAut h ha le_rfl), X * Y = Y * X := by
    intro hcomm
    apply hna
    intro x y hx hy
    have hX : toSimilitude h hR x ∈ D'.comap (linearSimAut h ha le_rfl) := by
      rw [Subgroup.mem_comap, ← hΞρ]
      exact ⟨_, hx, rfl⟩
    have hY : toSimilitude h hR y ∈ D'.comap (linearSimAut h ha le_rfl) := by
      rw [Subgroup.mem_comap, ← hΞρ]
      exact ⟨_, hy, rfl⟩
    have h1 := hcomm _ hX _ hY
    have h2 := congrArg (fun X : linearSimilitudes h 2 1 =>
      transportGL hR (X : GL (HypIndex 2 1) K)) h1
    simp only [toSimilitude, Subgroup.coe_mul] at h2
    rw [transportGL_mul h hR, transportGL_mul h hR, transportGL_transportGLInv h hR,
      transportGL_transportGLInv h hR] at h2
    exact Subtype.ext h2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hodd, -⟩ :=
    unitary_projective_nonabelian_plane_centralizer_cyclic_field_quotient h Nat.prime_five
      (by norm_num : 5 = 2 * 2 + 1) ha h5 hq D' hDI hDab hDp hcard hna'
  have hc : Nat.card (Subgroup.centralizer (A : Set (MulAut (primeFormP h (idGram K 5))))) =
      Nat.card (Subgroup.centralizer (D' : Set (MulAut (hypPSU h 2 1)))) := by
    rw [← map_centralizer_subgroup_mulEquiv Ξ A]
    exact (Subgroup.card_map_of_injective Ξ.injective).symm
  rw [hc]
  exact hodd

end Odd

end CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge
