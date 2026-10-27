module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.ConjTransport

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11
open scoped Matrix

section Matrices

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Algebra (ZMod 2) K]

omit [Algebra (ZMod 2) K] in
lemma transvection_mulVec_eq (k l : ι) (t : K) (u : ι → K) :
    Matrix.transvection k l t *ᵥ u = u + (Pi.single k (t * u l) : ι → K) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

lemma comm_single (f : Module.End (ZMod 2) (ι → K))
    (hf : ∀ M : Matrix ι ι K, M.det = 1 → ∀ v, f (M *ᵥ v) = M *ᵥ f v)
    {k l : ι} (hkl : k ≠ l) (t : K) (u : ι → K) :
    f (Pi.single k (t * u l) : ι → K) = (Pi.single k (t * f u l) : ι → K) := by
  have h := hf (Matrix.transvection k l t) (Matrix.det_transvection_of_ne k l hkl t) u
  rw [transvection_mulVec_eq, transvection_mulVec_eq, map_add] at h
  exact add_left_cancel h

lemma commutant_scalar [Nontrivial ι] (f : Module.End (ZMod 2) (ι → K))
    (hf : ∀ M : Matrix ι ι K, M.det = 1 → ∀ v, f (M *ᵥ v) = M *ᵥ f v) :
    ∃ a : K, ∀ v, f v = a • v := by
  set b : ι → K := fun k => f (Pi.single k 1 : ι → K) k with hbdef
  have claim1 : ∀ k l : ι, k ≠ l → ∀ t : K,
      f (Pi.single k t : ι → K) = (Pi.single k (t * b l) : ι → K) := by
    intro k l hkl t
    have h := comm_single f hf hkl t (Pi.single l 1 : ι → K)
    simpa [hbdef] using h
  have claim2 : ∀ k l : ι, k ≠ l → b k = b l := by
    intro k l hkl
    have h := congrFun (claim1 k l hkl 1) k
    simpa [hbdef] using h
  have hconst : ∀ k l : ι, b k = b l := by
    intro k l
    by_cases h : k = l
    · rw [h]
    · exact claim2 k l h
  set a : K := b (Classical.arbitrary ι) with hadef
  have ha : ∀ k, b k = a := fun k => hconst k _
  have hsingle : ∀ k (t : K), f (Pi.single k t : ι → K) = (Pi.single k (t * a) : ι → K) := by
    intro k t
    obtain ⟨l, hl⟩ := exists_ne k
    rw [claim1 k l hl.symm t, ha l]
  refine ⟨a, fun v => ?_⟩
  calc f v = f (∑ k, (Pi.single k (v k) : ι → K)) := by rw [Finset.univ_sum_single]
    _ = ∑ k, (Pi.single k (v k * a) : ι → K) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => hsingle k (v k)
    _ = a • v := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply, mul_comm]

end Matrices

section Natural

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Algebra (ZMod 2) K]

@[expose] def scalarHom (ψ : V ≃ₗ[ZMod 2] (ι → K)) : K →ₐ[ZMod 2] Module.End (ZMod 2) V where
  toFun a := ψ.symm.toLinearMap ∘ₗ (Algebra.lsmul (ZMod 2) K (ι → K) a) ∘ₗ ψ.toLinearMap
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp [smul_smul, mul_comm]
  map_zero' := by ext v; simp
  map_add' a b := by ext v; simp
  commutes' c := by ext v; simp

omit [Fintype ι] [DecidableEq ι] in
lemma scalarHom_apply (ψ : V ≃ₗ[ZMod 2] (ι → K)) (a : K) (v : V) :
    scalarHom ψ a v = ψ.symm (a • ψ v) := by
  simp [scalarHom]

omit [Fintype ι] [DecidableEq ι] in
lemma psi_scalarHom (ψ : V ≃ₗ[ZMod 2] (ι → K)) (a : K) (v : V) :
    ψ (scalarHom ψ a v) = a • ψ v := by
  rw [scalarHom_apply, LinearEquiv.apply_symm_apply]

lemma apply_of_mem_endCommutant {H : Subgroup (GLV V)} {f : Module.End (ZMod 2) V}
    (hf : f ∈ endCommutant H) {h : GLV V} (hh : h ∈ H) (v : V) :
    h (f v) = f (h v) :=
  LinearMap.congr_fun (mem_endCommutant_iff.mp hf h hh) v

lemma scalarHom_mem_endCommutant {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (GLV V)} (ψ : V ≃ₗ[ZMod 2] (ι → K)) (φ : ↥H ≃* ↥Γ₀)
    (hψ : ∀ (h : ↥H) (v : V),
      ψ ((h : GLV V) v) = ((φ h : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ ψ v)
    (a : K) : scalarHom ψ a ∈ endCommutant H := by
  have hψ' : ∀ (h : GLV V) (hh : h ∈ H) (v : V),
      ψ (h v) = ((φ ⟨h, hh⟩ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ ψ v :=
    fun h hh v => hψ ⟨h, hh⟩ v
  rw [mem_endCommutant_iff]
  intro h hh
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
  apply ψ.injective
  rw [hψ' h hh (scalarHom ψ a v), psi_scalarHom, psi_scalarHom, hψ' h hh v, Matrix.mulVec_smul]

lemma exists_scalarHom_eq_of_mem_endCommutant [Nontrivial ι]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (GLV V)}
    (hSL : ∀ M : Matrix ι ι K, M.det = 1 → ∃ g ∈ Γ₀, (g : Matrix ι ι K) = M)
    (ψ : V ≃ₗ[ZMod 2] (ι → K)) (φ : ↥H ≃* ↥Γ₀)
    (hψ : ∀ (h : ↥H) (v : V),
      ψ ((h : GLV V) v) = ((φ h : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ ψ v)
    {f : Module.End (ZMod 2) V} (hf : f ∈ endCommutant H) :
    ∃ a : K, scalarHom ψ a = f := by
  obtain ⟨F, hF⟩ : ∃ F : Module.End (ZMod 2) (ι → K), ∀ w, F w = ψ (f (ψ.symm w)) :=
    ⟨ψ.toLinearMap ∘ₗ f ∘ₗ ψ.symm.toLinearMap, fun w => rfl⟩
  have hFc : ∀ M : Matrix ι ι K, M.det = 1 → ∀ w, F (M *ᵥ w) = M *ᵥ F w := by
    intro M hM w
    obtain ⟨g, hg, hgM⟩ := hSL M hM
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ↥H, φ h₀ = ⟨g, hg⟩ := ⟨φ.symm ⟨g, hg⟩, by simp⟩
    have hφ : ((φ h₀ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = M := by
      rw [hh₀]
      exact hgM
    have hsame : ∀ v, ψ ((h₀ : GLV V) v) = M *ᵥ ψ v := fun v => by
      rw [hψ h₀ v, hφ]
    have hcomm := apply_of_mem_endCommutant hf h₀.2 (ψ.symm w)
    have key : M *ᵥ w = ψ ((h₀ : GLV V) (ψ.symm w)) := by
      rw [hsame, LinearEquiv.apply_symm_apply]
    rw [hF, hF, key, LinearEquiv.symm_apply_apply, ← hcomm, hsame]
  obtain ⟨a, ha⟩ := commutant_scalar F hFc
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  have h2 : ψ (f v) = a • ψ v := by
    have := ha (ψ v)
    rw [hF, LinearEquiv.symm_apply_apply] at this
    exact this
  rw [scalarHom_apply, ← h2, LinearEquiv.symm_apply_apply]

theorem endIsField_of_isNaturalMatrixModule [Finite V] [Nontrivial ι]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (GLV V)}
    (hSL : ∀ M : Matrix ι ι K, M.det = 1 → ∃ g ∈ Γ₀, (g : Matrix ι ι K) = M)
    (hmod : IsNaturalMatrixModule H Γ₀) :
    EndIsField H (Module.finrank (ZMod 2) K) := by
  obtain ⟨φ, ψ, hψ⟩ := hmod
  have : Nontrivial V := ψ.toEquiv.nontrivial
  have hK : Finite K := by
    have hfin : Finite (ι → K) := Finite.of_equiv V ψ.toEquiv
    exact Finite.of_injective (fun a : K => fun _ : ι => a)
      (fun a b h => congrFun h (Classical.arbitrary ι))
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite (ZMod 2) K := Module.finite_iff_finite.mpr hK
  have hpos : Module.finrank (ZMod 2) K ≠ 0 :=
    (Module.finrank_pos (R := ZMod 2) (M := K)).ne'
  have hcardK : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [Nat.card_zmod] at this
    exact this
  have : Fintype (GaloisField 2 (Module.finrank (ZMod 2) K)) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 (Module.finrank (ZMod 2) K)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardK, GaloisField.card 2 _ hpos]
  have hmemK : ∀ a : K, scalarHom ψ a ∈ endCommutant H :=
    scalarHom_mem_endCommutant ψ φ hψ
  let θ : K →ₐ[ZMod 2] ↥(endCommutant H) :=
    (scalarHom ψ).codRestrict (endCommutant H) hmemK
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact (RingHom.injective (scalarHom ψ : K →+* Module.End (ZMod 2) V)) (congrArg Subtype.val hab)
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨a, ha⟩ := exists_scalarHom_eq_of_mem_endCommutant hSL ψ φ hψ x.2
    exact ⟨a, Subtype.ext ha⟩
  let E1 : K ≃ₐ[ZMod 2] ↥(endCommutant H) := AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  let E2 : K ≃ₐ[ZMod 2] GaloisField 2 (Module.finrank (ZMod 2) K) :=
    FiniteField.algEquivOfCardEq 2 hcard
  exact ⟨E1.symm.trans E2⟩

end Natural

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
