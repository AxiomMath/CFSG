module

public import CFSG.LinearAlgebra.RootGroupSL.NoOuter
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.StandardType.LieKnownR2.PSL

open CFSG.LinearAlgebra.RootGroupSL
open Matrix

theorem no_additive_equivariant_dual_two {k X : Type} [Field k] [AddCommGroup X] [Module k X]
    [Module.Finite k X] (hX : 3 ≤ Module.finrank k X) (τ : Module.Dual k X →+ X)
    (hinj : Function.Injective τ)
    (hτ : ∀ (ψ : Module.Dual k X) (u : X), ψ u = 0 → ∀ φ : Module.Dual k X,
      τ (φ + φ u • ψ) = τ φ + ψ (τ φ) • u) : False := by
  classical
  have hXpos : 0 < Module.finrank k X := by omega
  obtain ⟨u0, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hXpos
  obtain ⟨ψ, hψu⟩ := Module.Projective.exists_dual_eq_one k (V := X) hu0
  have hψ : ψ ≠ 0 := by
    intro h0
    rw [h0] at hψu
    simpa using hψu
  have hrange : Module.finrank k (LinearMap.range ψ) = 1 := by
    have htop : LinearMap.range ψ = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro c
      have hx : ∃ x : X, ψ x ≠ 0 := by
        by_contra h
        push Not at h
        exact hψ (LinearMap.ext h)
      obtain ⟨x, hx⟩ := hx
      refine ⟨(c * (ψ x)⁻¹) • x, ?_⟩
      rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]
    rw [htop, finrank_top, CommSemiring.finrank_self]
  have hker : 2 ≤ Module.finrank k (LinearMap.ker ψ) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hrange] at hrn
    omega
  obtain ⟨v, hv⟩ :=
    exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.ker ψ) hker
  let w : Fin 2 → X := (Submodule.subtype (LinearMap.ker ψ)) ∘ v
  have hw : LinearIndependent k w :=
    hv.map' (Submodule.subtype (LinearMap.ker ψ)) (Submodule.ker_subtype _)
  have hw01 : LinearIndependent k ![w 0, w 1] := by
    have hfun : ![w 0, w 1] = w := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
    exact hw
  rw [LinearIndependent.pair_iff] at hw01
  have hmem : ∀ i : Fin 2, ψ (w i) = 0 := fun i => LinearMap.mem_ker.mp (v i).property
  have hw0ne : w 0 ≠ 0 := LinearIndependent.ne_zero (0 : Fin 2) hw
  have hw1ne : w 1 ≠ 0 := LinearIndependent.ne_zero (1 : Fin 2) hw
  obtain ⟨φ0, hφ0⟩ := Module.Projective.exists_dual_eq_one k (V := X) hw0ne
  obtain ⟨φ1, hφ1⟩ := Module.Projective.exists_dual_eq_one k (V := X) hw1ne
  have hτ0 : τ ψ = ψ (τ φ0) • w 0 := by
    have h := hτ ψ (w 0) (hmem 0) φ0
    rw [hφ0, one_smul, map_add] at h
    exact add_left_cancel h
  have hτ1 : τ ψ = ψ (τ φ1) • w 1 := by
    have h := hτ ψ (w 1) (hmem 1) φ1
    rw [hφ1, one_smul, map_add] at h
    exact add_left_cancel h
  have hc : ψ (τ φ0) • w 0 = ψ (τ φ1) • w 1 := hτ0.symm.trans hτ1
  have hcoeff : ψ (τ φ0) = 0 := by
    have hsum : ψ (τ φ0) • w 0 + (-(ψ (τ φ1))) • w 1 = 0 := by
      rw [neg_smul, ← sub_eq_add_neg, hc, sub_self]
    exact (hw01 _ _ hsum).1
  have hτψ0 : τ ψ = 0 := by
    rw [hτ0, hcoeff, zero_smul]
  exact hψ (hinj (hτψ0.trans (map_zero τ).symm))

open CFSG.LinearAlgebra.RootGroupSL.NoOuterGraph in
theorem exists_additive_equivariant_of_graph_form_two
    {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
    [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]
    (hk : Nat.card k = 2) (hE : Module.finrank k E = 1) (hX : 0 < Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (σ : k ≃+* k) (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace E X)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) :
    ∃ τ : Module.Dual k X →+ X, Function.Injective τ ∧
      ∀ (ψ : Module.Dual k X) (u : X), ψ u = 0 → ∀ φ : Module.Dual k X,
        τ (φ + φ u • ψ) = τ φ + ψ (τ φ) • u := by
  classical
  let prX : DSpace E X →ₗ[k] X :=
    (LinearMap.fst k X E).comp (LinearMap.snd k E (X × E))
  let f : Module.Dual k X → Module.Dual k (DSpace E X) := fun phi => phi.comp prX
  have hf_add : ∀ phi psi : Module.Dual k X, f (phi + psi) = f phi + f psi := by
    intro phi psi
    apply LinearMap.ext
    intro v
    rfl
  have hf_zero : f 0 = 0 := by
    apply LinearMap.ext
    intro v
    rfl
  let tau : Module.Dual k X →+ X :=
    { toFun := fun phi => (T (f phi)).2.1
      map_zero' := by rw [hf_zero, map_zero]; rfl
      map_add' := fun phi psi => by rw [hf_add, map_add]; rfl }
  have hfW_all : ∀ phi : Module.Dual k X, f phi ∈ AnnW k E X := by
    intro phi
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    rw [mem_flagW_iff] at hv
    simp [f, prX, hv.1]
  have hker : ∀ d : Module.Dual k X, tau d = 0 → d = 0 := by
    intro d hd
    apply LinearMap.ext
    intro x
    have hTK : T (f d) ∈ flagK k E X :=
      T_mem_flagK_of_mem_dualAnnW α hR T hα (hfW_all d)
    have hTW : T (f d) ∈ flagW k E X := by
      rw [mem_flagW_iff]
      exact ⟨hd, (mem_flagK_iff _).mp hTK⟩
    have hfK : f d ∈ AnnK k E X :=
      mem_dualAnnK_of_T_mem_flagW α hR T hα hTW
    have hx : f d (0, x, 0) = 0 :=
      (Submodule.mem_dualAnnihilator (f d)).mp hfK (0, x, 0)
        (by rw [mem_flagK_iff])
    simpa [f, prX] using hx
  refine ⟨tau, ?_, ?_⟩
  · intro phi psi hphi
    have hzero : tau (phi - psi) = 0 := by rw [map_sub, hphi, sub_self]
    exact sub_eq_zero.mp (hker (phi - psi) hzero)
  · intro ψ u hψu phi
    let t : X ≃ₗ[k] X := LinearEquiv.transvection hψu
    have ht_apply : ∀ x : X, t x = x + ψ x • u :=
      fun x => LinearEquiv.transvection.apply hψu x
    have ht_det : LinearEquiv.det t = 1 := LinearEquiv.transvection.det_eq_one hψu
    have hdet : LinearEquiv.det (1 : E ≃ₗ[k] E) * LinearEquiv.det t *
        LinearEquiv.det (1 : E ≃ₗ[k] E) = 1 := by
      rw [ht_det]
      simp
    let h : SpecialLinearGroup k (DSpace E X) :=
      blockSL (1 : E ≃ₗ[k] E) t (1 : E ≃ₗ[k] E) hdet
    have hN : h ∈ RootN := by
      refine (blockSL_mem_normalizer_iff (a := (1 : E ≃ₗ[k] E)) (g := t)
        (b := (1 : E ≃ₗ[k] E)) hdet).mpr ?_
      intro t'
      refine ⟨t', ?_⟩
      rfl
    obtain ⟨c, _hcW, hcK⟩ := action_flagW_and_second α hC hN
    have hc1 : c = 1 := by
      have hcard : Nat.card kˣ = 1 := by
        rw [Nat.card_units, hk]
      haveI : Subsingleton kˣ := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact Subsingleton.elim c 1
    have hvK : T (f phi) ∈ flagK k E X :=
      T_mem_flagK_of_mem_dualAnnW α hR T hα (hfW_all phi)
    have hsec := hcK _ hvK
    have hhinv : SpecialLinearGroup.toLinearEquiv h⁻¹ =
        blockDiag (1 : E ≃ₗ[k] E) t⁻¹ (1 : E ≃ₗ[k] E) := by
      rw [SpecialLinearGroup.toLinearEquiv_eq_coe, SpecialLinearGroup.coe_inv]
      change (blockDiag (1 : E ≃ₗ[k] E) t (1 : E ≃ₗ[k] E))⁻¹ =
        blockDiag (1 : E ≃ₗ[k] E) t⁻¹ (1 : E ≃ₗ[k] E)
      rw [blockDiag_inv]
      rfl
    have hcomp : f phi ∘ₗ (SpecialLinearGroup.toLinearEquiv h⁻¹).toLinearMap =
        f (phi ∘ₗ (t⁻¹).toLinearMap) := by
      rw [hhinv]
      apply LinearMap.ext
      intro v
      simp [f, prX, NoOuterGraph.blockDiag_apply]
    have hαapply : α h (T (f phi)) = T (f (phi ∘ₗ (t⁻¹).toLinearMap)) := by
      rw [hα h (f phi), hcomp]
    have hh_apply : (h (T (f phi))).2.1 = t (tau phi) := by
      change (blockDiag (1 : E ≃ₗ[k] E) t (1 : E ≃ₗ[k] E) (T (f phi))).2.1 =
        t (tau phi)
      rw [NoOuterGraph.blockDiag_apply]
      rfl
    have hkey : tau (phi ∘ₗ (t⁻¹).toLinearMap) = t (tau phi) := by
      have h' := hsec
      rw [hαapply, hh_apply, hc1] at h'
      simpa [tau] using h'
    have hneg_u : (-u : X) = u := by
      rw [← neg_one_smul (R := k) u, CharTwo.neg_eq (1 : k), one_smul]
    have htinv_apply : ∀ x : X, (t⁻¹).toLinearMap x = x + ψ x • u := by
      intro x
      have htinv_eq : t⁻¹ = LinearEquiv.transvection (f := ψ) (v := -u)
          (by simp [hψu]) :=
        LinearEquiv.transvection.inv_eq hψu (by simp [hψu])
      have h1 : (t⁻¹).toLinearMap x = x + ψ x • (-u) := by
        rw [htinv_eq]
        exact LinearEquiv.transvection.apply _ x
      rw [h1, hneg_u]
    have hphi_inv : phi ∘ₗ (t⁻¹).toLinearMap = phi + phi u • ψ := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, htinv_apply x]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      ring
    have ht_tau : t (tau phi) = tau phi + ψ (tau phi) • u := ht_apply (tau phi)
    rw [← hphi_inv, hkey, ht_tau]

theorem false_of_graph_form_two
    {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
    [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]
    (hk : Nat.card k = 2) (hE : Module.finrank k E = 1) (hX : 3 ≤ Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (σ : k ≃+* k) (T : Module.Dual k (DSpace E X) ≃+ DSpace E X)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace E X)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace E X)) (f : Module.Dual k (DSpace E X)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) : False := by
  obtain ⟨τ, hinj, hτ⟩ :=
    exists_additive_equivariant_of_graph_form_two hk hE (by omega) α hR hC σ T hT hα
  exact no_additive_equivariant_dual_two hX τ hinj hτ

theorem exists_conj_of_two_element_mem_Y_two
    {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
    [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]
    (hk : Nat.card k = 2) (hE : Module.finrank k E = 1) (hX : 3 ≤ Module.finrank k X)
    (α : MulAut (SpecialLinearGroup k (DSpace E X)))
    (hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)))
    (h2 : ∃ m : ℕ, α ^ (2 ^ m) = 1) :
    ∃ g : SpecialLinearGroup k (DSpace E X), α = MulAut.conj g := by
  classical
  haveI : Module.Finite k E := Module.Finite.of_finite
  have hfin : Module.finrank k (DSpace E X) =
      Module.finrank k E + Module.finrank k X + Module.finrank k E := by
    rw [Module.finrank_prod, Module.finrank_prod, add_assoc]
  have hV : 3 ≤ Module.finrank k (DSpace E X) := by
    rw [hfin, hE]
    omega
  obtain ⟨σ, hform⟩ :=
    exists_semilinear_form_of_mulAut_sl (F := k) (V := DSpace E X) hV α
  rcases hform with ⟨T, hT, hα⟩ | ⟨T, hT, hα⟩
  · have hσ : σ = RingEquiv.refl k := by
      haveI : Fintype k := Fintype.ofFinite k
      have hcard : Fintype.card k = 2 := by
        rw [← Nat.card_eq_fintype_card]
        exact hk
      have huniv : ({0, 1} : Finset k) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hcard, Finset.card_pair_eq_two_iff]
        exact zero_ne_one
      have hmem : ∀ x : k, x = 0 ∨ x = 1 := by
        intro x
        have hx : x ∈ ({0, 1} : Finset k) := by
          rw [huniv]
          exact Finset.mem_univ x
        simpa using hx
      refine RingEquiv.ext fun x => ?_
      rcases hmem x with h | h
      · rw [h]
        exact map_zero σ
      · rw [h]
        exact map_one σ
    have hTlin : ∀ (c : k) (v : DSpace E X), T (c • v) = c • T v := by
      intro c v
      rw [hT c v, hσ]
      rfl
    exact exists_conj_of_linear_form α T hTlin hα h2
  · exact False.elim (false_of_graph_form_two hk hE hX α hR hC σ T hT hα)

end CFSG.StandardType.LieKnownR2.PSL
