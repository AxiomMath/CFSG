module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix TableBOrth

namespace OrdPOm

variable {K : Type} [Field K]

section Weights

variable {V : Type} [AddCommGroup V] [Module K V]

theorem exists_orth_conj_weights_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    {QF : QuadraticForm K V} (hnd : (QuadraticMap.polarBilin QF).Nondegenerate)
    {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) {r : ℕ}
    (hW : ∀ T : Submodule K V, (∀ w ∈ T, QF w = 0) → Module.finrank K T ≤ r)
    {e f : Fin r → V} (hef : IsHypFamily QF e f)
    {G : Type} [CommGroup G] [Finite G] (ρ : G →* (V ≃ₗ[K] V))
    (hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup QF) (hexp : ∀ x : G, x ^ p = 1) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup QF, ∃ χ : Fin r → G →* Kˣ,
      (∀ x k, (g * ρ x * g⁻¹) (e k) = ((χ k x : Kˣ) : K) • e k) ∧
      (∀ x k, (g * ρ x * g⁻¹) (f k) = (((χ k x)⁻¹ : Kˣ) : K) • f k) ∧
      (∀ x v, (∀ k, QuadraticMap.polar QF (e k) v = 0) →
        (∀ k, QuadraticMap.polar QF (f k) v = 0) → (g * ρ x * g⁻¹) v = v) := by
  classical
  have hp := hpF.out
  have : NeZero p := ⟨hp.ne_zero⟩
  let ρ' : G →* Module.End K V :=
    { toFun := fun x => ((ρ x : V ≃ₗ[K] V) : V →ₗ[K] V)
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl }
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  have : HasEnoughRootsOfUnity K p := ⟨⟨_, hprim⟩, rootsOfUnity.isCyclic K p⟩
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  have hpK : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hcardu : IsUnit (Nat.card G : K) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      ((fun g : G => ⟨1, by rw [pow_one]; exact hexp g⟩) : IsPGroup p G)
    rw [hk, Nat.cast_pow]
    exact (IsUnit.mk0 _ hpK).pow k
  have hWtop := TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := ρ') hcardu
  set W : (G →* Kˣ) → Submodule K V := fun χ => ⨅ g, (ρ' g).eigenspace (χ g) with hWdef
  have hmemW : ∀ {χ : G →* Kˣ} {v : V}, v ∈ W χ → ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
    intro χ v hv g
    have := (Submodule.mem_iInf _).mp hv g
    rw [Module.End.mem_eigenspace_iff] at this
    exact this
  set B := QuadraticMap.polarBilin QF with hB
  have hBapp : ∀ v w, B v w = QuadraticMap.polar QF v w := fun _ _ => rfl
  have hBalt : LinearMap.BilinForm.IsAlt B := fun v => by
    rw [hBapp, QuadraticMap.polar_self, two_smul, CharTwo.add_self_eq_zero]
  have hpolρ : ∀ g v w, QuadraticMap.polar QF (ρ g v) (ρ g w) = QuadraticMap.polar QF v w :=
    fun g v w => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hρO g) v w
  have horth : ∀ χ ψ : G →* Kˣ, ψ ≠ χ⁻¹ → ∀ v ∈ W χ, ∀ w ∈ W ψ, B v w = 0 := by
    intro χ ψ hne v hv w hw
    by_contra hvw
    have hvw' : QuadraticMap.polar QF v w ≠ 0 := hvw
    apply hne
    ext g
    have h1 := hpolρ g v w
    rw [hmemW hv g, hmemW hw g, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      smul_smul, smul_eq_mul] at h1
    have h2 : ((χ g : Kˣ) : K) * ((ψ g : Kˣ) : K) = 1 :=
      mul_right_cancel₀ hvw' (h1.trans (one_mul _).symm)
    have h3 : χ g * ψ g = 1 := Units.ext (by rw [Units.val_mul, h2, Units.val_one])
    rw [MonoidHom.inv_apply, eq_inv_of_mul_eq_one_right h3]
  obtain ⟨n, bas, hbas, hbasW⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top hBalt hnd (W := W)
      (σ := fun χ => χ⁻¹) (fun χ => inv_inv χ) hWtop horth
  choose s hs using hbasW
  have hbB : ∀ x y, QuadraticMap.polar QF (bas x) (bas y) = Matrix.J (Fin n) K x y :=
    fun x y => by rw [← hBapp, ← LinearMap.BilinForm.toMatrix_apply bas, hbas]
  have hpair : ∀ i, s (Sum.inr i) = (s (Sum.inl i))⁻¹ := by
    intro i
    by_contra hne
    have h0 := horth _ _ hne _ (hs (Sum.inl i)) _ (hs (Sum.inr i))
    rw [hBapp, hbB] at h0
    simp [Matrix.J] at h0
  have hsp : ∀ x g, s x g ^ p = 1 := fun x g => by rw [← map_pow, hexp, map_one]
  have hρbas : ∀ g y, ρ g (bas y) = ((s y g : Kˣ) : K) • bas y := fun g y => hmemW (hs y) g
  have hQ0 : ∀ x, s x ≠ 1 → QF (bas x) = 0 := by
    intro x hx
    obtain ⟨g, hg⟩ : ∃ g, s x g ≠ 1 := by
      by_contra h
      push Not at h
      exact hx (MonoidHom.ext h)
    have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hρO g) (bas x)
    rw [hρbas, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : ((s x g : Kˣ) : K) * (s x g : K) ≠ 1 := by
      intro h
      exact hg (eq_one_of_sq_of_pow_prime hp hp2
        (Units.ext (by rw [sq, Units.val_mul, h, Units.val_one])) (hsp x g))
    have h3 : (((s x g : Kˣ) : K) * (s x g : K) - 1) * QF (bas x) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h2)
  set N : Finset (Fin n) := Finset.univ.filter fun i => s (Sum.inl i) ≠ 1 with hN
  have hNr : N.card ≤ r := by
    have hli : LinearIndependent K fun i : N => bas (Sum.inl (i : Fin n)) :=
      bas.linearIndependent.comp _ (fun i j h => Subtype.ext (Sum.inl_injective h))
    have hT : ∀ w ∈ Submodule.span K (Set.range fun i : N => bas (Sum.inl (i : Fin n))),
        QF w = 0 := by
      apply eq_zero_on_span
      · rintro _ ⟨i, rfl⟩
        exact hQ0 _ (Finset.mem_filter.mp i.2).2
      · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        rw [hbB]
        simp [Matrix.J]
    have := hW _ hT
    rwa [finrank_span_eq_card hli, Fintype.card_coe] at this
  have hinv1 : ∀ χ : G →* Kˣ, χ⁻¹ = 1 → χ = 1 := fun χ h => MonoidHom.ext fun g => by
    have := DFunLike.congr_fun h g
    rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at this
    rw [this, MonoidHom.one_apply]
  have hNmem : ∀ i : N, s (Sum.inl (i : Fin n)) ≠ 1 := fun i => (Finset.mem_filter.mp i.2).2
  have hNmem' : ∀ i : N, s (Sum.inr (i : Fin n)) ≠ 1 := fun i h => by
    rw [hpair] at h
    exact hNmem i (hinv1 _ h)
  have hNcard : Fintype.card N ≤ r := by rwa [Fintype.card_coe]
  set σ' : N → Fin r := fun i => Fin.castLE hNcard (Fintype.equivFin N i) with hσ'def
  have hσ'inj : Function.Injective σ' := fun a b h =>
    (Fintype.equivFin N).injective (Fin.castLE_injective hNcard h)
  have hJ1 : ∀ a b : Fin n,
      Matrix.J (Fin n) K (Sum.inl a) (Sum.inr b) = if a = b then 1 else 0 := by
    intro a b
    simp only [Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp [CharTwo.neg_eq]
  have hJ2 : ∀ a b : Fin n,
      Matrix.J (Fin n) K (Sum.inr a) (Sum.inl b) = if a = b then 1 else 0 := by
    intro a b
    simp only [Matrix.J, Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
  have hJ3 : ∀ a b : Fin n, Matrix.J (Fin n) K (Sum.inl a) (Sum.inl b) = 0 := by
    intro a b
    simp [Matrix.J]
  have hJ4 : ∀ a b : Fin n, Matrix.J (Fin n) K (Sum.inr a) (Sum.inr b) = 0 := by
    intro a b
    simp [Matrix.J]
  set u : N ⊕ N → V :=
    Sum.elim (fun i => bas (Sum.inl (i : Fin n))) (fun i => bas (Sum.inr (i : Fin n))) with hudef
  set u' : N ⊕ N → V := Sum.elim (fun i => e (σ' i)) (fun i => f (σ' i)) with hu'def
  have hu : LinearIndependent K u := by
    have h1 : u = bas ∘ Sum.map (fun i : N => (i : Fin n)) (fun i : N => (i : Fin n)) := by
      funext y
      rcases y with k | k <;> rfl
    rw [h1]
    exact bas.linearIndependent.comp _
      (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
  have hu' : LinearIndependent K u' := by
    have h1 : u' = Sum.elim e f ∘ Sum.map σ' σ' := by
      funext y
      rcases y with k | k <;> rfl
    rw [h1]
    exact hef.linearIndependent.comp _ (Sum.map_injective.mpr ⟨hσ'inj, hσ'inj⟩)
  obtain ⟨g, hgO, hgu⟩ := exists_orth_apply_eq hnd u u' hu hu'
    (by
      rintro (k | k)
      · rw [hu'def, Sum.elim_inl, hef.map_e, hudef, Sum.elim_inl, hQ0 _ (hNmem k)]
      · rw [hu'def, Sum.elim_inr, hef.map_f, hudef, Sum.elim_inr, hQ0 _ (hNmem' k)])
    (by
      rintro (i | i) (j | j)
      · simp only [Sum.elim_inl, hudef, hu'def]
        rw [hef.polar_ee, hbB, hJ3]
      · simp only [Sum.elim_inl, Sum.elim_inr, hudef, hu'def]
        rw [hef.polar_ef, hbB, hJ1]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hσ'inj.ne hij, Subtype.val_injective.ne hij]
      · simp only [Sum.elim_inl, Sum.elim_inr, hudef, hu'def]
        rw [QuadraticMap.polar_comm, hef.polar_ef, hbB, hJ2]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hσ'inj.ne (Ne.symm hij), Subtype.val_injective.ne hij]
      · simp only [Sum.elim_inr, hudef, hu'def]
        rw [hef.polar_ff, hbB, hJ4])
  have hge : ∀ i : N, g (bas (Sum.inl (i : Fin n))) = e (σ' i) := fun i => hgu (Sum.inl i)
  have hgf : ∀ i : N, g (bas (Sum.inr (i : Fin n))) = f (σ' i) := fun i => hgu (Sum.inr i)
  have hginv : ∀ v, g⁻¹ (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hgginv : ∀ v, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hrest : ∀ x v, (∀ i : N, QuadraticMap.polar QF (e (σ' i)) v = 0) →
      (∀ i : N, QuadraticMap.polar QF (f (σ' i)) v = 0) → (g * ρ x * g⁻¹) v = v := by
    intro x v hve hvf
    set w := g⁻¹ v with hw
    have hgw : g w = v := hgginv v
    have hpolg : ∀ a, QuadraticMap.polar QF (g a) v = QuadraticMap.polar QF a w := fun a => by
      rw [← hgw, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO]
    have hperp : ∀ y, s y ≠ 1 → QuadraticMap.polar QF (bas y) w = 0 := by
      rintro (i | i) hy
      · have hi : i ∈ N := by simp [hN, hy]
        rw [← hpolg, hge ⟨i, hi⟩, hve]
      · have hy' : s (Sum.inl i) ≠ 1 := by
          intro h1
          apply hy
          rw [hpair, h1]
          exact MonoidHom.ext fun g => by rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_one]
        have hi : i ∈ N := by simp [hN, hy']
        rw [← hpolg, hgf ⟨i, hi⟩, hvf]
    have hzero : ∀ y, B (bas y) (ρ x w - w) = 0 := by
      intro y
      rw [map_sub, hBapp, hBapp]
      have h1 : QuadraticMap.polar QF (bas y) (ρ x w) =
          ((s y x⁻¹ : Kˣ) : K) * QuadraticMap.polar QF (bas y) w := by
        have h2 := hpolρ x (ρ x⁻¹ (bas y)) w
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one,
          id, hρbas, QuadraticMap.polar_smul_left, smul_eq_mul] at h2
        exact h2
      rw [h1]
      by_cases hy : s y = 1
      · rw [hy, MonoidHom.one_apply, Units.val_one, one_mul, sub_self]
      · rw [hperp y hy, mul_zero, sub_zero]
    have hall : ∀ a, B a (ρ x w - w) = 0 := by
      intro a
      have h1 : B.flip (ρ x w - w) = 0 := bas.ext fun y => by
        rw [LinearMap.flip_apply, hzero, LinearMap.zero_apply]
      have := LinearMap.congr_fun h1 a
      rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
    have h0 : ρ x w - w = 0 := hnd.2 _ hall
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hw, sub_eq_zero.mp h0, hgw]
  have hchar : ∀ k : Fin r, ∃ χk : G →* Kˣ,
      (∀ x, (g * ρ x * g⁻¹) (e k) = ((χk x : Kˣ) : K) • e k) ∧
        (∀ x, (g * ρ x * g⁻¹) (f k) = (((χk x)⁻¹ : Kˣ) : K) • f k) := by
    intro k
    by_cases hk : ∃ i : N, σ' i = k
    · obtain ⟨i, rfl⟩ := hk
      refine ⟨s (Sum.inl (i : Fin n)), fun x => ?_, fun x => ?_⟩
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hge, hginv, hρbas, map_smul]
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hgf, hginv, hρbas, map_smul, hpair,
          MonoidHom.inv_apply]
    · push Not at hk
      refine ⟨1, fun x => ?_, fun x => ?_⟩
      · rw [MonoidHom.one_apply, Units.val_one, one_smul]
        refine hrest x _ (fun i => hef.polar_ee _ _) (fun i => ?_)
        rw [QuadraticMap.polar_comm, hef.polar_ef, ite_eq_right (hk i).symm]
      · rw [MonoidHom.one_apply, inv_one, Units.val_one, one_smul]
        refine hrest x _ (fun i => ?_) (fun i => hef.polar_ff _ _)
        rw [hef.polar_ef, ite_eq_right (hk i)]
  choose χ hχ using hchar
  exact ⟨g, hgO, χ, fun x k => (hχ k).1 x, fun x k => (hχ k).2 x,
    fun x v hve hvf => hrest x v (fun i => hve _) (fun i => hvf _)⟩

end Weights

section MatrixForm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)

theorem exists_orth_conj_diag_le [Finite K] [CharP K 2] {QF : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {r : ℕ}
    (hW : ∀ T : Submodule K (ι → K), (∀ w ∈ T, QF w = 0) → Module.finrank K T ≤ r)
    {a b : Fin r → ι} (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hb : Function.Injective b) (hab' : ∀ i j, a i ≠ b j) (d : (Fin r → Kˣ) → ι → Kˣ)
    (hda : ∀ u k, d u (a k) = u k)
    (hdb : ∀ u k, d u (b k) = (u k)⁻¹) (hdo : ∀ u i, (∀ k, i ≠ a k ∧ i ≠ b k) → d u i = 1)
    {A : Subgroup (GL ι K)} (hAO : A ≤ LargeEvenOrthGroup ⇑QF) (hA : IsElemAbelian p A) :
    ∃ g ∈ LargeEvenOrthGroup ⇑QF, ∃ χ : Fin r → A →* Kˣ,
      ∀ x : A, g * (x : GL ι K) * g⁻¹ = TauCeti.diagGL (d fun k => χ k x) := by
  classical
  let _ : CommGroup A := { (inferInstance : Group ↥A) with mul_comm := hA.1.is_comm.comm }
  set ρ : A →* ((ι → K) ≃ₗ[K] (ι → K)) := (toLinEquiv ι K).toMonoidHom.comp A.subtype with hρ
  have hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup QF := fun x =>
    mem_orthGroup_iff_toLinEquiv.mp (hAO x.2)
  have hexp : ∀ x : A, x ^ p = 1 := fun x => Subtype.ext (hA.2 x x.2)
  obtain ⟨g, hgO, χ, he, hf, hrest⟩ := exists_orth_conj_weights_le hnd hp2 hζo hW
    (isHypFamily_single hab hb hab') ρ hρO hexp
  refine ⟨(toLinEquiv ι K).symm g, ?_, χ, fun x => ?_⟩
  · rw [mem_orthGroup_iff_toLinEquiv, MulEquiv.apply_symm_apply]
    exact hgO
  · apply (toLinEquiv ι K).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun K ι).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, toLinEquiv_apply,
      TauCeti.diagGL_coe]
    have hdiag : (Matrix.diagonal fun j => ((d (fun k => χ k x) j : Kˣ) : K)) *ᵥ
        Pi.single i (1 : K) = ((d (fun k => χ k x) i : Kˣ) : K) • Pi.single i 1 := by
      funext j
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hji : j = i
      · subst hji
        rfl
      · rw [Pi.single_eq_of_ne hji, mul_zero, mul_zero]
    rw [hdiag]
    by_cases hia : ∃ k, i = a k
    · obtain ⟨k, rfl⟩ := hia
      rw [hda]
      exact he x k
    · by_cases hib : ∃ k, i = b k
      · obtain ⟨k, rfl⟩ := hib
        rw [hdb]
        exact hf x k
      · push Not at hia hib
        rw [hdo _ i fun k => ⟨hia k, hib k⟩, Units.val_one, one_smul]
        refine hrest x _ (fun k => ?_) (fun k => ?_)
        · rw [(hab k).polar_left, Pi.single_eq_of_ne (hib k).symm]
        · rw [(hab k).polar_right, Pi.single_eq_of_ne (hia k).symm]

theorem card_le_of_orth [Finite K] [CharP K 2] {QF : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {r : ℕ}
    (hW : ∀ T : Submodule K (ι → K), (∀ w ∈ T, QF w = 0) → Module.finrank K T ≤ r)
    {a b : Fin r → ι} (hab : ∀ k, SeitzReduction.OmegaPilot.IsHypCoord QF (a k) (b k))
    (hb : Function.Injective b) (hab' : ∀ i j, a i ≠ b j) (d : (Fin r → Kˣ) → ι → Kˣ)
    (hda : ∀ u k, d u (a k) = u k)
    (hdb : ∀ u k, d u (b k) = (u k)⁻¹) (hdo : ∀ u i, (∀ k, i ≠ a k ∧ i ≠ b k) → d u i = 1)
    {A : Subgroup (GL ι K)} (hAO : A ≤ LargeEvenOrthGroup ⇑QF) (hA : IsElemAbelian p A) :
    Nat.card A ≤ p ^ r := by
  obtain ⟨g, -, χ, hχ⟩ := exists_orth_conj_diag_le hnd hp2 hζo hW hab hb hab' d hda hdb hdo
    hAO hA
  have hexp : ∀ x : A, x ^ p = 1 := fun x => Subtype.ext (hA.2 x x.2)
  set φ : A → (Fin r → rootsOfUnity p K) := fun x k =>
    ⟨χ k x, (mem_rootsOfUnity p _).mpr (by rw [← map_pow, hexp, map_one])⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro x x' h
    have h1 : (fun k => χ k x) = fun k => χ k x' := funext fun k =>
      congrArg Subtype.val (congrFun h k)
    have h2 := hχ x
    rw [h1, ← hχ x'] at h2
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  calc Nat.card A ≤ Nat.card (Fin r → rootsOfUnity p K) := Nat.card_le_card_of_injective φ hφinj
    _ = Nat.card (rootsOfUnity p K) ^ r := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]
    _ ≤ p ^ r := Nat.pow_le_pow_left (card_rootsOfUnity K p) _

end MatrixForm

section Plus

variable [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] {ζ : Kˣ} {m : ℕ}

theorem exists_orth_conj_plus_le (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    {A : Subgroup (GL (Fin m ⊕ Fin m) K)} (hAO : A ≤ LargeEvenOrthGroup (LargeEvenQPlus K m))
    (hA : IsElemAbelian p A) :
    ∃ g ∈ LargeEvenOrthGroup (LargeEvenQPlus K m), ∃ χ : Fin m → A →* Kˣ,
      ∀ x : A, g * (x : GL (Fin m ⊕ Fin m) K) * g⁻¹ =
        TauCeti.diagGL (TableBSymp.pairedUnits fun k => χ k x) := by
  rw [← coe_qPlusForm] at hAO ⊢
  exact exists_orth_conj_diag_le (nondegenerate_qPlusForm m) hp2 hζo
    finrank_le_of_singular_qPlus isHypCoord_qPlusForm Sum.inr_injective
    (fun i j => Sum.inl_ne_inr) TableBSymp.pairedUnits (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with k | k <;> [exact absurd rfl (hi k).1; exact absurd rfl (hi k).2])
    hAO hA

theorem card_le_plus (hp2 : p ≠ 2) (hζo : orderOf ζ = p) {A : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hAO : A ≤ LargeEvenOrthGroup (LargeEvenQPlus K m)) (hA : IsElemAbelian p A) :
    Nat.card A ≤ p ^ m := by
  rw [← coe_qPlusForm] at hAO
  exact card_le_of_orth (nondegenerate_qPlusForm m) hp2 hζo
    finrank_le_of_singular_qPlus isHypCoord_qPlusForm Sum.inr_injective
    (fun i j => Sum.inl_ne_inr) TableBSymp.pairedUnits (fun _ _ => rfl) (fun _ _ => rfl)
    (fun u i hi => by
      rcases i with k | k <;> [exact absurd rfl (hi k).1; exact absurd rfl (hi k).2])
    hAO hA

end Plus

section Transfer

variable {U G H : Type*} [Group U] [Group G] [Group H] {p : ℕ}

theorem isElemAbelian_map (f : U →* G) {E : Subgroup U} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_comap (f : U →* G) (hf : Function.Injective f) {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := CFSG.Open.IsElemAbelian.comap hE hf

theorem transfer_mat (ψ : U →* G) (hψ : Function.Injective ψ) (j : U →* H)
    (hj : Function.Injective j) {E : Subgroup H} (hE : IsElemAbelian p E) (hEj : E ≤ j.range)
    {u : U} (hu : ∀ x ∈ E, j u * x = x * j u) :
    IsElemAbelian p ((E.comap j).map ψ) ∧ (E.comap j).map ψ ≤ ψ.range ∧
      Nat.card ((E.comap j).map ψ) = Nat.card E ∧
      ∀ z ∈ (E.comap j).map ψ, ψ u * z = z * ψ u := by
  refine ⟨isElemAbelian_map ψ (isElemAbelian_comap j hj hE), Subgroup.map_le_range ψ _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hψ, ← Subgroup.card_map_of_injective hj,
      Subgroup.map_comap_eq_self hEj]
  · rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply hj
    rw [map_mul, map_mul]
    exact hu _ hz

theorem transfer_range (ψ : U →* G) (hψ : Function.Injective ψ) (j : U →* H)
    (hj : Function.Injective j) {B : Subgroup G} (hB : IsElemAbelian p B) (hBψ : B ≤ ψ.range) :
    IsElemAbelian p ((B.comap ψ).map j) ∧ (B.comap ψ).map j ≤ j.range ∧
      Nat.card ((B.comap ψ).map j) = Nat.card B := by
  refine ⟨isElemAbelian_map j (isElemAbelian_comap ψ hψ hB), Subgroup.map_le_range j _, ?_⟩
  rw [Subgroup.card_map_of_injective hj, ← Subgroup.card_map_of_injective hψ,
    Subgroup.map_comap_eq_self hBψ]

end Transfer

end OrdPOm

end CFSG.StandardType
