module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def glToEnd : GL (Fin m ⊕ Fin m) K →* Module.End K (Fin m ⊕ Fin m → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin m ⊕ Fin m)).toAlgHom.toRingHom.toMonoidHom.comp
    (Units.coeHom _)

theorem glToEnd_apply (g : GL (Fin m ⊕ Fin m) K) (v : Fin m ⊕ Fin m → K) :
    glToEnd g v = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v :=
  rfl

theorem mem_symplecticGroup_of_mem_sp {g : GL (Fin m ⊕ Fin m) K} (hg : g ∈ LargeEvenSpGroup K m) :
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ∈ Matrix.symplecticGroup (Fin m) K := by
  have h : g ∈ TauCeti.GLSymplectic (Fin m) K := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact hg
  exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp h

theorem stdSymplecticBilinForm_mulVec {g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hg : g ∈ Matrix.symplecticGroup (Fin m) K) (v w : Fin m ⊕ Fin m → K) :
    TauCeti.stdSymplecticBilinForm K m (g *ᵥ v) (g *ᵥ w) =
      TauCeti.stdSymplecticBilinForm K m v w := by
  have hg' := SymplecticGroup.mem_iff'.mp hg
  rw [TauCeti.stdSymplecticBilinForm_apply, TauCeti.stdSymplecticBilinForm_apply]
  calc (g *ᵥ v) ⬝ᵥ Matrix.J (Fin m) K *ᵥ (g *ᵥ w)
      = v ⬝ᵥ (gᵀ * Matrix.J (Fin m) K * g) *ᵥ w := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v gᵀ,
          Matrix.vecMul_transpose]
    _ = v ⬝ᵥ Matrix.J (Fin m) K *ᵥ w := by rw [hg']

theorem exists_symplectic_weight_basis {p : ℕ} [hpF : Fact p.Prime] (hpK : (p : K) ≠ 0)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {E : Subgroup (GL (Fin m ⊕ Fin m) K)} [Finite E]
    (hESp : E ≤ LargeEvenSpGroup K m) (hE : IsElemAbelian p E) :
    ∃ P ∈ Matrix.symplecticGroup (Fin m) K, ∃ u : Fin m → E →* Kˣ, ∀ a : E,
      ((a : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * P =
        P * Matrix.diagonal fun x => ((pairedUnits fun i => u i a) x : K) := by
  classical
  let _ : CommGroup E := { (inferInstance : Group ↥E) with mul_comm := hE.1.is_comm.comm }
  set ρ : E →* Module.End K (Fin m ⊕ Fin m → K) := glToEnd.comp E.subtype with hρ
  have : NeZero p := ⟨hpF.out.ne_zero⟩
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  have : HasEnoughRootsOfUnity K p := ⟨⟨_, hprim⟩, rootsOfUnity.isCyclic K p⟩
  have : HasEnoughRootsOfUnity K (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (hE.2 a a.2))
  have hcard : IsUnit (Nat.card E : K) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hE)
    rw [hk, Nat.cast_pow]
    exact (IsUnit.mk0 _ hpK).pow k
  have hW := TauCeti.iSup_iInf_eigenspace_unitHom_eq_top_of_commGroup (ρ := ρ) hcard
  set W : (E →* Kˣ) → Submodule K (Fin m ⊕ Fin m → K) :=
    fun χ => ⨅ g, (ρ g).eigenspace (χ g) with hWdef
  have hmemW : ∀ {χ : E →* Kˣ} {v : Fin m ⊕ Fin m → K}, v ∈ W χ →
      ∀ g : E, ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
        ((χ g : Kˣ) : K) • v := by
    intro χ v hv g
    have := (Submodule.mem_iInf _).mp hv g
    rw [Module.End.mem_eigenspace_iff] at this
    exact this
  set B := TauCeti.stdSymplecticBilinForm K m with hB
  have horth : ∀ χ ψ : E →* Kˣ, ψ ≠ χ⁻¹ → ∀ v ∈ W χ, ∀ w ∈ W ψ, B v w = 0 := by
    intro χ ψ hne v hv w hw
    by_contra hvw
    apply hne
    ext g
    have hgSp := mem_symplecticGroup_of_mem_sp (hESp g.2)
    have h1 := stdSymplecticBilinForm_mulVec hgSp v w
    rw [hmemW hv g, hmemW hw g, LinearMap.map_smul₂, LinearMap.map_smul, smul_smul] at h1
    have h2 : ((χ g : Kˣ) : K) * ((ψ g : Kˣ) : K) = 1 := by
      have := mul_right_cancel₀ hvw (h1.trans (one_mul (B v w)).symm)
      exact this
    have h3 : χ g * ψ g = 1 := Units.ext (by rw [Units.val_mul, h2, Units.val_one])
    rw [MonoidHom.inv_apply, eq_inv_of_mul_eq_one_right h3]
  obtain ⟨m', b, hb, hbW⟩ :=
    (TauCeti.isAlt_stdSymplecticBilinForm K m).exists_basis_toMatrix_eq_J_of_iSup_eq_top
      (TauCeti.stdSymplecticBilinForm_nondegenerate K m) (W := W) (σ := fun χ => χ⁻¹)
      (fun χ => inv_inv χ) hW horth
  obtain rfl : m = m' := by
    have hcard := (Module.finrank_eq_card_basis b).symm.trans
      (Module.finrank_fintype_fun_eq_card K)
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  choose s hs using hbW
  have hbB (x y : Fin m ⊕ Fin m) : B (b x) (b y) = Matrix.J (Fin m) K x y := by
    rw [← LinearMap.BilinForm.toMatrix_apply b, hb]
  have hpair (i : Fin m) : s (Sum.inr i) = (s (Sum.inl i))⁻¹ := by
    by_contra hne
    have h0 := horth _ _ hne _ (hs (Sum.inl i)) _ (hs (Sum.inr i))
    rw [hbB] at h0
    simp [Matrix.J] at h0
  refine ⟨(Pi.basisFun K _).toMatrix b, ?_, fun i => s (Sum.inl i), fun a => ?_⟩
  · rw [SymplecticGroup.mem_iff']
    have hJ : LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin m ⊕ Fin m)) B =
        Matrix.J (Fin m) K := by
      ext x y
      rw [LinearMap.BilinForm.toMatrix_apply, hB, TauCeti.stdSymplecticBilinForm_apply]
      simp [Pi.basisFun_apply, mulVec_single, single_dotProduct]
    have hPJ := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K _) b B
    rwa [hJ, hb] at hPJ
  · ext i x
    have hx := congr_fun (hmemW (hs x) a) i
    have hsx : (pairedUnits (fun i => s (Sum.inl i) a) x : Kˣ) = s x a := by
      rcases x with x | x
      · rfl
      · simp only [pairedUnits, Sum.elim_inr]
        rw [hpair x, MonoidHom.inv_apply]
    rw [Matrix.mul_diagonal, hsx, Matrix.mul_apply, mul_comm]
    simpa [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply] using hx

theorem exists_symplectic_weight_basis_GL {p : ℕ} [Fact p.Prime] (hpK : (p : K) ≠ 0)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {E : Subgroup (GL (Fin m ⊕ Fin m) K)} [Finite E]
    (hESp : E ≤ LargeEvenSpGroup K m) (hE : IsElemAbelian p E) :
    ∃ P : GL (Fin m ⊕ Fin m) K, P ∈ LargeEvenSpGroup K m ∧ ∃ u : Fin m → E →* Kˣ, ∀ a : E,
      (a : GL (Fin m ⊕ Fin m) K) * P = P * TauCeti.diagGL (pairedUnits fun i => u i a) := by
  obtain ⟨P, hP, u, hu⟩ := exists_symplectic_weight_basis hpK hζo hESp hE
  refine ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin m) K ⟨P, hP⟩, ?_, u, fun a => ?_⟩
  · apply mem_sp_of_mem_symplecticGroup
    rw [TauCeti.GLSymplectic.coe_ofSymplecticGroup]
    exact hP
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, TauCeti.GLSymplectic.coe_ofSymplecticGroup,
      TauCeti.diagGL_coe]
    exact hu a

theorem weight_pow_eq_one {p : ℕ} {E : Subgroup (GL (Fin m ⊕ Fin m) K)} (hE : IsElemAbelian p E)
    (χ : E →* Kˣ) (a : E) : χ a ^ p = 1 := by
  rw [← map_pow, show a ^ p = 1 from Subtype.ext (hE.2 a a.2), map_one]

theorem card_le_of_isElemAbelian_sp [Finite K] {p : ℕ} [hpF : Fact p.Prime] (hpK : (p : K) ≠ 0)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {E : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hESp : E ≤ LargeEvenSpGroup K m) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ m := by
  classical
  obtain ⟨P, -, u, hu⟩ := exists_symplectic_weight_basis_GL hpK hζo hESp hE
  have : NeZero p := ⟨hpF.out.ne_zero⟩
  set φ : E → Fin m → rootsOfUnity p K :=
    fun a i => ⟨u i a, (mem_rootsOfUnity p _).mpr (weight_pow_eq_one hE (u i) a)⟩ with hφ
  have hφi : Function.Injective φ := by
    intro a a' h
    have hi : ∀ i, u i a = u i a' := fun i => congrArg Subtype.val (congrFun h i)
    have h1 : (a : GL (Fin m ⊕ Fin m) K) * P = (a' : GL (Fin m ⊕ Fin m) K) * P := by
      rw [hu a, hu a']
      congr 3
      funext i
      exact hi i
    exact Subtype.ext (mul_right_cancel h1)
  calc Nat.card E ≤ Nat.card (Fin m → rootsOfUnity p K) := Nat.card_le_card_of_injective φ hφi
    _ = Nat.card (rootsOfUnity p K) ^ m := by rw [Nat.card_fun, Nat.card_fin]
    _ ≤ p ^ m := Nat.pow_le_pow_left (card_rootsOfUnity K p) m

theorem exists_conj_eq_range_spTorusGL [Finite K] {p : ℕ} [hpF : Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {E : Subgroup (GL (Fin m ⊕ Fin m) K)} (hESp : E ≤ LargeEvenSpGroup K m)
    (hE : IsElemAbelian p E) (hcard : p ^ m ≤ Nat.card E) :
    ∃ P : GL (Fin m ⊕ Fin m) K, P ∈ LargeEvenSpGroup K m ∧
      E.map (MulAut.conj P⁻¹).toMonoidHom = (spTorusGL (m := m) hζ).range := by
  classical
  have : NeZero p := ⟨hpF.out.ne_zero⟩
  obtain ⟨P, hP, u, hu⟩ := exists_symplectic_weight_basis_GL hpK hζo hESp hE
  refine ⟨P, hP, ?_⟩
  have hprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  have hle : E.map (MulAut.conj P⁻¹).toMonoidHom ≤ (spTorusGL (m := m) hζ).range := by
    rintro _ ⟨a, ha, rfl⟩
    have hk : ∀ i, ∃ k < p, ζ ^ k = u i ⟨a, ha⟩ := fun i =>
      hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p _).mpr
        (weight_pow_eq_one hE (u i) ⟨a, ha⟩))
    choose k _ hk using hk
    refine ⟨fun i => Multiplicative.ofAdd ((k i : ℕ) : ZMod p), ?_⟩
    rw [spTorusGL_apply]
    have h1 : (pairedUnits fun i => zmodPowHom hζ (Multiplicative.ofAdd ((k i : ℕ) : ZMod p))) =
        pairedUnits fun i => u i ⟨a, ha⟩ := by
      congr 1
      funext i
      rw [zmodPowHom_natCast, hk]
    rw [h1, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
      show a * P = P * TauCeti.diagGL (pairedUnits fun i => u i ⟨a, ha⟩) from hu ⟨a, ha⟩,
      inv_mul_cancel_left]
  have hinj : Function.Injective (spTorusGL (m := m) hζ) := by
    intro f f' h
    apply spTorus_injective hζ hζo (hpF.out.odd_of_ne_two hp2)
    rw [spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod,
    Nat.card_fin, ← Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj P⁻¹).injective).toEquiv]
  exact hcard

end TableBSymp

end CFSG.StandardType
