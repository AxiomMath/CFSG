module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank

public section

open Polynomial Module

namespace CFSG.StandardType

namespace NSFrame

variable {K : Type} [Field K] {ℓ : ℕ} {g : K[X]} [Fact (Irreducible g)]

theorem root_isPrimitiveRoot (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) :
    IsPrimitiveRoot (AdjoinRoot.root g) ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero (ℓ : AdjoinRoot g) := by
    refine ⟨fun h0 => hℓK ?_⟩
    have h1 : algebraMap K (AdjoinRoot g) (ℓ : K) = 0 := by rw [map_natCast]; exact h0
    exact (injective_iff_map_eq_zero _).mp (algebraMap K (AdjoinRoot g)).injective _ h1
  rw [← isRoot_cyclotomic_iff]
  have h1 := (AdjoinRoot.isRoot_root g).dvd (map_dvd (AdjoinRoot.of g) hgd)
  rwa [map_cyclotomic] at h1

theorem ker_aeval_le_of_dvd {V : Type} [AddCommGroup V] [Module K V] (x : Module.End K V)
    {P Q : K[X]} (h : P ∣ Q) : LinearMap.ker (aeval x P) ≤ LinearMap.ker (aeval x Q) := by
  obtain ⟨R, rfl⟩ := h
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [mul_comm, map_mul, Module.End.mul_apply, hv, map_zero]

theorem exists_pow_ker_ne_bot {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) {x : Module.End K V}
    (hx : x ^ ℓ = 1) (hx1 : x ≠ 1) :
    ∃ j : ℕ, LinearMap.ker (aeval (x ^ j) g) ≠ ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g', hg', hg'd, hker⟩ := OrdPNS.exists_irreducible_ker_ne_bot hℓ hx hx1
  have hζ := root_isPrimitiveRoot (g := g) hℓ hℓK hgd
  have : NeZero (ℓ : AdjoinRoot g) := hζ.neZero'
  have hdvd : g'.map (algebraMap K (AdjoinRoot g)) ∣ (X ^ ℓ - C (1 : AdjoinRoot g)) := by
    have h1 : g'.map (algebraMap K (AdjoinRoot g)) ∣ cyclotomic ℓ (AdjoinRoot g) := by
      rw [← map_cyclotomic ℓ (algebraMap K (AdjoinRoot g))]
      exact Polynomial.map_dvd _ hg'd
    rw [map_one]
    exact h1.trans (cyclotomic.dvd_X_pow_sub_one ℓ (AdjoinRoot g))
  have hne : (X ^ ℓ - C (1 : AdjoinRoot g)) ≠ 0 := X_pow_sub_C_ne_zero hℓ.pos 1
  have hspl := (X_pow_sub_one_splits hζ).of_dvd hne hdvd
  have hdeg : (g'.map (algebraMap K (AdjoinRoot g))).degree ≠ 0 := by
    rw [degree_map]
    exact (degree_pos_of_irreducible hg').ne'
  obtain ⟨a, ha⟩ := hspl.exists_eval_eq_zero hdeg
  rw [eval_map_algebraMap] at ha
  have haprim : IsPrimitiveRoot a ℓ := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic ℓ (algebraMap K (AdjoinRoot g)), IsRoot,
      eval_map_algebraMap]
    obtain ⟨R, hR⟩ := hg'd
    rw [hR, map_mul, ha, zero_mul]
  obtain ⟨j, -, hj⟩ := haprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨j, fun hbot => hker ?_⟩
  have hroot : aeval a (g.comp (X ^ j)) = 0 := by
    rw [aeval_comp, map_pow, aeval_X, hj, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hmin := minpoly.eq_of_irreducible hg' ha
  have hdvd' : g' ∣ g.comp (X ^ j) :=
    (Dvd.intro _ hmin).trans (minpoly.dvd K a hroot)
  have hle := ker_aeval_le_of_dvd x hdvd'
  rw [aeval_comp, map_pow, aeval_X, hbot] at hle
  exact le_bot_iff.mp hle

variable [Finite K]

theorem exists_lineFrame {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K) {y : Module.End K W}
    (hgy : aeval y g = 0) (T : Set (Module.End K W)) (hTc : ∀ x ∈ T, ∀ x' ∈ T, Commute x x')
    (hTy : ∀ x ∈ T, Commute x y) (hTp : ∀ x ∈ T, x ^ ℓ = 1) :
    ∃ (ι : Type) (_ : Fintype ι) (Φ : (ι → AdjoinRoot g) ≃ₗ[K] W),
      ∀ x ∈ T, ∃ k : ι → ℕ, ∀ u, x (Φ u) = Φ (fun i => AdjoinRoot.root g ^ k i * u i) := by
  have hg : Irreducible g := Fact.out
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hg0 : g ≠ 0 := hg.ne_zero
  set φ : AdjoinRoot g →ₐ[K] Module.End K W :=
    Ideal.Quotient.liftₐ (Ideal.span {g}) (aeval y) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hgy, mul_zero]) with hφ
  have hφmk : ∀ P : K[X], φ (AdjoinRoot.mk g P) = aeval y P := fun _ => rfl
  let : Module (AdjoinRoot g) W := Module.compHom W φ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot g) (v : W), l • v = φ l v := fun _ _ => rfl
  have : IsScalarTower K (AdjoinRoot g) W := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have : Module.Finite (AdjoinRoot g) W :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot g) W
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := root_isPrimitiveRoot hℓ hℓK hgd
  have hcommφ : ∀ x : Module.End K W, Commute x y → ∀ l, Commute x (φ l) := by
    intro x hx l
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective l
    rw [hφmk]
    exact (OrdPNS.commute_aeval hx.symm P).symm
  let toL : ∀ x : Module.End K W, Commute x y → Module.End (AdjoinRoot g) W := fun x hx =>
    { toFun := x
      map_add' := x.map_add
      map_smul' := fun l v => by
        rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply, (hcommφ x hx l).eq,
          Module.End.mul_apply] }
  have : Finite (Module.End K W) := Module.finite_of_finite K
  let fT : T → Module.End (AdjoinRoot g) W := fun x => toL x.1 (hTy x.1 x.2)
  have hfc : ∀ i j, Commute (fT i) (fT j) := fun i j =>
    LinearMap.ext fun v => LinearMap.congr_fun (hTc i.1 i.2 j.1 j.2).eq v
  have hfp : ∀ i, fT i ^ ℓ = 1 := fun i => LinearMap.ext fun v => by
    rw [Module.End.pow_apply, Module.End.one_apply]
    have h1 := LinearMap.congr_fun (hTp i.1 i.2) v
    rw [Module.End.pow_apply, Module.End.one_apply] at h1
    exact h1
  obtain ⟨b, μ, hb⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ fT hfc hfp
  have hμp : ∀ i k, μ i k ^ ℓ = 1 := by
    intro i k
    have h1 := OrdPNS.pow_apply_of_apply_eq_smul (hb i k) ℓ
    rw [hfp i, Module.End.one_apply] at h1
    have h2 : (μ i k ^ ℓ - 1) • b k = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (b.ne_zero k))
  refine ⟨Fin (finrank (AdjoinRoot g) W), inferInstance, b.equivFun.symm.restrictScalars K, ?_⟩
  intro x hx
  choose k hk using fun i => hζ.eq_pow_of_pow_eq_one (hμp ⟨x, hx⟩ i)
  refine ⟨k, fun u => ?_⟩
  simp only [LinearEquiv.restrictScalars_apply, Basis.equivFun_symm_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : x (u i • b i) = u i • x (b i) := (fT ⟨x, hx⟩).map_smul (u i) (b i)
  rw [h1, show x (b i) = fT ⟨x, hx⟩ (b i) from rfl, hb, smul_smul, (hk i).2, mul_comm]

theorem exists_blockFrame (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Module.End K V)) (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x')
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) :
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ)
      (Φ : ((ι → AdjoinRoot g) × (κ → K)) ≃ₗ[K] V),
      ∀ x ∈ S, ∃ k : ι → ℕ, ∀ u w,
        x (Φ (u, w)) = Φ (fun i => AdjoinRoot.root g ^ k i * u i, w) := by
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases hS1 : ∀ x ∈ S, x = 1
  · refine ⟨Empty, Fin (finrank K V), inferInstance, inferInstance,
      LinearEquiv.uniqueProd.trans (Module.finBasis K V).equivFun.symm,
      fun x hx => ⟨Empty.elim, fun u w => ?_⟩⟩
    rw [hS1 x hx, Module.End.one_apply]
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  simp only [not_forall] at hS1
  obtain ⟨x₀, hx₀S, hx₀1⟩ := hS1
  obtain ⟨j, hj⟩ := exists_pow_ker_ne_bot hℓ hℓK hgd (hSp x₀ hx₀S) hx₀1
  set y := x₀ ^ j with hy
  have hyp : y ^ ℓ = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, hSp x₀ hx₀S, one_pow]
  have hyS : ∀ x ∈ S, Commute y x := fun x hx => (hSc x₀ hx₀S x hx).pow_left j
  obtain ⟨h, hcompl, -⟩ := OrdPNS.isCompl_ker_aeval hℓ hℓK hyp (Fact.out) hgd
  set V₁ := LinearMap.ker (aeval y g) with hV₁
  set V₂ := LinearMap.ker (aeval y h) with hV₂
  have hm : ∀ x ∈ S, ∀ P : K[X], ∀ v ∈ LinearMap.ker (aeval y P),
      x v ∈ LinearMap.ker (aeval y P) := fun x hx P => OrdPNS.mapsTo_ker_aeval (hyS x hx) P
  let r₁ : S → Module.End K V₁ := fun x => x.1.restrict (hm x.1 x.2 g)
  let r₂ : S → Module.End K V₂ := fun x => x.1.restrict (hm x.1 x.2 h)
  have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
  have hpos : 0 < finrank K V₁ :=
    Nat.pos_of_ne_zero fun h0 => hj (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨ι₂, κ₂, _, _, Φ₂, hΦ₂⟩ := ih (finrank K V₂) (by omega) (Set.range r₂)
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      exact OrdPNS.restrict_commute' (hSc x.1 x.2 x'.1 x'.2) _ _)
    (by
      rintro _ ⟨x, rfl⟩
      exact OrdPNS.restrict_pow_eq_one (hSp x.1 x.2) _) rfl
  set y₁ : Module.End K V₁ := y.restrict (OrdPNS.mapsTo_ker_aeval (Commute.refl y) g) with hy₁
  have hgy₁ : aeval y₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
    rw [OrdPNS.coe_aeval_restrict_apply]
    exact w.2)
  obtain ⟨ι₁, _, Φ₁, hΦ₁⟩ := exists_lineFrame hℓ hℓK hgd hgy₁ (Set.range r₁)
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      exact OrdPNS.restrict_commute' (hSc x.1 x.2 x'.1 x'.2) _ _)
    (by
      rintro _ ⟨x, rfl⟩
      exact OrdPNS.restrict_commute' (hyS x.1 x.2).symm _ _)
    (by
      rintro _ ⟨x, rfl⟩
      exact OrdPNS.restrict_pow_eq_one (hSp x.1 x.2) _)
  set Φ : ((ι₁ ⊕ ι₂ → AdjoinRoot g) × (κ₂ → K)) ≃ₗ[K] V :=
    ((LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ K (AdjoinRoot g)).prodCongr
      (LinearEquiv.refl K (κ₂ → K))).trans ((LinearEquiv.prodAssoc K _ _ _).trans
      ((Φ₁.prodCongr Φ₂).trans (Submodule.prodEquivOfIsCompl V₁ V₂ hcompl))) with hΦ
  have hΦapp : ∀ u w, Φ (u, w) = (Φ₁ (u ∘ Sum.inl) : V) + (Φ₂ (u ∘ Sum.inr, w) : V) :=
    fun u w => rfl
  refine ⟨ι₁ ⊕ ι₂, κ₂, inferInstance, inferInstance, Φ, fun x hx => ?_⟩
  obtain ⟨k₁, hk₁⟩ := hΦ₁ (r₁ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨k₂, hk₂⟩ := hΦ₂ (r₂ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Sum.elim k₁ k₂, fun u w => ?_⟩
  have e₁ := congrArg Subtype.val (hk₁ (u ∘ Sum.inl))
  have e₂ := congrArg Subtype.val (hk₂ (u ∘ Sum.inr) w)
  rw [LinearMap.coe_restrict_apply] at e₁ e₂
  rw [hΦapp, hΦapp, map_add, e₁, e₂]
  rfl

end NSFrame

end CFSG.StandardType
