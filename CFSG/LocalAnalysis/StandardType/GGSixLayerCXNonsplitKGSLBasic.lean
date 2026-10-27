module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSL

public section

namespace CFSG.StandardType

namespace LinNonsplit

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts

section Commutant

variable {F : Type} [Field F] {n : ℕ}

theorem exists_piMat_commutant [Finite F] (A : Subgroup (GL (Fin n) F))
    (hA : (Nat.card A : F) ≠ 0) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra F (D i))
      (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
      (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) F),
      (∀ i, NeZero (d i)) ∧ Function.Injective Φ ∧
      (∀ X : Matrix (Fin n) (Fin n) F, X ∈ Set.range Φ ↔
        ∀ g ∈ A, X * (g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) * X) ∧
      Function.Injective θ ∧ θ.range = Subgroup.centralizer (A : Set (GL (Fin n) F)) ∧
      ∀ w, ((θ w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
  have : NeZero (Nat.card A : F) := ⟨hA⟩
  have : Module.Finite (MonoidAlgebra F A) (rhoOf A).asModule :=
    Module.Finite.of_restrictScalars_finite F (MonoidAlgebra F A) (rhoOf A).asModule
  have : IsSemisimpleRing (Module.End (MonoidAlgebra F A) (rhoOf A).asModule) :=
    IsSemisimpleRing.moduleEnd (MonoidAlgebra F A) (rhoOf A).asModule
  have : Module.Finite F (Module.End (MonoidAlgebra F A) (rhoOf A).asModule) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ F (MonoidAlgebra F A) _ _ F)
      (LinearMap.restrictScalars_injective F)
  obtain ⟨r, D, d, _, _, _, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F
      (Module.End (MonoidAlgebra F A) (rhoOf A).asModule)
  have hfin : ∀ i, Finite (D i) := fun i => Module.finite_of_finite F
  let Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F :=
    ((LinearMap.toMatrixAlgEquiv' : Module.End F (Fin n → F) ≃ₐ[F] _).toAlgHom.comp
      (endRestrict A)).comp e.symm.toAlgHom
  have hΦinj : Function.Injective Φ :=
    (LinearMap.toMatrixAlgEquiv'.injective.comp (endRestrict_injective A)).comp e.symm.injective
  have hΦrange : ∀ X : Matrix (Fin n) (Fin n) F, X ∈ Set.range Φ ↔
      ∀ g ∈ A, X * (g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) * X := by
    intro X
    constructor
    · rintro ⟨y, rfl⟩ g hg
      have h := (mem_range_endRestrict A _).mp ⟨e.symm y, rfl⟩ ⟨g, hg⟩
      have h2 := congrArg (LinearMap.toMatrixAlgEquiv' : Module.End F (Fin n → F) ≃ₐ[F] _) h.eq
      rw [map_mul, map_mul, rhoOf_apply, ← Matrix.toLinAlgEquiv'_symm] at h2
      simpa [Φ] using h2
    · intro hX
      obtain ⟨f, hf⟩ := (mem_range_endRestrict A (Matrix.toLinAlgEquiv' X)).mpr fun g => by
        rw [rhoOf_apply]
        show _ * _ = _ * _
        rw [← map_mul, ← map_mul, hX g g.2]
      refine ⟨e f, ?_⟩
      show LinearMap.toMatrixAlgEquiv' (endRestrict A (e.symm (e f))) = X
      rw [e.symm_apply_apply, hf]
      exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' X
  refine ⟨r, D, d, fun i => littleWedderburn (D i), hfin, inferInstance, Φ,
    (Units.map Φ.toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom, hd, hΦinj, hΦrange, ?_, ?_,
    fun w => rfl⟩
  · exact (Units.map_injective (f := Φ.toMonoidHom) hΦinj).comp MulEquiv.piUnits.symm.injective
  · have hmem : ∀ X : GL (Fin n) F, X ∈ Subgroup.centralizer (A : Set (GL (Fin n) F)) →
        (X : Matrix (Fin n) (Fin n) F) ∈ Set.range Φ := fun X hX =>
      (hΦrange _).mpr fun g hg =>
        (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hX g hg)).symm
    ext X
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      apply Units.ext
      exact ((hΦrange _).mp ⟨_, rfl⟩ g hg).symm
    · intro hX
      obtain ⟨y, hy⟩ := hmem X hX
      obtain ⟨y', hy'⟩ := hmem X⁻¹ ((Subgroup.centralizer _).inv_mem hX)
      have h1 : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
      have h2 : y' * y = 1 := hΦinj (by rw [map_mul, hy, hy', Units.inv_mul, map_one])
      refine ⟨MulEquiv.piUnits ⟨y, y', h1, h2⟩, Units.ext ?_⟩
      show Φ ((MulEquiv.piUnits.symm (MulEquiv.piUnits ⟨y, y', h1, h2⟩) :
        (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))ˣ) : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
          = X
      rw [MulEquiv.symm_apply_apply]
      exact hy

end Commutant

theorem coprime_card_units {K : Type*} [Field K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K - 1) : (Nat.card Kˣ).Coprime p := by
  rw [Nat.card_units]
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK))

section Scalars

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem exists_pow_eq_scalar [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ} {x : G}
    (hx : x ^ p = 1) {A : GL (Fin (m + 1)) F} (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  have h1 := (LinFusion.ggInducedPairs ψ).pow_mem hA p
  rw [Prod.pow_mk, hx] at h1
  exact LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1

theorem exists_mem_ggInducedPairs_pow_eq_one [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F - 1) {x : G} (hx : x ^ p = 1)
    {A : GL (Fin (m + 1)) F} (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ A' : GL (Fin (m + 1)) F, (x, A') ∈ LinFusion.ggInducedPairs ψ ∧ A' ^ p = 1 := by
  obtain ⟨c, hc⟩ := exists_pow_eq_scalar hker hx hA
  obtain ⟨ν, hν⟩ := (Nat.Coprime.pow_left_bijective (coprime_card_units hp hpF)).2 c
  refine ⟨GeneralLinearGroup.scalar (Fin (m + 1)) ν⁻¹ * A, ?_, ?_⟩
  · have h := (LinFusion.ggInducedPairs ψ).mul_mem
      (LinTorus.one_scalar_mem_ggInducedPairs ψ ν⁻¹) hA
    rwa [Prod.mk_mul_mk, one_mul] at h
  · rw [(TypeA.PGLTor.commute_scalar ν⁻¹ A).mul_pow, hc, ← map_pow, ← map_mul, inv_pow]
    simp only at hν
    rw [hν, inv_mul_cancel, map_one]

theorem mul_comm_of_mem_ggInducedPairs [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F - 1) {x y : G} (hxy : x * y = y * x)
    {A B : GL (Fin (m + 1)) F} (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ)
    (hB : (y, B) ∈ LinFusion.ggInducedPairs ψ) (hAp : A ^ p = 1) : A * B = B * A := by
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).mul_mem hA hB)
    ((LinFusion.ggInducedPairs ψ).inv_mem ((LinFusion.ggInducedPairs ψ).mul_mem hB hA))
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h1
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
  set s := GeneralLinearGroup.scalar (Fin (m + 1)) c with hs
  have hconj : A * B * A⁻¹ = s * B := by
    calc A * B * A⁻¹ = A * B * (B * A)⁻¹ * B := by group
      _ = s * B := by rw [hc]
  have hiter : ∀ k : ℕ, A ^ k * B * (A ^ k)⁻¹ = s ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc A ^ (k + 1) * B * (A ^ (k + 1))⁻¹ = A * (A ^ k * B * (A ^ k)⁻¹) * A⁻¹ := by group
        _ = A * (s ^ k * B) * A⁻¹ := by rw [ih]
        _ = s ^ k * (A * B * A⁻¹) := by
          rw [hs, ← map_pow, ← mul_assoc A, ← TypeA.PGLTor.scalar_mul_comm]
          group
        _ = s ^ (k + 1) * B := by rw [hconj, pow_succ, mul_assoc]
  have hsp : s ^ p = 1 := by
    have h := hiter p
    rw [hAp, one_mul, inv_one, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hcp : c ^ p = 1 := by
    apply TypeA.PGLTor.scalar_injective (ι := Fin (m + 1))
    rw [map_pow, ← hs, hsp, map_one]
  have hco := orderOf_dvd_of_pow_eq_one hcp
  have hc1 : c = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (coprime_card_units hp hpF).symm hco (orderOf_dvd_natCard c)
  have hs1 : s = 1 := by rw [hs, hc1, map_one]
  calc A * B = A * B * (B * A)⁻¹ * (B * A) := by group
    _ = B * A := by rw [hc, hs1, one_mul]

theorem exists_eq_scalar_mul_zpow [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {x : G}
    {A : GL (Fin (m + 1)) F} (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ)
    {C : GL (Fin (m + 1)) F} (hC : C ∈ LinTorus.inducedMatrices ψ (Subgroup.zpowers x)) :
    ∃ (c : Fˣ) (k : ℤ), C = GeneralLinearGroup.scalar (Fin (m + 1)) c * A ^ k := by
  obtain ⟨e, he, heC⟩ := LinTorus.mem_inducedMatrices.mp hC
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  have hAk : (x ^ k, A ^ k) ∈ LinFusion.ggInducedPairs ψ :=
    (LinFusion.ggInducedPairs ψ).zpow_mem hA k
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem heC ((LinFusion.ggInducedPairs ψ).inv_mem hAk)
  rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h1
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_of_mem_ggInducedPairs_one hker h1
  exact ⟨c, k, by rw [← hc, inv_mul_cancel_right]⟩

theorem commute_of_mem_inducedMatrices [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {x : G}
    {A : GL (Fin (m + 1)) F} (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ)
    {M : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : Commute M (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    {C : GL (Fin (m + 1)) F} (hC : C ∈ LinTorus.inducedMatrices ψ (Subgroup.zpowers x)) :
    Commute M (C : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  obtain ⟨c, k, rfl⟩ := exists_eq_scalar_mul_zpow hker hA hC
  have h1 : Commute M ((A ^ k : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    hM.units_zpow_right k
  have h2 : Commute M ((GeneralLinearGroup.scalar (Fin (m + 1)) c : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    rw [GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) M).symm
  rw [Units.val_mul]
  exact h2.mul_right h1

theorem forall_mem_zpowers_exists {x : G} {A : GL (Fin (m + 1)) F}
    (hA : (x, A) ∈ LinFusion.ggInducedPairs ψ) :
    ∀ e ∈ Subgroup.zpowers x, ∃ C, (e, C) ∈ LinFusion.ggInducedPairs ψ := by
  intro e he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  exact ⟨A ^ k, (LinFusion.ggInducedPairs ψ).zpow_mem hA k⟩

end Scalars

section Blocks

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ b, Field (E b)] {d : ι → ℕ}

theorem eq_one_of_pow_eq_one_of_not_dvd {D : Type*} [Field D] [Finite D] {k : ℕ} (hk : 2 ≤ k)
    {p : ℕ} (hp : p.Prime) (hpS : ¬ p ∣ Nat.card (SpecialLinearGroup (Fin k) D))
    {g : GL (Fin k) D} (hg : g ^ p = 1) : g = 1 := by
  have hpD : ¬ p ∣ Nat.card D - 1 := fun h => hpS ((h.trans (Nat.sub_one_dvd_pow_sub_one _ 2)).trans
    (LayerPDiv.sq_sub_one_dvd_card_SL hk))
  have hdet : GeneralLinearGroup.det g = 1 := by
    have h1 : GeneralLinearGroup.det g ^ p = 1 := by rw [← map_pow, hg, map_one]
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (coprime_card_units hp hpD).symm
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  obtain ⟨s, hs⟩ : g ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) D →* _).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  have hsp : s ^ p = 1 := SpecialLinearGroup.toGL_injective (by rw [map_pow, hs, hg, map_one])
  have hs1 : s = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpS)
      (orderOf_dvd_of_pow_eq_one hsp) (orderOf_dvd_natCard s)
  rw [← hs, hs1, map_one]

theorem blockEmbed_mul_comm {w : PiGL E d} {b : ι} (hw : w b = 1)
    (s : SpecialLinearGroup (Fin (d b)) (E b)) :
    blockEmbed E d b s * w = w * blockEmbed E d b s := by
  funext i
  by_cases hi : i = b
  · subst hi
    simp [hw]
  · simp [blockEmbed_apply_of_ne hi]

theorem blockEmbed_mul_sub_one {w : PiGL E d} {b : ι} (hw : w b = 1)
    (s : SpecialLinearGroup (Fin (d b)) (E b)) :
    ((fun i => ((blockEmbed E d b s i : GL (Fin (d i)) (E i)) : Matrix (Fin (d i)) (Fin (d i)) (E i)))
      * ((fun i => ((w i : GL (Fin (d i)) (E i)) : Matrix (Fin (d i)) (Fin (d i)) (E i))) - 1) :
      Π i, Matrix (Fin (d i)) (Fin (d i)) (E i)) =
    (fun i => ((w i : GL (Fin (d i)) (E i)) : Matrix (Fin (d i)) (Fin (d i)) (E i))) - 1 := by
  funext i
  by_cases hi : i = b
  · subst hi
    simp [hw]
  · simp [blockEmbed_apply_of_ne hi]

end Blocks


section Unique

variable {F : Type} [Field F] {n : ℕ}

theorem eq_of_coord_eq_one {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ} [∀ i, Field (D i)]
    [∀ i, Algebra F (D i)] (hd : ∀ i, NeZero (d i))
    (Φ : (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
    (hΦinj : Function.Injective Φ) {B : Matrix (Fin n) (Fin n) F}
    (hrange : ∀ X : Matrix (Fin n) (Fin n) F, X * B = B * X → X ∈ Set.range Φ)
    {w : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)} (hw : Φ w = B) {j₁ j₂ : Fin r}
    (h₁ : w j₁ = 1) (h₂ : w j₂ = 1) : j₁ = j₂ := by
  classical
  by_contra hne
  set e₁ : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single j₁ 1 with he₁
  set e₂ : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := Pi.single j₂ 1 with he₂
  have hwe₁ : w * e₁ = e₁ := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁, h₁]
    · simp [he₁, hi]
  have he₂w : e₂ * w = e₂ := by
    funext i
    by_cases hi : i = j₂
    · subst hi
      simp [he₂, h₂]
    · simp [he₂, hi]
  have he₂₁ : e₂ * e₁ = 0 := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁, he₂, Ne.symm hne]
    · simp [he₁, hi]
  have he₁₁ : e₁ * e₁ = e₁ := by
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁]
    · simp [he₁, hi]
  have hcent : ∀ c, e₁ * c = c * e₁ := by
    intro c
    funext i
    by_cases hi : i = j₁
    · subst hi
      simp [he₁]
    · simp [he₁, hi]
  have hzero : ∀ M : Matrix (Fin n) (Fin n) F, Φ e₁ * M * Φ e₂ = 0 := by
    intro M
    have hXB : Φ e₁ * M * Φ e₂ * B = Φ e₁ * M * Φ e₂ := by
      rw [← hw, mul_assoc (Φ e₁ * M), ← map_mul, he₂w]
    have hBX : B * (Φ e₁ * M * Φ e₂) = Φ e₁ * M * Φ e₂ := by
      rw [← hw, ← mul_assoc, ← mul_assoc, ← map_mul, hwe₁]
    obtain ⟨c, hc⟩ := hrange _ (hXB.trans hBX.symm)
    calc Φ e₁ * M * Φ e₂ = Φ e₁ * (Φ e₁ * M * Φ e₂) := by
          rw [← mul_assoc, ← mul_assoc, ← map_mul, he₁₁]
      _ = Φ e₁ * Φ c := by rw [hc]
      _ = Φ c * Φ e₁ := by rw [← map_mul, ← map_mul, hcent]
      _ = Φ e₁ * M * Φ e₂ * Φ e₁ := by rw [hc]
      _ = 0 := by rw [mul_assoc (Φ e₁ * M), ← map_mul, he₂₁, map_zero, mul_zero]
  have hne₀ : ∀ j, (Pi.single j 1 : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≠ 0 := by
    intro j h
    have h1 := congrFun h j
    have := hd j
    simp at h1
  have hne₁ : Φ e₁ ≠ 0 := fun h => hne₀ j₁ (hΦinj (h.trans (map_zero Φ).symm))
  have hne₂ : Φ e₂ ≠ 0 := fun h => hne₀ j₂ (hΦinj (h.trans (map_zero Φ).symm))
  obtain ⟨a, k, hak⟩ : ∃ a k, Φ e₁ a k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₁ (Matrix.ext fun a k => h a k)
  obtain ⟨l, b, hlb⟩ : ∃ l b, Φ e₂ l b ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₂ (Matrix.ext fun l b => h l b)
  have h0 := congrFun (congrFun (hzero (Matrix.single k l 1)) a) b
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h0
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.zero_apply] at h0
    exact mul_ne_zero hak hlb h0
  · intro c _ hc
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ l) h

end Unique

section Core

variable {m : ℕ} {F : Type} [Field F] {r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ}
  [∀ i, Field (D i)]

theorem map_blockSL_le_range [∀ i, Finite (D i)] [∀ i, CharP (D i) 2]
    (θ : PiGL D d →* GL (Fin (m + 1)) F) {b : Fin r} (hb : GoodBlock D d b) :
    (blockSL D d b).map θ ≤
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →* _).range := by
  have hperf : ⁅blockSL D d b, blockSL D d b⁆ = blockSL D d b :=
    CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect (isPerfect_blockSL b hb.1 hb.2)
  rw [← hperf, Subgroup.map_commutator]
  refine (Subgroup.commutator_mono le_top le_top).trans ?_
  rw [← _root_.commutator_def, SpecialLinearGroup.range_toGL_eq_ker_det]
  exact Abelianization.commutator_subset_ker _

theorem isQuasisimple_comap_blockSL [∀ i, Finite (D i)] [∀ i, CharP (D i) 2]
    {θ : PiGL D d →* GL (Fin (m + 1)) F} (hθinj : Function.Injective θ) {b : Fin r}
    (hb : GoodBlock D d b) :
    CFSG.IsQuasisimple (((blockSL D d b).map θ).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →* _)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((Subgroup.equivMapOfInjective _ θ hθinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (map_blockSL_le_range θ hb))).symm).trans
        (Subgroup.equivMapOfInjective _ _ SpecialLinearGroup.toGL_injective).symm)
    (isQuasisimple_blockSL b hb.1 hb.2)

theorem conj_mem_comap_blockSL {θ : PiGL D d →* GL (Fin (m + 1)) F} {b : Fin r}
    {c s : SpecialLinearGroup (Fin (m + 1)) F} (hc : SpecialLinearGroup.toGL c ∈ θ.range)
    (hs : s ∈ ((blockSL D d b).map θ).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →* _)) :
    c * s * c⁻¹ ∈ ((blockSL D d b).map θ).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →* _) := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨g, hg, hgs⟩ := hs
  refine ⟨w * g * w⁻¹, conj_mem_blockSL b w hg, ?_⟩
  rw [map_mul, map_mul, map_inv, hw, hgs, map_mul, map_mul, map_inv]

theorem commutator_range_mulSingle_le (j : Fin r) :
    ⁅(MonoidHom.mulSingle (fun c => GL (Fin (d c)) (D c)) j).range,
      (MonoidHom.mulSingle (fun c => GL (Fin (d c)) (D c)) j).range⁆ ≤ blockSL D d j := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ (GeneralLinearGroup.det : GL (Fin (d j)) (D j) →* (D j)ˣ).ker := by
    refine Abelianization.commutator_subset_ker _ ?_
    rwa [_root_.commutator_def]
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hg'
  obtain ⟨s, rfl⟩ := hg'
  exact ⟨s, rfl⟩

theorem eq_bot_of_commutator_eq {X : Type*} [Group X] [Group.IsSolvable X] {H : Subgroup X}
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := X)
  have h : ∀ i, H ≤ derivedSeries X i := by
    intro i
    induction i with
    | zero => exact le_top
    | succ i ih =>
      rw [derivedSeries_succ, ← hH]
      exact Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hk ▸ h k)

end Core

theorem isComponentOf_map_of_le {L : Type*} [Group L] {G : Type*} [Group G] (ψ : L →* G)
    (hker : ψ.ker ≤ Subgroup.center L) {H : Subgroup G} {C₀ : Subgroup L}
    (hC₀H : C₀.map ψ ≤ H) (hnorm : ((C₀.map ψ).subgroupOf H).Normal) {S : Subgroup L}
    (hSC : S ≤ C₀) (hSn : ∀ c ∈ C₀, ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hSq : CFSG.IsQuasisimple S) :
    IsComponentOf (S.map ψ) H := by
  have hKq : CFSG.Assembly.IsQuasisimple (S.map ψ) := by
    refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_map hSq ψ fun hle => ?_)
    obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
    exact haa (Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle a.2)) a').symm)
  have hnormal : ((S.map ψ).subgroupOf (C₀.map ψ)).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨c, hc, hcg⟩ := g.2
    refine ⟨c * s * c⁻¹, hSn c hc s hs, ?_⟩
    simp only [map_mul, map_inv, hsx, hcg, Subgroup.coe_mul, Subgroup.coe_inv]
  exact ⟨(Subgroup.map_mono hSC).trans hC₀H,
    IsSubnormal.step (Subgroup.map_mono hSC) hnormal
      (IsSubnormal.step hC₀H hnorm (IsSubnormal.refl H)), hKq⟩

end LinNonsplit

end CFSG.StandardType
