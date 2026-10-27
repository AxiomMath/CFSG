module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenComponents

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley

section Conj

variable {G : Type*} [Group G]

theorem conj_mul_conj_eq_iff (m a b : G) :
    m * a * m⁻¹ * (m * b * m⁻¹) = m * b * m⁻¹ * (m * a * m⁻¹) ↔ a * b = b * a := by
  have e : ∀ x y : G, m * x * m⁻¹ * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := fun x y => by group
  rw [e, e]
  constructor
  · intro h
    have := congrArg (fun z => m⁻¹ * z * m) h
    simpa [mul_assoc] using this
  · intro h
    rw [h]

theorem conj_center_iff {P : Subgroup G} (m : G) {x : G} (hx : x ∈ P) :
    (∀ y ∈ P, m * x * m⁻¹ * (m * y * m⁻¹) = m * y * m⁻¹ * (m * x * m⁻¹)) ↔
      (⟨x, hx⟩ : P) ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hc y
    apply Subtype.ext
    exact ((conj_mul_conj_eq_iff m _ _).1 (hc y y.2)).symm
  · intro hc y hy
    exact (conj_mul_conj_eq_iff m _ _).2 (congrArg Subtype.val (hc ⟨y, hy⟩)).symm

end Conj

section Toral

variable {Ω : Type} [Field Ω]

theorem conj_toral {P Q : Subgroup (ModGL Tag.E6 Ω)}
    (h : ∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ Q, (∀ x ∈ P, h * z * x = x * (h * z)) →
      h * z ∈ torusGroup Tag.E6 Ω) (m h₀ z : ModGL Tag.E6 Ω) (hh : h₀ ∈ torusGroup Tag.E6 Ω)
    (hz : z ∈ Q) (hc : ∀ x ∈ P, m * (h₀ * z) * m⁻¹ * (m * x * m⁻¹) =
      m * x * m⁻¹ * (m * (h₀ * z) * m⁻¹)) :
    m * (h₀ * z) * m⁻¹ ∈ (fun g => m * g * m⁻¹) '' (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) :=
  ⟨h₀ * z, h h₀ hh z hz fun x hx => (conj_mul_conj_eq_iff m _ _).1 (hc x hx), rfl⟩

end Toral

theorem E6_even_supported_finite_layers_detect_full_module_commutants (Ω : Type) [Field Ω]
    [CharP Ω 2] [IsAlgClosed Ω] :
    (∀ D : E6EvenFixedRootDatum Ω,
      e6Commutant (D.orbitGroup : Set (ModGL Tag.E6 Ω)) =
        e6Commutant (D.rootGroup : Set (ModGL Tag.E6 Ω)) ∧
      (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ D.rootGroup,
        (∀ x ∈ D.orbitGroup, h * z * x = x * (h * z)) → h * z ∈ torusGroup Tag.E6 Ω) ∧
      (∀ x : D.orbitGroup, x ∈ Subgroup.center D.orbitGroup ↔
        (x : ModGL Tag.E6 Ω) ∈ D.torus ∧ ∀ α ∈ D.Ξ, torusRootChar (x : ModGL Tag.E6 Ω) α = 1) ∧
      D.torus = supportedTorus Tag.E6 Ω D.support ∧
      (∀ [Fintype D.support] (a : D.support → Ωˣ),
        a ∈ (supportedTorusHom Tag.E6 Ω D.support).ker ↔
          ∀ i : Fin Tag.E6.rank, ∏ j : D.support, a j ^ Tag.E6.cartan j i = 1) ∧
      (∀ m : ModGL Tag.E6 Ω,
        e6Commutant ((fun g => m * g * m⁻¹) '' (D.orbitGroup : Set (ModGL Tag.E6 Ω))) =
          e6Commutant ((fun g => m * g * m⁻¹) '' (D.rootGroup : Set (ModGL Tag.E6 Ω))) ∧
        (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ D.rootGroup, (∀ x ∈ D.orbitGroup,
          m * (h * z) * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * (h * z) * m⁻¹)) →
          m * (h * z) * m⁻¹ ∈
            (fun g => m * g * m⁻¹) '' (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω))) ∧
        ∀ x ∈ D.orbitGroup, ((∀ y ∈ D.orbitGroup,
          m * x * m⁻¹ * (m * y * m⁻¹) = m * y * m⁻¹ * (m * x * m⁻¹)) ↔
            x ∈ D.torus ∧ ∀ α ∈ D.Ξ, torusRootChar x α = 1))) ∧
    (∀ J : Set (Fin Tag.E6.rank), (J = e6QpSupport 12 ∨ J = e6QpSupport 13) →
      e6Delta J e6ε = e6ε' ∧ e6Delta J e6ε' = e6ε ∧
      ∀ f : ℕ, 2 ≤ f →
        e6Commutant (e6P24 Ω J f : Set (ModGL Tag.E6 Ω)) =
          e6Commutant (e6Q24 Ω : Set (ModGL Tag.E6 Ω)) ∧
        (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ e6Q24 Ω,
          (∀ x ∈ e6P24 Ω J f, h * z * x = x * (h * z)) → h * z ∈ torusGroup Tag.E6 Ω) ∧
        (∀ x : e6P24 Ω J f, x ∈ Subgroup.center (e6P24 Ω J f) ↔
          (x : ModGL Tag.E6 Ω) ∈ e6Q24 Ω ⊓ torusGroup Tag.E6 Ω ∧
            ∀ α ∈ parabolicRoots Tag.E6 e6Supp24, torusRootChar (x : ModGL Tag.E6 Ω) α = 1) ∧
        e6Q24 Ω ⊓ torusGroup Tag.E6 Ω = supportedTorus Tag.E6 Ω e6Supp24 ∧
        (∀ [Fintype e6Supp24] (a : e6Supp24 → Ωˣ),
          a ∈ (supportedTorusHom Tag.E6 Ω e6Supp24).ker ↔
            ∀ i : Fin Tag.E6.rank, ∏ j : e6Supp24, a j ^ Tag.E6.cartan j i = 1) ∧
        ∀ m : ModGL Tag.E6 Ω,
          e6Commutant ((fun g => m * g * m⁻¹) '' (e6P24 Ω J f : Set (ModGL Tag.E6 Ω))) =
            e6Commutant ((fun g => m * g * m⁻¹) '' (e6Q24 Ω : Set (ModGL Tag.E6 Ω))) ∧
          (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ e6Q24 Ω, (∀ x ∈ e6P24 Ω J f,
            m * (h * z) * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * (h * z) * m⁻¹)) →
            m * (h * z) * m⁻¹ ∈
              (fun g => m * g * m⁻¹) '' (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω))) ∧
          ∀ x ∈ e6P24 Ω J f, ((∀ y ∈ e6P24 Ω J f,
            m * x * m⁻¹ * (m * y * m⁻¹) = m * y * m⁻¹ * (m * x * m⁻¹)) ↔
              x ∈ e6Q24 Ω ⊓ torusGroup Tag.E6 Ω ∧
                ∀ α ∈ parabolicRoots Tag.E6 e6Supp24, torusRootChar x α = 1)) ∧
    (∀ J : Set (Fin Tag.E6.rank), J ≠ Set.univ → (∀ i, i ∈ J ↔ e6Rho i ∈ J) → ∀ f : ℕ, 2 ≤ f →
      (letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) →
      (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Ξ : ι → Set (Fin Tag.E6.rank → ℤ))
          (P : ι → Subgroup (ModGL Tag.E6 Ω)), Function.Injective Ξ ∧
          Set.range Ξ = e6ComponentOrbits J ∧ ∀ k, IsE6EvenFactor Ω J f (Ξ k) (P k)) ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Ξ : ι → Set (Fin Tag.E6.rank → ℤ))
        (P : ι → Subgroup (ModGL Tag.E6 Ω)), Function.Injective Ξ →
        Set.range Ξ = e6ComponentOrbits J → (∀ k, IsE6EvenFactor Ω J f (Ξ k) (P k)) →
        (∀ k l, k ≠ l → ∀ x ∈ P k, ∀ y ∈ P l, Commute x y) ∧
        ∃ μ : (∀ k, P k) →* ModGL Tag.E6 Ω,
          (∀ k (y : P k), μ (Pi.mulSingle k y) = y) ∧ μ.range = ⨆ k, P k ∧
          e6Commutant (μ.range : Set (ModGL Tag.E6 Ω)) =
            e6Commutant (rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 J) : Set (ModGL Tag.E6 Ω)) ∧
          (∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 J),
            (∀ x ∈ μ.range, h * z * x = x * (h * z)) → h * z ∈ torusGroup Tag.E6 Ω) ∧
          (∀ x : ∀ k, P k, μ x = 1 ↔ (∀ k, x k ∈ Subgroup.center (P k)) ∧
            ∀ i : Fin Tag.E6.rank, torusRootChar (μ x) (Pi.single i 1) = 1) ∧
          ∀ m : ModGL Tag.E6 Ω,
            e6Commutant ((fun g => m * g * m⁻¹) '' (μ.range : Set (ModGL Tag.E6 Ω))) =
              e6Commutant ((fun g => m * g * m⁻¹) ''
                (rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 J) : Set (ModGL Tag.E6 Ω))) ∧
            ∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 J),
              (∀ x ∈ μ.range,
                m * (h * z) * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * (h * z) * m⁻¹)) →
              m * (h * z) * m⁻¹ ∈
                (fun g => m * g * m⁻¹) '' (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω))) := by
  refine ⟨fun D => ?_, fun J hJ => ?_, fun J hJ hst f hf halg => ?_⟩
  ·
    have htor := fun h hh z hz hc =>
      D.mem_torusGroup_of_commute_orbitGroup (h := h) (z := z) hh hz hc
    refine ⟨D.e6Commutant_orbitGroup, htor, D.mem_center_orbitGroup_iff,
      D.torus_eq_supportedTorus, fun a => (supportedTorusHom Tag.E6 Ω D.support).mem_ker.trans
        (supportedTorusHom_eq_one_iff D.support a), fun m => ⟨e6Commutant_conj_eq
          D.e6Commutant_orbitGroup m, fun h hh z hz hc => conj_toral htor m h z hh hz hc,
            fun x hx => ?_⟩⟩
    rw [conj_center_iff m hx]
    exact D.mem_center_orbitGroup_iff ⟨x, hx⟩
  ·
    refine ⟨e6Delta_e6ε hJ, e6Delta_e6ε' hJ, fun f hf => ?_⟩
    have hC := e6Commutant_e6P24_subsystemGroup (Ω := Ω) hJ hf
    have htor : ∀ h ∈ torusGroup Tag.E6 Ω, ∀ z ∈ e6Q24 Ω,
        (∀ x ∈ e6P24 Ω J f, h * z * x = x * (h * z)) → h * z ∈ torusGroup Tag.E6 Ω :=
      fun h hh z hz hc => mem_torusGroup_of_commute_of_e6Commutant_eq hC hh
        ((e6Q24_eq_subsystemGroup Ω) ▸ hz) hc
    have hQT : e6Q24 Ω ⊓ torusGroup Tag.E6 Ω = supportedTorus Tag.E6 Ω e6Supp24 := by
      rw [e6Q24_eq_subsystemGroup, subsystemGroup_inf_torusGroup_eq_supportedTorus]
    have hZ : ∀ x : e6P24 Ω J f, x ∈ Subgroup.center (e6P24 Ω J f) ↔
        (x : ModGL Tag.E6 Ω) ∈ e6Q24 Ω ⊓ torusGroup Tag.E6 Ω ∧
          ∀ α ∈ parabolicRoots Tag.E6 e6Supp24, torusRootChar (x : ModGL Tag.E6 Ω) α = 1 := by
      intro x
      rw [mem_center_iff_of_e6Commutant_eq (e6P24_le_subsystemGroup f) hC]
      exact and_congr_left' ⟨fun h => ⟨e6P24_le_e6Q24 f x.2, h⟩, fun h => h.2⟩
    refine ⟨e6Commutant_e6P24 hJ f hf, htor, hZ, hQT,
      fun a => (supportedTorusHom Tag.E6 Ω e6Supp24).mem_ker.trans
        (supportedTorusHom_eq_one_iff e6Supp24 a),
      fun m => ⟨e6Commutant_conj_eq (e6Commutant_e6P24 hJ f hf) m,
        fun h hh z hz hc => conj_toral htor m h z hh hz hc, fun x hx => ?_⟩⟩
    rw [conj_center_iff m hx]
    exact hZ ⟨x, hx⟩
  ·
    obtain ⟨m₀, rfl⟩ := (gammaStable_iff_mem_e6QpSupport J).1 ⟨hJ, hst⟩
    refine ⟨?_, fun ι _ _ Ξ P hinj hrange hP => ?_⟩
    ·
      classical
      have hfin : (e6ComponentOrbits (e6QpSupport m₀)).Finite := by
        have : e6ComponentOrbits (e6QpSupport m₀) =
            (fun i => e6Xi (e6QpSupport m₀) i) '' e6QpSupport m₀ := by
          ext Ξ
          constructor
          · rintro ⟨i, hi, rfl⟩
            exact ⟨i, hi, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            exact ⟨i, hi, rfl⟩
        rw [this]
        exact (Set.toFinite _).image _
      have hex : ∀ Ξ : e6ComponentOrbits (e6QpSupport m₀), ∃ P,
          IsE6EvenFactor Ω (e6QpSupport m₀) f Ξ P := fun Ξ =>
        exists_isE6EvenFactor halg hJ hst hf Ξ.2
      choose P hP using hex
      exact ⟨e6ComponentOrbits (e6QpSupport m₀), hfin.fintype, inferInstance, Subtype.val, P,
        Subtype.val_injective, Subtype.range_coe, hP⟩
    ·
      have hmem : ∀ k, ∃ i ∈ e6QpSupport m₀, Ξ k = e6Xi (e6QpSupport m₀) i := fun k => by
        have : Ξ k ∈ Set.range Ξ := ⟨k, rfl⟩
        rw [hrange] at this
        exact this
      have hsep : ∀ k l, k ≠ l → IsSeparated (rootSetSupport (Ξ k)) (rootSetSupport (Ξ l)) := by
        intro k l hkl
        obtain ⟨i, hi, hik⟩ := hmem k
        obtain ⟨i', hi', hil⟩ := hmem l
        rw [hik, hil]
        exact isSeparated_rootSetSupport m₀ hi hi' (by rw [← hik, ← hil]; exact hinj.ne hkl)
      have hcover : e6QpSupport m₀ = ⋃ k, rootSetSupport (Ξ k) := by
        ext j
        rw [mem_iff_exists_rootSetSupport m₀ j, Set.mem_iUnion, ← hrange]
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, hj⟩
          exact ⟨k, hj⟩
        · rintro ⟨k, hj⟩
          exact ⟨_, ⟨k, rfl⟩, hj⟩
      obtain ⟨hcomm, μ, hμ1, hμ2, hμ3, hμ4, hμ5⟩ := e6_product_layers (e6QpSupport m₀)
        (fun k => rootSetSupport (Ξ k)) P hsep hcover (fun k => (hP k).le)
        (fun k => (hP k).e6Commutant_eq hf)
      rw [subsystemGroup_eq_rootSpan] at hμ3 hμ4
      exact ⟨hcomm, μ, hμ1, hμ2, hμ3, hμ4, hμ5, fun m => ⟨e6Commutant_conj_eq hμ3 m,
        fun h hh z hz hc => conj_toral (P := μ.range) hμ4 m h z hh hz hc⟩⟩

end CFSG.RankThree.Lattice
