module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionOrbits

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.FourSection

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

theorem conjSet_one (S : Set G) : conjSet S 1 = S := by
  ext x
  simp only [conjSet, inv_one, one_mul, mul_one, Set.image_id']

theorem conjSet_mul (S : Set G) (g h : G) : conjSet (conjSet S g) h = conjSet S (g * h) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, ⟨y, hy, rfl⟩, by group⟩

theorem mem_conjSet {S : Set G} {x : G} (hx : x ∈ S) (g : G) : g⁻¹ * x * g ∈ conjSet S g :=
  ⟨x, hx, rfl⟩

theorem conjSet_eq_of_subset {D : Set G} {g : G} (h1 : conjSet D g ⊆ D)
    (h2 : conjSet D g⁻¹ ⊆ D) : conjSet D g = D := by
  refine Set.Subset.antisymm h1 fun d hd => ?_
  have hd' : g * d * g⁻¹ ∈ D := by
    simpa only [inv_inv] using h2 (mem_conjSet hd g⁻¹)
  exact ⟨g * d * g⁻¹, hd', by group⟩

theorem mem_involutionCoset_self (Q : Subgroup G) (u : G) : u ∈ involutionCoset Q u :=
  ⟨1, Q.one_mem, mul_one u⟩

theorem conjSet_involutionCoset_subset_of_fix {Q : Subgroup G} {u g : G}
    (hgQ : ∀ y ∈ Q, g⁻¹ * y * g ∈ Q) (hgu : g⁻¹ * u * g = u) :
    conjSet (involutionCoset Q u) g ⊆ involutionCoset Q u := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨g⁻¹ * y * g, hgQ y hy, ?_⟩
  calc u * (g⁻¹ * y * g) = (g⁻¹ * u * g) * (g⁻¹ * y * g) := by rw [hgu]
    _ = g⁻¹ * (u * y) * g := by group

theorem conjSet_involutionCoset_subset_of_inv {Q : Subgroup G} {u a : G}
    (haQ : ∀ y ∈ Q, a⁻¹ * y * a ∈ Q) (hua : u * a * u⁻¹ = a⁻¹) (ha2 : a ^ 2 ∈ Q) :
    conjSet (involutionCoset Q u) a ⊆ involutionCoset Q u := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [pow_two] at ha2
  refine ⟨a * a * (a⁻¹ * y * a), Q.mul_mem ha2 (haQ y hy), ?_⟩
  calc u * (a * a * (a⁻¹ * y * a)) = (u * a * u⁻¹) * u * y * a := by group
    _ = a⁻¹ * (u * y) * a := by rw [hua]; group

theorem conjSet_involutionCoset_eq_iff {H A B Q : Subgroup G} {u : G} (hQH : Q ≤ H)
    (hQn : (Q.subgroupOf H).Normal) (hQA : Q ≤ A) (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hBH : B ≤ H) (hinv : ∀ a ∈ A, u * a * u⁻¹ = a⁻¹)
    (hsq : ∀ a ∈ A, a ^ 2 ∈ Q) (hsurj : ∀ y ∈ Q, ∃ a ∈ A, a ^ 2 = y)
    (hBu : ∀ b ∈ B, b⁻¹ * u * b = u) (hCu : ∀ g ∈ H, g⁻¹ * u * g = u → g ∈ Q ⊔ B)
    {g : G} (hg : g ∈ H) :
    conjSet (involutionCoset Q u) g = involutionCoset Q u ↔ g ∈ A ⊔ B := by
  constructor
  · intro hstab
    have hmem : g⁻¹ * u * g ∈ involutionCoset Q u := by
      rw [← hstab]
      exact mem_conjSet (mem_involutionCoset_self Q u) g
    obtain ⟨y, hy, hyu⟩ := hmem
    obtain ⟨a, ha, rfl⟩ := hsurj y hy
    change u * a ^ 2 = g⁻¹ * u * g at hyu
    have hc : (g * a⁻¹)⁻¹ * u * (g * a⁻¹) = u := by
      calc (g * a⁻¹)⁻¹ * u * (g * a⁻¹) = a * (g⁻¹ * u * g) * a⁻¹ := by group
        _ = a * (u * a ^ 2) * a⁻¹ := by rw [hyu]
        _ = (a * (u * a * u⁻¹)) * u := by rw [pow_two]; group
        _ = u := by rw [hinv a ha]; group
    have hgaQB := hCu _ (H.mul_mem hg (H.inv_mem (hAH ha))) hc
    have hgaAB : g * a⁻¹ ∈ A ⊔ B := sup_le_sup_right hQA B hgaQB
    rw [show g = g * a⁻¹ * a by group]
    exact (A ⊔ B).mul_mem hgaAB (Subgroup.mem_sup_left ha)
  · intro hgAB
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAH hAn hBH hgAB
    have hQconj : ∀ k ∈ H, ∀ y ∈ Q, k⁻¹ * y * k ∈ Q := fun k hk y hy =>
      conj_inv_mem_of_normal hQH hQn hk hy
    have haΔ : conjSet (involutionCoset Q u) a = involutionCoset Q u := by
      refine conjSet_eq_of_subset
        (conjSet_involutionCoset_subset_of_inv (hQconj a (hAH ha)) (hinv a ha) (hsq a ha))
        (conjSet_involutionCoset_subset_of_inv (hQconj a⁻¹ (H.inv_mem (hAH ha)))
          ?_ (hsq a⁻¹ (A.inv_mem ha)))
      rw [hinv a⁻¹ (A.inv_mem ha)]
    have hbΔ : conjSet (involutionCoset Q u) b = involutionCoset Q u :=
      conjSet_eq_of_subset
        (conjSet_involutionCoset_subset_of_fix (hQconj b (hBH hb)) (hBu b hb))
        (conjSet_involutionCoset_subset_of_fix (hQconj b⁻¹ (H.inv_mem (hBH hb)))
          (hBu b⁻¹ (B.inv_mem hb)))
    rw [← conjSet_mul, haΔ, hbΔ]

theorem exists_bijOn_conjugates {H A : Subgroup G} {beta : rightCosetSpace H} {Δ : Set G}
    (hbeta : beta ≠ rightCosetMk H 1) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (htrans : ∀ ω, ω ≠ rightCosetMk H 1 → ∃ h ∈ H, rightCosetTranslate H beta h = ω)
    (hstab : ∀ g ∈ H, conjSet Δ g = Δ ↔
      setTranslate H (rightOrbit H A beta) g = rightOrbit H A beta) :
    ∃ f : Set G → Set (rightCosetSpace H),
      Set.BijOn f {D | ∃ h ∈ H, D = conjSet Δ h} (orbitsOffBase H A) ∧
      f Δ = rightOrbit H A beta ∧
      ∀ h ∈ H, ∀ D ∈ {D : Set G | ∃ h ∈ H, D = conjSet Δ h},
        f (conjSet D h) = setTranslate H (f D) h := by
  let f : Set G → Set (rightCosetSpace H) := fun D =>
    {ω | ∃ h ∈ H, D = conjSet Δ h ∧ ω ∈ setTranslate H (rightOrbit H A beta) h}
  have hf : ∀ h ∈ H, f (conjSet Δ h) = setTranslate H (rightOrbit H A beta) h := by
    intro h hh
    ext ω
    constructor
    · rintro ⟨h', hh', hD, hω⟩
      have h1 : conjSet Δ (h' * h⁻¹) = Δ := by
        rw [← conjSet_mul, ← hD, conjSet_mul, mul_inv_cancel, conjSet_one]
      have h2 := (hstab _ (H.mul_mem hh' (H.inv_mem hh))).mp h1
      have h3 : setTranslate H (rightOrbit H A beta) h' =
          setTranslate H (rightOrbit H A beta) h := by
        calc setTranslate H (rightOrbit H A beta) h'
            = setTranslate H (rightOrbit H A beta) (h' * h⁻¹ * h) := by
              rw [inv_mul_cancel_right]
          _ = setTranslate H (setTranslate H (rightOrbit H A beta) (h' * h⁻¹)) h :=
              (setTranslate_mul H _ _ _).symm
          _ = setTranslate H (rightOrbit H A beta) h := by rw [h2]
      rw [← h3]
      exact hω
    · intro hω
      exact ⟨h, hh, rfl, hω⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro D ⟨h, hh, rfl⟩
    rw [hf h hh]
    exact setTranslate_mem_orbitsOffBase hAH hAn hh (rightOrbit_mem_orbitsOffBase hbeta)
  · rintro D ⟨h, hh, rfl⟩ D' ⟨h', hh', rfl⟩ heq
    rw [hf h hh, hf h' hh'] at heq
    have h1 : setTranslate H (rightOrbit H A beta) (h * h'⁻¹) = rightOrbit H A beta := by
      rw [← setTranslate_mul, heq, setTranslate_inv_cancel]
    have h2 := (hstab _ (H.mul_mem hh (H.inv_mem hh'))).mpr h1
    calc conjSet Δ h = conjSet Δ (h * h'⁻¹ * h') := by rw [inv_mul_cancel_right]
      _ = conjSet (conjSet Δ (h * h'⁻¹)) h' := (conjSet_mul _ _ _).symm
      _ = conjSet Δ h' := by rw [h2]
  · intro O hO
    obtain ⟨h, hh, rfl⟩ := exists_setTranslate_eq hAH hAn htrans hO
    exact ⟨conjSet Δ h, ⟨h, hh, rfl⟩, hf h hh⟩
  · have h1 := hf 1 H.one_mem
    rwa [conjSet_one, setTranslate_one] at h1
  · rintro h hh D ⟨h₀, hh₀, rfl⟩
    rw [conjSet_mul, hf _ (H.mul_mem hh₀ hh), hf h₀ hh₀, setTranslate_mul]

theorem existsUnique_conjSet_eq {H X : Subgroup G} {Δ : Set G} {θ : Set (Set G)}
    {Λ : Set (Set (rightCosetSpace H))} {P₀ : Set (rightCosetSpace H)}
    {f : Set G → Set (rightCosetSpace H)} (hbij : Set.BijOn f θ Λ) (hfΔ : f Δ = P₀)
    (hΔθ : Δ ∈ θ) (hequiv : ∀ h ∈ H, ∀ D ∈ θ, f (conjSet D h) = setTranslate H (f D) h)
    (hθ : ∀ h ∈ H, ∀ D ∈ θ, conjSet D h ∈ θ) (hXH : X ≤ H)
    (hreg : ∀ O ∈ Λ, ∀ O' ∈ Λ, O ≠ P₀ → O' ≠ P₀ → ∃! x : X, setTranslate H O x = O')
    {D D' : Set G} (hD : D ∈ θ) (hD' : D' ∈ θ) (hDΔ : D ≠ Δ) (hD'Δ : D' ≠ Δ) :
    ∃! x : X, conjSet D x = D' := by
  have hne : ∀ E ∈ θ, E ≠ Δ → f E ≠ P₀ := fun E hE hEΔ hfE =>
    hEΔ (hbij.injOn hE hΔθ (hfE.trans hfΔ.symm))
  obtain ⟨x, hx, huniq⟩ := hreg _ (hbij.mapsTo hD) _ (hbij.mapsTo hD') (hne D hD hDΔ)
    (hne D' hD' hD'Δ)
  refine ⟨x, ?_, fun y hy => huniq y ?_⟩
  · apply hbij.injOn (hθ _ (hXH x.2) D hD) hD'
    rw [hequiv _ (hXH x.2) D hD, hx]
  · change conjSet D y = D' at hy
    rw [← hequiv _ (hXH y.2) D hD, hy]

theorem conjSet_eq_of_fixes {H : Subgroup G} {θ : Set (Set G)}
    {Λ : Set (Set (rightCosetSpace H))} {f : Set G → Set (rightCosetSpace H)}
    (hbij : Set.BijOn f θ Λ)
    (hequiv : ∀ h ∈ H, ∀ D ∈ θ, f (conjSet D h) = setTranslate H (f D) h)
    (hθ : ∀ h ∈ H, ∀ D ∈ θ, conjSet D h ∈ θ) {g : G} (hg : g ∈ H)
    (hfix : ∀ O ∈ Λ, setTranslate H O g = O) {D : Set G} (hD : D ∈ θ) : conjSet D g = D := by
  apply hbij.injOn (hθ g hg D hD) hD
  rw [hequiv g hg D hD, hfix _ (hbij.mapsTo hD)]

end CFSG.ShultStronglyClosedTI.FinalChain.FourSection
