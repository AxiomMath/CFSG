module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.FourSection

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

theorem setTranslate_one (H : Subgroup G) (O : Set (rightCosetSpace H)) :
    setTranslate H O 1 = O := by
  ext ω
  simp only [setTranslate, Set.mem_image, rightCosetTranslate_one, exists_eq_right]

theorem setTranslate_mul (H : Subgroup G) (O : Set (rightCosetSpace H)) (g k : G) :
    setTranslate H (setTranslate H O g) k = setTranslate H O (g * k) := by
  simp only [setTranslate, Set.image_image, rightCosetTranslate_mul]

theorem setTranslate_inv_cancel (H : Subgroup G) (O : Set (rightCosetSpace H)) (g : G) :
    setTranslate H (setTranslate H O g) g⁻¹ = O := by
  rw [setTranslate_mul, mul_inv_cancel, setTranslate_one]

theorem translate_mem_setTranslate {H : Subgroup G} {O : Set (rightCosetSpace H)}
    {ω : rightCosetSpace H} (hω : ω ∈ O) (g : G) :
    rightCosetTranslate H ω g ∈ setTranslate H O g :=
  ⟨ω, hω, rfl⟩

theorem setTranslate_injective (H : Subgroup G) (g : G) :
    Function.Injective (fun O : Set (rightCosetSpace H) => setTranslate H O g) := by
  intro O O' hOO'
  have h := congrArg (fun P => setTranslate H P g⁻¹) hOO'
  simpa only [setTranslate_inv_cancel] using h

theorem translate_inv_cancel (H : Subgroup G) (ω : rightCosetSpace H) (g : G) :
    rightCosetTranslate H (rightCosetTranslate H ω g) g⁻¹ = ω := by
  rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]

theorem translate_ne_base {H : Subgroup G} {ω : rightCosetSpace H}
    (hω : ω ≠ rightCosetMk H 1) {g : G} (hg : g ∈ H) :
    rightCosetTranslate H ω g ≠ rightCosetMk H 1 := by
  intro hωg
  apply hω
  rw [← translate_inv_cancel H ω g, hωg]
  exact (PairInvolutionFixedField.translate_base_iff H g⁻¹).mpr (H.inv_mem hg)

theorem conj_mem_of_normal {H A : Subgroup G} (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    {h : G} (hh : h ∈ H) {a : G} (ha : a ∈ A) : h * a * h⁻¹ ∈ A := by
  have hc := hAn.conj_mem ⟨a, hAH ha⟩ ha ⟨h, hh⟩
  exact hc

theorem conj_inv_mem_of_normal {H A : Subgroup G} (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    {h : G} (hh : h ∈ H) {a : G} (ha : a ∈ A) : h⁻¹ * a * h ∈ A := by
  simpa only [inv_inv] using conj_mem_of_normal hAH hAn (H.inv_mem hh) ha

theorem mem_rightOrbit_self (H A : Subgroup G) (ω : rightCosetSpace H) :
    ω ∈ rightOrbit H A ω :=
  ⟨1, A.one_mem, rightCosetTranslate_one H ω⟩

theorem translate_mem_rightOrbit {H A : Subgroup G} (ω : rightCosetSpace H) {a : G}
    (ha : a ∈ A) : rightCosetTranslate H ω a ∈ rightOrbit H A ω :=
  ⟨a, ha, rfl⟩

theorem rightOrbit_translate {H A : Subgroup G} (ω : rightCosetSpace H) {a : G} (ha : a ∈ A) :
    rightOrbit H A (rightCosetTranslate H ω a) = rightOrbit H A ω := by
  ext ω'
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, (rightCosetTranslate_mul H ω a b).symm⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨a⁻¹ * b, A.mul_mem (A.inv_mem ha) hb, ?_⟩
    rw [rightCosetTranslate_mul, mul_inv_cancel_left]

theorem rightOrbit_eq_of_mem {H A : Subgroup G} {ω ω' : rightCosetSpace H}
    (h : ω' ∈ rightOrbit H A ω) : rightOrbit H A ω' = rightOrbit H A ω := by
  obtain ⟨a, ha, rfl⟩ := h
  exact rightOrbit_translate ω ha

theorem setTranslate_rightOrbit {H A : Subgroup G} (ω : rightCosetSpace H) {g : G}
    (hg : ∀ a ∈ A, g⁻¹ * a * g ∈ A) (hg' : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    setTranslate H (rightOrbit H A ω) g = rightOrbit H A (rightCosetTranslate H ω g) := by
  ext ω'
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * a * g, hg a ha, ?_⟩
    dsimp only
    rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
    congr 1
    group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨rightCosetTranslate H ω (g * a * g⁻¹), ⟨_, hg' a ha, rfl⟩, ?_⟩
    dsimp only
    rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
    congr 1
    group

theorem setTranslate_rightOrbit_of_normal {H A : Subgroup G} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) {h : G} (hh : h ∈ H) (ω : rightCosetSpace H) :
    setTranslate H (rightOrbit H A ω) h = rightOrbit H A (rightCosetTranslate H ω h) :=
  setTranslate_rightOrbit ω (fun _ ha => conj_inv_mem_of_normal hAH hAn hh ha)
    (fun _ ha => conj_mem_of_normal hAH hAn hh ha)

theorem setTranslate_rightOrbit_of_mem {H A : Subgroup G} (ω : rightCosetSpace H) {a : G}
    (ha : a ∈ A) : setTranslate H (rightOrbit H A ω) a = rightOrbit H A ω := by
  rw [setTranslate_rightOrbit ω (fun b hb => A.mul_mem (A.mul_mem (A.inv_mem ha) hb) ha)
    (fun b hb => A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)), rightOrbit_translate ω ha]

theorem setTranslate_eq_of_mem_orbitsOffBase {H A : Subgroup G} {O : Set (rightCosetSpace H)}
    (hO : O ∈ orbitsOffBase H A) {a : G} (ha : a ∈ A) : setTranslate H O a = O := by
  obtain ⟨ω, -, rfl⟩ := hO
  exact setTranslate_rightOrbit_of_mem ω ha

theorem setTranslate_mem_orbitsOffBase {H A : Subgroup G} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) {h : G} (hh : h ∈ H) {O : Set (rightCosetSpace H)}
    (hO : O ∈ orbitsOffBase H A) : setTranslate H O h ∈ orbitsOffBase H A := by
  obtain ⟨ω, hω, rfl⟩ := hO
  exact ⟨rightCosetTranslate H ω h, translate_ne_base hω hh,
    setTranslate_rightOrbit_of_normal hAH hAn hh ω⟩

theorem rightOrbit_mem_orbitsOffBase {H A : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) : rightOrbit H A beta ∈ orbitsOffBase H A :=
  ⟨beta, hbeta, rfl⟩

theorem eq_one_of_translate_eq {H A : Subgroup G} {beta : rightCosetSpace H} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hAB : A ⊓ pairPointStabilizer H beta = ⊥)
    (htrans : ∀ ω, ω ≠ rightCosetMk H 1 → ∃ h ∈ H, rightCosetTranslate H beta h = ω)
    {ω : rightCosetSpace H} (hω : ω ≠ rightCosetMk H 1) {a : G} (ha : a ∈ A)
    (hfix : rightCosetTranslate H ω a = ω) : a = 1 := by
  obtain ⟨h, hh, rfl⟩ := htrans ω hω
  have hc : h * a * h⁻¹ ∈ A := conj_mem_of_normal hAH hAn hh ha
  have hcB : h * a * h⁻¹ ∈ pairPointStabilizer H beta := by
    refine ⟨?_, ?_⟩
    · rw [rightCosetStabilizer_base]
      exact hAH hc
    · change h * a * h⁻¹ ∈ rightCosetStabilizer H beta
      rw [mem_rightCosetStabilizer_iff, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul,
        hfix, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hbot : h * a * h⁻¹ ∈ A ⊓ pairPointStabilizer H beta := ⟨hc, hcB⟩
  rw [hAB, Subgroup.mem_bot] at hbot
  calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
    _ = 1 := by rw [hbot]; group

theorem card_rightOrbit {H A : Subgroup G} {ω : rightCosetSpace H}
    (hfree : ∀ a ∈ A, rightCosetTranslate H ω a = ω → a = 1) :
    Nat.card (rightOrbit H A ω) = Nat.card A := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun a : A => ⟨rightCosetTranslate H ω a, a, a.2, rfl⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h := congrArg
      (fun p : rightOrbit H A ω => rightCosetTranslate H (p : rightCosetSpace H) (b : G)⁻¹) hab
    simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h
    exact Subtype.ext (mul_inv_eq_one.mp (hfree _ (A.mul_mem a.2 (A.inv_mem b.2)) h))
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem card_orbitsOffBase_mul [Finite G] {H A : Subgroup G} (hAH : A ≤ H)
    (hfree : ∀ ω : rightCosetSpace H, ω ≠ rightCosetMk H 1 → ∀ a ∈ A,
      rightCosetTranslate H ω a = ω → a = 1) :
    Nat.card (orbitsOffBase H A) * Nat.card A = Nat.card (rightCosetSpace H) - 1 := by
  classical
  let Γ : Set (rightCosetSpace H) := {rightCosetMk H 1}ᶜ
  let π : Γ → orbitsOffBase H A := fun ω => ⟨rightOrbit H A ω.1, ω.1, ω.2, rfl⟩
  have hfiber : ∀ O : orbitsOffBase H A, Nat.card {ω : Γ // π ω = O} = Nat.card A := by
    rintro ⟨O, ω₀, hω₀, rfl⟩
    rw [← card_rightOrbit (hfree ω₀ hω₀)]
    apply Nat.card_congr
    exact
      { toFun := fun ω => ⟨ω.1.1, by
          have h := congrArg Subtype.val ω.2
          change rightOrbit H A ω.1.1 = rightOrbit H A ω₀ at h
          exact (Set.ext_iff.mp h ω.1.1).mp (mem_rightOrbit_self H A ω.1.1)⟩
        invFun := fun ω => ⟨⟨ω.1, by
          obtain ⟨a, ha, hωa⟩ := ω.2
          rw [← hωa]
          exact translate_ne_base hω₀ (hAH ha)⟩, Subtype.ext (rightOrbit_eq_of_mem ω.2)⟩
        left_inv := fun ω => rfl
        right_inv := fun ω => rfl }
  let : Fintype (orbitsOffBase H A) := Fintype.ofFinite _
  have hsum := Nat.card_congr (Equiv.sigmaFiberEquiv π)
  rw [Nat.card_sigma] at hsum
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [← Nat.card_eq_fintype_card] at hsum
  rw [hsum, Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]

theorem exists_setTranslate_eq {H A : Subgroup G} {beta : rightCosetSpace H} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal)
    (htrans : ∀ ω, ω ≠ rightCosetMk H 1 → ∃ h ∈ H, rightCosetTranslate H beta h = ω)
    {O : Set (rightCosetSpace H)} (hO : O ∈ orbitsOffBase H A) :
    ∃ h ∈ H, setTranslate H (rightOrbit H A beta) h = O := by
  obtain ⟨ω, hω, rfl⟩ := hO
  obtain ⟨h, hh, rfl⟩ := htrans ω hω
  exact ⟨h, hh, setTranslate_rightOrbit_of_normal hAH hAn hh beta⟩

theorem setTranslate_rightOrbit_eq_iff {H A : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) {g : G} (hg : g ∈ H) :
    setTranslate H (rightOrbit H A beta) g = rightOrbit H A beta ↔
      g ∈ A ⊔ pairPointStabilizer H beta := by
  have hBH : pairPointStabilizer H beta ≤ H := pairPointStabilizer_le_point H beta
  constructor
  · intro hfix
    rw [setTranslate_rightOrbit_of_normal hAH hAn hg] at hfix
    have hmem : rightCosetTranslate H beta g ∈ rightOrbit H A beta :=
      hfix ▸ mem_rightOrbit_self H A _
    obtain ⟨a, ha, hga⟩ := hmem
    have hb : g * a⁻¹ ∈ pairPointStabilizer H beta := by
      refine ⟨?_, ?_⟩
      · rw [rightCosetStabilizer_base]
        exact H.mul_mem hg (H.inv_mem (hAH ha))
      · change g * a⁻¹ ∈ rightCosetStabilizer H beta
        rw [mem_rightCosetStabilizer_iff, ← rightCosetTranslate_mul, ← hga,
          translate_inv_cancel]
    have hga' : g = g * a⁻¹ * a := by group
    rw [hga']
    exact (A ⊔ pairPointStabilizer H beta).mul_mem (Subgroup.mem_sup_right hb)
      (Subgroup.mem_sup_left ha)
  · intro hgAB
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAH hAn hBH hgAB
    have hbβ : rightCosetTranslate H beta b = beta :=
      (mem_rightCosetStabilizer_iff H beta b).mp hb.2
    rw [← setTranslate_mul, setTranslate_rightOrbit_of_mem beta ha,
      setTranslate_rightOrbit_of_normal hAH hAn (hBH hb), hbβ]

end CFSG.ShultStronglyClosedTI.FinalChain.FourSection
