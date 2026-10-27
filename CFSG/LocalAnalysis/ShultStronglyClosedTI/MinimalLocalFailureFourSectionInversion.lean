module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionOrbits

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.FourSection

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G]

theorem mem_rightOrbit_of_fixed [Finite G] {H A Q : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hAH : A ≤ H) (hQA : Q ≤ A)
    (hfreeβ : ∀ a ∈ A, rightCosetTranslate H beta a = beta → a = 1)
    {j : G} (hjB : j ∈ pairPointStabilizer H beta) (hjQ : ∀ c ∈ Q, c * j = j * c)
    (hcard : Nat.card (rightFixedSet H j) = Nat.card Q + 1)
    {ω : rightCosetSpace H} (hω : ω ≠ rightCosetMk H 1)
    (hωj : rightCosetTranslate H ω j = ω) : ω ∈ rightOrbit H A beta := by
  let T : Set (rightCosetSpace H) := (fun c => rightCosetTranslate H beta c) '' (Q : Set G)
  have hTinj : Set.InjOn (fun c => rightCosetTranslate H beta c) (Q : Set G) := by
    intro c hc c' hc' hcc'
    change rightCosetTranslate H beta c = rightCosetTranslate H beta c' at hcc'
    have h1 : rightCosetTranslate H beta (c * c'⁻¹) = beta := by
      rw [← rightCosetTranslate_mul, hcc', translate_inv_cancel]
    exact mul_inv_eq_one.mp (hfreeβ _ (A.mul_mem (hQA hc) (A.inv_mem (hQA hc'))) h1)
  have hTcard : T.ncard = Nat.card Q := by
    rw [hTinj.ncard_image]
    exact (Nat.card_coe_set_eq (Q : Set G)).symm
  have hαT : rightCosetMk H 1 ∉ T := by
    rintro ⟨c, hc, hcα⟩
    exact translate_ne_base hbeta (hAH (hQA hc)) hcα
  have hsub : insert (rightCosetMk H 1) T ⊆ rightFixedSet H j := by
    rintro ω' (rfl | ⟨c, hc, rfl⟩)
    · exact (PairInvolutionFixedField.translate_base_iff H j).mpr
        (pairPointStabilizer_le_point H beta hjB)
    · change rightCosetTranslate H (rightCosetTranslate H beta c) j =
        rightCosetTranslate H beta c
      rw [rightCosetTranslate_mul, hjQ c hc, ← rightCosetTranslate_mul,
        (mem_rightCosetStabilizer_iff H beta j).mp hjB.2]
  have heq : insert (rightCosetMk H 1) T = rightFixedSet H j := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [Set.ncard_insert_of_notMem hαT, hTcard, ← Nat.card_coe_set_eq, hcard]
  have hωF : ω ∈ rightFixedSet H j := hωj
  rw [← heq] at hωF
  rcases hωF with hα | ⟨c, hc, rfl⟩
  · exact absurd hα hω
  · exact translate_mem_rightOrbit beta (hQA hc)

theorem inv_of_fixes_orbits [Finite G] {H A Q X : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hQA : Q ≤ A) (hXH : X ≤ H)
    (hfree : ∀ ω : rightCosetSpace H, ω ≠ rightCosetMk H 1 → ∀ a ∈ A,
      rightCosetTranslate H ω a = ω → a = 1)
    (hXQ : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1}, ∃ x ∈ X, x⁻¹ * a * x = b)
    {j : G} (hjB : j ∈ pairPointStabilizer H beta) (hj2 : j * j = 1)
    (hjQ : ∀ c ∈ Q, c * j = j * c)
    (hjΛ : ∀ O ∈ orbitsOffBase H A, setTranslate H O j = O)
    (hcard : Nat.card (rightFixedSet H j) = Nat.card Q + 1)
    (hΛ : ∃ O ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta)
    (φ : A →* Q) (hφ : ∀ a : A, (φ a : G) = (a : G) * j * (a : G)⁻¹ * j⁻¹)
    (hφker : φ.ker = Q.subgroupOf A) (hφsurj : Function.Surjective φ)
    (hφX : ∀ x ∈ X, ∀ a a' : A, (a' : G) = x * a * x⁻¹ → (φ a' : G) = x * φ a * x⁻¹)
    (ψ : A →* Q) (hψ : ∀ a : A, (ψ a : G) = (a : G) ^ 2) (hψker : ψ.ker = Q.subgroupOf A)
    (hψX : ∀ x ∈ X, ∀ a a' : A, (a' : G) = x * a * x⁻¹ → (ψ a' : G) = x * ψ a * x⁻¹) :
    ∀ a ∈ A, j * a * j⁻¹ = a⁻¹ := by
  have hjH : j ∈ H := pairPointStabilizer_le_point H beta hjB
  obtain ⟨O, ⟨ω, hω, rfl⟩, hOβ⟩ := hΛ
  have hmem : rightCosetTranslate H ω j ∈ rightOrbit H A ω := by
    rw [← hjΛ _ ⟨ω, hω, rfl⟩]
    exact translate_mem_setTranslate (mem_rightOrbit_self H A ω) j
  obtain ⟨a₀, ha₀, hωa₀⟩ := hmem
  have ha₀Q : a₀ ∉ Q := by
    intro ha₀Q
    obtain ⟨b, hb⟩ := hφsurj ⟨a₀, ha₀Q⟩
    have hb' : (b : G) * j * (b : G)⁻¹ * j⁻¹ = a₀ := by
      rw [← hφ b, hb]
    have hfixb : rightCosetTranslate H (rightCosetTranslate H ω b) j =
        rightCosetTranslate H ω b := by
      calc rightCosetTranslate H (rightCosetTranslate H ω b) j
          = rightCosetTranslate H (rightCosetTranslate H ω j) (j⁻¹ * b * j) := by
            rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
            congr 1
            group
        _ = rightCosetTranslate H (rightCosetTranslate H ω a₀) (j⁻¹ * b * j) := by
            rw [hωa₀]
        _ = rightCosetTranslate H ω b := by
            rw [rightCosetTranslate_mul, ← hb']
            congr 1
            calc (b : G) * j * (b : G)⁻¹ * j⁻¹ * (j⁻¹ * b * j)
                = b * j * (b : G)⁻¹ * (j * j)⁻¹ * b * j := by group
              _ = b * j * j := by rw [hj2, inv_one]; group
              _ = b := by rw [mul_assoc, hj2, mul_one]
    have hin := mem_rightOrbit_of_fixed hbeta hAH hQA (hfree beta hbeta) hjB hjQ hcard
      (translate_ne_base hω (hAH b.2)) hfixb
    apply hOβ
    rw [← rightOrbit_translate ω b.2, rightOrbit_eq_of_mem hin]
  have hfix₀ : rightCosetTranslate H ω (a₀ * (j⁻¹ * a₀ * j)) = ω := by
    calc rightCosetTranslate H ω (a₀ * (j⁻¹ * a₀ * j))
        = rightCosetTranslate H (rightCosetTranslate H ω a₀) (j⁻¹ * a₀ * j) :=
          (rightCosetTranslate_mul H ω _ _).symm
      _ = rightCosetTranslate H (rightCosetTranslate H ω j) (j⁻¹ * a₀ * j) := by rw [hωa₀]
      _ = rightCosetTranslate H ω (a₀ * j) := by
          rw [rightCosetTranslate_mul]
          congr 1
          group
      _ = rightCosetTranslate H (rightCosetTranslate H ω a₀) j :=
          (rightCosetTranslate_mul H ω _ _).symm
      _ = rightCosetTranslate H (rightCosetTranslate H ω j) j := by rw [hωa₀]
      _ = ω := by rw [rightCosetTranslate_mul, hj2, rightCosetTranslate_one]
  have hconj : j⁻¹ * a₀ * j = a₀⁻¹ := eq_inv_of_mul_eq_one_right
    (hfree ω hω _ (A.mul_mem ha₀ (conj_inv_mem_of_normal hAH hAn hjH ha₀)) hfix₀)
  have hφψ₀ : (φ ⟨a₀, ha₀⟩ : G) = (ψ ⟨a₀, ha₀⟩ : G) := by
    rw [hφ, hψ]
    change a₀ * j * a₀⁻¹ * j⁻¹ = a₀ ^ 2
    rw [← hconj, pow_two]
    group
  have hkerψ : ∀ a : A, (ψ a : G) = 1 → (a : G) ∈ Q := by
    intro a ha
    have hk : a ∈ ψ.ker := MonoidHom.mem_ker.mpr (Subtype.ext ha)
    rw [hψker] at hk
    exact hk
  have hkerφ : ∀ a : A, (a : G) ∈ Q → (φ a : G) = 1 := by
    intro a ha
    have hk : a ∈ φ.ker := by
      rw [hφker]
      exact ha
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  have hagree : ∀ a : A, (φ a : G) = (ψ a : G) := by
    intro a
    by_cases ha1 : (ψ a : G) = 1
    · rw [hkerφ a (hkerψ a ha1), ha1]
    have hψ₀1 : (ψ ⟨a₀, ha₀⟩ : G) ≠ 1 := fun h1 => ha₀Q (hkerψ _ h1)
    obtain ⟨x, hx, hxa⟩ := hXQ _ ⟨(ψ ⟨a₀, ha₀⟩).2, hψ₀1⟩ _ ⟨(ψ a).2, ha1⟩
    have hxinv : x⁻¹ ∈ X := X.inv_mem hx
    let a' : A := ⟨x⁻¹ * a₀ * x⁻¹⁻¹, conj_mem_of_normal hAH hAn (hXH hxinv) ha₀⟩
    have hψa' : (ψ a' : G) = ψ a := by
      rw [hψX x⁻¹ hxinv ⟨a₀, ha₀⟩ a' rfl, inv_inv, hxa]
    have hφa' : (φ a' : G) = ψ a := by
      rw [hφX x⁻¹ hxinv ⟨a₀, ha₀⟩ a' rfl, hφψ₀, inv_inv, hxa]
    have hdiff : (ψ (a'⁻¹ * a) : G) = 1 := by
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψa', inv_mul_cancel]
    have hφdiff := hkerφ _ (hkerψ _ hdiff)
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one] at hφdiff
    rw [← hφdiff, hφa']
  intro a ha
  have e : a * j * a⁻¹ * j⁻¹ = a ^ 2 := by
    have h := hagree ⟨a, ha⟩
    rw [hφ, hψ] at h
    exact h
  calc j * a * j⁻¹ = (a⁻¹ * (a * j * a⁻¹ * j⁻¹))⁻¹ := by group
    _ = (a⁻¹ * a ^ 2)⁻¹ := by rw [e]
    _ = a⁻¹ := by group

theorem eq_of_ne_one_of_inv {A Q J : Subgroup G} (hQA : Q < A)
    (hinv : ∀ j ∈ J, j ≠ 1 → ∀ a ∈ A, j * a * j⁻¹ = a⁻¹)
    (hcent : ∀ j ∈ J, j ≠ 1 → A ⊓ Subgroup.centralizer ({j} : Set G) = Q)
    {j k : G} (hj : j ∈ J) (hj1 : j ≠ 1) (hk : k ∈ J) (hk1 : k ≠ 1) : j = k := by
  by_contra hjk
  have hne : j * k⁻¹ ≠ 1 := fun h => hjk (mul_inv_eq_one.mp h)
  have hA : A ≤ A ⊓ Subgroup.centralizer ({j * k⁻¹} : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hinv k⁻¹ (J.inv_mem hk) (inv_ne_one.mpr hk1) a ha
    have h2 := hinv j hj hj1 a⁻¹ (A.inv_mem ha)
    rw [inv_inv] at h1 h2
    calc a * (j * k⁻¹) = (j * (k⁻¹ * a * k) * j⁻¹) * (j * k⁻¹) := by rw [h1, h2]
      _ = j * k⁻¹ * a := by group
  rw [hcent _ (J.mul_mem hj (J.inv_mem hk)) hne] at hA
  exact hQA.not_ge hA

end CFSG.ShultStronglyClosedTI.FinalChain.FourSection
