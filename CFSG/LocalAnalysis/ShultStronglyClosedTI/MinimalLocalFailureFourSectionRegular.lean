module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSectionOrbits

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.FourSection

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

theorem setTranslate_rightOrbit_beta {H A : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) {b : G}
    (hb : b ∈ pairPointStabilizer H beta) :
    setTranslate H (rightOrbit H A beta) b = rightOrbit H A beta := by
  rw [setTranslate_rightOrbit_of_normal hAH hAn (pairPointStabilizer_le_point H beta hb),
    (mem_rightCosetStabilizer_iff H beta b).mp hb.2]

theorem setTranslate_ne_rightOrbit {H A : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) {b : G}
    (hb : b ∈ pairPointStabilizer H beta) {O : Set (rightCosetSpace H)}
    (hO : O ≠ rightOrbit H A beta) : setTranslate H O b ≠ rightOrbit H A beta := by
  intro hOb
  apply hO
  apply setTranslate_injective H b
  change setTranslate H O b = setTranslate H (rightOrbit H A beta) b
  rw [hOb, setTranslate_rightOrbit_beta hAH hAn hb]

theorem eq_one_of_mul_self_eq_one {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G}
    (hx : x ∈ X) (hxx : x * x = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
  have hX' : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hX'
    exact absurd (even_iff_two_dvd.mpr hX') (Nat.not_even_iff_odd.mpr hX)

theorem eq_rightOrbit_of_setTranslate_eq [Finite G] {H A : Subgroup G}
    {beta : rightCosetSpace H} (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) {x : G}
    (hxH : x ∈ H) (hcent : A ⊓ Subgroup.centralizer ({x} : Set G) = ⊥)
    (hfix : {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} =
      {rightCosetMk H 1, beta})
    {O : Set (rightCosetSpace H)} (hO : O ∈ orbitsOffBase H A)
    (hOx : setTranslate H O x = O) : O = rightOrbit H A beta := by
  obtain ⟨ω, hω, rfl⟩ := hO
  have hmem : rightCosetTranslate H ω x ∈ rightOrbit H A ω := by
    rw [← hOx]
    exact translate_mem_setTranslate (mem_rightOrbit_self H A ω) x
  obtain ⟨a₀, ha₀, hωa₀⟩ := hmem
  let F : A → A := fun b => ⟨(b : G) * (x⁻¹ * (b : G)⁻¹ * x),
    A.mul_mem b.2 (conj_inv_mem_of_normal hAH hAn hxH (A.inv_mem b.2))⟩
  have hFinj : Function.Injective F := by
    intro b b' hbb'
    have hF : (b : G) * (x⁻¹ * (b : G)⁻¹ * x) = (b' : G) * (x⁻¹ * (b' : G)⁻¹ * x) :=
      congrArg Subtype.val hbb'
    have hc : (b' : G)⁻¹ * b ∈ A ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem b'.2) b.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (b' : G)⁻¹ * b * x
          = x * ((b' : G)⁻¹ * ((b' : G) * (x⁻¹ * (b' : G)⁻¹ * x)) * x⁻¹ * b * x) := by group
        _ = x * ((b' : G)⁻¹ * ((b : G) * (x⁻¹ * (b : G)⁻¹ * x)) * x⁻¹ * b * x) := by rw [hF]
        _ = x * ((b' : G)⁻¹ * b) := by group
    rw [hcent, Subgroup.mem_bot] at hc
    exact Subtype.ext (inv_mul_eq_one.mp hc).symm
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hFinj ⟨a₀, ha₀⟩
  have hFb : (b : G) * (x⁻¹ * (b : G)⁻¹ * x) = a₀ := congrArg Subtype.val hb
  have hbfix : rightCosetTranslate H (rightCosetTranslate H ω b) x =
      rightCosetTranslate H ω b := by
    calc rightCosetTranslate H (rightCosetTranslate H ω b) x
        = rightCosetTranslate H (rightCosetTranslate H ω x) (x⁻¹ * b * x) := by
          rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
          congr 1
          group
      _ = rightCosetTranslate H (rightCosetTranslate H ω a₀) (x⁻¹ * b * x) := by rw [hωa₀]
      _ = rightCosetTranslate H ω b := by
          rw [rightCosetTranslate_mul, ← hFb]
          congr 1
          group
  have hfixmem : rightCosetTranslate H ω b ∈
      {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} := hbfix
  rw [hfix] at hfixmem
  rcases hfixmem with hα | hβ
  · exact absurd hα (translate_ne_base hω (hAH b.2))
  · rw [Set.mem_singleton_iff] at hβ
    rw [← rightOrbit_translate ω b.2, hβ]

theorem eq_one_of_setTranslate_eq [Finite G] {H A X : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) (hXH : X ≤ H)
    (hcent : ∀ x ∈ X, x ≠ 1 → A ⊓ Subgroup.centralizer ({x} : Set G) = ⊥)
    (hfix : ∀ x ∈ X, x ≠ 1 → {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} =
      {rightCosetMk H 1, beta})
    {x : G} (hx : x ∈ X) {O : Set (rightCosetSpace H)} (hO : O ∈ orbitsOffBase H A)
    (hOβ : O ≠ rightOrbit H A beta) (hOx : setTranslate H O x = O) : x = 1 := by
  by_contra hx1
  exact hOβ (eq_rightOrbit_of_setTranslate_eq hAH hAn (hXH hx) (hcent x hx hx1)
    (hfix x hx hx1) hO hOx)

theorem existsUnique_setTranslate_eq [Finite G] {H A X : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hXB : X ≤ pairPointStabilizer H beta)
    (hfreeX : ∀ x ∈ X, ∀ O ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      setTranslate H O x = O → x = 1)
    (hcard : Nat.card (orbitsOffBase H A) = Nat.card X + 1)
    {O O' : Set (rightCosetSpace H)} (hO : O ∈ orbitsOffBase H A)
    (hO' : O' ∈ orbitsOffBase H A) (hOβ : O ≠ rightOrbit H A beta)
    (hO'β : O' ≠ rightOrbit H A beta) : ∃! x : X, setTranslate H O x = O' := by
  let S : Set (Set (rightCosetSpace H)) := orbitsOffBase H A \ {rightOrbit H A beta}
  let Φ : X → S := fun x => ⟨setTranslate H O x,
    setTranslate_mem_orbitsOffBase hAH hAn (pairPointStabilizer_le_point H beta (hXB x.2)) hO,
    setTranslate_ne_rightOrbit hAH hAn (hXB x.2) hOβ⟩
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : setTranslate H O x = setTranslate H O y := congrArg Subtype.val hxy
    have h2 : setTranslate H O ((x : G) * (y : G)⁻¹) = O := by
      rw [← setTranslate_mul, h1, setTranslate_inv_cancel]
    have h3 := hfreeX _ (X.mul_mem x.2 (X.inv_mem y.2)) O hO hOβ h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hS : Nat.card S = Nat.card X := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (rightOrbit_mem_orbitsOffBase hbeta),
      ← Nat.card_coe_set_eq, hcard, Nat.add_sub_cancel]
  have hbij := hΦ.bijective_of_nat_card_le hS.le
  obtain ⟨x, hx⟩ := hbij.2 ⟨O', hO', hO'β⟩
  refine ⟨x, congrArg Subtype.val hx, fun y hy => hΦ ?_⟩
  rw [hx]
  exact Subtype.ext hy

theorem two_transitive_orbitsOffBase {H A X : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (htrans : ∀ ω, ω ≠ rightCosetMk H 1 → ∃ h ∈ H, rightCosetTranslate H beta h = ω)
    (hXB : X ≤ pairPointStabilizer H beta)
    (hreg : ∀ O ∈ orbitsOffBase H A, ∀ O' ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      O' ≠ rightOrbit H A beta → ∃ x ∈ X, setTranslate H O x = O') :
    ∀ O₁ ∈ orbitsOffBase H A, ∀ O₂ ∈ orbitsOffBase H A, ∀ O₃ ∈ orbitsOffBase H A,
      ∀ O₄ ∈ orbitsOffBase H A, O₁ ≠ O₂ → O₃ ≠ O₄ →
        ∃ h ∈ H, setTranslate H O₁ h = O₃ ∧ setTranslate H O₂ h = O₄ := by
  intro O₁ hO₁ O₂ hO₂ O₃ hO₃ O₄ hO₄ h12 h34
  obtain ⟨h₁, hh₁, rfl⟩ := exists_setTranslate_eq hAH hAn htrans hO₁
  obtain ⟨h₃, hh₃, rfl⟩ := exists_setTranslate_eq hAH hAn htrans hO₃
  have hback : ∀ (O : Set (rightCosetSpace H)) (g : G),
      setTranslate H (setTranslate H O g⁻¹) g = O := by
    intro O g
    rw [setTranslate_mul, inv_mul_cancel, setTranslate_one]
  have hP : ∀ (O : Set (rightCosetSpace H)) (g : G), g ∈ H → O ∈ orbitsOffBase H A →
      O ≠ setTranslate H (rightOrbit H A beta) g →
        setTranslate H O g⁻¹ ∈ orbitsOffBase H A ∧
          setTranslate H O g⁻¹ ≠ rightOrbit H A beta := by
    intro O g hg hO hne
    refine ⟨setTranslate_mem_orbitsOffBase hAH hAn (H.inv_mem hg) hO, fun heq => hne ?_⟩
    rw [← hback O g, heq]
  obtain ⟨hP₂, hP₂β⟩ := hP O₂ h₁ hh₁ hO₂ (Ne.symm h12)
  obtain ⟨hP₄, hP₄β⟩ := hP O₄ h₃ hh₃ hO₄ (Ne.symm h34)
  obtain ⟨x, hx, hxP⟩ := hreg _ hP₂ _ hP₄ hP₂β hP₄β
  refine ⟨h₁⁻¹ * x * h₃, H.mul_mem (H.mul_mem (H.inv_mem hh₁)
    (pairPointStabilizer_le_point H beta (hXB hx))) hh₃, ?_, ?_⟩
  · rw [setTranslate_mul, show h₁ * (h₁⁻¹ * x * h₃) = x * h₃ by group, ← setTranslate_mul,
      setTranslate_rightOrbit_beta hAH hAn (hXB hx)]
  · rw [show h₁⁻¹ * x * h₃ = h₁⁻¹ * (x * h₃) by group, ← setTranslate_mul, ← setTranslate_mul,
      hxP, hback]

theorem setTranslate_eq_of_commute {H A X : Subgroup G} {beta : rightCosetSpace H}
    (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal) (hXodd : Odd (Nat.card X))
    (hfreeX : ∀ x ∈ X, ∀ O ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      setTranslate H O x = O → x = 1)
    (hreg : ∀ O ∈ orbitsOffBase H A, ∀ O' ∈ orbitsOffBase H A, O ≠ rightOrbit H A beta →
      O' ≠ rightOrbit H A beta → ∃ x ∈ X, setTranslate H O x = O')
    {j : G} (hjB : j ∈ pairPointStabilizer H beta) (hj2 : j * j = 1)
    (hjX : ∀ x ∈ X, x * j = j * x) {O : Set (rightCosetSpace H)}
    (hO : O ∈ orbitsOffBase H A) : setTranslate H O j = O := by
  by_cases hOβ : O = rightOrbit H A beta
  · rw [hOβ]
    exact setTranslate_rightOrbit_beta hAH hAn hjB
  have hOj := setTranslate_mem_orbitsOffBase hAH hAn (pairPointStabilizer_le_point H beta hjB) hO
  have hOjβ := setTranslate_ne_rightOrbit hAH hAn hjB hOβ
  obtain ⟨x, hx, hxj⟩ := hreg O hO _ hOj hOβ hOjβ
  have hxx : setTranslate H O (x * x) = O := by
    calc setTranslate H O (x * x) = setTranslate H (setTranslate H O x) x :=
          (setTranslate_mul H O x x).symm
      _ = setTranslate H (setTranslate H O j) x := by rw [hxj]
      _ = setTranslate H O (j * x) := setTranslate_mul H O j x
      _ = setTranslate H O (x * j) := by rw [hjX x hx]
      _ = setTranslate H (setTranslate H O x) j := (setTranslate_mul H O x j).symm
      _ = setTranslate H (setTranslate H O j) j := by rw [hxj]
      _ = O := by rw [setTranslate_mul, hj2, setTranslate_one]
  have hx1 : x = 1 :=
    eq_one_of_mul_self_eq_one hXodd hx (hfreeX _ (X.mul_mem hx hx) O hO hOβ hxx)
  rw [← hxj, hx1, setTranslate_one]

end CFSG.ShultStronglyClosedTI.FinalChain.FourSection
