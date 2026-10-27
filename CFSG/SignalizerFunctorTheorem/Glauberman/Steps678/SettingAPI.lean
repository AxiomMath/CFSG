module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeCoreConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.WeakClosureConjugation

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

omit [Finite G] in
theorem isPGroup_actor (h : Setting p A θ) : IsPGroup p A :=
  elementary_abelian_isPGroup p A h.elementary

omit [Finite G] in
theorem large_one (h : Setting p A θ) : p ^ 1 ≤ Nat.card A :=
  (Nat.pow_le_pow_right h.prime.pos (by norm_num : 1 ≤ 3)).trans h.large

omit [Finite G] in
theorem large_two (h : Setting p A θ) : p ^ (1 + 1) ≤ Nat.card A :=
  (Nat.pow_le_pow_right h.prime.pos (by norm_num : 1 + 1 ≤ 3)).trans h.large

omit [Finite G] in
theorem large_sq (h : Setting p A θ) : p ^ 2 ≤ Nat.card A :=
  (Nat.pow_le_pow_right h.prime.pos (by norm_num : 2 ≤ 3)).trans h.large

theorem coprime_card (h : Setting p A θ) {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) : Nat.Coprime p (Nat.card X) :=
  signalizer_subgroup_coprime p 1 h.prime A h.elementary (large_one h) θ h.conditions.coprime X
    hX.1 hX.2

theorem prime_support (h : Setting p A θ) {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ Nat.card X) :
    ℓ = 2 ∨ ℓ = 3 := by
  obtain ⟨S, hS, hdS⟩ := signalizer_compatible_prime_support p 1 ℓ h.prime hℓ A h.elementary
    (large_two h) θ h.conditions.coprime X hX hd
  have hmem : ℓ ∈ signalizerSpectrum p 1 A θ := ⟨hℓ, S, hS, hdS⟩
  rw [h.spectrum] at hmem
  simpa using hmem

omit [Finite G] in
theorem actor_ne (h : Setting p A θ) {ℓ : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3) : p ≠ ℓ := by
  intro hpl
  have hmem : p ∈ signalizerSpectrum p 1 A θ := by
    rw [h.spectrum]
    rcases hℓ with rfl | rfl <;> simp [hpl]
  exact signalizer_spectrum_prime_excluded p 1 h.prime A θ h.conditions.coprime hmem

theorem prime_of_two_or_three {q : ℕ} (hq : q = 2 ∨ q = 3) : q.Prime := by
  rcases hq with rfl | rfl
  exacts [Nat.prime_two, Nat.prime_three]

omit [Finite G] in
theorem mem_spectrum (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    q ∈ signalizerSpectrum p 1 A θ := by
  rw [h.spectrum]
  rcases hq with rfl | rfl <;> simp

theorem support_two_three (h : Setting p A θ) {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) {q r : ℕ} (hqr : (q = 2 ∧ r = 3) ∨ (q = 3 ∧ r = 2)) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ℓ = q ∨ ℓ = r := by
  intro ℓ hℓ hd
  rcases prime_support h hX hℓ hd with rfl | rfl <;> rcases hqr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp

omit [Finite G] in
theorem compat_of_le {X Y : Subgroup G} (hX : solvableSignalizerCompatible p 1 A θ X)
    (hYX : Y ≤ X) (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    solvableSignalizerCompatible p 1 A θ Y :=
  solvable_signalizer_compatible_of_le p 1 A θ X Y hX hYX hY

omit [Finite G] in
theorem compat_value (h : Setting p A θ) {S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    solvableSignalizerCompatible p 1 A θ (θ S) :=
  solvable_signalizer_value_compatible p 1 A θ h.conditions S hS

omit [Finite G] in
theorem isSolvable_of_compat {X : Subgroup G} (hX : solvableSignalizerCompatible p 1 A θ X) :
    Group.IsSolvable X :=
  hX.2

omit [Finite G] in
theorem commonFixed_le_value {S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    signalizerCommonFixed p 1 A θ ≤ θ S :=
  inf_le_right.trans ((iInf_le _ S).trans (iInf_le _ hS))

omit [Finite G] in
theorem commonFixed_le_centralizer :
    signalizerCommonFixed p 1 A θ ≤ Subgroup.centralizer (A : Set G) :=
  inf_le_left

omit [Finite G] in
theorem inf_centralizer_le_commonFixed {X : Subgroup G} (hX : signalizerCompatible p 1 A θ X) :
    X ⊓ Subgroup.centralizer (A : Set G) ≤ signalizerCommonFixed p 1 A θ := by
  refine le_inf inf_le_right ?_
  refine le_iInf fun S => le_iInf fun hS => ?_
  exact (inf_le_inf_left X (Subgroup.centralizer_le hS.1)).trans (hX.2 S hS)

omit [Finite G] in
theorem actor_le_normalizer_commonFixed :
    A ≤ Subgroup.normalizer (signalizerCommonFixed p 1 A θ : Set G) :=
  (Subgroup.le_centralizer_iff.mpr commonFixed_le_centralizer).trans
    (Subgroup.centralizer_le_normalizer _)

theorem compat_commonFixed (h : Setting p A θ) :
    solvableSignalizerCompatible p 1 A θ (signalizerCommonFixed p 1 A θ) := by
  obtain ⟨S, hS⟩ := signalizerFunctorEk_nonempty p 1 h.prime A h.elementary (large_one h)
  have : Group.IsSolvable (θ S) := h.conditions.solvable S hS
  refine ⟨⟨actor_le_normalizer_commonFixed, fun T hT => inf_le_left.trans
    (commonFixed_le_value hT)⟩, ?_⟩
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (commonFixed_le_value hS))

omit [Finite G] in
theorem compat_conj {X : Subgroup G} (hX : solvableSignalizerCompatible p 1 A θ X) {c : G}
    (hc : c ∈ signalizerCommonFixed p 1 A θ) :
    solvableSignalizerCompatible p 1 A θ (conjugateSubgroup c X) :=
  solvable_signalizer_compatible_conjugate p 1 A X θ hX ⟨c, hc⟩

omit [Finite G] in
theorem commonFixed_le_normalizer_value {S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    signalizerCommonFixed p 1 A θ ≤ Subgroup.normalizer (θ S : Set G) :=
  (commonFixed_le_value hS).trans Subgroup.le_normalizer

theorem normalizerCompletion_spec (h : Setting p A θ) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : solvableSignalizerCompatible p 1 A θ X) :
    solvableSignalizerCompatible p 1 A θ (signalizerNormalizerCompletion p 1 A θ X) ∧
      X ≤ signalizerNormalizerCompletion p 1 A θ X ∧
      signalizerNormalizerCompletion p 1 A θ X ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ Y : Subgroup G, signalizerCompatible p 1 A θ Y → Y ≤ Subgroup.normalizer (X : Set G) →
        Y ≤ signalizerNormalizerCompletion p 1 A θ X := by
  have hcomp : solvableSignalizerCompatible p 1 A θ (signalizerNormalizerCompletion p 1 A θ X) :=
    h.locallyComplete.1 X hX0 hX
  have hctrl := signalizer_normalizer_completion_control p 1 h.prime A X h.elementary
    (large_two h) θ h.conditions.coprime hX.1 hcomp.1
  refine ⟨hcomp, hctrl.2.1, ?_, hctrl.2.2.2⟩
  unfold signalizerNormalizerCompletion
  refine iSup₂_le fun S _ => ?_
  exact inf_le_right

theorem exists_maximal_ge {X : Subgroup G} (hX : solvableSignalizerCompatible p 1 A θ X) :
    ∃ M, Maximal (solvableSignalizerCompatible p 1 A θ) M ∧ X ≤ M := by
  obtain ⟨M, hXM, hM⟩ := Finite.exists_le_maximal (p := solvableSignalizerCompatible p 1 A θ)
    (a := X) hX
  exact ⟨M, hM, hXM⟩

theorem exists_maximal_prime (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3) :
    ∃ S, Maximal (signalizerPrimeCompatible p 1 q A θ) S ∧ S ≠ ⊥ := by
  have hq' : q.Prime := prime_of_two_or_three hq
  obtain ⟨-, S₀, hS₀, hdvd⟩ := mem_spectrum h hq
  obtain ⟨sylow, hnorm, hne⟩ := normalized_subgroup_invariant_sylow_nontrivial p q h.prime hq' A
    (θ S₀) (isPGroup_actor h) (h.conditions.normalized S₀ hS₀) (h.conditions.coprime S₀ hS₀) hdvd
  have hWq : IsPGroup q ((sylow : Subgroup (θ S₀)).map (θ S₀).subtype) :=
    sylow.isPGroup'.map _
  have hWcomp : signalizerCompatible p 1 A θ ((sylow : Subgroup (θ S₀)).map (θ S₀).subtype) :=
    signalizer_compatible_of_le p 1 A θ (compat_value h hS₀).1 (Subgroup.map_subtype_le _) hnorm
  obtain ⟨S, hWS, hS⟩ := Finite.exists_le_maximal
    (p := signalizerPrimeCompatible p 1 q A θ)
    (a := (sylow : Subgroup (θ S₀)).map (θ S₀).subtype) ⟨hWcomp, hWq⟩
  exact ⟨S, hS, fun hbot => hne (le_bot_iff.mp (hbot ▸ hWS))⟩

theorem compat_of_pGroup {q : ℕ} (hq : q.Prime) {X : Subgroup G} (hqX : IsPGroup q X)
    (hX : signalizerCompatible p 1 A θ X) : solvableSignalizerCompatible p 1 A θ X := by
  have : Fact q.Prime := ⟨hq⟩
  have := hqX.isNilpotent
  exact ⟨hX, inferInstance⟩

theorem exists_actor_sylow (h : Setting p A θ) {X V : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hX : signalizerCompatible p 1 A θ X) (hV : IsPGroup r V) (hVX : V ≤ X)
    (hVA : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ P : Subgroup G, V ≤ P ∧ IsSylowOf r P X ∧ A ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨sylow, hVle, hnorm⟩ := normalized_pgroup_actor_sylow_containing p r h.prime hr A X V
    (isPGroup_actor h) hX.1 (coprime_card h hX) hVX hV hVA
  exact ⟨(sylow : Subgroup X).map X.subtype, hVle, ⟨sylow, rfl⟩, hnorm⟩

theorem exists_conj_le_sylow (h : Setting p A θ) {X P V : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hX : signalizerCompatible p 1 A θ X) (hP : IsSylowOf r P X)
    (hPA : A ≤ Subgroup.normalizer (P : Set G)) (hV : IsPGroup r V) (hVX : V ≤ X)
    (hVA : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ c ∈ X ⊓ Subgroup.centralizer (A : Set G), conjugateSubgroup c V ≤ P := by
  obtain ⟨P', hVP', hP'X, hP'A⟩ := exists_actor_sylow h hr hX hV hVX hVA
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨s', rfl⟩ := hP'X
  obtain ⟨c, hc, hconj⟩ := normalized_sylows_conjugate_by_common_fixed p r h.prime hr A X
    (isPGroup_actor h) hX.1 (coprime_card h hX) s' s hP'A hPA
  refine ⟨c, hc, ?_⟩
  rw [← hconj]
  exact Subgroup.map_mono hVP'

theorem isSylowOf_of_maximal (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S X : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hX : signalizerCompatible p 1 A θ X) (hCA : signalizerCommonFixed p 1 A θ ≤ X) :
    IsSylowOf q (S ⊓ X) X := by
  have hq' : q.Prime := prime_of_two_or_three hq
  obtain ⟨c, sylow, hsyl, -⟩ := signalizer_prime_local_sylow p 1 q h.prime hq' (actor_ne h hq) A
    h.elementary h.large θ h.conditions.coprime h.conditions.normalized h.conditions.balanced S X
    hS hX
  have hcX : c.val ∈ X := hCA c.property
  have hconjX : conjugateSubgroup c.val X = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hcX)
  have hS' : IsSylowOf q (conjugateSubgroup c.val (S ⊓ X)) X := by
    have hEq : conjugateSubgroup c.val (S ⊓ X) = conjugateSubgroup c.val S ⊓ X := by
      change (S ⊓ X).map (MulAut.conj c.val).toMonoidHom = _
      rw [Subgroup.map_inf _ _ _ (MulAut.conj c.val).injective]
      change _ ⊓ conjugateSubgroup c.val X = _
      rw [hconjX]
    rw [hEq]
    exact ⟨sylow, hsyl⟩
  have hback := sylowOf_conj hq' hS' (X.inv_mem hcX)
  rw [conjugate_subgroup_inv_cancel] at hback
  exact hback

omit [Finite G] in
theorem le_normalizer_centralizer {B X : Subgroup G} (h : B ≤ Subgroup.normalizer (X : Set G)) :
    B ≤ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ b ∈ B, ∀ y ∈ Subgroup.centralizer (X : Set G),
      b * y * b⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : b⁻¹ * x * b ∈ X := by
      have := Subgroup.le_normalizer_iff.mp h b⁻¹ (B.inv_mem hb) x hx
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hy (b⁻¹ * x * b) hx'
    calc x * (b * y * b⁻¹) = b * ((b⁻¹ * x * b) * y) * b⁻¹ := by group
      _ = b * (y * (b⁻¹ * x * b)) * b⁻¹ := by rw [hc]
      _ = (b * y * b⁻¹) * x := by group
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key b hb y, fun hy => ?_⟩
  have := key b⁻¹ (B.inv_mem hb) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem actor_le_normalizer_of_le_commonFixed {P : Subgroup G}
    (hP : P ≤ signalizerCommonFixed p 1 A θ) : A ≤ Subgroup.normalizer (P : Set G) :=
  (Subgroup.le_centralizer_iff.mpr (hP.trans commonFixed_le_centralizer)).trans
    (Subgroup.centralizer_le_normalizer _)

theorem compat_of_le_commonFixed {q : ℕ} (hq : q.Prime) {P : Subgroup G} (hP : IsPGroup q P)
    (hPCA : P ≤ signalizerCommonFixed p 1 A θ) : solvableSignalizerCompatible p 1 A θ P :=
  compat_of_pGroup hq hP ⟨actor_le_normalizer_of_le_commonFixed hPCA, fun _ hS =>
    inf_le_left.trans (hPCA.trans (commonFixed_le_value hS))⟩

@[expose] def thetaCentralizer (p : ℕ) (A : Subgroup G) (θ : Subgroup G → Subgroup G)
    (P : Subgroup G) : Subgroup G :=
  signalizerNormalizerCompletion p 1 A θ P ⊓ Subgroup.centralizer (P : Set G)

omit [Finite G] in
theorem thetaCentralizer_le_centralizer (P : Subgroup G) :
    thetaCentralizer p A θ P ≤ Subgroup.centralizer (P : Set G) :=
  inf_le_right

omit [Finite G] in
theorem thetaCentralizer_le_normalizerCompletion (P : Subgroup G) :
    thetaCentralizer p A θ P ≤ signalizerNormalizerCompletion p 1 A θ P :=
  inf_le_left

theorem compat_thetaCentralizer (h : Setting p A θ) {P : Subgroup G} (hP0 : P ≠ ⊥)
    (hP : solvableSignalizerCompatible p 1 A θ P) :
    solvableSignalizerCompatible p 1 A θ (thetaCentralizer p A θ P) := by
  obtain ⟨hNC, -, -, -⟩ := normalizerCompletion_spec h hP0 hP
  exact compat_of_le hNC inf_le_left
    (normalizer_inf_of_le A _ _ hNC.1.1 (le_normalizer_centralizer hP.1.1))

theorem le_thetaCentralizer (h : Setting p A θ) {P Y : Subgroup G} (hP0 : P ≠ ⊥)
    (hP : solvableSignalizerCompatible p 1 A θ P) (hY : signalizerCompatible p 1 A θ Y)
    (hYC : Y ≤ Subgroup.centralizer (P : Set G)) : Y ≤ thetaCentralizer p A θ P := by
  obtain ⟨-, -, -, hmax⟩ := normalizerCompletion_spec h hP0 hP
  exact le_inf (hmax Y hY (hYC.trans (Subgroup.centralizer_le_normalizer _))) hYC

theorem thetaCentralizer_mono (h : Setting p A θ) {S F : Subgroup G} (hS0 : S ≠ ⊥)
    (hS : solvableSignalizerCompatible p 1 A θ S) (hF0 : F ≠ ⊥)
    (hF : solvableSignalizerCompatible p 1 A θ F) (hSF : S ≤ F) :
    thetaCentralizer p A θ F ≤ thetaCentralizer p A θ S :=
  le_thetaCentralizer h hS0 hS (compat_thetaCentralizer h hF0 hF).1
    (inf_le_right.trans (Subgroup.centralizer_le hSF))

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
