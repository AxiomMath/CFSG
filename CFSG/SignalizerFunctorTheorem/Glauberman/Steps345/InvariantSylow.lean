module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Compat
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment
public import CFSG.LocalAnalysis.SignalizerFunctor.ProductFixedPoints
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem Setting.exists_invariant_sylow (h : Setting p A θ) {X V : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hX : signalizerCompatible p 1 A θ X) (hV : IsPGroup r V) (hVX : V ≤ X)
    (hVA : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ P : Subgroup G, V ≤ P ∧ IsSylowOf r P X ∧ A ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨S, hVS, hAS⟩ := normalized_pgroup_actor_sylow_containing p r h.prime hr A X V
    h.isPGroup hX.1 (h.coprime_card hX) hVX hV hVA
  exact ⟨(S : Subgroup X).map X.subtype, hVS, ⟨S, rfl⟩, hAS⟩

omit [Finite G] in
private theorem sylow_fixed_of_normalizer {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {r : ℕ} (S : Sylow r X)
    (hS : A ≤ Subgroup.normalizer (((S : Subgroup X).map X.subtype : Subgroup G) : Set G)) :
    let _action := conjugationAction A X hAX
    ∀ a : A, a • S = S := by
  intro _action
  refine (invariant_sylow_subgroup_iff (ActorType := A) r S).mpr fun a e he => ?_
  obtain ⟨s, hs, hse⟩ := Subgroup.le_normalizer_iff.mp hS a.1 a.2 (e : G)
    (Subgroup.mem_map_of_mem X.subtype he)
  have : a • e = s := Subtype.ext hse.symm
  rw [this]
  exact hs

omit [Finite G] in
private theorem conj_mem_of_smul_eq {X : Subgroup G} {r : ℕ} {S S' : Sylow r X} {g : X}
    (hg : g • S' = S) {s : X} (hs : s ∈ (S' : Subgroup X)) : g * s * g⁻¹ ∈ (S : Subgroup X) := by
  subst hg
  exact ⟨s, hs, rfl⟩

theorem Setting.exists_conj_le_sylow (h : Setting p A θ) {X P V : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hX : signalizerCompatible p 1 A θ X) (hP : IsSylowOf r P X)
    (hPA : A ≤ Subgroup.normalizer (P : Set G)) (hV : IsPGroup r V) (hVX : V ≤ X)
    (hVA : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ c ∈ X ⊓ Subgroup.centralizer (A : Set G), conjugateSubgroup c V ≤ P := by
  obtain ⟨P', hVP', ⟨S', rfl⟩, hP'A⟩ := h.exists_invariant_sylow hr hX hV hVX hVA
  obtain ⟨S, rfl⟩ := hP
  let _action := conjugationAction A X hX.1
  obtain ⟨g, hg, hfix⟩ := invariant_sylows_conjugate_by_fixed_element p r h.prime hr A
    h.isPGroup X (h.coprime_card hX) S' S (sylow_fixed_of_normalizer hX.1 S' hP'A)
    (sylow_fixed_of_normalizer hX.1 S hPA)
  refine ⟨g.1, ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, ?_⟩
  · have hga := hfix ⟨a, ha⟩
    have hga' := congrArg Subtype.val hga
    change a * (g : G) * a⁻¹ = g at hga'
    exact mul_inv_eq_iff_eq_mul.mp hga'
  · rintro - ⟨v, hv, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hVP' hv
    exact ⟨g * s * g⁻¹, conj_mem_of_smul_eq hg hs, rfl⟩

theorem Setting.isSylowOf_of_maximal (h : Setting p A θ) {q : ℕ} (hq : q.Prime)
    {S X : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hX : signalizerCompatible p 1 A θ X) (hSX : S ≤ X) : IsSylowOf q S X := by
  obtain ⟨P, hSP, hP, hAP⟩ := h.exists_invariant_sylow hq hX hS.prop.2 hSX hS.prop.1.1
  obtain ⟨Q, rfl⟩ := hP
  have hPX : (Q : Subgroup X).map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hle : (Q : Subgroup X).map X.subtype ≤ S :=
    hS.le_of_ge ⟨signalizer_compatible_of_le p 1 A θ hX hPX hAP, Q.isPGroup'.map X.subtype⟩ hSP
  exact ⟨Q, le_antisymm hle hSP⟩

theorem Setting.isSylowOf_inf_commonFixed (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S) :
    IsSylowOf q (S ⊓ signalizerCommonFixed p 1 A θ) (signalizerCommonFixed p 1 A θ) := by
  have hq' : q.Prime := by
    rcases hq with rfl | rfl
    exacts [Nat.prime_two, Nat.prime_three]
  obtain ⟨T, hT, -⟩ := signalizer_prime_local_sylow_of_common_normalizes p 1 q h.prime hq'
    (h.p_ne hq) A h.elementary h.large θ h.conditions.coprime h.conditions.normalized
    h.conditions.balanced S _ hS compatible_commonFixed Subgroup.le_normalizer
  exact ⟨T, hT⟩

theorem Setting.compatible_sup_of_permute (h : Setting p A θ) {X Y : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) (hY : signalizerCompatible p 1 A θ Y)
    (hperm : subgroupProduct X Y = ((X ⊔ Y : Subgroup G) : Set G)) :
    signalizerCompatible p 1 A θ (X ⊔ Y) := by
  refine ⟨(le_inf hX.1 hY.1).trans (Subgroup.inf_normalizer_le_normalizer_sup X Y), ?_⟩
  rintro S₀ hS₀ z ⟨hz, hzc⟩
  let _action := ambientConjugationAction S₀
  let _baseAction : MulAction S₀ G := _action.toMulAction
  have hfix : ∀ w : G, w ∈ Subgroup.centralizer (S₀ : Set G) ↔ ∀ s : S₀, s • w = w := by
    intro w
    constructor
    · intro hw s
      change (s : G) * w * (s : G)⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hw s.1 s.2)
    · intro hw
      refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
      have hws := hw ⟨s, hs⟩
      change s * w * s⁻¹ = w at hws
      exact mul_inv_eq_iff_eq_mul.mp hws
  have hdec : ∃ x ∈ X, ∃ y ∈ Y, x * y = z := by
    change z ∈ subgroupProduct X Y
    rw [hperm]
    exact hz
  obtain ⟨x, hx, y, hy, hxy, hxf, hyf⟩ := fixed_product_decomposition p h.prime S₀
    (elementary_abelian_isPGroup p S₀ (elementary_abelian_of_le p h.elementary hS₀.1)) G X Y
    (fun s e he => Subgroup.le_normalizer_iff.mp hX.1 s.1 (hS₀.1 s.2) e he)
    (fun s e he => Subgroup.le_normalizer_iff.mp hY.1 s.1 (hS₀.1 s.2) e he)
    ((h.coprime_card hX).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) z
    ((hfix z).mp hzc) hdec
  rw [← hxy]
  exact (θ S₀).mul_mem (hX.2 S₀ hS₀ ⟨hx, (hfix x).mpr hxf⟩)
    (hY.2 S₀ hS₀ ⟨hy, (hfix y).mpr hyf⟩)

end CFSG.SignalizerFunctorTheorem.Glauberman
