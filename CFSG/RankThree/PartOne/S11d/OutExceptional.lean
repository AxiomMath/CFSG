module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
  CFSG.ComponentClassification.UnbalancedCatalog

theorem outPNice_G2 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -, h3⟩, hm⟩ := h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f = 1 := by omega
    subst this
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hK
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_F4 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .F4 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf1 K hK
  have : NeZero (2 * f) := ⟨by omega⟩
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_E7E8_of_untwisted {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) (hf1 : 1 ≤ f) (hm : UntwistedChevalleyModel X τ (2 ^ f)) :
    OutPNice p X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf1 K hK τ hτ
  have hcard := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_E7 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .E7 2 f) : OutPNice p X :=
  outPNice_E7E8_of_untwisted hp .E7 (Or.inl rfl) h.1.2.1 h.2

theorem outPNice_E8 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .E8 2 f) : OutPNice p X :=
  outPNice_E7E8_of_untwisted hp .E8 (Or.inr rfl) h.1.2.1 h.2

theorem outPNice_trialityD4 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .D4 (2 ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .D4 Nat.prime_two hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, hord, -, -, ⟨E⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf1 K hcard σ' hσ'
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hord]; omega)
  exact OutPNice.of_mulEquiv (e.trans E) (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_twistedF4 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) : OutPNice p X := by
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier X 2 f ⟨hadm, a, hfa, hmodel⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
  have : Finite X := hX.1
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv _ E.toEquiv
  exact OutPNice.of_mulEquiv E (outPNice_of_isCyclic_outer hp hcyc)

theorem outPNice_Suzuki {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : SuzukiModel X 2 f) : OutPNice p X := by
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hcyc := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK').1
  have : Finite (suzukiGroup a K) := inferInstance
  exact OutPNice.of_mulEquiv e (outPNice_of_isCyclic_outer hp hcyc)

end CFSG.RankThree.PartOne.OutStructure
