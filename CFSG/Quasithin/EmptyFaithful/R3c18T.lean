module

public import CFSG.Quasithin.EmptyFaithful.R3c18P
public import CFSG.Quasithin.EmptyFaithful.R3c18F
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.PartTwo.KFacts.AutTriality

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts

@[expose] def D4Cl (p : ℕ) (x : ℤ) : Prop :=
  (p : ℤ) ∣ x - 1 ∨ (p : ℤ) ∣ x + 1 ∨ (p : ℤ) ∣ x ^ 2 + x + 1 ∨ (p : ℤ) ∣ x ^ 2 - x + 1

theorem D4Cl.of_pow {p : ℕ} (hp : p.Prime) {x : ℤ} (h : D4Cl p (x ^ p)) : D4Cl p x := by
  have : Fact p.Prime := ⟨hp⟩
  unfold D4Cl at h ⊢
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

section Shape

set_option linter.unusedSectionVars false


@[expose] def D4Class : Prop :=
  ∀ {f : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ f) → ∀ {p : ℕ}, p.Prime → 5 ≤ p →
    2 ≤ CFSG.pRank p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) → D4Cl p ((2 : ℤ) ^ f)

@[expose] def D4Rank : Prop :=
  ∀ {f : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ f) → ∀ {p : ℕ}, p.Prime → 5 ≤ p → D4Cl p ((2 : ℤ) ^ f) →
    2 ≤ CFSG.pRank p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

end Shape

section Orientation

set_option linter.unusedSectionVars false


theorem exists_std_orientation {k : Type} [Field k] [Finite k] {f₀ p : ℕ} (hp3 : ¬ 3 ∣ p)
    (hk : Nat.card k = 2 ^ (3 * f₀)) (σ₀ : k ≃+* k) (hσ₀3 : σ₀ ^ 3 = 1)
    (hσ₀ : ∀ x, σ₀ x = x ^ 2 ^ (p * f₀)) :
    ∃ σ' : k ≃+* k, (∀ x, σ' x = x ^ 2 ^ f₀) ∧
      Nonempty (↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 k σ'.toRingHom)) := by
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 1 := ⟨p / 3, by omega⟩
    refine ⟨σ₀, fun x => ?_, ⟨MulEquiv.refl _⟩⟩
    rw [hσ₀, hm, show (3 * m + 1) * f₀ = f₀ + m * (3 * f₀) by ring,
      pow_two_pow_add_mul hk x f₀ m]
  · obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 2 := ⟨p / 3, by omega⟩
    have hσ₀' : ∀ x, σ₀ x = x ^ 2 ^ (2 * f₀) := fun x => by
      rw [hσ₀, hm, show (3 * m + 2) * f₀ = 2 * f₀ + m * (3 * f₀) by ring,
        pow_two_pow_add_mul hk x (2 * f₀) m]
    refine ⟨σ₀ ^ 2, fun x => ?_, ?_⟩
    · rw [pow_two, RingAut.mul_apply, hσ₀', hσ₀', ← pow_mul, ← pow_add,
        show 2 * f₀ + 2 * f₀ = f₀ + 1 * (3 * f₀) by ring, pow_two_pow_add_mul hk x f₀ 1]
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
        triality_diagram_transposition_exchanges_field_orientations k σ₀ hσ₀3
      exact ⟨e⟩

end Orientation


section Embedding

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K]

theorem baseChangeGL_mem_graphFixed {σ δ : K ≃+* K}
    (hΓ : twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {g : ModGL TwistTag.D4.tag (fixSubfield δ)}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) :
    baseChangeGL (fixSubfield δ).subtype g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      entrywiseFixedGroup TwistTag.D4.tag δ := by
  have h := map_baseChangeGL_twistedFixedGroup_le TwistTag.D4 σ δ
    ⟨g, graphFixedRootGroup_le _ _ _ hg, rfl⟩
  rwa [hΓ] at h

@[expose] noncomputable def subfieldEmb {σ δ : K ≃+* K}
    (hΓ : twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) →*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ((baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype).comp
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).subtype).codRestrict _
    fun g => (baseChangeGL_mem_graphFixed hΓ g.2).1

theorem subfieldEmb_injective {σ δ : K ≃+* K}
    (hΓ : twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    Function.Injective (subfieldEmb (σ := σ) (δ := δ) hΓ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem fieldActor_subfieldEmb {σ δ : K ≃+* K}
    (hΓ : twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (g : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom)) :
    fieldActorHom (t := TwistTag.D4) σ δ (subfieldEmb hΓ g) = subfieldEmb hΓ g :=
  Subtype.ext (by
    rw [fieldActorHom_apply, coe_fieldActor]
    exact (mem_entrywiseFixedGroup.1 (baseChangeGL_mem_graphFixed hΓ g.2).2).2)

end Embedding


section Frame

set_option linter.unusedSectionVars false


@[expose] noncomputable def pFrameD4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hcls : D4Class)
    (hrk : D4Rank) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    PFrame p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (K ≃+* K) where
  fld := fieldActorHom (t := TwistTag.D4) σ
  fld_inter := fun c hc => (isInnerAut_fieldActor_iff hf hK hσ).1 hc
  conj_mem := fun α _ _ => by
    obtain ⟨g, δ, h⟩ := exists_conj_mul_fieldActor hf hK hσ α
    exact ⟨1, MulAut.conj g, ⟨g, rfl⟩, δ, by rw [h, inv_one, one_mul, mul_one]; rfl⟩
  sq := fun h2 c hc => by
    classical
    have : Fact p.Prime := ⟨hp⟩
    have : Fintype K := Fintype.ofFinite K
    have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨hpf3, hfix⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
      (by omega : 1 ≤ 3 * f) hK' c
    rw [hc] at hpf3 hfix
    have hp3 : ¬ 3 ∣ p := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
      omega
    have hpf : p ∣ f := by
      rcases (Nat.Prime.dvd_mul hp).1 hpf3 with h3 | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
      · exact h
    obtain ⟨f₀, hf₀⟩ := hpf
    have hp0 : 0 < p := hp.pos
    have hf₀1 : 1 ≤ f₀ := by
      rcases Nat.eq_zero_or_pos f₀ with h0 | h0
      · rw [h0, mul_zero] at hf₀
        omega
      · exact h0
    have hk₀ : Nat.card ↥(fixSubfield c) = 2 ^ (3 * f₀) := by
      rw [hfix, hf₀, show 3 * (p * f₀) = p * (3 * f₀) by ring, Nat.mul_div_cancel_left _ hp0]
    have hk₀' : Nat.card ↥(fixSubfield c) = (2 ^ f₀) ^ 3 := by rw [hk₀, ← pow_mul, mul_comm]
    have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun x => by
      rw [pow_iter_frob σ hσ 3 x, ← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    have hσ3pt : ∀ x, σ (σ (σ x)) = x := fun x => congrArg (fun ψ : K ≃+* K => ψ x) hσ3
    have hσ₀3 : fixSubfieldRestrict σ c ^ 3 = 1 := fixSubfieldRestrict_pow_eq_one c hσ3
    have hσ₀ : ∀ x : ↥(fixSubfield c), fixSubfieldRestrict σ c x = x ^ 2 ^ (p * f₀) := fun x =>
      Subtype.ext (by rw [coe_fixSubfieldRestrict, hσ, hf₀]; rfl)
    obtain ⟨σ', hσ', ⟨e⟩⟩ := exists_std_orientation hp3 hk₀ (fixSubfieldRestrict σ c) hσ₀3 hσ₀
    have hq : (2 : ℤ) ^ f = ((2 : ℤ) ^ f₀) ^ p := by rw [hf₀, mul_comm, pow_mul]
    have hcl : D4Cl p ((2 : ℤ) ^ f) := hcls σ hf hK hσ hp hp5 h2
    have hcl₀ : D4Cl p ((2 : ℤ) ^ f₀) := D4Cl.of_pow hp (by rw [← hq]; exact hcl)
    have : Finite (ModGL TwistTag.D4.tag ↥(fixSubfield c)) := finite_modGL
    have : Finite ↥(graphFixedRootGroup TwistTag.D4 ↥(fixSubfield c) σ'.toRingHom) :=
      Subtype.finite
    have : Finite ↥(graphFixedRootGroup TwistTag.D4 ↥(fixSubfield c)
        (fixSubfieldRestrict σ c).toRingHom) := Subtype.finite
    have hrk' : 2 ≤ CFSG.pRank p
        ↥(graphFixedRootGroup TwistTag.D4 ↥(fixSubfield c) σ'.toRingHom) :=
      hrk σ' hf₀1 hk₀' hσ' hp hp5 hcl₀
    have hrk₀ : 2 ≤ CFSG.pRank p ↥(graphFixedRootGroup TwistTag.D4 ↥(fixSubfield c)
        (fixSubfieldRestrict σ c).toRingHom) := by
      rw [pRank_congr hp.one_lt e]
      exact hrk'
    obtain ⟨E₀, hE₀, hE₀el⟩ := exists_sq_of_two_le_pRank hp hrk₀
    have hcharK : ringChar K = 2 := ringChar.eq K 2
    have hΓ := (even_triality_fixed_group_eq_root_group K hcharK σ hσ3pt).1
    refine ⟨E₀.map (subfieldEmb hΓ), ?_, CFSG.SectionRank.isElemAbelian_map hE₀el _, ?_⟩
    · rw [Subgroup.card_map_of_injective (subfieldEmb_injective hΓ), hE₀]
    · rintro _ ⟨y, -, rfl⟩
      exact fieldActor_subfieldEmb hΓ y

theorem qLiePRankFam_d4 (hcls : D4Class) (hrk : D4Rank) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) := by
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hf, hm⟩ hS2 hX
  obtain ⟨-, K, hKf, hKfin, hKcard, σ₀, hσ₀, ⟨e⟩⟩ := hm
  have hK : Nat.card K = (2 ^ f) ^ 3 := by rw [hKcard]; rfl
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := 3 * f) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨iso⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  let ψ : ↥S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans iso
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv ↥S ψ.toEquiv
  exact pframe_core hC ((pFrameD4 hp hp5 hcls hrk hf K hK σ hσ).ofMulEquiv hp.one_lt ψ) hS2 hX

end Frame

end R3c18

end CFSG.Quasithin
