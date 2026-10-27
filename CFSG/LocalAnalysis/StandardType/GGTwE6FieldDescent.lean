module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Descent
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.RecipeExcLang

theorem pow_two_pow_mul_odd {k : Type} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = (2 ^ m) ^ 2) {p : ℕ} (hp : Odd p) (c : k) :
    c ^ 2 ^ (m * p) = c ^ 2 ^ m := by
  obtain ⟨j, rfl⟩ := hp
  have : Fintype k := Fintype.ofFinite k
  have hc : Fintype.card k = (2 ^ m) ^ 2 := by rw [← Nat.card_eq_fintype_card, hk]
  rw [show 2 ^ (m * (2 * j + 1)) = 2 ^ m * ((2 ^ m) ^ 2) ^ j by ring, pow_mul, ← hc,
    FiniteField.pow_card_pow]

theorem charP_two_of_card_sq {k : Type} [Field k] [Finite k] {m : ℕ}
    (hk : Nat.card k = (2 ^ m) ^ 2) : CharP k 2 := by
  have : Fintype k := Fintype.ofFinite k
  exact charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul])

theorem fixSubfield_card_of_odd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (δ : K ≃+* K) (hδ : Odd (orderOf δ)) :
    orderOf δ ∣ n ∧ Nat.card (fixSubfield δ) = (2 ^ (n / orderOf δ)) ^ 2 := by
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, Nat.mul_comm]
  obtain ⟨hd, hc⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK' δ
  have hdn : orderOf δ ∣ n := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 hδ) hd
  refine ⟨hdn, ?_⟩
  rw [hc, Nat.mul_div_assoc 2 hdn, ← pow_mul, Nat.mul_comm 2]

theorem fixSubfieldRestrict_eq_pow {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K} {m p : ℕ}
    (hK₀ : Nat.card (fixSubfield δ) = (2 ^ m) ^ 2) (hp : Odd p)
    (hσ : ∀ c, σ c = c ^ 2 ^ (m * p)) (c : fixSubfield δ) :
    fixSubfieldRestrict σ δ c = c ^ 2 ^ m := by
  apply Subtype.ext
  rw [coe_fixSubfieldRestrict, hσ, ← pow_two_pow_mul_odd hK₀ hp c]
  exact (SubmonoidClass.coe_pow c _).symm

section Certs


theorem twistedE6InndiagGL_le_twInndiagGroup {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    twistedE6InndiagGL K σ ≤ twInndiagGroup K σ := by
  refine sup_le (graphFixedRootGroup_le_twInndiag σ) ?_
  rintro _ ⟨u, rfl⟩
  exact rootDiagUnit_mem_twInndiag fun i => compatDiag_perm u i

theorem e6InndiagGL_le_inndiagGroup (K : Type) [Field K] :
    e6InndiagGL K ≤ inndiagGroup Tag.E6 K := by
  refine sup_le (fun g hg => ⟨1, g, hg, by rw [rootDiagUnit_one, one_mul]⟩) ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨b, 1, one_mem _, (mul_one _).symm⟩

theorem mem_twistedE6InndiagGL_of_baseChangeGL {K₀ K : Type} [Field K₀] [Finite K₀] [Field K]
    [Finite K] (ι : K₀ →+* K) {m : ℕ} (hm : 1 ≤ m) (hK₀ : Nat.card K₀ = (2 ^ m) ^ 2)
    {σ₀ : K₀ ≃+* K₀} {σ : K ≃+* K} (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ m) (hι : ∀ c, σ (ι c) = ι (σ₀ c))
    {x₀ : ModGL TwistTag.E6.tag K₀} (hx₀ : x₀ ∈ inndiagGroup TwistTag.E6.tag K₀)
    (hx : baseChangeGL ι x₀ ∈ twistedE6InndiagGL K σ) : x₀ ∈ twistedE6InndiagGL K₀ σ₀ := by
  have h1 := twistHom_eq_of_mem_twInndiag (twistedE6InndiagGL_le_twInndiagGroup σ hx)
  have h2 : twistHom TwistTag.E6 K₀ σ₀.toRingHom x₀ = x₀ := by
    apply baseChangeGL_injective ι
    rw [← twistHom_baseChangeGL ι (σ := σ.toRingHom) (RingHom.ext fun c => (hι c).symm), h1]
  set L₀ := AlgebraicClosure K₀
  haveI : CharP K₀ 2 := charP_two_of_card_sq hK₀
  haveI : CharP L₀ 2 := charP_of_injective_algebraMap (algebraMap K₀ L₀).injective 2
  set Fr₀ : L₀ →+* L₀ := iterateFrobenius L₀ 2 m with hFrdef
  have hFr₀ : ∀ c, Fr₀ c = c ^ 2 ^ m := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hcomm : (algebraMap K₀ L₀).comp σ₀.toRingHom = Fr₀.comp (algebraMap K₀ L₀) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ₀, hFr₀,
        map_pow]
  have hF : twistHom TwistTag.E6 L₀ Fr₀ (baseChangeGL (algebraMap K₀ L₀) x₀) =
      baseChangeGL (algebraMap K₀ L₀) x₀ := by
    rw [twistHom_baseChangeGL (algebraMap K₀ L₀) hcomm, h2]
  obtain ⟨w, hw, hwx⟩ := exists_mem_twInndiag_of_twist_fixed hm hK₀ hσ₀ hFr₀
    (baseChangeGL_mem_adjointGroup_of_mem_inndiag (algebraMap K₀ L₀) hx₀) hF
  rw [← baseChangeGL_injective _ hwx]
  exact NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ₀ hw

end Certs

end CFSG.StandardType.TwE6FieldCore

end
