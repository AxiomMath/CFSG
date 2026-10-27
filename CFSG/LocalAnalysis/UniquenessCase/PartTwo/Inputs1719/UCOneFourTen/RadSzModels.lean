module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenFam
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallPSL
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTwD4
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Nodes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.TwE6Nodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Minuscule.MinData.Valid
  CFSG.ClassicalInvolution.ModelFacts.ChevAut

private theorem hasBorelModel_of_model_psl
    {Y : Type} [Group Y] {m f : ℕ} (h : StatedClassicalModel Y .PSL m 2 f) :
    HasBorelModel Y := by
  obtain ⟨hadm, F, _, _, hcard, ⟨e⟩⟩ := h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hadm.2.2.1; omega⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact hasBorelModel_psl (m := m')
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m' + 1) F).trans
      e.symm)

private theorem hasBorelModel_of_model_f4
    {Y : Type} [Group Y] {f : ℕ} (h : UntwistedChevalleyModel Y .F4 (2 ^ f)) :
    HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite ↥(adjointGroup .F4 K) := generated_group_finite .F4 K
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_f4 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_f4 i)⟩

private theorem hasBorelModel_of_model_e8
    {Y : Type} [Group Y] {f : ℕ} (h : UntwistedChevalleyModel Y .E8 (2 ^ f)) :
    HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_e8 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_e8 i)⟩

private theorem hasBorelModel_of_model_e6
    {Y : Type} [Group Y] {f : ℕ} (h : UntwistedChevalleyModel Y .E6 (2 ^ f)) :
    HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_e6 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_e6 i)⟩

private theorem hasBorelModel_of_model_e7
    {Y : Type} [Group Y] {f : ℕ} (h : UntwistedChevalleyModel Y .E7 (2 ^ f)) :
    HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite ↥(e7Data_valid.minGroup K) := finite_minGroup e7Data_valid K
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_e7 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_e7 i)⟩

private theorem hasBorelModel_of_model_g2
    {Y : Type} [Group Y] {f : ℕ} (h : UntwistedChevalleyModel Y .G2 (2 ^ f)) :
    HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact hasBorelModel_g2 e

section TwistedE6

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField)

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k}

omit [Finite k] [CharP k 2] in
private theorem hasSL2Node_twE6_one :
    HasSL2Node (twistedDatum k θ) (nf 1) (fixedField θ) := by
  have h1 : orbitMap (nd 3) = nf 1 := by decide
  refine ⟨rFixed θ (nd 3) rfl, rFixed_injective θ (nd 3) rfl, fun c => ?_, fun c => ?_⟩
  · rw [← tv01_eq_sl2Upper]
    exact rFixed_upper θ (nd 3) rfl h1 c
  · rw [← tv10_eq_sl2Lower]
    exact rFixed_lower θ (nd 3) rfl h1 c

omit [Finite k] [CharP k 2] in
private theorem hasSL2Node_e6tw_orbitNode
    (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) :
    HasSL2Node (twistedDatum k θ) i k := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine ⟨slOrbitHom θ hθ hab, slOrbitHom_injective θ hθ hab, fun c => ?_, fun c => ?_⟩
  · refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) (proj_single a) hne1 _).2
      ⟨c, ?_⟩
    rw [show (sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) = slUpper k c from rfl,
      slOrbitHom_upper, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  · refine (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) (proj_neg_single a) hne2
      _).2 ⟨c, ?_⟩
    rw [show (sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) = slLower k c from rfl,
      slOrbitHom_slLower, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

private theorem hasInvolThree_e6tw
    (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k) :
    ∀ i : Fin (Tag.rank .F4), HasInvolThree (twistedDatum k θ) i := by
  have hcharF : CharP (fixedField θ) 2 :=
    RingHom.charP _ (fixedField θ).subtype_injective 2
  have h0 : HasInvolThree (twistedDatum k θ) (nf 0) :=
    HasSL2Node.hasInvolThree (F := fixedField θ)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.hasSL2Node_twE6_zero)
  have h1 : HasInvolThree (twistedDatum k θ) (nf 1) :=
    HasSL2Node.hasInvolThree (F := fixedField θ) hasSL2Node_twE6_one
  have h2 : HasInvolThree (twistedDatum k θ) (nf 2) :=
    HasSL2Node.hasInvolThree (hasSL2Node_e6tw hθ hK4)
  have h3 : HasInvolThree (twistedDatum k θ) (nf 3) :=
    HasSL2Node.hasInvolThree
      (hasSL2Node_e6tw_orbitNode hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)
        (i := nf 3) (by decide))
  intro i
  have hi : i = nf 0 ∨ i = nf 1 ∨ i = nf 2 ∨ i = nf 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

private theorem hasBorelModel_of_model_twistedE6
    {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel Y .E6 (2 ^ f)) : HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ f) ^ 2 := hcard
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK', pow_mul])
  have h2le : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h2le 2
  have hθ : ∀ c, σ (σ c) = c := involutive_of_card hK' hσ
  have : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
  have : Finite ↥(fixedGroup K σ) := Subtype.finite
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
    borelQuotient_e6tw hθ hK4 hK' hσ e, fun i => hasInvolThree_e6tw hθ hK4 i⟩

end TwistedE6

section TrialityD4

open CFSG.LieType.Steinberg.TwistedD4 CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

private theorem hasInvolThree_d4tw
    (hσ : ∀ c, σ (σ (σ c)) = c) : ∀ i : Fin (Tag.rank .G2), HasInvolThree (twistedDatum σ) i := by
  have hcharF : CharP (fixedField σ) 2 :=
    RingHom.charP _ (fixedField σ).subtype_injective 2
  have h0 : HasInvolThree (twistedDatum σ) (ng 0) :=
    HasSL2Node.hasInvolThree (hasSL2Node_d4tw_long hσ)
  have h1 : HasInvolThree (twistedDatum σ) (ng 1) :=
    HasSL2Node.hasInvolThree (hasSL2Node_d4tw hσ)
  intro i
  have hi : i = ng 0 ∨ i = ng 1 := by revert i; decide
  rcases hi with rfl | rfl
  exacts [h0, h1]

private theorem hasBorelModel_of_model_trialityD4
    {Y : Type} [Group Y] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel Y .D4 (2 ^ f)) : HasBorelModel Y := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hcard
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f * 3)
      (by rw [← Nat.card_eq_fintype_card, hK', pow_mul])
  have h2le : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK' hσ
  have : Finite ↥(adjointGroup d4 K) := generated_group_finite d4 K
  have : Finite ↥(twistedGroup σ) := Subtype.finite
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
    borelQuotient_d4tw h2le hK' hσ e, fun i => hasInvolThree_d4tw hσ3 i⟩

end TrialityD4

theorem hasBorelModel_of_lieModel
    {S : Type} [Group S] {t : CFSG.Open.StatedLieTag} {m f : ℕ}
    (h : CFSG.Blueprint.LieModel S t m 2 f) (hB2 : t ≠ .twistedB2) (hF4 : t ≠ .twistedF4)
    (hT : t ≠ .Tits) : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.HasBorelModel S := by
  rcases h with ⟨ht, hcl⟩ | ⟨-, ht, hce⟩ | ⟨-, ht, hree⟩ | ⟨-, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hasBorelModel_of_model_psl hcl
    · exact hasBorelModel_of_model_psu hcl
    · exact hasBorelModel_of_model_psp hcl
    · exact absurd rfl hcl.1.2.2.2
    · exact hasBorelModel_of_model_pomegaPlus hcl
    · exact hasBorelModel_of_model_pomegaMinus hcl
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hasBorelModel_of_model_g2 hce.2
    · exact hasBorelModel_of_model_f4 hce.2
    · exact hasBorelModel_of_model_e6 hce.2
    · exact hasBorelModel_of_model_e7 hce.2
    · exact hasBorelModel_of_model_e8 hce.2
    · exact hasBorelModel_of_model_twistedE6 hce.1.2.1 hce.2
    · exact hasBorelModel_of_model_trialityD4 hce.1.2.1 hce.2
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hree.1.2.2.2.1 (by norm_num)
    · exact absurd rfl hF4
    · exact absurd rfl hT
  · exact absurd ht hB2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
