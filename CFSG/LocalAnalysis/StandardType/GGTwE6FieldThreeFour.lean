module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwoLocalToral
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TwE6RootKill CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_twLangData_of_conj_torus {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgA : ∀ x ∈ A, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * g ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K)) :
    ∃ D : TwLangData K σ (2 ^ n) A, D.c = 1 := by
  haveI : CharP K 2 := charP_two_of_card_sq hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K _).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  have hF := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ _ hFr
  obtain ⟨v, g0, hg0C, hg0, hB⟩ := exists_lang_torus_of_conj_torus_twisted 2 TwistTag.E6 n hn
    (A := A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (by rintro _ ⟨x, hx, rfl⟩; exact (hF (Subgroup.mem_map_of_mem _ (hAI hx))).2) hg
    (by rintro _ ⟨x, hx, rfl⟩; exact hgA x hx)
  refine ⟨⟨v, iterateFrobenius _ 2 n, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => ?_⟩, rfl⟩
  simp only [one_mul, inv_one, mul_one]
  exact hB _ (Subgroup.mem_map_of_mem _ hx)

theorem map_baseChangeGL_twistedE6InndiagGL_le {K₀ K : Type} [Field K₀] [Field K]
    (ι : K₀ →+* K) {σ₀ : K₀ ≃+* K₀} {σ : K ≃+* K} (hι : ∀ c, σ (ι c) = ι (σ₀ c)) :
    (twistedE6InndiagGL K₀ σ₀).map (baseChangeGL ι) ≤ twistedE6InndiagGL K σ := by
  rw [twistedE6InndiagGL, twistedE6InndiagGL, Subgroup.map_sup]
  refine sup_le_sup (map_baseChangeGL_graphFixedRootGroup_le (σ := σ₀.toRingHom)
    (Fr := σ.toRingHom) σ₀.surjective hι) ?_
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  change baseChangeGL ι (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ₀.toRingHom u)) ∈ _
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom)
    (b := fun i => Units.map ι.toMonoidHom (compatDiag TwistTag.E6 σ₀.toRingHom u i)) fun i =>
      Units.ext (by simp only [compatDiag_perm, Units.coe_map]; exact (hι _).symm)
  rw [baseChangeGL_rootDiagUnit, ← hw]
  exact MonoidHom.mem_range.2 ⟨w, rfl⟩


theorem exists_twLangData_of_twNormTwo (hT : ExcFramesHalf.BigElemAbelianToralBar .E6 3)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A)
    (hU : TwNormTwo K σ A) : ∃ D : TwLangData K σ (2 ^ n) A, D.c = 1 := by
  haveI : CharP K 2 := charP_two_of_card_sq hK
  obtain ⟨g, hg, hgA⟩ := exists_conj_torus_of_twNormTwo hT hK hσ h3
    (algebraMap K (AlgebraicClosure K)) hAI hA hcard hU
  exact exists_twLangData_of_conj_torus
    (Nat.one_le_iff_ne_zero.2 fun h0 => by subst h0; norm_num at h3) hK hσ hAI hg hgA

theorem subfieldLangDatumThreeFour_of_toral (hT : ExcFramesHalf.BigElemAbelianToralBar .E6 3) :
    SubfieldLangDatumThreeFour := by
  intro K₀ K _ _ _ _ ι σ₀ σ q₀ hK₀ hK hσ₀ hσ hchar h3 A₀ hA₀I hA₀ hA₀c hU
  haveI : CharP K₀ 2 := ringChar.of_eq hchar
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  obtain ⟨k, -, hk⟩ := FiniteField.card K₀ 2
  have hdvd : q₀ ∣ 2 ^ (k : ℕ) := by
    rw [← hk, ← Nat.card_eq_fintype_card, hK₀]
    exact dvd_pow_self q₀ two_ne_zero
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 fun h0 => by
    subst h0
    norm_num at h3
  have hK' : Nat.card K = (2 ^ (m * 3)) ^ 2 := by rw [hK, pow_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ (m * 3) := fun c => by rw [hσ, pow_mul]
  have h3' : 3 ∣ 2 ^ (m * 3) + 1 := h3.trans (by
    simpa only [one_pow, pow_mul] using Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (n := 3) ⟨1, rfl⟩)
  have hι : ∀ c, σ (ι c) = ι (σ₀ c) := fun c => by
    rw [hσ', ← map_pow, pow_two_pow_mul_odd hK₀ (p := 3) ⟨1, rfl⟩ c, hσ₀]
  letI : Algebra K₀ K := ι.toAlgebra
  let j' : K →ₐ[K₀] AlgebraicClosure K₀ := IsAlgClosed.lift
  set j : K →+* AlgebraicClosure K₀ := (j' : K →+* AlgebraicClosure K₀)
  have hj : j.comp ι = algebraMap K₀ (AlgebraicClosure K₀) := j'.comp_algebraMap
  obtain ⟨g, hg, hgA⟩ := exists_conj_torus_of_twNormTwo hT hK' hσ' h3' j
    ((Subgroup.map_mono hA₀I).trans (map_baseChangeGL_twistedE6InndiagGL_le ι hι)) (hA₀.map _)
    ((Subgroup.card_map_of_injective (baseChangeGL_injective ι)).trans hA₀c).ge hU
  refine exists_twLangData_of_conj_torus hm hK₀ hσ₀ hA₀I hg fun x hx => ?_
  have := hgA _ (Subgroup.mem_map_of_mem _ hx)
  rwa [baseChangeGL_baseChangeGL, hj] at this

end CFSG.StandardType.TwE6FieldCore

end
