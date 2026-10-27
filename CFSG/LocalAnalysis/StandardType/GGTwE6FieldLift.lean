module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLiftTwist
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6RootKill


theorem exists_rootDiagUnit_of_twLangData {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) (hc : D.c = 1) {x}
    (hx : x ∈ A) : ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 =
        rootDiagUnit TwistTag.E6.tag a := by
  have h := D.hc x hx
  simp only [hc, one_mul, inv_one, mul_one] at h
  obtain ⟨t, ht, hte⟩ := h
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht).1
  refine ⟨a, ?_⟩
  rw [← hte]
  change D.g0⁻¹ * (D.g0 * rootDiagUnit TwistTag.E6.tag a * D.g0⁻¹) * D.g0 = _
  group

theorem exists_lift_twLangData {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ 2] [Field K]
    [Finite K] (ι : K₀ →+* K) {σ₀ : K₀ ≃+* K₀} (σ : K ≃+* K) {m p : ℕ} (hm : 1 ≤ m)
    (hp : Odd p) (hK : Nat.card K = (2 ^ (m * p)) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ (m * p))
    {A₀ : Subgroup (ModGL TwistTag.E6.tag K₀)} (D₀ : TwLangData K₀ σ₀ (2 ^ m) A₀)
    (hc : D₀.c = 1) (hAI : A₀.map (baseChangeGL ι) ≤ twistedE6InndiagGL K σ) :
    ∃ D : TwLangData K σ (2 ^ (m * p)) (A₀.map (baseChangeGL ι)), D.c = 1 ∧
      ∀ α, TwDataKills D α → TwDataKills D₀ α := by
  set L₀ := AlgebraicClosure K₀
  set L := AlgebraicClosure K
  letI : Algebra K₀ L := ((algebraMap K L).comp ι).toAlgebra
  let j' : L₀ →ₐ[K₀] L := IsAlgClosed.lift
  set j : L₀ →+* L := (j' : L₀ →+* L)
  have hj : j.comp (algebraMap K₀ L₀) = (algebraMap K L).comp ι := j'.comp_algebraMap
  haveI : CharP L₀ 2 := charP_of_injective_algebraMap (algebraMap K₀ L₀).injective 2
  haveI : CharP L 2 := charP_of_injective_ringHom j.injective 2
  obtain ⟨k, rfl⟩ := hp
  obtain ⟨w, hw⟩ := exists_twistHom_pow_odd D₀.Fr D₀.hg0 k
  set Fr : L →+* L := iterateFrobenius L 2 (m * (2 * k + 1)) with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ (m * (2 * k + 1)) := fun c => by
    rw [hFrdef, iterateFrobenius_def]
  have hcomm : j.comp (D₀.Fr ^ (2 * k + 1)) = Fr.comp j := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, ringHom_pow_apply_eq_pow D₀.hFr, map_pow, hFr,
      pow_mul]
  have hg : twistHom TwistTag.E6 L Fr (baseChangeGL j D₀.g0) =
      baseChangeGL j D₀.g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
    rw [twistHom_baseChangeGL j hcomm, hw, map_mul, baseChangeGL_canonicalRep]
  have hconj : ∀ x₀, (baseChangeGL j D₀.g0)⁻¹ * baseChangeGL (algebraMap K L)
      (baseChangeGL ι x₀) * baseChangeGL j D₀.g0 =
        baseChangeGL j (D₀.g0⁻¹ * baseChangeGL (algebraMap K₀ L₀) x₀ * D₀.g0) := fun x₀ => by
    rw [map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hj]
  have hFix : ∀ y ∈ (A₀.map (baseChangeGL ι)).map (baseChangeGL (algebraMap K L)),
      twistHom TwistTag.E6 L Fr y = y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two
        (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ (hAI hx)))).2
  have hT : ∀ y ∈ (A₀.map (baseChangeGL ι)).map (baseChangeGL (algebraMap K L)),
      (baseChangeGL j D₀.g0)⁻¹ * y * baseChangeGL j D₀.g0 ∈ torusGroup TwistTag.E6.tag L := by
    rintro _ ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩
    obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_of_twLangData D₀ hc hx₀
    rw [hconj, ha₀, baseChangeGL_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  refine ⟨⟨w, Fr, hFr, baseChangeGL j D₀.g0, baseChangeGL_mem_adjointGroup j D₀.hg0C, hg, 1,
    one_mem _, fun x hx => ?_⟩, rfl, fun α hkill x₀ hx₀ => ?_⟩
  · simp only [one_mul, inv_one, mul_one]
    exact mem_lang_torus_of_datum _ hFix hg hT _ (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨a, ha, hα⟩ := hkill _ (Subgroup.mem_map_of_mem _ hx₀)
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_of_twLangData D₀ hc hx₀
  change rootDiagUnit _ a = (baseChangeGL j D₀.g0)⁻¹ *
    baseChangeGL (algebraMap K L) (1 * baseChangeGL ι x₀ * 1⁻¹) * baseChangeGL j D₀.g0 at ha
  simp only [one_mul, inv_one, mul_one] at ha
  have hae : a = fun i => Units.map j.toMonoidHom (a₀ i) := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [ha, hconj, ha₀, baseChangeGL_rootDiagUnit]
  refine ⟨a₀, by rw [hc, one_mul, inv_one, mul_one, ha₀], ?_⟩
  rw [hae, CFSG.RankThree.PartOne.KE.rootChar_map_tuple] at hα
  exact Units.map_injective (f := j.toMonoidHom) j.injective (hα.trans (map_one _).symm)

end CFSG.StandardType.TwE6FieldCore

end
