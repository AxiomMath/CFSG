module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL5
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)


open CFSG.Blueprint.Chevalley (TwistTag)

open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)


private theorem k1566l10a_center_bot_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

open CFSG.LieType.Chevalley (graphFixedRootGroup)


theorem d4_center_bot {Y : Type} [Group Y] [Finite Y]
    {p f : ℕ} (hY : LieModel Y .trialityD4 0 p f) : Subgroup.center Y = ⊥ := by
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 p f :=
    LieModel.chevalleyExceptionalModel hY (by decide)
  have hp : p.Prime := hc.1.1
  have hf : 1 ≤ f := hc.1.2.1
  obtain ⟨K, _, _, σ, _, _, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hc.2
  exact k1566l10a_center_bot_of_mulEquiv e.symm
    (CFSG.LieType.Chevalley.exceptional_fixed_center_trivial TwistTag.D4 K σ)

private theorem k1566l10b_zmod3 (u : ZMod 3) (hu : u ≠ 0) : u = 1 ∨ u = -1 := by
  revert u
  decide

private theorem k1566l10b_zmod3_unit (u : ZMod 3) (hu : u ≠ 0) :
    ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧ u = (eps : ZMod 3) := by
  rcases k1566l10b_zmod3 u hu with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; decide⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; decide⟩

private theorem k1566l10b_sign (p f : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧ (p : ZMod 3) ^ f = (eps : ZMod 3) := by
  have hp0 : (p : ZMod 3) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm
  exact k1566l10b_zmod3_unit _ (pow_ne_zero f hp0)

private theorem k1566l10b_core
    (sd3_map : ∀ {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']
      (e : H ≃* H') {Q T V : Subgroup H} {y : H} {e1 e2 : ℕ}, SD3 H Q T V y e1 e2 →
      SD3 H' (Q.map e.toMonoidHom) (T.map e.toMonoidHom) (V.map e.toMonoidHom) (e y) e1 e2)
    (numerics : ∀ {p f : ℕ}, p.Prime → p ≠ 3 → 1 ≤ f → ∀ {eps : ℤ}, eps = 1 ∨ eps = -1 →
      (p : ZMod 3) ^ f = (eps : ZMod 3) →
      ((eps * (p : ℤ) ^ f : ℤ) : ZMod 3) = 1 ∧
        ¬ (3 : ℤ) ^ max (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 1)
            (padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) ∣ eps * (p : ℤ) ^ f - 1)
    (hOut : OutTrialityInput) (hT : TrialityTarget)
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hY : LieModel Y .trialityD4 0 p f)
    (hp3 : p ≠ 3) : OutCase Y := by
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 p f :=
    LieModel.chevalleyExceptionalModel hY (by decide)
  have hp : p.Prime := hc.1.1
  have hf : 1 ≤ f := hc.1.2.1
  obtain ⟨K, _, _, σ, hKcard, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hc.2
  have hKcard3 : Nat.card K = (p ^ f) ^ 3 := by
    simpa [TwistTag.order] using hKcard
  obtain ⟨eps, heps, hcong⟩ := k1566l10b_sign p f hp hp3
  have hOO : OutOrderThree ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (fieldActor (t := TwistTag.D4) σ σ) :=
    hOut p f K σ hp hp3 hf hKcard3 hσ
  obtain ⟨Q, T, V, y, hSD, hSc, -⟩ := hT K p f hp hp3 hf hKcard3 σ hσ eps heps hcong
  have hnum := numerics hp hp3 hf heps hcong
  refine Or.inr ⟨MulAut.congr e.symm (fieldActor (t := TwistTag.D4) σ σ),
    Q.map e.symm.toMonoidHom, T.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom,
    e.symm y, padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) + 1,
    padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)), eps * (p : ℤ) ^ f,
    ?_, ?_, ?_, ?_, hnum.1, hnum.2⟩
  · rw [← map_pow, d4_actor_cube hKcard3 σ hσ, map_one]
  · exact outOrderThree_map_mulEquiv e.symm hOO
  · exact sd3_map e.symm hSD
  · exact scalarAction_map_mulEquiv e.symm hSc

theorem d4_outCase (hOut : OutTrialityInput)
    (hT : TrialityTarget) {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hY : LieModel Y .trialityD4 0 p f) (hp3 : p ≠ 3) : OutCase Y :=
  k1566l10b_core sd3_map_mulEquiv numerics_d4 hOut hT hY hp3

private theorem k1566l10c_zmod3_units (u : ZMod 3) (hu : u ≠ 0) :
    ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧ u = (eps : ZMod 3) := by
  have h : u = 1 ∨ u = 2 := by revert hu; decide +revert
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; decide⟩
  · exact ⟨-1, Or.inr rfl, by rw [h]; decide⟩

private theorem k1566l10c_exists_iso {X N : Type} [Group X] [Group N] [Finite X] [Finite N]
    (e : X ≃* N) (S : Sylow 3 X) (Qs : Sylow 3 N) :
    ∃ E : X ≃* N, S.map E.toMonoidHom = (Qs : Subgroup N) := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N
    (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S) Qs
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hcoe : ((Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S : Sylow 3 N) :
      Subgroup N).map (MulAut.conj g).toMonoidHom = (Qs : Subgroup N) := by
    have h2 := congrArg (fun x : Sylow 3 N => (x : Subgroup N)) hg
    rw [← h2, Sylow.coe_subgroup_smul]
    simp only [Subgroup.pointwise_smul_def]
    rfl
  have hEto : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
    ext x
    rfl
  rw [hEto, ← Subgroup.map_map]
  simpa only [Sylow.coe_mapSurjective, MulEquiv.toMonoidHom_eq_coe] using hcoe

private theorem k1566l10c_fusion_transport {X N : Type} [Group X] [Group N]
    (E : X ≃* N) {V : Subgroup N} {y : N}
    (hfus : ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z) :
    ∀ z' ∈ V.map E.symm.toMonoidHom, z' ≠ 1 →
      (E.symm y) * z' * (E.symm y)⁻¹ = z' → Fusion27 z' := by
  intro z' hz' hz'1 hyz'
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hz'
  have hz1 : z ≠ 1 := by
    intro h
    apply hz'1
    rw [h, map_one]
  have hyz : y * z * y⁻¹ = z := by
    have h4 := congrArg (fun t => E t) hyz'
    rw [MulEquiv.coe_toMonoidHom] at h4
    rw [map_mul, map_mul, map_inv] at h4
    simpa using h4
  simpa only [MulEquiv.coe_toMonoidHom] using
    fusion27_map_mulEquiv E.symm (hfus z hz hz1 hyz)

private theorem k1566l10c_core (hT : TrialityTarget)
    (hsd3 : ∀ {H H' : Type} [Group H] [Group H'] [Finite H] [Finite H']
      (e : H ≃* H') {Q T V : Subgroup H} {y : H} {e1 e2 : ℕ},
      SD3 H Q T V y e1 e2 →
      SD3 H' (Q.map e.toMonoidHom) (T.map e.toMonoidHom) (V.map e.toMonoidHom) (e y) e1 e2)
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hY : LieModel Y .trialityD4 0 p f)
    (hp3 : p ≠ 3) : D4InnerDatum Y := by
  intro S
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 p f :=
    LieModel.chevalleyExceptionalModel hY (by decide)
  have hp : p.Prime := hc.1.1
  have hf : 1 ≤ f := hc.1.2.1
  obtain ⟨K, _, _, σ, hKcard, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hc.2
  have hKcard3 : Nat.card K = (p ^ f) ^ 3 := hKcard
  have hpz : (p : ZMod 3) ≠ 0 := by
    intro h
    have h' : p ≡ 0 [MOD 3] := (ZMod.natCast_eq_natCast_iff p 0 3).1 (by simpa using h)
    have h3 : 3 ∣ p := Nat.modEq_zero_iff_dvd.1 h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3).symm
  have hpf : (p : ZMod 3) ^ f ≠ 0 := pow_ne_zero f hpz
  obtain ⟨eps, heps, heps_eq⟩ := k1566l10c_zmod3_units _ hpf
  obtain ⟨Q, T, V, y, hSD, -, hfus⟩ := hT K p f hp hp3 hf hKcard3 σ hσ eps heps heps_eq
  classical
  let C0 := ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  have hQp : IsPGroup 3 Q := hSD.1
  have hQidx : ¬ 3 ∣ Q.index := hSD.2.1
  let Qs : Sylow 3 C0 := hQp.toSylow hQidx
  obtain ⟨E, hE⟩ := k1566l10c_exists_iso e S Qs
  have hE' : (S : Subgroup Y).map E.toMonoidHom = Q := hE
  have hQmap : Q.map E.symm.toMonoidHom = (S : Subgroup Y) := by
    rw [← hE', Subgroup.map_map]
    have hcomp : E.symm.toMonoidHom.comp E.toMonoidHom = MonoidHom.id Y := by
      ext x
      exact E.symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  let a := padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))
  refine ⟨T.map E.symm.toMonoidHom, V.map E.symm.toMonoidHom, E.symm y, a + 1, a, ?_, ?_⟩
  · simpa only [hQmap] using hsd3 E.symm hSD
  · exact k1566l10c_fusion_transport E hfus

theorem d4_innerDatum (hT : TrialityTarget)
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hY : LieModel Y .trialityD4 0 p f)
    (hp3 : p ≠ 3) : D4InnerDatum Y :=
  k1566l10c_core hT sd3_map_mulEquiv hY hp3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
