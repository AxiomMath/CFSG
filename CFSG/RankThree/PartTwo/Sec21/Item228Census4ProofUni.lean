module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofL3Aut
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofL3Type

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars)

open Matrix

namespace Item228Census4Proof

variable {p f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData p f K}

theorem mem_centMod_of_psuConj_fix {B : unitaryIsom3 hK} {g : unitarySU p f K 3}
    (hfix : psuConj hK B (unitaryProj hK 3 g) = unitaryProj hK 3 g) :
    (g : GL (Fin 3) K) ∈ Sec4.centMod (Sec4.slPi false 3 (p ^ f) K) B := by
  rw [Sec4.mem_centMod_iff_scalar]
  refine ⟨g.2, ?_⟩
  change psuConj hK B (g : unitaryPSU hK 3) = (g : unitaryPSU hK 3) at hfix
  rw [psuConj_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hfix
  set G₀ : GL (Fin 3) K := ((g : unitarySU p f K 3) : GL (Fin 3) K) with hG₀
  set s := GeneralLinearGroup.scalar (Fin 3) c with hs
  have h2 : ((B : GL (Fin 3) K) * G₀ * (B : GL (Fin 3) K)⁻¹)⁻¹ * G₀ = s := by
    rw [← hc]
    simp [coe_suConj, G₀]
  have hcen : ∀ h : GL (Fin 3) K, h * s = s * h := fun h => (commute_scalar c h).eq
  refine ⟨s, ⟨c, rfl⟩, ?_⟩
  calc G₀ * (B : GL (Fin 3) K) * G₀⁻¹ =
      G₀ * (((B : GL (Fin 3) K) * G₀ * (B : GL (Fin 3) K)⁻¹)⁻¹ * G₀) * G₀⁻¹ *
        (B : GL (Fin 3) K) := by group
    _ = s * (B : GL (Fin 3) K) := by rw [h2, hcen G₀, mul_inv_cancel_right]

theorem exists_data_false (h3 : 3 ∣ p ^ f + 1) (hp2 : p ≠ 2) {B : unitaryIsom3 hK}
    (hB1 : psuConj hK B ≠ 1) (hB3 : psuConj hK B ^ 3 = 1) :
    ∃ (_ : Sec4.PiField false p f K) (_ : Sec4.ModThree false (p ^ f)) (τ : K),
      τ ^ 3 = 1 ∧ τ ≠ 1 ∧ (2 : K) ≠ 0 ∧ (B : GL (Fin 3) K) ∈ Sec4.glPi false 3 (p ^ f) K ∧
      (B : GL (Fin 3) K) ∉ Sec4.zPi false 3 (p ^ f) K ∧
      (B : GL (Fin 3) K) ^ 3 ∈ Sec4.zPi false 3 (p ^ f) K := by
  have := hK.finite
  have : CharP K p := hK.charP
  have hPi : Sec4.PiField false p f K := ⟨hK.prime, hK.one_le, by
    rw [Sec4.piCard, Bool.cond_false, hK.card, ← pow_mul, mul_comm]⟩
  have hq : Sec4.ModThree false (p ^ f) := by
    change p ^ f % 3 = 2
    omega
  have hcard3 : 3 ∣ Nat.card K - 1 := by
    rw [hK.card, pow_mul']
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : p ^ f % 3 = 2 := hq
      rw [this]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hK.prime.pos _)
    omega
  obtain ⟨τ, hτ, hτ1⟩ := exists_cube_root_of_unity hcard3
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp hdvd)
  have hπ : false = false → UnitaryFieldData p f K := fun _ => hK
  have hq' : false = false → Sec4.ModThree false (p ^ f) := fun _ => hq
  have hZ := Sec4.zPi_eq hπ hq' hτ hτ1
  have hBH : (B : GL (Fin 3) K) ∈ Sec4.glPi false 3 (p ^ f) K := (Sec4.mem_glPi_false hK).mpr B.2
  refine ⟨hPi, hq, τ, hτ, hτ1, h2, hBH, ?_, ?_⟩
  · rw [hZ]
    exact fun h => hB1 ((Sec4.psuConj_eq_one_iff B).mpr h.2)
  · rw [hZ]
    refine ⟨(Sec4.glPi false 3 (p ^ f) K).pow_mem hBH 3, ?_⟩
    have := (Sec4.psuConj_eq_one_iff (B ^ 3)).mp (by rw [map_pow, hB3])
    simpa using this

theorem false_of_fix_unitaryPSU (h3 : 3 ∣ p ^ f + 1) (hp2 : p ≠ 2) {B : unitaryIsom3 hK}
    (hB1 : psuConj hK B ≠ 1) (hB3 : psuConj hK B ^ 3 = 1) {Qs : Subgroup (unitaryPSU hK 3)}
    {m : ℕ} (eQ : Qs ≃* projSL 2 (GaloisField 2 m)) (hm : 2 ≤ m)
    (hfix : ∀ q ∈ Qs, psuConj hK B q = q) : False := by
  obtain ⟨hPi, hq, τ, hτ, hτ1, h2, hBH, hBZ, hB3'⟩ := exists_data_false h3 hp2 hB1 hB3
  set M₀ : Subgroup (unitarySU p f K 3) := Qs.comap (unitaryProj hK 3) with hM₀
  set M : Subgroup (GL (Fin 3) K) := M₀.map (unitarySU p f K 3).subtype with hMdef
  let ι : M₀ ≃* M := M₀.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let ψ₀ : M₀ →* Qs := ((unitaryProj hK 3).comp M₀.subtype).codRestrict Qs fun g => g.2
  let ψ : M →* Qs := ψ₀.comp ι.symm.toMonoidHom
  have hιv : ∀ g : M₀, ((ι g : M) : GL (Fin 3) K) = ((g : unitarySU p f K 3) : GL (Fin 3) K) :=
    fun g => rfl
  have hψι : ∀ g : M₀, ψ (ι g) = ψ₀ g := fun g => by
    change ψ₀ (ι.symm (ι g)) = ψ₀ g
    rw [MulEquiv.symm_apply_apply]
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨g, hg⟩ := unitaryProj_surjective hK 3 (q : unitaryPSU hK 3)
    have hgM : g ∈ M₀ := by
      change unitaryProj hK 3 g ∈ Qs
      rw [hg]
      exact q.2
    refine ⟨ι ⟨g, hgM⟩, ?_⟩
    rw [hψι]
    exact Subtype.ext hg
  have hker : ∀ g : M, ψ g = 1 → (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := ι.surjective g
    rw [hψι] at hg
    have h1 : unitaryProj hK 3 (g₀ : unitarySU p f K 3) = 1 := congrArg Subtype.val hg
    rw [← MonoidHom.mem_ker, ker_unitaryProj] at h1
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp h1
    exact ⟨c, by rw [hιv, hc]⟩
  have hMle : M ≤ Sec4.centMod (Sec4.slPi false 3 (p ^ f) K) B := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_centMod_of_psuConj_fix (hfix _ hg)
  have : IsSimpleGroup Qs := isSimpleGroup_of_mulEquiv hm eQ
  exact false_of_le_centMod_odd hPi hq hτ hτ1 h2 hBH hBZ hB3' hMle ψ hψ hker
    (exists_not_commute_of_mulEquiv_projSL eQ) (exists_two_involutions hm eQ)

theorem false_of_fix_unitarySU (h3 : 3 ∣ p ^ f + 1) (hp2 : p ≠ 2) {B : unitaryIsom3 hK}
    (hB1 : psuConj hK B ≠ 1) (hB3 : psuConj hK B ^ 3 = 1) {Qs : Subgroup (unitarySU p f K 3)}
    {m : ℕ} (eQ : Qs ≃* projSL 2 (GaloisField 2 m)) (hm : 2 ≤ m)
    (hfix : ∀ k ∈ Qs, psuConj hK B (unitaryProj hK 3 k) = unitaryProj hK 3 k) : False := by
  obtain ⟨hPi, hq, τ, hτ, hτ1, h2, hBH, hBZ, hB3'⟩ := exists_data_false h3 hp2 hB1 hB3
  set M : Subgroup (GL (Fin 3) K) := Qs.map (unitarySU p f K 3).subtype with hMdef
  let ι : Qs ≃* M := Qs.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let ψ : M →* Qs := ι.symm.toMonoidHom
  have hψ : Function.Surjective ψ := ι.symm.surjective
  have hker : ∀ g : M, ψ g = 1 → (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    intro g hg
    have h1 : g = 1 := ι.symm.injective (hg.trans (map_one _).symm)
    rw [h1]
    exact (StatedScalars (Fin 3) K).one_mem
  have hMle : M ≤ Sec4.centMod (Sec4.slPi false 3 (p ^ f) K) B := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_centMod_of_psuConj_fix (hfix _ hg)
  have : IsSimpleGroup Qs := isSimpleGroup_of_mulEquiv hm eQ
  exact false_of_le_centMod_odd hPi hq hτ hτ1 h2 hBH hBZ hB3' hMle ψ hψ hker
    (exists_not_commute_of_mulEquiv_projSL eQ) (exists_two_involutions hm eQ)

end Item228Census4Proof

open Item228Census4Proof

section Certs


theorem census228L3TypeUniOdd_holds : Census228L3TypeUniOdd := by
  intro G _ _ X A K K₀ m hL hP hAmax hA27 hAN hAC hdiag _ _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm
    hm0 hme
  obtain ⟨p, f, F, _, hF, h3, hp2, hiso⟩ := hP
  exfalso
  obtain ⟨b, hbA, hbN, hβ1, N, Kb, hcfg⟩ := Item228Census2Proof.config228Aut_of hAmax hA27 hAN
    hAC hρ hρr hKK hK0X hK0C hnorm hU hKm hm0 hme
  have hb3 : b ^ 3 = 1 := hAmax.prop.2 b hbA
  have hm2 := two_le_of_even hm0 hme
  obtain ⟨eK⟩ := hcfg.equiv
  have hβ3 := thetaQuotMulAut_pow_three hbN hb3
  rcases hiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    have hmem : inducedAutHom X e ⟨b, hbN⟩ ∈ (psuConj hF).range := by
      by_cases ho : Sec4.InducesOuterTheta b X
      · exact (outer223Cross_holds G X b hL hb3 (hdiag b hbA ho)).2.2.1 p f F hF h3 e hbN
      · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta hbN ho
        rw [inducedAutHom_apply, ← hy, congr_mulAutConj]
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e y)
        rw [← hg, conj_mk_eq_psuConj]
        exact ⟨_, rfl⟩
    obtain ⟨B, hB⟩ := hmem
    rw [inducedAutHom_apply] at hB
    have hB1 : psuConj hF B ≠ 1 := fun h =>
      hβ1 ((MulAut.congr e).injective ((hB.symm.trans h).trans (map_one _).symm))
    have hB3 : psuConj hF B ^ 3 = 1 := by rw [hB, ← map_pow, hβ3, map_one]
    refine false_of_fix_unitaryPSU h3 hp2 hB1 hB3 (Qs := Kb.map e.toMonoidHom)
      ((Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK) hm2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hB]
    simp [MulAut.congr_apply, hcfg.fix k (hcfg.le hk)]
  ·
    have hq2 : 2 < p ^ f := by
      have h3p : 3 ≤ p := by
        have := hF.prime.two_le
        omega
      calc 2 < 3 := by norm_num
        _ ≤ p := h3p
        _ ≤ p ^ f := Nat.le_self_pow (by have := hF.one_le; omega) p
    have hmem : MulAut.congr (suCenterEquiv hF hq2)
        (centerDescend _ (inducedAutHom X e ⟨b, hbN⟩)) ∈ (psuConj hF).range := by
      by_cases ho : Sec4.InducesOuterTheta b X
      · exact (outer223Cross_holds G X b hL hb3 (hdiag b hbA ho)).2.2.2 p f F hF hq2 h3 e hbN
      · obtain ⟨y, hy⟩ := mem_range_conj_of_not_inducesOuterTheta hbN ho
        rw [inducedAutHom_apply, ← hy, congr_mulAutConj, centerDescend_conj, congr_mulAutConj]
        refine ⟨⟨((e y : unitarySU p f F 3) : GL (Fin 3) F),
          unitarySU_le_unitaryIsom3 (e y).2⟩, ?_⟩
        rw [← conj_mk_eq_psuConj]
        rfl
    obtain ⟨B, hB⟩ := hmem
    rw [inducedAutHom_apply] at hB
    have hB1 : psuConj hF B ≠ 1 := by
      intro h
      apply hβ1
      have h1 : centerDescend _ (MulAut.congr e (Sec4.thetaQuotMulAut X
          (Sec4.compAction X ⟨b, hbN⟩))) = 1 :=
        (MulAut.congr (suCenterEquiv hF hq2)).injective ((hB.symm.trans h).trans (map_one _).symm)
      have h2 := Item223CensusProof.centerDescend_injective_unitarySU hF hq2
        (h1.trans (map_one _).symm)
      exact (MulAut.congr e).injective (h2.trans (map_one _).symm)
    have hB3 : psuConj hF B ^ 3 = 1 := by
      rw [hB, ← map_pow, ← map_pow, ← map_pow, hβ3, map_one, map_one, map_one]
    refine false_of_fix_unitarySU h3 hp2 hB1 hB3 (Qs := Kb.map e.toMonoidHom)
      ((Kb.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eK) hm2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hB]
    have hk' : e (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) k) = e k := by
      rw [hcfg.fix k (hcfg.le hk)]
    change (suCenterEquiv hF hq2) (centerDescend _ (MulAut.congr e
      (Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩)))
        ((suCenterEquiv hF hq2).symm (unitaryProj hF 3 (e k)))) = unitaryProj hF 3 (e k)
    have hsymm : (suCenterEquiv hF hq2).symm (unitaryProj hF 3 (e k)) =
        ((e k : unitarySU p f F 3) : unitarySU p f F 3 ⧸ Subgroup.center _) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hsymm, centerDescend_mk]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hk']
    rfl

end Certs

end CFSG.RankThree.PartTwo.Sec21
