module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalGen
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalBasis
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.StandardType

namespace GGOppRad

open Matrix CFSG.Open CFSG.LieType.BorelTits

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem tInv_tInv (g : Matrix.SpecialLinearGroup ι K) : tInv (tInv g) = g :=
  tInv.symm_apply_apply g

omit [Finite K] in
theorem map_tInv_stdUop (ℓ : ι → ℕ) :
    (stdUop (K := K) ℓ).map (tInv : Matrix.SpecialLinearGroup ι K ≃* _).toMonoidHom =
      stdU ℓ := by
  rw [stdUop, Subgroup.map_map]
  have h : (tInv : Matrix.SpecialLinearGroup ι K ≃* _).toMonoidHom.comp tInv.toMonoidHom =
      MonoidHom.id _ := MonoidHom.ext fun g => tInv_tInv g
  rw [h, Subgroup.map_id]

omit [Finite K] in
theorem pCoreOf_normalizer_stdUop (p : ℕ) {ℓ : ι → ℕ}
    (h : pCoreOf p (Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) =
      stdU ℓ) :
    pCoreOf p (Subgroup.normalizer (stdUop (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) =
      stdUop ℓ := by
  rw [stdUop, ← Subgroup.map_equiv_normalizer_eq, pCoreOf_map_mulEquiv, h]

theorem exists_opposite_stdU (p : ℕ) [Fact p.Prime] [CharP K p] {ℓ : ι → ℕ}
    (hQ : pCoreOf p (Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) =
      stdU ℓ)
    (hN : Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K)) = stdP ℓ)
    (hne : stdU (K := K) ℓ ≠ ⊥) :
    pCoreOf p (Subgroup.normalizer (stdUop (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) =
        stdUop ℓ ∧
      Nat.card (stdUop (K := K) ℓ) = Nat.card (stdU (K := K) ℓ) ∧
      stdUop (K := K) ℓ ⊓
        Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K)) = ⊥ ∧
      stdU (K := K) ℓ ⊔ stdUop ℓ = ⊤ ∧
      ∀ V : Subgroup (Matrix.SpecialLinearGroup ι K),
        pCoreOf p (Subgroup.normalizer (V : Set (Matrix.SpecialLinearGroup ι K))) = V →
        Nat.card V = Nat.card (stdU (K := K) ℓ) →
        V ⊓ Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K)) = ⊥ →
        ∃ u ∈ stdU (K := K) ℓ, V = (stdUop ℓ).map (MulAut.conj u).toMonoidHom := by
  refine ⟨pCoreOf_normalizer_stdUop p hQ, card_stdUop ℓ, ?_,
    sup_stdU_stdUop (exists_lt_of_stdU_ne_bot hne), fun V hVrad hVcard hVbot => ?_⟩
  · rw [hN]
    exact stdUop_inf_stdP ℓ
  have hVp : IsPGroup p V := by
    rw [← hVrad]
    exact pCoreOf_isPGroup p _
  obtain ⟨hVeq, -⟩ := eq_flagKernel_of_pCoreOf slRep p slRep_injective hVrad
  have hbot : flagKernel slRep (fixFlag slRep V) ⊓ flagStab slRep (stdFlag (K := K) ℓ) = ⊥ := by
    rw [← hVeq]
    rw [hN] at hVbot
    exact hVbot
  obtain ⟨M, hM⟩ := exists_stdFlag_eq_top (K := K) ℓ
  have hcompl : ∀ j, ∃ k, IsCompl (stdFlag (K := K) ℓ k) (fixFlag slRep V j) :=
    exists_isCompl_of_inf_flagStab_eq_bot (slRep (ι := ι) (K := K))
      (containsTransvections_slRep (ι := ι) (K := K)) (stdFlag_mono ℓ) (stdFlag_zero ℓ) hM
      (fixFlag_mono (slRep (ι := ι) (K := K)) V) hbot
  have hD : OppData ℓ (fixFlag slRep V) := ⟨fixFlag_mono slRep V, fixFlag_zero slRep V,
    exists_fixFlag_eq_top slRep p V hVp, hcompl⟩
  have hVD : V = (stdU (K := K) hD.idx).map (MulAut.conj hD.elt).toMonoidHom :=
    hVeq.trans hD.flagKernel_eq
  have hcV : Nat.card V = Nat.card (stdU (K := K) hD.idx) :=
    (congrArg (fun X : Subgroup (Matrix.SpecialLinearGroup ι K) => Nat.card X) hVD).trans
      (Subgroup.card_map_of_injective (MulAut.conj _).injective)
  have hc1 : Nat.card (stdU (K := K) ℓ) ≤ Nat.card (stdUop (K := K) hD.idx) := by
    rw [card_stdUop, ← hVcard, hcV]
  have heq : stdUop (K := K) hD.idx = stdU ℓ :=
    Subgroup.eq_of_le_of_card_ge hD.stdUop_idx_le hc1
  have hmem : hD.elt ∈ stdU (K := K) ℓ := by
    rw [← heq]
    exact hD.elt_mem_stdUop
  refine ⟨hD.elt, hmem, hVD.trans ?_⟩
  rw [← map_tInv_stdUop hD.idx, heq]
  rfl

theorem ggOppRadGood_stdU [CharP K 2] {ℓ : ι → ℕ} (hQ : GGRadicalTwo ⊤ (stdU (K := K) ℓ))
    (hN : (⊤ : Subgroup (Matrix.SpecialLinearGroup ι K)) ⊓
      Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K)) = stdP ℓ)
    (hne : stdU (K := K) ℓ ≠ ⊥) : GGOppRadGood ⊤ (stdU (K := K) ℓ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : pCoreOf 2 ((⊤ : Subgroup (Matrix.SpecialLinearGroup ι K)) ⊓
      Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) = stdU ℓ := hQ
  rw [top_inf_eq] at hQ' hN
  rw [ggOppRadGood_iff]
  simp only [top_inf_eq]
  exact ⟨stdUop ℓ, exists_opposite_stdU 2 hQ' hN hne⟩

theorem exists_opposite_sl (p : ℕ) [Fact p.Prime] [CharP K p]
    {Q : Subgroup (Matrix.SpecialLinearGroup ι K)} (hQne : Q ≠ ⊥)
    (hQ : pCoreOf p (Subgroup.normalizer (Q : Set (Matrix.SpecialLinearGroup ι K))) = Q) :
    ∃ V₀ : Subgroup (Matrix.SpecialLinearGroup ι K),
      pCoreOf p (Subgroup.normalizer (V₀ : Set (Matrix.SpecialLinearGroup ι K))) = V₀ ∧
      Nat.card V₀ = Nat.card Q ∧
      V₀ ⊓ Subgroup.normalizer (Q : Set (Matrix.SpecialLinearGroup ι K)) = ⊥ ∧ Q ⊔ V₀ = ⊤ ∧
      ∀ V : Subgroup (Matrix.SpecialLinearGroup ι K),
        pCoreOf p (Subgroup.normalizer (V : Set (Matrix.SpecialLinearGroup ι K))) = V →
        Nat.card V = Nat.card Q →
        V ⊓ Subgroup.normalizer (Q : Set (Matrix.SpecialLinearGroup ι K)) = ⊥ →
        ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom := by
  have hQp : IsPGroup p Q := by
    rw [← hQ]
    exact pCoreOf_isPGroup p _
  obtain ⟨hQeq, hQN⟩ := eq_flagKernel_of_pCoreOf (slRep (ι := ι) (K := K)) p slRep_injective hQ
  obtain ⟨g, ℓ, hF⟩ := exists_eq_flagMap_stdFlag (fixFlag_mono (slRep (ι := ι) (K := K)) Q)
    (fixFlag_zero (slRep (ι := ι) (K := K)) Q)
    (exists_fixFlag_eq_top (slRep (ι := ι) (K := K)) p Q hQp)
  have hQU : Q = (stdU (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [stdU, ← flagKernel_flagMap, ← hF]
    exact hQeq
  have hQP : Subgroup.normalizer (Q : Set (Matrix.SpecialLinearGroup ι K)) =
      (stdP (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [stdP, ← flagStab_flagMap, ← hF, ← hQN]
  have htop : ∀ x : Matrix.SpecialLinearGroup ι K,
      x ∈ Subgroup.normalizer ((⊤ : Subgroup (Matrix.SpecialLinearGroup ι K)) :
        Set (Matrix.SpecialLinearGroup ι K)) := fun x =>
    Subgroup.mem_normalizer_iff.mpr fun _ =>
      ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
  have hQ0 : stdU (K := K) ℓ = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hQU, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]
  have hrad0 : pCoreOf p (Subgroup.normalizer
      (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K))) = stdU ℓ := by
    have h := pCoreOf_inf_normalizer_map_conj p (G₀ := ⊤) (V := Q) (by rwa [top_inf_eq])
      (htop g⁻¹)
    rw [top_inf_eq] at h
    rw [hQ0]
    exact h
  have hN0 : Subgroup.normalizer (stdU (K := K) ℓ : Set (Matrix.SpecialLinearGroup ι K)) =
      stdP ℓ := by
    rw [hQ0, ← GGTwoSig.map_conj_normalizer, hQP, ← GGTwoSig.map_conj_mul,
      inv_mul_cancel, GGTwoSig.map_conj_one]
  have hne0 : stdU (K := K) ℓ ≠ ⊥ := fun h => hQne (by rw [hQU, h, Subgroup.map_bot])
  have h := exists_opposite_map_conj p (G₀ := ⊤) (Q := stdU (K := K) ℓ)
    (by simp only [top_inf_eq]; exact ⟨stdUop ℓ, exists_opposite_stdU p hrad0 hN0 hne0⟩)
    (htop g)
  rw [← hQU] at h
  simpa only [top_inf_eq] using h

theorem ggOppRadGood_sl [CharP K 2] {Q : Subgroup (Matrix.SpecialLinearGroup ι K)}
    (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ⊤ Q) : GGOppRadGood ⊤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : pCoreOf 2 ((⊤ : Subgroup (Matrix.SpecialLinearGroup ι K)) ⊓
      Subgroup.normalizer (Q : Set (Matrix.SpecialLinearGroup ι K))) = Q := hQ
  rw [top_inf_eq] at hQ'
  rw [ggOppRadGood_iff]
  simp only [top_inf_eq]
  exact exists_opposite_sl 2 hQne hQ'

omit [Finite K] in
theorem eq_one_of_mem_center_of_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP K p]
    {z : Matrix.SpecialLinearGroup ι K}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup ι K)) (hp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · exact Subsingleton.elim _ _
  have hcp : c ^ p = 1 := by
    have h1 := congrArg (fun x : Matrix.SpecialLinearGroup ι K => (x : Matrix ι ι K) a a) hp
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h1
    rw [← hc, Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h1
    simpa using h1
  have hc1 : c = 1 := frobenius_inj K p (by simpa [frobenius_def] using hcp)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [← hc, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

omit [Finite K] in
theorem eq_one_of_mem_center_of_sq_eq_one [CharP K 2] {z : Matrix.SpecialLinearGroup ι K}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup ι K)) (h2 : z ^ 2 = 1) : z = 1 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  eq_one_of_mem_center_of_pow_eq_one 2 hz h2

theorem exists_opposite_of_sl (p : ℕ) [Fact p.Prime] [CharP K p] {G : Type*} [Group G] [Finite G]
    (ψ : Matrix.SpecialLinearGroup ι K →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup ι K)) {Q : Subgroup G}
    (hQne : Q ≠ ⊥) (hQ : pCoreOf p (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = Q) :
    ∃ V₀ : Subgroup G, pCoreOf p (ψ.range ⊓ Subgroup.normalizer (V₀ : Set G)) = V₀ ∧
      Nat.card V₀ = Nat.card Q ∧ V₀ ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ ∧
      Q ⊔ V₀ = ψ.range ∧
      ∀ V : Subgroup G, pCoreOf p (ψ.range ⊓ Subgroup.normalizer (V : Set G)) = V →
        Nat.card V = Nat.card Q → V ⊓ (ψ.range ⊓ Subgroup.normalizer (Q : Set G)) = ⊥ →
        ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom :=
  exists_opposite_of_lift ψ p hker
    (fun _ hz hp => eq_one_of_mem_center_of_pow_eq_one p (hker hz) hp)
    (fun _ hQne' hQ' => exists_opposite_sl p hQne' hQ') hQne hQ

theorem ggOppRadGood_of_sl [CharP K 2] {G : Type*} [Group G] [Finite G]
    (ψ : Matrix.SpecialLinearGroup ι K →* G)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup ι K)) {Q : Subgroup G}
    (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ψ.range Q) : GGOppRadGood ψ.range Q :=
  GGOppRadGood.of_lift ψ hker (fun _ hz h2 => eq_one_of_mem_center_of_sq_eq_one (hker hz) h2)
    (fun _ hQne' hQ' => ggOppRadGood_sl hQne' hQ') hQne hQ

theorem intrinsic_opposition_of_sl_central_quotient
    {F : Type} [Field F] [Finite F] {r n : ℕ}
    [Fact r.Prime] [CharP F r]
    {L : Type} [Group L] [Finite L]
    (π : Matrix.SpecialLinearGroup (Fin n) F →* L)
    (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (Q : Subgroup L) (hQne : Q ≠ ⊥)
    (hQ : pCoreOf r (Subgroup.normalizer (Q : Set L)) = Q) :
    ∃ V : Subgroup L,
      pCoreOf r (Subgroup.normalizer (V : Set L)) = V ∧
      Nat.card V = Nat.card Q ∧
      V ⊓ Subgroup.normalizer (Q : Set L) = ⊥ ∧
      Q ⊔ V = ⊤ ∧
      ∀ W : Subgroup L,
        pCoreOf r (Subgroup.normalizer (W : Set L)) = W →
        Nat.card W = Nat.card Q →
        W ⊓ Subgroup.normalizer (Q : Set L) = ⊥ →
        ∃ q ∈ Q, W = V.map (MulAut.conj q).toMonoidHom := by
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπ
  have h := exists_opposite_of_sl r π hker hQne (by rw [hrange, top_inf_eq]; exact hQ)
  rw [hrange] at h
  simpa only [top_inf_eq] using h

end GGOppRad

end CFSG.StandardType
