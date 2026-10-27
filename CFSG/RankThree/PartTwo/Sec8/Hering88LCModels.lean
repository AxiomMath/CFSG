module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2
public import CFSG.RankThree.PartTwo.Sec8.HeringD4KF84

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section General

variable {M N : Type*} [Group M] [Group N]

@[expose] def LC2At (g : M) : Prop :=
  inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set M)) ≠ ⊥ →
    ∀ p ∈ Subgroup.centralizer ({g} : Set M), ∀ q ∈ Subgroup.centralizer ({g} : Set M),
      p * q * p⁻¹ * q⁻¹ ∈ inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set M))

theorem residual_centralizer_map (e : M ≃* N) (g : M) :
    (inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set M))).map e.toMonoidHom =
      inSubgroup perfectResidual (Subgroup.centralizer ({e g} : Set N)) := by
  rw [KFacts.map_inSubgroup_perfectResidual, map_centralizer_singleton]

theorem LC2At.of_mulEquiv (e : M ≃* N) {g : M} (h : LC2At (e g)) : LC2At g := by
  intro hne p hp q hq
  have hne' : inSubgroup perfectResidual (Subgroup.centralizer ({e g} : Set N)) ≠ ⊥ := by
    rw [← residual_centralizer_map e g]
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : e x ∈ (inSubgroup perfectResidual (Subgroup.centralizer ({g} : Set M))).map
        e.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (e.injective (this.trans (map_one e).symm))
  have hpe : e p ∈ Subgroup.centralizer ({e g} : Set N) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hp]
  have hqe : e q ∈ Subgroup.centralizer ({e g} : Set N) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hq]
  have h1 := h hne' (e p) hpe (e q) hqe
  rw [← residual_centralizer_map e g] at h1
  obtain ⟨r, hr, hre⟩ := h1
  have : r = p * q * p⁻¹ * q⁻¹ := e.injective (by
    rw [show e r = e.toMonoidHom r from rfl, hre]
    simp only [map_mul, map_inv])
  rwa [this] at hr

theorem lc2At_of_commutator {g : M} {S : Subgroup M}
    (hSC : S ≤ Subgroup.centralizer ({g} : Set M)) (hS : ⁅S, S⁆ = S)
    (hcomm : ∀ p ∈ Subgroup.centralizer ({g} : Set M),
      ∀ q ∈ Subgroup.centralizer ({g} : Set M), p * q * p⁻¹ * q⁻¹ ∈ S) : LC2At g := by
  intro _ p hp q hq
  rw [Sec21.Item228Census3Proof.inSubgroup_perfectResidual_eq_of_commutator hSC hS hcomm]
  exact hcomm p hp q hq

theorem lc2At_of_isPerfect [Finite M] {g : M}
    (hC : Group.IsPerfect (Subgroup.centralizer ({g} : Set M))) : LC2At g := by
  intro _ p hp q hq
  rw [inSubgroup_perfectResidual_of_isPerfect hC]
  exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)

structure InnerFacts (Q : Type*) [Group Q] : Prop where
  center : ∀ z : Q, (∀ y : Q, z * y = y * z) → z = 1
  lc1 : ∀ τ : MulAut Q, (∃ k : ℕ, τ ^ 2 ^ k = 1) → ∀ g : Q, g ^ 3 = 1 → g ≠ 1 → τ g = g →
    KFacts.IsInnerAut τ
  lc2 : ∀ g : Q, g ^ 3 = 1 → g ≠ 1 → LC2At g

theorem InnerFacts.of_mulEquiv (e : M ≃* N) (h : InnerFacts N) : InnerFacts M where
  center z hz := by
    have : e z = 1 := h.center (e z) fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz y]
    exact e.injective (this.trans (map_one e).symm)
  lc1 τ hτ g hg3 hg1 hτg := by
    obtain ⟨k, hk⟩ := hτ
    refine (KFacts.isInnerAut_congr e τ).mp (h.lc1 (MulAut.congr e τ) ⟨k, ?_⟩ (e g)
      (by rw [← map_pow, hg3, map_one]) (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm)))
      ?_)
    · rw [← map_pow, hk, map_one]
    · change e (τ (e.symm (e g))) = e g
      rw [MulEquiv.symm_apply_apply, hτg]
  lc2 g hg3 hg1 := LC2At.of_mulEquiv e (h.lc2 (e g) (by rw [← map_pow, hg3, map_one])
    (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))))

theorem isInnerAut_of_pow_two_pow_of_normalForm {Γ : Type*} [Group Γ] (ψ : Γ →* MulAut M)
    (h : ∀ α : MulAut M, ∃ (m : M) (γ : Γ), α = MulAut.conj m * ψ γ)
    (hΓ : ∀ γ : Γ, γ ^ 3 = 1) {α : MulAut M} {k : ℕ} (hα : α ^ 2 ^ k = 1) :
    KFacts.IsInnerAut α := by
  open CFSG.ComponentClassification.OuterAutomorphisms in
  set π := QuotientGroup.mk' (inner M) with hπ
  obtain ⟨m, γ, rfl⟩ := h α
  have hm : π (MulAut.conj m) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨m, rfl⟩
  have h3 : orderOf (π (MulAut.conj m * ψ γ)) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
    rw [map_mul, hm, one_mul, ← map_pow, ← map_pow, hΓ, map_one, map_one])
  have h2 : orderOf (π (MulAut.conj m * ψ γ)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow, hα, map_one])
  have h1 : orderOf (π (MulAut.conj m * ψ γ)) = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h := Nat.dvd_gcd h3 h2
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at h
  have := (QuotientGroup.eq_one_iff (N := inner M) _).mp (orderOf_eq_one_iff.mp h1)
  exact this

theorem conj_ne_one (g : M) {z : M} (hz : z ≠ 1) : g * z * g⁻¹ ≠ 1 := by
  intro h
  apply hz
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem ringEquiv_pow_three_of_card_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (σ : K ≃+* K) : σ ^ 3 = 1 := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have h1 := pow_card_eq_one' (G := K ≃+* K) (x := σ)
  rwa [h] at h1

end General

section Models


theorem innerFacts_g2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    InnerFacts (adjointGroup Tag.G2 K) := by
  have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]; norm_num
  have hZ : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨fun z hz => ?_, fun τ hτ _ _ _ _ => ?_, fun z hz3 hz1 => ?_⟩
  · have : z ∈ Subgroup.center (adjointGroup Tag.G2 K) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rwa [hZ, Subgroup.mem_bot] at this
  · obtain ⟨k, hk⟩ := hτ
    exact isInnerAut_of_pow_two_pow_of_normalForm (KFacts.g2FieldHom K)
      (KFacts.g2_automorphism_normal_form hK3 hK4).1 (ringEquiv_pow_three_of_card_eight hK) hk
  · obtain ⟨g, hg⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds K h3 hK4 z hz3 hz1
    have he : (MulAut.conj g : adjointGroup Tag.G2 K ≃* adjointGroup Tag.G2 K) z =
        g * z * g⁻¹ := rfl
    refine LC2At.of_mulEquiv (MulAut.conj g) ?_
    rw [he]
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hz'1 : g * z * g⁻¹ ≠ 1 := conj_ne_one g hz1
    rcases hg with hS | hL
    · exact lc2At_of_isPerfect
        (Sec11.KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hK4 hS hz'3 hz'1).1
    · obtain ⟨hcomm, -⟩ := Sec11.KS11Lie4Proof.g2ThreeBCentMinus_holds K h3 hK4 _ hL hz'3 hz'1
      intro _ p hp q hq
      rw [Item83Proof.inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2 hK3 hK4 hL hz'3 hz'1]
      exact hcomm p hp q hq

theorem innerFacts_triality {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    InnerFacts (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hK8 : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hK4 : 4 ≤ Nat.card K := by rw [hK8]; norm_num
  have P : Sec19.D4Par 1 K σ := ⟨le_rfl, hK, hσ⟩
  have hσ3 : σ ^ 3 = 1 := P.sigma_pow_three
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hq3 : ¬ 3 ∣ 2 ^ 1 := by norm_num
  refine ⟨fun z hz => ?_, fun τ hτ _ _ _ _ => ?_, fun z hz3 hz1 => ?_⟩
  · have : z ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_center_iff.mpr fun y => (hz y).symm
    rwa [hZ, Subgroup.mem_bot] at this
  · obtain ⟨k, hk⟩ := hτ
    refine isInnerAut_of_pow_two_pow_of_normalForm (fieldActorHom (t := TwistTag.D4) σ)
      (fun α => ?_) (ringEquiv_pow_three_of_card_eight hK8) hk
    obtain ⟨g, δ, hgδ⟩ := KFacts.exists_conj_mul_fieldActor le_rfl hK hσ α
    exact ⟨g, δ, hgδ⟩
  · obtain ⟨g, hg⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ 1) σ hK hσ hq3 z hz3 hz1
    have he : (MulAut.conj g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) z = g * z * g⁻¹ := rfl
    refine LC2At.of_mulEquiv (MulAut.conj g) ?_
    rw [he]
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hz'1 : g * z * g⁻¹ ≠ 1 := conj_ne_one g hz1
    rcases hg with hS | hC
    ·
      intro hne
      exact (hne (HeringD4.residual_eq_bot_two hK hσ hS hz'3 hz'1)).elim
    ·
      obtain ⟨hcomm, -⟩ := Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ 1) σ hK hσ hq3 _ hC
        hz'3 hz'1
      refine lc2At_of_commutator (S := Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
        (fun s hs => ?_) ?_ hcomm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hC s hs
      · exact Subgroup.isPerfect_iff.mp (Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4).1

end Models

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
