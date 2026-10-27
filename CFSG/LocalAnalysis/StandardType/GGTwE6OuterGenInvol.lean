module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeOuterInn

public section

namespace CFSG.StandardType.TwE6OuterGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.SeitzReduction.TwistedE6Pilot

theorem mul_comm_of_mem_normal {G : Type*} [Group G] {N U : Subgroup G} (hN : N.Normal)
    (hUN : ∀ u ∈ U, u ∈ N → u = 1) {s : G} (hs : s ∈ N) (hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U)
    {t : G} (ht : t ∈ U) : s * t = t * s := by
  have hU : s * t * s⁻¹ * t⁻¹ ∈ U := mul_mem (hsU t ht) (inv_mem ht)
  have hN' : s * t * s⁻¹ * t⁻¹ ∈ N := by
    have h := mul_mem hs (hN.conj_mem s⁻¹ (inv_mem hs) t)
    rwa [← mul_assoc, ← mul_assoc] at h
  calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
    _ = t * s := by rw [hUN _ hU hN', one_mul]

section Normal


variable {K : Type} [Field K] [Finite K]

theorem normal_range_twistedE6InndiagConj {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (twistedE6InndiagConj K σ).range.Normal := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  rw [range_twistedE6InndiagConj, ← hker]
  exact MonoidHom.normal_ker Θ

theorem exists_outer_involution_commute {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {U : Subgroup (MulAut (twistedE6RootGroup K σ))} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUI : ∀ u ∈ U, u ∈ (twistedE6InndiagConj K σ).range → u = 1) :
    ∃ t ∈ U, t ^ 2 = 1 ∧ t ∉ (twistedE6InndiagConj K σ).range ∧
      ∀ s ∈ (twistedE6InndiagConj K σ).range, (∀ u ∈ U, s * u * s⁻¹ ∈ U) → s * t = t * s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hU2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hU (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  rw [← Subgroup.orderOf_coe] at hx
  refine ⟨x, x.2, by rw [← hx]; exact pow_orderOf_eq_one _, fun h => ?_, fun s hs hsU =>
    mul_comm_of_mem_normal (normal_range_twistedE6InndiagConj hp hf hK σ hσ) hUI hs hsU x.2⟩
  rw [hUI x x.2 h, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem coe_mem_of_conj_mem_range {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {a : twistedE6InndiagGL K σ}
    (ha : twistedE6InndiagConj K σ a ∈
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range) :
    (a : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := by
  obtain ⟨g, hg⟩ := ha
  have h : twistedE6InndiagConj K σ ⟨g, le_sup_left (b := twistedE6DiagGL K σ) g.2⟩ =
      twistedE6InndiagConj K σ a := by
    rw [← hg]
    exact MulEquiv.ext fun _ => Subtype.ext rfl
  rw [← twistedE6InndiagConj_injective hℓ hf hK σ hσ h]
  exact g.2

end Normal

section Outer


variable {K : Type} [Field K] [Finite K]

private theorem eq_one_of_inv_conj_of_commute {Q : Type*} [Group Q] {d e p : Q}
    (hinv : e * p * e⁻¹ = p⁻¹) (hdp : d * p = p * d) (hc : d * e * p = p * (d * e))
    (h3 : p ^ 3 = 1) : p = 1 := by
  have hep : e * p = p * e := by
    refine mul_left_cancel (a := d) ?_
    calc d * (e * p) = d * e * p := (mul_assoc _ _ _).symm
      _ = p * (d * e) := hc
      _ = d * p * e := by rw [← mul_assoc, hdp]
      _ = d * (p * e) := mul_assoc _ _ _
  have hp : p = p⁻¹ := by rw [← hinv, hep, mul_inv_cancel_right]
  have h2 : p * p = 1 := by
    calc p * p = p * p⁻¹ := congrArg (p * ·) hp
      _ = 1 := mul_inv_cancel p
  calc p = p ^ 3 * (p * p)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem mem_range_conj_of_commute_outer {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {t x : MulAut (twistedE6RootGroup K σ)}
    (ht2 : t ^ 2 = 1) (htI : t ∉ (twistedE6InndiagConj K σ).range)
    (hx : x ∈ (twistedE6InndiagConj K σ).range) (hxt : t * x = x * t) :
    x ∈ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  haveI : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hσσ := apply_apply_eq hK hσ'
  set I := (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range
    with hI
  haveI : I.Normal := RootCentExc.normal_range_mulAutConj
  have hψ : ∀ y ∈ I, QuotientGroup.mk' I y = 1 := fun y hy => by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).2 hy
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, -, -, -, hout⟩, hfield, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, htd⟩ : ∃ g u, t = MulAut.conj g *
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ := by
    rcases hout t ht2 with h | ⟨-, h⟩
    · exact absurd (by rw [range_twistedE6InndiagConj]; exact Subgroup.mem_sup_left h) htI
    · exact h
  have hη : fieldActor σ σ = etaAut σ.toRingHom hσσ :=
    MulEquiv.ext fun y => Subtype.ext (by rw [hfield, coe_etaAut])
  obtain ⟨b', hb'⟩ : compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈
      (RootCentExc.compatParamAut σ.toRingHom).range := by
    rw [NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag]
    exact ⟨u, rfl⟩
  have hx' : x ∈ I ⊔ (RootCentExc.compatParamAut σ.toRingHom).range := by
    rw [NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag]
    rw [range_twistedE6InndiagConj] at hx
    exact hx
  obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  have hc := congrArg (QuotientGroup.mk' I) hxt
  rw [htd, hη, ← hb'] at hc
  simp only [map_mul, hψ _ ⟨g, rfl⟩, hψ a ha, one_mul] at hc
  have hinv := NoOffTwE6Three.etaAut_conj_compatParamAut_mul_inv_quotient σ.toRingHom hσσ hσ'
    (TwE6Toral.two_le_two_pow hf) hK b
  rw [map_mul, map_mul, map_inv] at hinv
  have hdp : QuotientGroup.mk' I (RootCentExc.compatParamAut σ.toRingHom b') *
      QuotientGroup.mk' I (RootCentExc.compatParamAut σ.toRingHom b) =
      QuotientGroup.mk' I (RootCentExc.compatParamAut σ.toRingHom b) *
      QuotientGroup.mk' I (RootCentExc.compatParamAut σ.toRingHom b') := by
    rw [← map_mul, ← map_mul, mul_comm b' b, map_mul, map_mul]
  have h3 : QuotientGroup.mk' I (RootCentExc.compatParamAut σ.toRingHom b) ^ 3 = 1 := by
    rw [← map_pow]
    exact hψ _ (TwE6Toral.compatParamAut_pow_three_mem (TwE6Toral.two_le_two_pow hf) hK hσ' b)
  have hP := eq_one_of_inv_conj_of_commute hinv hdp hc h3
  rw [QuotientGroup.mk'_apply] at hP
  exact mul_mem ha ((QuotientGroup.eq_one_iff _).1 hP)

end Outer

end CFSG.StandardType.TwE6OuterGen

end
