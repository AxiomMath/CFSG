module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.EmptyFaithful.S152RD4
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.Timmesfeld.ExceptionalOrders


theorem exists_conj_of_pow_seven {X : Type} [Group X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) (α : MulAut X) (hα : α ^ 7 = 1) :
    ∃ c : X, α = MulAut.conj c := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hm
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  set α' := MulAut.congr e α with hα'
  have h7 : Θ α' ^ 7 = 1 := by rw [← map_pow, hα', ← map_pow, hα, map_one, map_one]
  have hΘ : Θ α' = 1 := by
    have h1 : orderOf (Θ α') ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    have h2 : orderOf (Θ α') ∣ 3 := by
      have h3 := orderOf_dvd_natCard (Θ α')
      rwa [hcard] at h3
    have h4 : orderOf (Θ α') ∣ Nat.gcd 7 3 := Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using h4))
  have hmem : α' ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* _).range := by
    rw [← hker]
    exact hΘ
  obtain ⟨g, hg⟩ := hmem
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 : α' (e x) = e (α x) := by
    rw [hα']
    change e (α (e.symm (e x))) = e (α x)
    rw [MulEquiv.symm_apply_apply]
  have h2 : α' (e x) = g * e x * g⁻¹ := by rw [← hg]; rfl
  have h3 : α x = e.symm (g * e x * g⁻¹) := by
    rw [← h2, h1, MulEquiv.symm_apply_apply]
  rw [h3, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem center_eq_bot {X : Type} [Group X] (hm : ChevalleyExceptionalModel X .trialityD4 2 1) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, K, _, _, σ, -, -, ⟨e⟩⟩ := exists_mulEquiv_triality_model hm
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    have h1 := congrArg e (hx (e.symm y))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  rw [hZ, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

theorem isSimpleGroup_of_perfect {X : Type} [Group X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) [Group.IsPerfect X] : IsSimpleGroup X := by
  obtain ⟨-, K, _, _, σ, -, -, ⟨e⟩⟩ := exists_mulEquiv_triality_model hm
  have hperf : Group.IsPerfect ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have := (isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 K σ
    (Subgroup.isPerfect_iff.mp hperf)).1
  exact e.isSimpleGroup

theorem not_dvd_card_of_sylow_le {X : Type} [Group X] [Finite X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) {U M : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) (hUM : U ≤ M) (hM : M ≠ ⊤) :
    ¬ 49 ∣ Nat.card M := by
  obtain ⟨K, _, _, σ, φ, hK, hσ, hUφ, hres, -⟩ := even_rank_two_residual_triality hm hU
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  obtain ⟨j, hj⟩ := (hres.2.2.1 M' (hUM.trans hMM')).mp hM'.covBy_top
  set a := d4Index j with ha
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have hcardM' : Nat.card M' = Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
    rw [hj, Subgroup.card_map_of_injective φ.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP := card_graphFixedParabolic_singleton_d4 σ a
  have hB := card_graphFixedRootBorel (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) σ.surjective
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUU : Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) = Nat.card U := by
    have h1 : Nat.card (U.map φ.toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective φ.injective
    rw [hUφ] at h1
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv).symm
  obtain ⟨m, hm2⟩ := IsPGroup.iff_card.mp hU.2.1
  have hLa : ∀ b, Nat.card (orbitField TwistTag.D4 K σ.toRingHom b) =
      (2 ^ 1) ^ (TwistTag.D4.orbit b).card := fun b =>
    card_orbitField_D4_orientation Nat.prime_two le_rfl hK (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ c) b
  have hT : Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∣ 7 := by
    rw [graphFixedRootTorus_eq_compatTorus σ.surjective]
    have h1 := card_compatTorus_mul (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    rw [card_compatSubgroup, Finset.prod_congr rfl fun b _ => by rw [hLa b]] at h1
    have h2 : ∏ b : Fin TwistTag.D4.foldedTag.rank, ((2 ^ 1) ^ (TwistTag.D4.orbit b).card - 1) =
        7 := by decide
    rw [h2] at h1
    exact Dvd.intro _ h1
  have hs : (TwistTag.D4.orbit a).card = 3 ∨ (TwistTag.D4.orbit a).card = 1 := by
    rcases foldedRank_D4_cases a with h | h <;> rw [h] <;> decide
  intro h49
  have hdvd : 49 ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) *
      (2 ^ m * (1 + (2 ^ 1) ^ (TwistTag.D4.orbit a).card)) := by
    have h1 := h49.trans (Subgroup.card_dvd_of_le hMM')
    rw [hcardM', hP, hB, hUU, hm2, hLa a] at h1
    rwa [mul_assoc] at h1
  have hcop : Nat.Coprime 49 (2 ^ m * (1 + (2 ^ 1) ^ (TwistTag.D4.orbit a).card)) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num)) ?_
    rcases hs with h | h <;> rw [h] <;> norm_num
  have h7 := (hcop.dvd_of_dvd_mul_right hdvd).trans hT
  norm_num at h7

end CFSG.Quasithin.H13.D42
