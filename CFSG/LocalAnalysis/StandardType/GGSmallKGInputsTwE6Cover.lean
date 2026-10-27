module

public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwRank
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

@[expose] def GGTwE6ThreeSixInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    3 ∣ n → ∃ E : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E

@[expose] def GGTwE6ThreeCoverCenterInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      3 ∣ Nat.card (Subgroup.center L') →
      ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E

namespace SmallKG

theorem exists_isElemAbelian_lift {L' R : Type*} [Group L'] [Group R] [Finite L'] {p : ℕ}
    [hp : Fact p.Prime] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ¬ p ∣ Nat.card ψ.ker) {E : Subgroup R} (hE : IsElemAbelian p E) :
    ∃ E' : Subgroup L', IsElemAbelian p E' ∧ Nat.card E' = Nat.card E := by
  set Y : Subgroup L' := E.comap ψ with hY
  set f : Y →* E := (ψ.comp Y.subtype).codRestrict E (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨l, rfl⟩ := hψ e
    exact ⟨⟨l, he⟩, rfl⟩
  have hEp : IsPGroup p (⊤ : Subgroup E) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE.2 _ g.1.2))⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow p Y))
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hEp le_top).symm
  have hinj : ∀ y ∈ (Q₀ : Subgroup Y), f y = 1 → y = 1 := by
    intro y hy h1
    have hyk : (y : L') ∈ ψ.ker := congrArg Subtype.val h1
    obtain ⟨k, hk⟩ := Q₀.isPGroup' ⟨y, hy⟩
    have hord : orderOf (⟨y, hyk⟩ : ψ.ker) ∣ p ^ k := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
      have := congrArg (fun z : (Q₀ : Subgroup Y) => ((z : Y) : L')) hk
      simpa using this
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hord
    rcases j with _ | j
    · have h1' : (⟨y, hyk⟩ : ψ.ker) = 1 := orderOf_eq_one_iff.1 (by simpa using hj')
      have h2 : (y : L') = 1 := congrArg Subtype.val h1'
      exact Subtype.ext h2
    · exfalso
      apply hker
      have h2 := orderOf_dvd_natCard (⟨y, hyk⟩ : ψ.ker)
      rw [hj'] at h2
      exact (dvd_pow_self p (Nat.succ_ne_zero j)).trans h2
  have hcardQ : Nat.card (Q₀ : Subgroup Y) = Nat.card E := by
    rw [← TableBExc.E6Three.card_map_eq_of_ker f hinj, hQ, Subgroup.card_top]
  have hQab : IsElemAbelian p (Q₀ : Subgroup Y) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · have hc : f a * f b = f b * f a :=
        Subtype.ext (TableB.IsElemAbelian.comm hE (f a).2 (f b).2)
      have h1 : f ((a : Y) * b * ((b : Y) * a)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, hc, mul_inv_cancel]
      have h2 := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) h1
      exact mul_inv_eq_one.mp h2
    · refine hinj _ (pow_mem hy p) ?_
      rw [map_pow]
      exact Subtype.ext (hE.2 _ (f y).2)
  refine ⟨(Q₀ : Subgroup Y).map Y.subtype, TableB.isElemAbelian_map hQab _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hcardQ]

theorem orderOf_two_pow_zmod_three {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) :
    orderOf (((2 ^ n : ℕ)) : ZMod 3) = 2 := by
  have h0 : (((2 ^ n + 1 : ℕ)) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).2 h3
  have h1 : (((2 ^ n : ℕ)) : ZMod 3) = 2 := by
    have h0' : (((2 ^ n : ℕ)) : ZMod 3) + 1 = 0 := by exact_mod_cast h0
    generalize (((2 ^ n : ℕ)) : ZMod 3) = x at h0' ⊢
    revert x
    decide
  rw [h1]
  exact orderOf_eq_prime (by decide) (by decide)

section Five


theorem exists_isElemAbelian_recipeR_five {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ E : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hbij : Function.Bijective (iterateFrobenius K 2 n) :=
    ⟨(iterateFrobenius K 2 n).injective,
      Finite.surjective_of_injective (iterateFrobenius K 2 n).injective⟩
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n) hbij with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨E₀, hE₀, hc⟩ := exists_elemAbelian_twistedE6_three_two Nat.prime_two hn K hK σ hσ
    (orderOf_two_pow_zmod_three h3)
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := hσ
  obtain ⟨e, T₀, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ.toRingHom hσ'
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom
    hσ').2.2.1
  have hZ : Subgroup.center ↥(twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* ↥(twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hcard : Nat.card (E₀.map (recipeEquiv T hZ).toMonoidHom) = Nat.card E₀ :=
    Subgroup.card_map_of_injective (recipeEquiv T hZ).injective
  have h5 : 3 ^ 5 ≤ Nat.card (E₀.map (recipeEquiv T hZ).toMonoidHom) := by
    rw [hcard]
    omega
  exact ⟨E₀.map (recipeEquiv T hZ).toMonoidHom, TableB.isElemAbelian_map hE₀ _, h5⟩

end Five

end SmallKG

theorem ggTwE6ThreeCoverRankInput_of_inputs
    (hS : GGTwE6ThreeSixInput) (hC : GGTwE6ThreeCoverCenterInput) :
    GGTwE6ThreeCoverRankInput := by
  intro K _ _ n hn hK h3 L' _ _ ψ hψ hker hperf
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker
    (TwE6Delta.center_recipeR_eq_bot hn hK)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hz : 3 ∣ Nat.card (Subgroup.center L')
  · obtain ⟨E, hE, hEc⟩ := hC K n hn hK h3 L' ψ hψ hker hperf hz
    exact ⟨⟨E, hE, le_trans (by norm_num) hEc⟩, fun _ => ⟨E, hE, hEc⟩⟩
  · have hk : ¬ 3 ∣ Nat.card ψ.ker := by
      rw [hkc]
      exact hz
    obtain ⟨E₅, hE₅, hc₅⟩ := SmallKG.exists_isElemAbelian_recipeR_five hn hK h3
    obtain ⟨E', hE', hc'⟩ := SmallKG.exists_isElemAbelian_lift hψ hk hE₅
    refine ⟨⟨E', hE', hc' ▸ hc₅⟩, fun h => ?_⟩
    rcases h with h3n | h3z
    · obtain ⟨E₆, hE₆, hc₆⟩ := hS K n hn hK h3 h3n
      obtain ⟨E'', hE'', hc''⟩ := SmallKG.exists_isElemAbelian_lift hψ hk hE₆
      exact ⟨E'', hE'', hc'' ▸ hc₆⟩
    · exact absurd h3z hz

end CFSG.StandardType
