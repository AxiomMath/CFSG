module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.Evidence.TimmesfeldAGLModels
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Evidence.TimmesfeldAGL
public import CFSG.Sporadic.J2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors tors_of_not_dvd)

private theorem gctt_torsBound_psl {r : ℕ} (hr : r.Prime) {f : ℕ} (hf : 1 ≤ f)
    (h3 : 3 ∣ 2 ^ f + 1) : torsBound r .PSL 6 2 f = 1 := by
  have hpow : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd hpow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have h3nd : ¬ 3 ∣ 2 ^ f - 1 := by
    intro hd
    have hsub : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h3 hd
    have heq : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [heq] at hsub
    norm_num at hsub
  have h6 : Nat.Coprime 6 (2 ^ f - 1) := by
    refine Nat.coprime_of_dvd fun k hk hk6 hkd => ?_
    have hk6' : k ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hk6
    rcases (hk.dvd_mul).mp hk6' with hk2 | hk3
    · have hk_eq : k = 2 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 hk2
      subst hk_eq
      exact (Odd.not_two_dvd_nat hodd) hkd
    · have hk_eq : k = 3 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).1 hk3
      subst hk_eq
      exact h3nd hkd
  have hg : genericOrders .PSL 6 2 f = (1, 1) := by
    simp only [genericOrders]
    exact Prod.ext h6 rfl
  have hex : exceptionalOrders .PSL 6 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  unfold torsBound
  rw [hg, hex]
  simp [h1]

private theorem gctt_torsBound_psu {r : ℕ} (hr : r.Prime) {f : ℕ} (hf : 1 ≤ f)
    (h3 : 3 ∣ 2 ^ f - 1) : torsBound r .PSU 6 2 f = 1 := by
  have hpow : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hodd : Odd (2 ^ f + 1) := by
    have heven : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact Even.add_odd heven odd_one
  have h3nd : ¬ 3 ∣ 2 ^ f + 1 := by
    intro hd
    have hsub : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hd h3
    have heq : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [heq] at hsub
    norm_num at hsub
  have h6 : Nat.Coprime 6 (2 ^ f + 1) := by
    refine Nat.coprime_of_dvd fun k hk hk6 hkd => ?_
    have hk6' : k ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hk6
    rcases (hk.dvd_mul).mp hk6' with hk2 | hk3
    · have hk_eq : k = 2 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 hk2
      subst hk_eq
      exact (Odd.not_two_dvd_nat hodd) hkd
    · have hk_eq : k = 3 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).1 hk3
      subst hk_eq
      exact h3nd hkd
  have hg : genericOrders .PSU 6 2 f = (1, 1) := by
    simp only [genericOrders]
    exact Prod.ext h6 rfl
  have hf1 : f ≠ 1 := by
    intro h
    subst h
    norm_num at h3
  have hex : exceptionalOrders .PSU 6 2 f = (1, 1) := by
    simp [exceptionalOrders, hf1]
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  unfold torsBound
  rw [hg, hex]
  simp [h1]

private theorem gctt_torsBound_pomm {r : ℕ} (hr : r.Prime) {f : ℕ} (hf : 1 ≤ f) :
    torsBound r .POmegaMinus 4 2 f = 1 := by
  have hodd : Odd ((2 ^ f) ^ 4 + 1) := by
    have heven : Even ((2 ^ f) ^ 4) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
    exact Even.add_odd heven odd_one
  have hcop : Nat.Coprime 4 ((2 ^ f) ^ 4 + 1) := by
    change Nat.Coprime (2 ^ 2) ((2 ^ f) ^ 4 + 1)
    exact (Nat.coprime_pow_left_iff (by norm_num) 2 _).2 (Nat.coprime_two_left.2 hodd)
  have hg : genericOrders .POmegaMinus 4 2 f = (1, 1) := by
    simp only [genericOrders]
    exact Prod.ext hcop rfl
  have hex : exceptionalOrders .POmegaMinus 4 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  unfold torsBound
  rw [hg, hex]
  simp [h1]

theorem gctt_centre_bot {K X : Type} [Group K] [Finite K] [Group X] (hK : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n p f)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f))
    (hb : ∀ r : ℕ, r.Prime → torsBound r t n p f = 1) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  by_contra hg1
  have hne : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hle := center_torsion_le_native hK e hm hT hr
  rw [hb r hr] at hle
  have hsub : Subsingleton {z : Subgroup.center K // z ^ r = 1} :=
    Finite.card_le_one_iff_subsingleton.mp hle
  have hord : orderOf (g ^ (orderOf g / r)) = r :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hrd
  let z : {z : Subgroup.center K // z ^ r = 1} :=
    ⟨⟨g ^ (orderOf g / r), Subgroup.pow_mem _ hg _⟩, by
      refine Subtype.ext ?_
      change (g ^ (orderOf g / r)) ^ r = 1
      rw [← orderOf_dvd_iff_pow_eq_one, hord]⟩
  let o : {z : Subgroup.center K // z ^ r = 1} := ⟨1, one_pow r⟩
  have hz1 : z = o := Subsingleton.elim _ _
  have h1 : g ^ (orderOf g / r) = 1 := congrArg (fun w : {z : Subgroup.center K // z ^ r = 1} =>
    ((w.1 : Subgroup.center K) : K)) hz1
  rw [h1, orderOf_one] at hord
  exact hr.one_lt.ne hord

theorem gctt_of_markedModel {lab : LargeEvenLabel}
    (hb : ∀ r : ℕ, r.Prime →
      torsBound r (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1)
    {R : Type} [Group R] (hM : MarkedModel lab R) (hsimple : IsSimpleGroup R)
    (hperfR : commutator R = ⊤)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier R ≃*
      generic (markTag lab) (markRank lab) (markChar lab) (markDeg lab) ×
        exceptional (markTag lab) (markRank lab) (markChar lab) (markDeg lab)))
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (hs : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Subgroup.center L' = ⊥ := by
  have hnonab : ∃ a b : R, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : commutator R = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      by_contra hab
      exact hcon ⟨a, b, hab⟩
    rw [hperfR] at hcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : R)
    exact hx (Subgroup.mem_bot.mp (hcomm ▸ Subgroup.mem_top x))
  have hcR : Subgroup.center R = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b).symm
  have hkerc : ψ.ker = Subgroup.center L' := by
    refine le_antisymm hker fun z hz => ?_
    have hzR : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨y, rfl⟩ := hs r
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hz y)
    rw [hcR, Subgroup.mem_bot] at hzR
    exact MonoidHom.mem_ker.mpr hzR
  let e : L' ⧸ Subgroup.center L' ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hs)
  exact gctt_centre_bot hperf e hM hT hb

private theorem gctt_markedModel_twisted {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∨ lab.tag = .twD) :
    LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at h hn hl
  rcases h with rfl | rfl
  · obtain ⟨hl1, hl2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeUnitary_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩

theorem ggCentreTrivialTwKnown_holds :
    GGCentreTrivialTwKnown := by
  intro f hf
  refine ⟨fun h3 => ?_, fun h3 => ?_, ?_⟩
  · intro Q hQ
    have hlab : LargeEvenInLambda2 ⟨.twA, 5, f⟩ := by simp [LargeEvenInLambda2, hf]
    have hmarked : LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ _ _ =>
        MarkedModel ⟨.twA, 5, f⟩ R := gctt_markedModel_twisted hlab (Or.inl rfl)
    have hb : ∀ r : ℕ, r.Prime →
        torsBound r (markTag ⟨.twA, 5, f⟩) (markRank ⟨.twA, 5, f⟩)
          (markChar ⟨.twA, 5, f⟩) (markDeg ⟨.twA, 5, f⟩) = 1 := by
      intro r hr
      simp only [markTag, markRank, markChar, markDeg]
      exact gctt_torsBound_psu hr hf h3
    refine largeEvenRawDatum_mono ?_ (hmarked Q hQ)
    rintro R _ I F ⟨hq, hM⟩
    obtain ⟨hperfR, hT⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hsimple : IsSimpleGroup R := CFSG.Evidence.isSimpleGroup_of_lieModel hM
    exact ⟨hq, fun L' _ _ ψ hs hker hperf =>
      gctt_of_markedModel hb hM hsimple hperfR hT L' ψ hs hker hperf⟩
  · intro Q hQ
    have hlab : LargeEvenInLambda2 ⟨.A, 5, f⟩ := by simp [LargeEvenInLambda2, hf]
    have hmarked : LargeEvenLabelAll ⟨.A, 5, f⟩ fun R _ _ _ =>
        MarkedModel ⟨.A, 5, f⟩ R :=
      SCFourCover.largeEvenLabelAll_markedModel_classical hlab (Or.inl rfl)
    have hb : ∀ r : ℕ, r.Prime →
        torsBound r (markTag ⟨.A, 5, f⟩) (markRank ⟨.A, 5, f⟩)
          (markChar ⟨.A, 5, f⟩) (markDeg ⟨.A, 5, f⟩) = 1 := by
      intro r hr
      simp only [markTag, markRank, markChar, markDeg]
      exact gctt_torsBound_psl hr hf h3
    refine largeEvenRawDatum_mono ?_ (hmarked Q hQ)
    rintro R _ I F ⟨hq, hM⟩
    obtain ⟨hperfR, hT⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hsimple : IsSimpleGroup R := CFSG.Evidence.isSimpleGroup_of_lieModel hM
    exact ⟨hq, fun L' _ _ ψ hs hker hperf =>
      gctt_of_markedModel hb hM hsimple hperfR hT L' ψ hs hker hperf⟩
  · intro Q hQ
    have hlab : LargeEvenInLambda2 ⟨.twD, 4, f⟩ := by simp [LargeEvenInLambda2, hf]
    have hmarked : LargeEvenLabelAll ⟨.twD, 4, f⟩ fun R _ _ _ =>
        MarkedModel ⟨.twD, 4, f⟩ R := gctt_markedModel_twisted hlab (Or.inr rfl)
    have hb : ∀ r : ℕ, r.Prime →
        torsBound r (markTag ⟨.twD, 4, f⟩) (markRank ⟨.twD, 4, f⟩)
          (markChar ⟨.twD, 4, f⟩) (markDeg ⟨.twD, 4, f⟩) = 1 := by
      intro r hr
      simp only [markTag, markRank, markChar, markDeg]
      exact gctt_torsBound_pomm hr hf
    refine largeEvenRawDatum_mono ?_ (hmarked Q hQ)
    rintro R _ I F ⟨hq, hM⟩
    obtain ⟨hperfR, hT⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hsimple : IsSimpleGroup R := CFSG.Evidence.isSimpleGroup_of_lieModel hM
    exact ⟨hq, fun L' _ _ ψ hs hker hperf =>
      gctt_of_markedModel hb hM hsimple hperfR hT L' ψ hs hker hperf⟩

end CFSG.StandardType
