module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoA5
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

private theorem gct_torsBound_psp {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (n f : ℕ) (hf : 1 ≤ f) :
    torsBound r .PSp n 2 f = 1 := by
  have hodd : Odd (2 ^ f - 1) := by
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    exact Nat.Even.sub_odd this (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hg : genericOrders .PSp n 2 f = (1, 1) := by
    simp only [genericOrders]
    exact Prod.ext (Nat.coprime_two_left.2 hodd) rfl
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  have h2 : tors r 2 = 1 :=
    tors_of_not_dvd fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  have hex : exceptionalOrders .PSp n 2 f = (2, 1) ∨ exceptionalOrders .PSp n 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; simp_all) | simp_all
  unfold torsBound
  rw [hg]
  rcases hex with hex | hex <;> rw [hex] <;> simp [h1, h2]

private theorem gct_torsBound_f4 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (f : ℕ) :
    torsBound r .F4 0 2 f = 1 := by
  have hg : genericOrders .F4 0 2 f = (1, 1) := by
    simp only [genericOrders]
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  have h2 : tors r 2 = 1 :=
    tors_of_not_dvd fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  have hex : exceptionalOrders .F4 0 2 f = (2, 1) ∨ exceptionalOrders .F4 0 2 f = (1, 1) := by
    unfold exceptionalOrders
    split <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; simp_all) | simp_all
  unfold torsBound
  rw [hg]
  rcases hex with hex | hex <;> rw [hex] <;> simp [h1, h2]

private theorem gct_two_group {K X : Type} [Group K] [Finite K] [Group X] (hK : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n p f)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f))
    (hb : ∀ r : ℕ, r.Prime → r ≠ 2 → torsBound r t n p f = 1) :
    ∀ g ∈ Subgroup.center K, ∃ k : ℕ, orderOf g = 2 ^ k := by
  intro g hg
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨(orderOf g).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hpos ?_⟩
  intro r hr hrd
  by_contra hr2
  have hle := center_torsion_le_native hK e hm hT hr
  rw [hb r hr hr2] at hle
  have hsub : Subsingleton {z : Subgroup.center K // z ^ r = 1} :=
    Finite.card_le_one_iff_subsingleton.mp hle
  have hord : orderOf (g ^ (orderOf g / r)) = r := orderOf_pow_orderOf_div hpos hrd
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

private theorem gct_of_markedModel {lab : LargeEvenLabel}
    (hb : ∀ r : ℕ, r.Prime → r ≠ 2 →
      torsBound r (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1)
    {R : Type} [Group R] (hM : MarkedModel lab R) (hsimple : IsSimpleGroup R)
    (hperfR : commutator R = ⊤)
    (hT : Nonempty (CFSG.Open.griessHopfMultiplier R ≃*
      generic (markTag lab) (markRank lab) (markChar lab) (markDeg lab) ×
        exceptional (markTag lab) (markRank lab) (markChar lab) (markDeg lab)))
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (hs : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ∀ g ∈ Subgroup.center L', ∃ k : ℕ, orderOf g = 2 ^ k := by
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
  exact gct_two_group hperf e hM hT hb

theorem ggCentreTwoKnown_holds :
    GGCentreTwoKnown := by
  intro lab hlab hcase Q hQ
  have hf : 1 ≤ lab.n := hlab.1
  have hmarked : LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
    rcases hcase with ⟨htag, -⟩ | hF4
    · exact SCFourCover.largeEvenLabelAll_markedModel_classical hlab
        (by rcases htag with h | h; exacts [Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))])
    · exact SCFourCover.largeEvenLabelAll_markedModel_f4e6 hlab (Or.inl hF4)
  have hb : ∀ r : ℕ, r.Prime → r ≠ 2 →
      torsBound r (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1 := by
    intro r hr hr2
    rcases hcase with ⟨htag, -⟩ | hF4
    · have h1 : markTag lab = .PSp := by rcases htag with h | h <;> simp [markTag, h]
      have h2 : markChar lab = 2 := by rcases htag with h | h <;> simp [markChar, h]
      have h3 : markDeg lab = lab.n := by rcases htag with h | h <;> simp [markDeg, h]
      rw [h1, h2, h3]
      exact gct_torsBound_psp hr hr2 _ _ hf
    · have h1 : markTag lab = .F4 := by simp [markTag, hF4]
      have h2 : markChar lab = 2 := by simp [markChar, hF4]
      have h3 : markRank lab = 0 := by simp [markRank, hF4]
      rw [h1, h2, h3]
      exact gct_torsBound_f4 hr hr2 _
  refine largeEvenRawDatum_mono ?_ (hmarked Q hQ)
  rintro R _ I F ⟨hq, hM⟩
  obtain ⟨hperfR, hT⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
  have hsimple : IsSimpleGroup R := CFSG.Evidence.isSimpleGroup_of_lieModel hM
  exact ⟨hq, fun L' _ _ ψ hs hker hperf =>
    gct_of_markedModel hb hM hsimple hperfR hT L' ψ hs hker hperf⟩

end CFSG.StandardType
