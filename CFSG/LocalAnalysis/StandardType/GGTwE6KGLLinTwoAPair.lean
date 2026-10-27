module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Mark
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutWitCommon
import CFSG.Assembly.GL83StatedBridge
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open TableB

private theorem le_of_ppd_dvd_ordA_linTwo {r p k : ℕ} (hr : 1 ≤ r) (hk : 0 < k)
    (hp : Timmesfeld.IsPrimitivePrimeDivisor p k) (hd : p ∣ ordA r (2 ^ 1)) : k ≤ r + 1 := by
  obtain ⟨i, hi, hki⟩ :=
    ((CFSG.SeitzReduction.F4Pilot.profile_idxA (f := 1) hr le_rfl).prim p k hp hk).1 hd
  rw [Finset.mem_Icc] at hi
  rw [one_mul] at hki
  exact (Nat.le_of_dvd (by omega) hki).trans hi.2

private theorem not_ordA_two_dvd_linTwo {r n : ℕ} (hr : 1 ≤ r) (hr9 : r + 1 ≤ 9) (hn : 1 ≤ n)
    (h81 : ¬ (r = 8 ∧ n = 1)) : ¬ ordA 2 (2 ^ (3 * n)) ∣ ordA r (2 ^ 1) := fun hd => by
  obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordA_two_nine hn
  have := le_of_ppd_dvd_ordA_linTwo hr (by omega) hp (hpd.trans hd)
  omega

private theorem not_ordTwistedA_two_dvd_linTwo {r n : ℕ} (hr : 1 ≤ r) (hr9 : r + 1 ≤ 9)
    (hn : 1 ≤ n) : ¬ ordTwistedA 2 (2 ^ (3 * n)) ∣ ordA r (2 ^ 1) := fun hd => by
  obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordTwistedA_two_eighteen hn
  have := le_of_ppd_dvd_ordA_linTwo hr (by omega) hp (hpd.trans hd)
  omega

private theorem largeEvenLabelAll_card_linTwo (r : ℕ) :
    LargeEvenLabelAll ⟨.A, r, 1⟩ fun R _ _ _ => Nat.card R = ordA r (2 ^ 1) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  have hK2 : Nat.card K = 2 := hK
  have he : (r + 1) * (r + 1 - 1) / 2 = r * (r + 1) / 2 := by
    rw [Nat.add_sub_cancel, Nat.mul_comm]
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := r + 1)
    (by omega)
  rw [← largeEvenSLGroup_eq_statedSL, hK2, he] at hc
  exact hc

private theorem eq_one_of_commute_singer_linTwo {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {p : ℕ} (hp : Timmesfeld.IsPrimitivePrimeDivisor p 9)
    {A M : Matrix (Fin 9) (Fin 9) K} (hA : A ^ 3 = 1) (hM : M ^ p = 1) (hM1 : M ≠ 1)
    (hAM : A * M = M * A) : A = 1 := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  have hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = 9 := by
    rw [hK, Nat.cast_ofNat]
    exact (orderOf_eq_iff (by norm_num)).2 ⟨(Timmesfeld.Bang.dvd_two_pow_sub_one_iff 9).1 hp.2.1,
      fun m hm hm0 h1 => hp.2.2 m hm0 hm ((Timmesfeld.Bang.dvd_two_pow_sub_one_iff m).2 h1)⟩
  obtain ⟨hirr, hdeg⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.minpoly_irreducible_natDegree_eq
      (by norm_num) hord hM hM1
  have hroot := minpoly.aeval K M
  generalize minpoly K M = μ at hirr hdeg hroot
  haveI : Fact (Irreducible μ) := ⟨hirr⟩
  have hμ0 : μ ≠ 0 := hirr.ne_zero
  have hker : ∀ a ∈ Ideal.span ({μ} : Set (Polynomial K)),
      (Polynomial.aeval M).toRingHom a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    simp [hroot]
  let ψ : AdjoinRoot μ →+* Matrix (Fin 9) (Fin 9) K :=
    Ideal.Quotient.lift (Ideal.span ({μ} : Set (Polynomial K))) (Polynomial.aeval M).toRingHom
      hker
  obtain ⟨a, ha⟩ := CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.eq_image_of_commute
    (by norm_num) hirr hdeg ψ (fun _ => rfl) hAM
  haveI : Module.Finite K (AdjoinRoot μ) := (AdjoinRoot.powerBasis hμ0).finite
  haveI : Finite (AdjoinRoot μ) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot μ) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot μ) = 2 ^ 9 := by
    rw [Module.card_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hμ0).finrank,
      AdjoinRoot.powerBasis_dim hμ0, hdeg, hK]
  have h2 : A ^ 2 = A := by
    have h9 : A ^ 2 ^ 9 = A := by rw [← ha, ← map_pow, ← hcard, FiniteField.pow_card]
    rwa [show 2 ^ 9 = 3 * 170 + 2 by norm_num, pow_add, pow_mul, hA, one_pow, one_mul] at h9
  calc A = A ^ 2 := h2.symm
    _ = A * A := sq A
    _ = A ^ 2 * A := by rw [h2]
    _ = A ^ 3 := (pow_succ A 2).symm
    _ = 1 := hA

private theorem eq_one_of_injective_linTwo {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) (hf : Function.Injective f)
    (hH : ∀ g h : H, g ^ 3 = 1 → h ^ p = 1 → h ≠ 1 → g * h = h * g → g = 1) {g h : G}
    (hg : g ^ 3 = 1) (hh : h ^ p = 1) (hh1 : h ≠ 1) (hgh : g * h = h * g) : g = 1 :=
  hf <| by
    rw [map_one]
    exact hH (f g) (f h) (by rw [← map_pow, hg, map_one]) (by rw [← map_pow, hh, map_one])
      (fun e => hh1 (hf (by rw [e, map_one]))) (by rw [← map_mul, hgh, map_mul])

private theorem largeEvenLabelAll_singer_linTwo (r : ℕ) :
    LargeEvenLabelAll ⟨.A, r, 1⟩ fun R _ I _ => r = 8 → I ⊆ LargeEvenInnSet R ∧
      ∀ p, Timmesfeld.IsPrimitivePrimeDivisor p 9 → ∀ x y : R, x ^ 3 = 1 → y ^ p = 1 →
        y ≠ 1 → x * y = y * x → x = 1 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun h8 => ?_⟩
  subst h8
  have hK2 : Nat.card K = 2 := hK
  letI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
  show LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 9) K)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 9) K)) ∧
    ∀ p, Timmesfeld.IsPrimitivePrimeDivisor p 9 →
      ∀ x y : LargeEvenProj (LargeEvenSLGroup (Fin 9) K),
        x ^ 3 = 1 → y ^ p = 1 → y ≠ 1 → x * y = y * x → x = 1
  refine ⟨matConjImage_gl_subset_inn (by rw [hu]; exact Nat.coprime_one_left _),
    fun p hp x y => ?_⟩
  have hb : (LargeEvenScalars (Fin 9) K).subgroupOf (LargeEvenSLGroup (Fin 9) K) = ⊥ := by
    rw [show LargeEvenScalars (Fin 9) K = ⊥ from
      LocalAnalysis.RankThreeTheoremC.KFactProofs.statedScalars_eq_bot_of_card_two hK2]
    exact Subgroup.bot_subgroupOf _
  let e := (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  refine eq_one_of_injective_linTwo ((LargeEvenSLGroup (Fin 9) K).subtype.comp e.toMonoidHom)
    (fun a b hab => e.injective (Subtype.ext hab)) (fun g h hg hh hh1 hgh => ?_)
  refine Units.val_eq_one.1 (eq_one_of_commute_singer_linTwo hKf hp
    (A := (g : Matrix (Fin 9) (Fin 9) K)) (M := (h : Matrix (Fin 9) (Fin 9) K)) ?_ ?_
    (fun h1 => hh1 (Units.val_eq_one.1 h1)) ?_)
  · rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, hh, Units.val_one]
  · rw [← Units.val_mul, hgh, Units.val_mul]

private theorem ne_top_of_isComponentOf_ggFix_linTwo {R : Type} [Group R] {s : MulAut R}
    (hs : s ≠ 1) {J₁ : Subgroup R} (hJ : Assembly.IsComponentOf J₁ (ggFix s)) : J₁ ≠ ⊤ := by
  rintro rfl
  exact hs (MulEquiv.ext fun r => by simpa using mem_ggFix.1 (hJ.1 (Subgroup.mem_top r)))

private theorem center_eq_bot_linTwo {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  obtain ⟨a, b, hab⟩ := hna
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R)).resolve_right fun h =>
    hab (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a)

theorem ggInndiagOnCompAt_A_two_aPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hn : lab.n = 1) (hr : lab.rank + 1 ≤ 9) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at htag hn hr
  subst htag hn
  have hr1 : 1 ≤ r := by
    obtain ⟨-, h1, -⟩ := hlab
    exact h1
  unfold GGInndiagOnCompAt
  refine (largeEvenLabelAll_and (largeEvenLabelAll_card_linTwo r)
    (largeEvenLabelAll_singer_linTwo r)).mono
    fun R _ I _ ⟨hcard, hsing⟩ hR hna hfin s _ n hs3 hs1 _ _ hsI _ h3 J₁ hJ₁ hmark _ => ?_
  haveI := hfin
  have hJ : J₁ ≠ ⊤ := ne_top_of_isComponentOf_ggFix_linTwo hs1 hJ₁
  have hN : 0 < ordA r (2 ^ 1) := by
    rw [← hcard]
    exact Nat.card_pos
  have hn1 : 1 ≤ n := (odd_of_three_dvd_two_pow_add_one_noJ1 h3).pos
  rcases exists_label_disjunct_marking hmark with hm | hm
  · by_cases h81 : r = 8 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := h81
      obtain ⟨hinn, hS⟩ := hsing rfl
      obtain ⟨-, hdvd⟩ := ordA_two_dvd_card_of_marking hm
      obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordA_two_nine (n := 1) le_rfl
      haveI : Fact p.Prime := ⟨hp.1⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p (hpd.trans hdvd)
      obtain ⟨x, rfl⟩ := hinn hsI
      have hinj := CFSG.mulAutConj_injective_of_center_eq_bot (center_eq_bot_linTwo hR hna)
      have hxy := mem_ggFix.1 (hJ₁.1 y.2)
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hxy
      refine hs1 ?_
      rw [hS p hp x y (hinj (by rw [map_pow, hs3, map_one]))
        (by rw [← hy, ← Subgroup.orderOf_coe]; exact pow_orderOf_eq_one _)
        (fun h => hp.1.one_lt.ne' (by rw [← hy, ← Subgroup.orderOf_coe, h, orderOf_one])) hxy,
        map_one]
    · exact not_largeEvenMarking_A2_of_card hN hcard
        (fun _ => Or.inl (not_ordA_two_dvd_linTwo hr1 hr hn1 h81)) hJ hm
  · exact not_largeEvenMarking_twA2_of_card hN hcard
      (fun _ => Or.inl (not_ordTwistedA_two_dvd_linTwo hr1 hr hn1)) hJ hm

end CFSG.StandardType.SCFourCover

end
