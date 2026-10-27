module

public import CFSG.Quasithin.Background.RonanF13Bender
public import CFSG.Quasithin.Background.RonanF13SUMat
public import CFSG.Quasithin.Background.RonanF13SUSemi
public import CFSG.Quasithin.Background.RonanF13Finish
public import CFSG.Quasithin.Background.RonanF13Z3
public import CFSG.Quasithin.Background.RonanF13CoverAux
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.RonanF13

open CFSG.Open CFSG.Quasithin CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

theorem ringEquiv_eq_frobenius {F : Type*} [Field F] [Finite F] [CharP F 2] (φ : F ≃+* F) :
    ∃ k : ℕ, ∀ c : F, φ c = c ^ 2 ^ k := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra _ _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  let φa : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := φ) (fun x => by
    have := RingHom.ext_zmod ((φ : F →+* F).comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)
    exact DFunLike.congr_fun this x)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).2 φa
  refine ⟨n.1, fun c => ?_⟩
  have h1 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ n.1) c = φa c := by
    rw [← hn]
  have h2 : φ c = φa c := rfl
  rw [h2, ← h1, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp

theorem aut_statedSU_semilinear {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (α : MulAut ↥(StatedSU 3 (2 ^ n) F)) :
    ∃ (A : GL (Fin 3) F) (φ : F ≃+* F),
      (∀ x : ↥(StatedSU 3 (2 ^ n) F), ((α x : ↥(StatedSU 3 (2 ^ n) F)) : GL (Fin 3) F) =
        A * glAut φ (x : GL (Fin 3) F) * A⁻¹) ∧ ∀ r : ℕ, α ^ r = 1 → φ ^ r = 1 := by
  have h : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hnq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ n = 2 ^ 1 := by simpa using h2
    have := Nat.pow_right_injective le_rfl this
    omega
  let e : ↥(StatedSU 3 (2 ^ n) F) ≃* ↥(gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
    MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)
  obtain ⟨A, φ, hα, hr⟩ := aut_gramSU_semilinear h hnq (MulAut.congr e α)
  refine ⟨(A : GL (Fin 3) F), φ, fun x => ?_, fun r hαr => hr r ?_⟩
  · have h1 := congrArg (fun y : ↥(gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =>
      ((y : GL (Fin 3) F))) (DFunLike.congr_fun hα (e x))
    simpa [suTheta, primeFormConjSU, primeFormFieldSU, MulAut.congr_apply, e,
      MulEquiv.subgroupCongr_apply] using h1
  · rw [← map_pow, hαr, map_one]

theorem ker_le_of_normalizer {K K' : Type*} [Group K] [Group K'] (π : K →* K')
    (hZ : π.ker ≤ Subgroup.center K) (hodd : ∀ z ∈ π.ker, Odd (orderOf z))
    {T D : Subgroup K} (hT : IsPGroup 2 T) (hTD : T ⊔ D = Subgroup.normalizer (T : Set K))
    (hDodd : Odd (Nat.card D)) : π.ker ≤ D := by
  intro z hz
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  have hzc : ∀ g, g * z = z * g := fun g => Subgroup.mem_center_iff.mp (hZ hz) g
  have hzN : z ∈ Subgroup.normalizer (T : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have : z * h * z⁻¹ = h := by rw [← hzc h, mul_inv_cancel_right]
    rw [this]
  have hzTD : z ∈ T ⊔ D := by rw [hTD]; exact hzN
  obtain ⟨t, ht, d, hd, hzd⟩ := (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hDN).mp hzTD
  have hdodd : Odd (orderOf d) := by
    have h1 : orderOf d ∣ Nat.card D := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hDodd h1
  have htd : t = z * d⁻¹ := by rw [hzd]; group
  have hcomm : Commute z d⁻¹ := by
    have : Commute z d := (hzc d).symm
    exact this.inv_right
  have htodd : Odd (orderOf t) := by
    have h4 := hcomm.orderOf_mul_dvd_lcm
    rw [← htd, orderOf_inv] at h4
    exact Odd.of_dvd_nat ((hodd z hz).mul hdodd) (h4.trans (Nat.lcm_dvd_mul _ _))
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have ht1 : t = 1 := eq_one_of_odd_orderOf_of_pow' htodd (congrArg Subtype.val hk)
  have : z = d := by rw [hzd, ht1, one_mul]
  rw [this]
  exact hd

section Main


theorem rankOneTwist_statedSU {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) : RankOneTwist ↥(StatedSU 3 (2 ^ n) F) := by
  classical
  set S : Subgroup (GL (Fin 3) F) := StatedSU 3 (2 ^ n) F with hSdef
  set H₀ : Subgroup ↥S := (StatedScalars (Fin 3) F).subgroupOf S with hH₀
  intro T D α hT hTodd hTD hDodd hαT hαD hαodd hcomm
  set π : ↥S →* StatedProj S := QuotientGroup.mk' H₀ with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = H₀ := QuotientGroup.ker_mk' _
  have hZ : π.ker ≤ Subgroup.center ↥S := by
    rw [hker]
    exact statedSU_scalars_le_center
  have hker3 : ∀ z ∈ π.ker, z ^ 3 = 1 := by
    intro z hz
    rw [hker] at hz
    exact statedSU_three_kernel z hz
  have hodd_ker : ∀ z ∈ π.ker, Odd (orderOf z) := by
    intro z hz
    rw [hker] at hz
    exact statedSU_three_scalars_odd z hz
  have h : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hcharF : CharP F 2 := h.charP
  have hcardH₀ : Nat.card H₀ = Nat.gcd 3 (2 ^ n + 1) := by
    have h1 := card_unitaryScalars h (n := 3) (by norm_num)
    rw [unitaryScalars_eq h (by norm_num)] at h1
    exact h1
  obtain ⟨ε, hB⟩ := benderType_statedProj hn hF
  have hε : ε = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
    rcases hB.cases' with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · exact he
  have hDN : D ≤ Subgroup.normalizer (T : Set ↥S) := hTD ▸ le_sup_right
  have hT' : IsPGroup 2 (T.map π) := hT.map π
  have hTodd' : ¬ 2 ∣ (T.map π).index := fun hd =>
    hTodd (hd.trans (Subgroup.index_map_dvd T hπsurj))
  have hnorm : T.map π ⊔ D.map π = Subgroup.normalizer ((T.map π : Subgroup _) : Set _) := by
    apply le_antisymm
    · refine sup_le Subgroup.le_normalizer ?_
      rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.le_normalizer_map π ⟨d, hDN hd, rfl⟩
    · intro x' hx'
      obtain ⟨x, rfl⟩ := hπsurj x'
      have hxN := mem_normalizer_of_central_cover π hZ hodd_ker hT hx'
      rw [← hTD] at hxN
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem π hxN
  have hDodd' : Odd (Nat.card (D.map π)) := Odd.of_dvd_nat hDodd (Subgroup.card_map_dvd D π)
  have hcardD' : Nat.card (D.map π) = (2 ^ n - 1) * ε :=
    bender_card_hall hB hT' hTodd' hnorm hDodd'
  have hcycD' : IsCyclic ↥(D.map π) := bender_hall_cyclic hB hT' hTodd' hnorm hDodd'
  have hkerD : π.ker ≤ D := ker_le_of_normalizer π hZ hodd_ker hT hTD hDodd
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have h1 := ((isRankOneSylowCyclic_statedProj hn hF).1 (T.map π) hT' hTodd').1
    apply h1
    rw [hbot, Subgroup.map_bot]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  obtain ⟨g, hg⟩ := hcycD'.exists_generator
  obtain ⟨d₀, hd₀D, hd₀g⟩ := Subgroup.mem_map.mp g.2
  have hd₀ord : orderOf (π d₀) = Nat.card (D.map π) := by
    have h1 := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [hd₀g, ← h1]
    exact Subgroup.orderOf_coe g
  have hdvd1 : Nat.card (D.map π) ∣ orderOf d₀ := hd₀ord ▸ orderOf_map_dvd π d₀
  have hdvd2 : orderOf d₀ ∣ Nat.card (D.map π) * Nat.card H₀ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h1 : d₀ ^ Nat.card (D.map π) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, ← hd₀ord]
      exact pow_orderOf_eq_one _
    rw [hker] at h1
    have h2 : (⟨d₀ ^ Nat.card (D.map π), h1⟩ : ↥H₀) ^ Nat.card H₀ = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [pow_mul]
    exact h3
  obtain ⟨gg, hgg⟩ : ∃ gg, gg = Nat.gcd 3 (2 ^ n + 1) := ⟨_, rfl⟩
  have hgg_dvd : gg ∣ 3 := hgg ▸ Nat.gcd_dvd_left _ _
  have hεg : ε * gg = 2 ^ n + 1 := by
    rw [hε, hgg]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hcardH₀' : Nat.card H₀ = gg := hcardH₀.trans hgg.symm
  have hD'g : Nat.card (D.map π) * gg = 2 ^ (2 * n) - 1 := by
    rw [hcardD', mul_assoc, hεg, pow_mul']
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2n' : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ h2n
    zify [h2n, h2n']
    ring
  have hDpos : 0 < Nat.card (D.map π) := Nat.card_pos
  obtain ⟨s, hs⟩ := hdvd1
  have hsgg : s ∣ gg := by
    have h1 : Nat.card (D.map π) * s ∣ Nat.card (D.map π) * gg := by
      rw [← hs, ← hcardH₀']
      exact hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hDpos h1
  obtain ⟨c, hc⟩ := hsgg
  have hc13 : c = 1 ∨ c = 3 := by
    have h1 : c ∣ gg := Dvd.intro_left s hc.symm
    exact (Nat.dvd_prime Nat.prime_three).mp (h1.trans hgg_dvd)
  have hcN : c * orderOf d₀ = 2 ^ (2 * n) - 1 := by
    rw [hs, ← hD'g, hc]
    ring
  have hd₀pow : d₀ ^ (Nat.card F - 1) = 1 := by
    have h1 : orderOf d₀ ∣ 2 ^ (2 * n) - 1 := Dvd.intro_left c hcN
    have h2 : Nat.card F = 2 ^ (2 * n) := by rw [hF, ← pow_mul, mul_comm]
    rw [h2]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hDgen' : ∀ x ∈ D, ∃ (a : ℕ) (z : ↥S), z ∈ H₀ ∧ x = d₀ ^ a * z := by
    intro x hx
    have hxD' : π x ∈ D.map π := Subgroup.mem_map_of_mem π hx
    have hmem : (⟨π x, hxD'⟩ : ↥(D.map π)) ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg ⟨π x, hxD'⟩)
    obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    have hπa : π (d₀ ^ a) = π x := by
      rw [map_pow, hd₀g]
      exact congrArg Subtype.val ha
    have hz : (d₀ ^ a)⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
    rw [hker] at hz
    exact ⟨a, (d₀ ^ a)⁻¹ * x, hz, by group⟩
  have hDgen : ∀ x ∈ D, ∃ (a : ℕ) (z : ↥S) (c₀ : F),
      (∀ v : Fin 3 → F, Mv S z v = c₀ • v) ∧ x = d₀ ^ a * z := by
    intro x hx
    obtain ⟨a, z, hz, hxe⟩ := hDgen' x hx
    obtain ⟨c₀, hc₀⟩ := (Subgroup.mem_subgroupOf.mp hz : ((z : ↥S) : GL (Fin 3) F) ∈
      StatedScalars (Fin 3) F)
    refine ⟨a, z, (c₀ : F), fun v => ?_, hxe⟩
    rw [Mv_apply, ← hc₀]
    funext i
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  obtain ⟨A, φ, hα, hφ⟩ := aut_statedSU_semilinear hn hF α
  obtain ⟨k, hk⟩ := ringEquiv_eq_frobenius φ
  have hαr : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  have hφr : φ ^ orderOf α = 1 := hφ _ hαr
  have hα1 : α d₀ = d₀ ^ 2 ^ k :=
    frob_of_semilinear (S := S) α A φ (2 ^ k) hk hα (orderOf α) hαodd hαr hφr T D hT hT1 hDN hαT
      hαD d₀ hd₀D hd₀pow hDgen
  have hfix : α d₀ = d₀ :=
    twist_finish_elem α hα1 hαodd (hcomm d₀ hd₀D) (M := 2 * n) (c := c) (by omega) hc13
      (fun _ => by omega) hcN
  have hH₀cyc : IsCyclic ↥H₀ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hgg_dvd with h1 | h3
    · haveI : Subsingleton ↥H₀ := (Nat.card_eq_one_iff_unique.mp (hcardH₀'.trans h1)).1
      infer_instance
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card (hcardH₀'.trans h3)
  have hmapH₀ : ∀ z ∈ H₀, α z ∈ H₀ := by
    intro z hz
    obtain ⟨c₀, hc₀⟩ := (Subgroup.mem_subgroupOf.mp hz : ((z : ↥S) : GL (Fin 3) F) ∈
      StatedScalars (Fin 3) F)
    have h1 : glAut φ (Matrix.GeneralLinearGroup.scalar (Fin 3) c₀) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : F →* F) c₀) := by
      apply Units.ext
      rw [coe_glAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ), Units.coe_map]
      rfl
    have h2 : A * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : F →* F) c₀) * A⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (φ : F →* F) c₀) := by
      rw [(commute_scalar (Units.map (φ : F →* F) c₀) A).eq, mul_inv_cancel_right]
    rw [Subgroup.mem_subgroupOf, hα, ← hc₀, h1, h2]
    exact ⟨_, rfl⟩
  have hαH₀ : ∀ x, α x ∈ H₀ ↔ x ∈ H₀ := by
    have himg : H₀.map α.toMonoidHom = H₀ := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨z, hz, rfl⟩
        exact hmapH₀ z hz
      · rw [Subgroup.card_map_of_injective α.injective]
    intro x
    constructor
    · intro hx
      rw [← himg] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := α.injective hyx
      rw [← this]
      exact hy
    · exact fun hx => hmapH₀ x hx
  have hαz : ∀ z ∈ H₀, α z = z :=
    aut_trivial_of_cyclic_exp3 H₀ hH₀cyc (fun z hz => hker3 z (hker ▸ hz)) α hαH₀ hαodd
  intro x hx
  obtain ⟨a, z, hz, hxe⟩ := hDgen' x hx
  rw [hxe, map_mul, map_pow, hfix, hαz z hz]

end Main

end CFSG.Quasithin.RonanF13
