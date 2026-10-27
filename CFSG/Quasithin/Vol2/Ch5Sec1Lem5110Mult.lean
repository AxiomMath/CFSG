module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
public import CFSG.RankThree.ThinCatalog.FiveModels
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Mult5110

open CFSG.RankThree.PerfectCover CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup

theorem card_center_dvd {X J : Type} [Group X] [Finite X] [Group J] (hX : CFSG.IsQuasisimple X)
    (e : X ⧸ center X ≃* J) : Nat.card (center X) ∣ Nat.card (hopfMultiplier J) := by
  have : Group.IsPerfect X := hX.1
  have hq := centralQuotientMap_surjective e
  have hk := centralQuotientMap_ker e
  have hJ : Group.IsPerfect J := isPerfect_of_quasisimple_quotient hX e
  have : Finite J := Finite.of_surjective _ hq
  have : Finite (hopfMultiplier J) := finite_hopfMultiplier hJ
  have h := Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective (centralQuotientMap e) hq hk.le)
  rwa [hk] at h

theorem card_hopfMultiplier_eq
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel J t n p f) :
    Nat.card (hopfMultiplier J) =
      (Multiplier.genericOrders t n p f).1 * (Multiplier.genericOrders t n p f).2 *
        ((Multiplier.exceptionalOrders t n p f).1 * (Multiplier.exceptionalOrders t n p f).2) := by
  rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv]
  exact CFSG.ComponentClassification.HarrisLit.card_griessHopfMultiplier_eq hGA hm

private theorem dvd_of_odd_dvd_mul_two_pow {z g a : ℕ} (hz : Odd z) (h : z ∣ g * 2 ^ a) : z ∣ g :=
  (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hz)).dvd_of_dvd_mul_right h

private theorem gcd_two_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Nat.gcd 2 (2 ^ k - 1) = 1 := by
  have h2 : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one)

theorem center_eq_bot_psl2
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (center X))) {k : ℕ}
    (h : IsPSL 2 2 k (X ⧸ center X)) : center X = ⊥ := by
  have hd := card_center_dvd hX (MulEquiv.refl _)
  rw [card_hopfMultiplier_eq hGA ⟨h.1, Or.inl h⟩,
    show Multiplier.genericOrders .PSL 2 2 k = (Nat.gcd 2 (2 ^ k - 1), 1) from rfl, mul_one,
    gcd_two_two_pow_sub_one h.1.2.1, one_mul] at hd
  have hexc : (Multiplier.exceptionalOrders .PSL 2 2 k).1 *
      (Multiplier.exceptionalOrders .PSL 2 2 k).2 ∣ 1 * 2 ^ 1 := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp (dvd_of_odd_dvd_mul_two_pow hodd
    (hd.trans hexc)))

theorem center_eq_bot_psp4
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (center X))) {k : ℕ}
    (h : IsPSp4 2 k (X ⧸ center X)) : center X = ⊥ := by
  have hd := card_center_dvd hX (MulEquiv.refl _)
  rw [card_hopfMultiplier_eq hGA ⟨h.1, Or.inl h⟩,
    show Multiplier.genericOrders .PSp 2 2 k = (Nat.gcd 2 (2 ^ k - 1), 1) from rfl, mul_one,
    gcd_two_two_pow_sub_one h.1.2.1, one_mul] at hd
  have hexc : (Multiplier.exceptionalOrders .PSp 2 2 k).1 *
      (Multiplier.exceptionalOrders .PSp 2 2 k).2 ∣ 1 * 2 ^ 0 := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp (dvd_of_odd_dvd_mul_two_pow hodd
    (hd.trans hexc)))

theorem exists_lift_of_coprime_index
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (m : ℕ) (hcop : Nat.Coprime m (Nat.card p.ker))
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ := by
  set h₀ := hopfLift p₀ hp₀ hk₀ with hh₀
  set h := hopfLift p hp hk with hh
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective p hp hk
  have hcomp₀ : p₀.comp h₀ = hopfCoverMap J := comp_hopfLift p₀ hp₀ hk₀
  have hcomp : p.comp h = hopfCoverMap J := comp_hopfLift p hp hk
  have hmap₀ : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hmap : (hopfMultiplier J).map h = p.ker := map_hopfMultiplier_hopfLift p hp hk
  have hfin : Finite (hopfMultiplier J) := by
    have : Finite J := Finite.of_surjective _ hp
    exact finite_hopfMultiplier (Group.IsPerfect.ofSurjective hp)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have h2 : 0 < Nat.card (hopfMultiplier J) := Nat.card_pos
      rw [hcard, h0, mul_zero] at h2
      exact absurd h2 (lt_irrefl 0)
    · exact h0
  have hker₀ : ∀ u ∈ h₀.ker, u ∈ hopfMultiplier J ∧ u ^ m = 1 := by
    let ψ : hopfMultiplier J →* p₀.ker :=
      (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun x ↦ by
        rw [← hmap₀]
        exact ⟨x, x.2, rfl⟩
    have hψs : Function.Surjective ψ := by
      rintro ⟨c, hc⟩
      rw [← hmap₀] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcardk : Nat.card ψ.ker * Nat.card p₀.ker = Nat.card (hopfMultiplier J) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
      rw [mul_comm]
      exact h1.symm
    have hkm : Nat.card ψ.ker = m := by
      have hpos : 0 < Nat.card p₀.ker := Nat.card_pos
      have h2 : Nat.card ψ.ker * Nat.card p₀.ker = m * Nat.card p₀.ker := by
        rw [hcardk, hcard, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    intro u hu
    have hum : u ∈ hopfMultiplier J := by
      change hopfCoverMap J u = 1
      rw [← hcomp₀, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hu, map_one]
    refine ⟨hum, ?_⟩
    have hψu : ψ ⟨u, hum⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.1 hu)
    have hmem : (⟨u, hum⟩ : hopfMultiplier J) ∈ ψ.ker := hψu
    have := orderOf_dvd_natCard (⟨⟨u, hum⟩, hmem⟩ : ψ.ker)
    rw [hkm] at this
    have h3 : (⟨⟨u, hum⟩, hmem⟩ : ψ.ker) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 this
    exact congrArg (fun z : ψ.ker ↦ ((z : hopfMultiplier J) : HopfCover J)) h3
  have hle : h₀.ker ≤ h.ker := by
    intro u hu
    obtain ⟨hum, hu3⟩ := hker₀ u hu
    rw [MonoidHom.mem_ker]
    have hhu : h u ∈ p.ker := by
      rw [← hmap]
      exact ⟨u, hum, rfl⟩
    have hpow : (⟨h u, hhu⟩ : p.ker) ^ m = 1 := Subtype.ext (by
      change (h u) ^ m = 1
      rw [← map_pow, hu3, map_one])
    have hord : (⟨h u, hhu⟩ : p.ker) ^ Nat.card p.ker = 1 := pow_card_eq_one'
    have h1 : (⟨h u, hhu⟩ : p.ker) = 1 := by
      have := (pow_gcd_eq_one (a := (⟨h u, hhu⟩ : p.ker))).2 ⟨hpow, hord⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    exact congrArg Subtype.val h1
  let α : S₀ →* E := (h₀.liftOfRightInverse (Function.surjInv h₀s)
    (Function.rightInverse_surjInv h₀s)) ⟨h, hle⟩
  have hα : ∀ u, α (h₀ u) = h u := fun u ↦
    h₀.liftOfRightInverse_comp_apply (Function.surjInv h₀s) (Function.rightInverse_surjInv h₀s)
      ⟨h, hle⟩ u
  refine ⟨α, ?_, ?_⟩
  · intro e
    obtain ⟨u, rfl⟩ := hs e
    exact ⟨h₀ u, hα u⟩
  · refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨u, rfl⟩ := h₀s x
    rw [MonoidHom.comp_apply, hα, ← MonoidHom.comp_apply, hcomp, ← MonoidHom.comp_apply, hcomp₀]

theorem isSL3Ch5_of_odd_center
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (center X))) {k : ℕ}
    (h : IsPSL 3 2 k (X ⧸ center X)) : IsSL3Ch5 k X := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨a, ha⟩ : ∃ a, (Multiplier.exceptionalOrders .PSL 3 2 k).1 *
      (Multiplier.exceptionalOrders .PSL 3 2 k).2 = 2 ^ a := by
    unfold Multiplier.exceptionalOrders
    split <;> first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨4, rfl⟩ | simp_all
  have hM : Nat.card (hopfMultiplier (X ⧸ center X)) = Nat.gcd 3 (2 ^ k - 1) * 2 ^ a := by
    rw [card_hopfMultiplier_eq hGA ⟨h.1, Or.inl h⟩, ha,
      show Multiplier.genericOrders .PSL 3 2 k = (Nat.gcd 3 (2 ^ k - 1), 1) from rfl, mul_one]
  have hd := card_center_dvd hX (MulEquiv.refl _)
  rw [hM] at hd
  have hz3 : Nat.card (center X) ∣ 3 :=
    (dvd_of_odd_dvd_mul_two_pow hodd hd).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨hadm, F, _, _, hF, ⟨eJ⟩⟩ := h
  rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with hz | hz
  ·
    have hbot := Subgroup.eq_bot_of_card_eq _ hz
    let e₁ : X ≃* X ⧸ center X :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    exact Or.inl (Or.inl ⟨by simp [classicalTags],
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e₁.trans eJ⟩⟩⟩)
  ·
    have hg : Nat.gcd 3 (2 ^ k - 1) = 3 := by
      have h1 := dvd_of_odd_dvd_mul_two_pow hodd hd
      rw [hz] at h1
      exact Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) h1
    let p₀ : Matrix.SpecialLinearGroup (Fin 3) F →* X ⧸ center X :=
      eJ.symm.toMonoidHom.comp ((projectiveSpecialLinearGroupEquivStatedProj 3 F).toMonoidHom.comp
        (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F))))
    have hp₀ : Function.Surjective p₀ :=
      eJ.symm.surjective.comp ((projectiveSpecialLinearGroupEquivStatedProj 3 F).surjective.comp
        (QuotientGroup.mk'_surjective _))
    have hk₀ : p₀.ker = center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      ext x
      simp only [MonoidHom.mem_ker, p₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hS₀ : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
    have hcard0 : Nat.card p₀.ker = 3 := by
      have hr : rootsOfUnity 3 F = (powMonoidHom 3 : Fˣ →* Fˣ).ker := by
        ext x
        rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [hk₀, Nat.card_congr
          (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
        Fintype.card_fin, hr, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hF, Nat.gcd_comm, hg]
    obtain ⟨α, hαs, -⟩ := exists_lift_of_coprime_index hS₀ inferInstance p₀ hp₀ hk₀.le
      (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le (2 ^ a)
      (by rw [QuotientGroup.ker_mk', hz]; exact Nat.Coprime.pow_left _ (by norm_num))
      (by rw [hM, hcard0, hg])
    have hcS : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = Nat.card (X ⧸ center X) * 3 := by
      rw [card_eq_card_mul_card_ker p₀ hp₀, hcard0]
    have hcX : Nat.card X = Nat.card (X ⧸ center X) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center X), hz]
    have hbij := hαs.bijective_of_nat_card_le (hcS.trans hcX.symm).le
    exact Or.inr ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.ofBijective α hbij).symm⟩⟩

theorem center_eq_bot_sz {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ : Nat.card (center X) = 1 ∨ Nat.card (center X) = 3)
    {k : ℕ} (h : SuzukiModel (X ⧸ center X) 2 k) : center X = ⊥ := by
  rcases hZ with hZ | hZ
  · exact Subgroup.eq_bot_of_card_eq _ hZ
  · exfalso
    have h3 := CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel h
    refine CFSG.RankThree.PartTwo.Sec13.not_three_dvd_card_of_forall_pow_three_mem hX.1
      (center X) le_rfl hZ.le (fun x hx ↦ ?_) (hZ ▸ Subgroup.card_subgroup_dvd_card _)
    have h1 : orderOf (x : X ⧸ center X) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
    have h2 : orderOf (x : X ⧸ center X) ∣ Nat.card (X ⧸ center X) := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h4 | h4
    · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
    · exact absurd (h4 ▸ h2) h3

end CFSG.Quasithin.H13.Mult5110
