module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Open.StatedCenterThree
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

section Generic

theorem mulEquiv_of_card_center_le {X Y₁ Y₂ : Type} [Group X] [Finite X] [Group Y₁] [Group Y₂]
    (f₁ : X →* Y₁) (f₂ : X →* Y₂) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (hle : f₁.ker ≤ f₂.ker) (e : Y₁ ⧸ Subgroup.center Y₁ ≃* Y₂ ⧸ Subgroup.center Y₂)
    (hZ : Nat.card (Subgroup.center Y₁) ≤ Nat.card (Subgroup.center Y₂)) :
    Nonempty (Y₁ ≃* Y₂) := by
  have hF₁ : Finite Y₁ := Finite.of_surjective f₁ h₁
  have hF₂ : Finite Y₂ := Finite.of_surjective f₂ h₂
  have hX1 := CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker f₁ h₁
  have hX2 := CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker f₂ h₂
  have hY1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y₁)
  have hY2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y₂)
  have hqe : Nat.card (Y₁ ⧸ Subgroup.center Y₁) = Nat.card (Y₂ ⧸ Subgroup.center Y₂) :=
    Nat.card_congr e.toEquiv
  have hpos1 : 0 < Nat.card (Subgroup.center Y₁) := Nat.card_pos
  have hposq : 0 < Nat.card (Y₂ ⧸ Subgroup.center Y₂) := Nat.card_pos
  have hk : Nat.card f₂.ker ≤ Nat.card f₁.ker := by
    rw [hY1, hqe] at hX1
    rw [hY2] at hX2
    have h3 : Nat.card (Y₂ ⧸ Subgroup.center Y₂) *
        (Nat.card (Subgroup.center Y₁) * Nat.card f₁.ker) =
        Nat.card (Y₂ ⧸ Subgroup.center Y₂) *
        (Nat.card (Subgroup.center Y₂) * Nat.card f₂.ker) := by
      rw [← mul_assoc, ← mul_assoc, ← hX1, ← hX2]
    have h4 := Nat.eq_of_mul_eq_mul_left hposq h3
    have h5 : Nat.card (Subgroup.center Y₁) * Nat.card f₂.ker ≤
        Nat.card (Subgroup.center Y₂) * Nat.card f₂.ker := Nat.mul_le_mul_right _ hZ
    rw [← h4] at h5
    exact Nat.le_of_mul_le_mul_left h5 hpos1
  have hker : f₁.ker = f₂.ker := Subgroup.eq_of_le_of_card_ge hle hk
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ h₂))⟩

theorem card_center_dvd_table_of_model (hGA : CFSG.Open.GriessAllModelsStatement)
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L) {t : StatedLieTag} {n p f : ℕ}
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) t n p f) :
    Nat.card (Subgroup.center L) ∣
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  have : Group.IsPerfect L := hL.1
  have hm : CFSG.Models.LieModel (L ⧸ Subgroup.center L) t n p f := ⟨hmod.1, .inl hmod⟩
  obtain ⟨-, ⟨e⟩⟩ := hGA _ t n p f hm
  let q := CFSG.RankThree.PerfectCover.centralQuotientMap (MulEquiv.refl (L ⧸ Subgroup.center L))
  have hq : Function.Surjective q :=
    CFSG.RankThree.PerfectCover.centralQuotientMap_surjective _
  have hk : q.ker = Subgroup.center L := CFSG.RankThree.PerfectCover.centralQuotientMap_ker _
  have hXp : Group.IsPerfect (L ⧸ Subgroup.center L) :=
    CFSG.RankThree.PerfectCover.isPerfect_of_quasisimple_quotient hL (MulEquiv.refl _)
  have hψ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hk.le
  have h1 : Nat.card q.ker ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (L ⧸ Subgroup.center L)) :=
    Subgroup.card_dvd_of_surjective hψ
  rw [hk, Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
    Nat.card_congr e.toEquiv] at h1
  simpa only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod] using h1

theorem quotCenter_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Γ : Subgroup (GL ι F)) [hperf : Group.IsPerfect Γ] [hs : IsSimpleGroup (StatedProj Γ)]
    {A : Type} [Group A] (π : ↥Γ ≃* A) : Nonempty (A ⧸ Subgroup.center A ≃* StatedProj Γ) := by
  have hnc : ∃ a b : StatedProj Γ, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative (StatedProj Γ) ⟨⟨hcon⟩⟩
  have hZ : Subgroup.center ↥Γ = (StatedScalars ι F).subgroupOf Γ :=
    CFSG.LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient _
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center Γ) hs hnc
  refine ⟨QuotientGroup.congr (Subgroup.center A) ((StatedScalars ι F).subgroupOf Γ) π.symm ?_⟩
  rw [Subgroup.map_center_eq π.symm, hZ]

end Generic

section Families

theorem card_center_le_sl3 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hodd : Odd (Nat.card (Subgroup.center Q))) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 3 F)) :
    Nat.card (Subgroup.center Q) ≤ Nat.card (Subgroup.center ↥(StatedSL 3 F)) := by
  have hadm : StatedLieAdmissible .PSL 3 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
      fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hd := card_center_dvd_table_of_model hGA hQ hmod
  have hg : genericOrders .PSL 3 2 n = (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
  rw [hg] at hd
  have hx : ∃ j : ℕ, (exceptionalOrders .PSL 3 2 n).1 * (exceptionalOrders .PSL 3 2 n).2 = 2 ^ j := by
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact ⟨0, rfl⟩
  obtain ⟨j, hj⟩ := hx
  rw [hj] at hd
  have hcop : Nat.Coprime (Nat.card (Subgroup.center Q)) (2 ^ j) := by
    apply Nat.Coprime.pow_right
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_ |>.symm
    have := Nat.odd_iff.mp hodd
    omega
  have hd' : Nat.card (Subgroup.center Q) ∣ Nat.gcd 3 (2 ^ n - 1) :=
    hcop.dvd_of_dvd_mul_right (by simpa using hd)
  have hpos : 0 < Nat.card (Subgroup.center ↥(StatedSL 3 F)) := Nat.card_pos
  by_cases h3 : 3 ∣ 2 ^ n - 1
  · rw [← hF] at h3
    have hc := CFSG.Open.StatedCenterThree.card_center_statedSL_three h3
    rw [hc]
    have : Nat.gcd 3 (2 ^ n - 1) = 3 := Nat.gcd_eq_left (by rwa [hF] at h3)
    rw [this] at hd'
    exact Nat.le_of_dvd (by norm_num) hd'
  · have : Nat.gcd 3 (2 ^ n - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    rw [this, Nat.dvd_one] at hd'
    omega

theorem card_center_eq_one_sp4 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.IsQuasisimple Q) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSp 2 F)) :
    Nat.card (Subgroup.center Q) = 1 := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hadm : StatedLieAdmissible .PSp 2 2 n :=
    ⟨Nat.prime_two, by omega, le_rfl, fun h => by
      have := congrArg Prod.snd h
      simp only at this
      omega⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSp 2 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hd := card_center_dvd_table_of_model hGA hQ hmod
  have hg : genericOrders .PSp 2 2 n = (Nat.gcd 2 (2 ^ n - 1), 1) := rfl
  have he : exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  rw [hg, he] at hd
  have hcop : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_
    intro h2
    have h3 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hcop] at hd
  simpa using hd

theorem card_center_eq_one_sl4 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.IsQuasisimple Q) (hodd : Odd (Nat.card (Subgroup.center Q))) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ 1)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 4 F)) : Nat.card (Subgroup.center Q) = 1 := by
  have hadm : StatedLieAdmissible .PSL 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
      fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 4 2 1 :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hd := card_center_dvd_table_of_model hGA hQ hmod
  have hg : genericOrders .PSL 4 2 1 = (1, 1) := rfl
  have he : exceptionalOrders .PSL 4 2 1 = (2, 1) := rfl
  rw [hg, he] at hd
  have hcop : Nat.Coprime (Nat.card (Subgroup.center Q)) 2 := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_ |>.symm
    have := Nat.odd_iff.mp hodd
    omega
  have : Nat.card (Subgroup.center Q) ∣ 1 := hcop.dvd_of_dvd_mul_right (by simpa using hd)
  exact Nat.dvd_one.mp this

theorem card_center_eq_one_sl5 (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.IsQuasisimple Q) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 1)
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 5 F)) : Nat.card (Subgroup.center Q) = 1 := by
  have hadm : StatedLieAdmissible .PSL 5 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
      fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 5 2 1 :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  have hd := card_center_dvd_table_of_model hGA hQ hmod
  have hg : genericOrders .PSL 5 2 1 = (1, 1) := rfl
  have he : exceptionalOrders .PSL 5 2 1 = (1, 1) := rfl
  rw [hg, he] at hd
  simpa using hd

end Families

end CFSG.Quasithin.RonanF918
