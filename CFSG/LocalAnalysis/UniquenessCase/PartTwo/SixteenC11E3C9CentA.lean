module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section CommuteSup

variable {X : Type*} [Group X] {H K : Subgroup X}

theorem s1611e3_exists_mul_of_mem_sup_of_commute
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : X} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hH : H ≤ Subgroup.normalizer (K : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : a * z * a⁻¹ = z := by
        rw [hcomm a ha z hz]
        group
      change a * z * a⁻¹ ∈ K
      rwa [h1]
    · intro hy
      refine ⟨MulAut.conj a⁻¹ y, ?_, ?_⟩
      · have h1 : a⁻¹ * y * a⁻¹⁻¹ = y := by
          rw [hcomm a⁻¹ (H.inv_mem ha) y hy]
          group
        change a⁻¹ * y * a⁻¹⁻¹ ∈ K
        rwa [h1]
      · change a * (a⁻¹ * y * a⁻¹⁻¹) * a⁻¹ = y
        group
  haveI : (K.subgroupOf (H ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  have hx' : (⟨x, hx⟩ : ↥(H ⊔ K)) ∈ H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨(a : X), ha, (b : X), hb, congrArg Subtype.val hab⟩

end CommuteSup

variable {W : Type} [CommGroup W] [Finite W]

theorem s1611e3_seven_eq_one_of_fix_isIrr {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hL : IsPSL 3 2 1 ↥L) (hI : XMod.IsIrr ↥L I) (hcI : Nat.card ↥I = 8)
    {a : MulAut W} (haL : a ∈ L) (ha7 : a ^ 7 = 1) {z : W} (hzI : z ∈ I) (hz1 : z ≠ 1)
    (haz : a z = z) : a = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : IsPGroup 7 ↥(Subgroup.zpowers a) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ha7
  have hsub : Subgroup.zpowers a ≤ L := Subgroup.zpowers_le.mpr haL
  have hinvI : ∀ p ∈ Subgroup.zpowers a, ∀ v ∈ I, p v ∈ I :=
    fun p hp v hv => hI.1 ⟨p, hsub hp⟩ v hv
  let act : MulAction ↥(Subgroup.zpowers a) ↥I :=
    { smul := fun p v => ⟨p.1 v.1, hinvI p.1 p.2 v.1 v.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  letI := act
  have hfixC : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers a) ↥I) =
      Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun w =>
          ⟨w.1.1, ⟨(mem_fixV (X := Subgroup.zpowers a)).2
            (fun p hp => congrArg Subtype.val (w.2 ⟨p, hp⟩)), w.1.2⟩⟩
        invFun := fun v =>
          ⟨⟨v.1, v.2.2⟩, fun p =>
            Subtype.ext ((mem_fixV (X := Subgroup.zpowers a)).1 v.2.1 p.1 p.2)⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  have hmod := hP.card_modEq_card_fixedPoints ↥I
  rw [hcI, hfixC] at hmod
  have hcard_dvd : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) ∣ 8 := by
    rw [← hcI]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hzmem : z ∈ fixV (Subgroup.zpowers a) ⊓ I :=
    ⟨mem_fixV_zpowers_iff_apply.mpr haz, hzI⟩
  have hcard_ge : 2 ≤ Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) := by
    have h1mem : (1 : W) ∈ fixV (Subgroup.zpowers a) ⊓ I :=
      ⟨(fixV _).one_mem, I.one_mem⟩
    have hne : (⟨(1 : W), h1mem⟩ : ↥(fixV (Subgroup.zpowers a) ⊓ I)) ≠ ⟨z, hzmem⟩ := by
      intro h
      exact hz1 (Subtype.ext_iff.mp h).symm
    haveI : Nontrivial ↥(fixV (Subgroup.zpowers a) ⊓ I) := ⟨_, _, hne⟩
    have h := Finite.one_lt_card (α := ↥(fixV (Subgroup.zpowers a) ⊓ I))
    omega
  have hcard8 : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) = 8 := by
    have hdvd' : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) ∣ 2 ^ 3 := by
      simpa only [show (8 : ℕ) = 2 ^ 3 by norm_num] using hcard_dvd
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hmod1 : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) % 7 = 1 := by
      have h : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ I) % 7 = 8 % 7 := hmod.symm
      norm_num at h
      exact h
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at hk
      rw [hk] at hmod1
      norm_num at hmod1
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hk
      rw [hk] at hmod1
      norm_num at hmod1
    · rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at hk
      exact hk
  have hle_fix : I ≤ fixV (Subgroup.zpowers a) := by
    have heq : fixV (Subgroup.zpowers a) ⊓ I = I :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard8, hcI])
    rw [← heq]
    exact inf_le_left
  exact rank3_inj hL (fun x hx v hv => hI.1 ⟨x, hx⟩ v hv)
    (s16c167_norm_irr_nontrivial hI hcI) a haL
    (fun v hv => mem_fixV.mp (hle_fix hv) a (Subgroup.mem_zpowers a))

theorem s1611e3_eq_of_mul_eq_mul_of_inf_bot {A B : Subgroup W} (h : A ⊓ B = ⊥)
    {u u' v v' : W} (hu : u ∈ A) (hu' : u' ∈ B) (hv : v ∈ A) (hv' : v' ∈ B)
    (hmul : u * u' = v * v') : u = v ∧ u' = v' := by
  have h1 : v⁻¹ * u = v' * u'⁻¹ := by
    calc v⁻¹ * u = v⁻¹ * (u * u') * u'⁻¹ := by group
      _ = v⁻¹ * (v * v') * u'⁻¹ := by rw [hmul]
      _ = v' * u'⁻¹ := by group
  have hmem : v⁻¹ * u ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem hv) hu, by rw [h1]; exact B.mul_mem hv' (B.inv_mem hu')⟩
  rw [h, Subgroup.mem_bot] at hmem
  have huv : u = v := (inv_mul_eq_one.mp hmem).symm
  subst huv
  exact ⟨rfl, mul_left_cancel hmul⟩

theorem s1611e3_seven_eq_one_of_fix_natSum3 {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hL : IsPSL 3 2 1 ↥L) (hJ : NatSum3 L J)
    {a : MulAut W} (haL : a ∈ L) (ha7 : a ^ 7 = 1) {z : W} (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (haz : a z = z) : a = 1 := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, hsum⟩ := hJ
  have hinv₀ : ∀ g ∈ L, ∀ x ∈ I₀, g x ∈ I₀ := fun g hg x hx => hi₀.1 ⟨g, hg⟩ x hx
  have hinv₁ : ∀ g ∈ L, ∀ x ∈ I₁, g x ∈ I₁ := fun g hg x hx => hi₁.1 ⟨g, hg⟩ x hx
  have hinv₂ : ∀ g ∈ L, ∀ x ∈ I₂, g x ∈ I₂ := fun g hg x hx => hi₂.1 ⟨g, hg⟩ x hx
  have hinv01 : ∀ g ∈ L, ∀ x ∈ I₀ ⊔ I₁, g x ∈ I₀ ⊔ I₁ := by
    intro g hg x hx
    rw [Subgroup.mem_sup] at hx ⊢
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := hx
    exact ⟨g x₀, hinv₀ g hg x₀ hx₀, g x₁, hinv₁ g hg x₁ hx₁, (map_mul g x₀ x₁).symm⟩
  have hzJ' : z ∈ (I₀ ⊔ I₁) ⊔ I₂ := by rw [hsum]; exact hzJ
  obtain ⟨y, hy, z₂, hz₂, hyz⟩ := Subgroup.mem_sup.1 hzJ'
  have hsplit : a y * a z₂ = y * z₂ := by rw [← map_mul, hyz, haz]
  have hay : a y = y :=
    (s1611e3_eq_of_mul_eq_mul_of_inf_bot h012 (hinv01 a haL y hy)
      (hinv₂ a haL z₂ hz₂) hy hz₂ hsplit).1
  have haz₂ : a z₂ = z₂ :=
    (s1611e3_eq_of_mul_eq_mul_of_inf_bot h012 (hinv01 a haL y hy)
      (hinv₂ a haL z₂ hz₂) hy hz₂ hsplit).2
  by_cases hz₂1 : z₂ = 1
  · have hy1 : y ≠ 1 := by
      intro h
      exact hz1 (by rw [← hyz, h, hz₂1, mul_one])
    obtain ⟨y₀, hy₀, y₁, hy₁, hy₀y₁⟩ := Subgroup.mem_sup.1 hy
    have hsplit' : a y₀ * a y₁ = y₀ * y₁ := by rw [← map_mul, hy₀y₁, hay]
    have hay₀ : a y₀ = y₀ :=
      (s1611e3_eq_of_mul_eq_mul_of_inf_bot h01 (hinv₀ a haL y₀ hy₀)
        (hinv₁ a haL y₁ hy₁) hy₀ hy₁ hsplit').1
    have hay₁ : a y₁ = y₁ :=
      (s1611e3_eq_of_mul_eq_mul_of_inf_bot h01 (hinv₀ a haL y₀ hy₀)
        (hinv₁ a haL y₁ hy₁) hy₀ hy₁ hsplit').2
    by_cases hy₁1 : y₁ = 1
    · have hy₀1 : y₀ ≠ 1 := by
        intro h
        exact hy1 (by rw [← hy₀y₁, h, hy₁1, mul_one])
      exact s1611e3_seven_eq_one_of_fix_isIrr hL hi₀ hc₀ haL ha7 hy₀ hy₀1 hay₀
    · exact s1611e3_seven_eq_one_of_fix_isIrr hL hi₁ hc₁ haL ha7 hy₁ hy₁1 hay₁
  · exact s1611e3_seven_eq_one_of_fix_isIrr hL hi₂ hc₂ haL ha7 hz₂ hz₂1 haz₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
