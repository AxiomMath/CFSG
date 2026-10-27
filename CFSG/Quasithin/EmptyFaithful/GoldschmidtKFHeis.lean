module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOuterThree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFTwo
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

omit [Finite G] in
theorem card_sup_zpowers_of_mem_normalizer {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) (hinf : A ⊓ Subgroup.zpowers x = ⊥) :
    Nat.card ↥(A ⊔ Subgroup.zpowers x) = Nat.card ↥A * Nat.card ↥(Subgroup.zpowers x) := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hx
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers x) hle
  let Φ : ↥A × ↥(Subgroup.zpowers x) → ↥(A ⊔ Subgroup.zpowers x) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
    have h2 : ((a' : G)⁻¹ * (a : G)) = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h1]
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * (a : G) ∈ A ⊓ Subgroup.zpowers x :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ (Subgroup.zpowers x).mul_mem b'.2
        ((Subgroup.zpowers x).inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hab' : a = a' := Subtype.ext (inv_mul_eq_one.mp hmem).symm
    have hbb : (b : G) = b' := by
      have : (b' : G) * (b : G)⁻¹ = 1 := by rw [← h2, hmem]
      exact (mul_inv_eq_one.mp this).symm
    exact Prod.ext hab' (Subtype.ext hbb)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ ((A ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hy
    rw [hset] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem isPOnePlusTwo_of_card_twentySeven {U : Type*} [Group U] [Finite U] (hcard : Nat.card U = 27)
    (h3 : ∀ x : U, x ^ 3 = 1) (hnc : ¬ IsMulCommutative U) : IsPOnePlusTwo 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 U := fun x => ⟨1, by rw [pow_one]; exact h3 x⟩
  obtain ⟨-, -, -, hZ⟩ := CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP h3
    (by rw [hcard]; norm_num) hnc
  have hq : Nat.card (U ⧸ Subgroup.center U) = 9 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center U)
    rw [hcard, hZ] at this
    omega
  have hcomm : IsMulCommutative (U ⧸ Subgroup.center U) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hq]; norm_num)
  have hpow : ∀ x : U ⧸ Subgroup.center U, x ^ 3 = 1 := by
    intro x
    refine QuotientGroup.induction_on x fun y => ?_
    rw [← QuotientGroup.mk_pow, h3 y]
    exact QuotientGroup.mk_one _
  have hnt : Nontrivial (U ⧸ Subgroup.center U) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hq]
    norm_num
  have helem : CFSG.IsElementaryAbelian 3 (U ⧸ Subgroup.center U) :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  exact ⟨⟨hZ, helem, hnt⟩, by rw [hcard]; norm_num, h3⟩

theorem KFHyp.mem_normalizer_F (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {F : Subgroup G}
    (hFL : F ≤ L) (hFel : CFSG.Assembly.IsElemAbelian 3 F)
    (hFσ : ∀ x ∈ F, (τ * f) * x = x * (τ * f))
    (hFodd : ∀ l ∈ L, (τ * f) * l = l * (τ * f) → Odd (orderOf l) → l ∈ F) {g : G}
    (hg : g ∈ I) (hgσ : (τ * f) * g = g * (τ * f)) : g ∈ Subgroup.normalizer (F : Set G) := by
  have hconj : ∀ g ∈ I, (τ * f) * g = g * (τ * f) → ∀ a ∈ F, g * a * g⁻¹ ∈ F := by
    intro g hg hgσ a ha
    have haL : g * a * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h.r.hNL hg) a).mp (hFL ha)
    have hcomm : (τ * f) * (g * a * g⁻¹) = (g * a * g⁻¹) * (τ * f) := by
      have h1 : (τ * f) * g⁻¹ = g⁻¹ * (τ * f) := by
        calc (τ * f) * g⁻¹ = g⁻¹ * (g * (τ * f)) * g⁻¹ := by group
          _ = g⁻¹ * ((τ * f) * g) * g⁻¹ := by rw [hgσ]
          _ = g⁻¹ * (τ * f) := by group
      calc (τ * f) * (g * a * g⁻¹) = ((τ * f) * g) * a * g⁻¹ := by group
        _ = g * ((τ * f) * a) * g⁻¹ := by rw [hgσ]; group
        _ = g * (a * (τ * f)) * g⁻¹ := by rw [hFσ a ha]
        _ = g * a * ((τ * f) * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (τ * f) := by rw [h1]; group
    have hcube : (g * a * g⁻¹) ^ 3 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hFel.2 a ha, map_one]
    have hodd : Odd (orderOf (g * a * g⁻¹)) := by
      have hd : orderOf (g * a * g⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> decide
    exact hFodd _ haL hcomm hodd
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hconj g hg hgσ a
  · intro hga
    have hginv : (τ * f) * g⁻¹ = g⁻¹ * (τ * f) := by
      calc (τ * f) * g⁻¹ = g⁻¹ * (g * (τ * f)) * g⁻¹ := by group
        _ = g⁻¹ * ((τ * f) * g) * g⁻¹ := by rw [hgσ]
        _ = g⁻¹ * (τ * f) := by group
    have := hconj g⁻¹ (I.inv_mem hg) hginv _ hga
    simpa [mul_assoc] using this

theorem KFHyp.exists_threeOnePlusTwo (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ F B : Subgroup G, F ≤ L ∧ F ≤ B ∧ B ≤ I ∧ B ≤ Subgroup.centralizer ({τ * f} : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card ↥F = 9 ∧
      (∀ g ∈ I, (τ * f) * g = g * (τ * f) → g ∈ Subgroup.normalizer (F : Set G)) ∧
      (∀ l ∈ L, (τ * f) * l = l * (τ * f) → Odd (orderOf l) → l ∈ F) ∧
      IsPOnePlusTwo 3 ↥B ∧ ∃ b ∈ B, b ^ 3 = 1 ∧ ∃ v ∈ V₁, b * v * b⁻¹ ≠ v := by
  classical
  obtain ⟨F, hFL, hFel, hF9, hFσ, hFodd, -⟩ := h.sigma_structure h113
  obtain ⟨y, hyX, hyL, hyσ⟩ := h.exists_mem_X_centralizes_sigma
  have hyI : y ∈ I := h.Yp_le_I (h.hXY hyX)
  obtain ⟨a, ha⟩ := h.hX3.exists_card_eq
  have hy3 : y ^ 3 = 1 := by
    refine h.pow_three_of_pow h113 hyI ⟨a, ?_⟩
    have : (⟨y, hyX⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val this
    rw [ha] at h2
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hy1 : y ≠ 1 := fun h1 => hyL (h1 ▸ L.one_mem)
  have hyN : y ∈ Subgroup.normalizer (F : Set G) :=
    h.mem_normalizer_F hFL hFel hFσ hFodd hyI hyσ
  have hmove : ∃ v ∈ V₁, y * v * y⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    have hmem : y ∈ Subgroup.centralizer (V₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := hcon v hv
      calc v * y = (y * v * y⁻¹) * y := by rw [this]
        _ = y * v := by group
    rw [h.hcl'] at hmem
    have hodd : Odd (orderOf y) := by
      have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> decide
    exact hyL (mem_of_odd_orderOf_of_mem_sup_zpowers h.sigma_ne_one h.sigma_sq
      (h.r.hNL h.sigma_mem_I) hmem hodd)
  set B : Subgroup G := F ⊔ Subgroup.zpowers y with hB
  have hinf : F ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzF, hzy⟩
    rw [Subgroup.mem_bot]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzy
    have hj : y ^ j = y ^ (j % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv j 3]
      rw [zpow_add, zpow_mul]
      have h3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
      rw [h3, one_zpow, mul_one]
    have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rw [hj]
    rcases hr with hr | hr | hr
    · rw [hr]; simp
    · exfalso
      rw [hj, hr, zpow_one] at hzF
      exact hyL (hFL hzF)
    · exfalso
      rw [hj, hr] at hzF
      have hsq : (y ^ (2 : ℤ)) ^ 2 = y := by
        have hy3' : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
        rw [zpow_two, pow_two]
        calc y * y * (y * y) = y * (y * (y * y)) := by simp only [mul_assoc]
          _ = y := by rw [hy3', mul_one]
      exact hyL (hFL (hsq ▸ F.pow_mem hzF 2))
  have hycard : Nat.card ↥(Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h1
  have hBcard : Nat.card ↥B = 27 := by
    rw [hB, card_sup_zpowers_of_mem_normalizer hyN hinf, hF9, hycard]
  have hBI : B ≤ I := sup_le (hFL.trans h.L_le_I) (Subgroup.zpowers_le.mpr hyI)
  have hBσ : B ≤ Subgroup.centralizer ({τ * f} : Set G) := by
    refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hFσ x hx).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyσ.symm
  have hB3 : ∀ x : ↥B, x ^ 3 = 1 := by
    intro x
    have hxI : (x : G) ∈ I := hBI x.2
    have hdvd : (x : G) ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥B) (x := x)
      rw [hBcard] at this
      simpa using congrArg Subtype.val this
    have h27 : (x : G) ^ 3 = 1 := h.pow_three_of_pow h113 hxI ⟨3, by simpa using hdvd⟩
    exact Subtype.ext (by simpa using h27)
  have hnc : ¬ IsMulCommutative ↥B := by
    intro hcomm
    have hel : CFSG.Assembly.IsElemAbelian 3 B :=
      ⟨hcomm, fun x hx => by simpa using congrArg Subtype.val (hB3 ⟨x, hx⟩)⟩
    have hrank : 3 ≤ CFSG.Assembly.pRank 3 I :=
      CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three hBI hel
        (by rw [hBcard]; norm_num)
    have hV2 : IsPGroup 2 ↥V₁ :=
      IsPGroup.of_card (n := 2) (by rw [h.r.ctx.hyp.decomp.card₁]; norm_num)
    have hpc : pCoreOf 2 I ≠ ⊥ := by
      intro hbot
      have hV1I : V₁ ≤ I := h.hI ▸ Subgroup.le_normalizer
      have hle : V₁ ≤ pCoreOf 2 I :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV1I h.hI.le hV2
      have hV1bot : V₁ = ⊥ := le_bot_iff.mp (hbot ▸ hle)
      have : Nat.card ↥V₁ = 4 := h.r.ctx.hyp.decomp.card₁
      rw [hV1bot, Subgroup.card_bot] at this
      omega
    have hle2 : CFSG.Assembly.pRank 3 I ≤ 2 :=
      pRank_le_two_of_pCoreOf_ne_bot h.r.ctx.hyp.hyp.qtfe.qtke hpc Nat.prime_three (by norm_num)
    omega
  refine ⟨F, B, hFL, le_sup_left, hBI, hBσ, hFel, hF9, ?_, hFodd,
    isPOnePlusTwo_of_card_twentySeven hBcard hB3 hnc, y, ?_, hy3, hmove⟩
  · intro g hg hgσ
    exact h.mem_normalizer_F hFL hFel hFσ hFodd hg hgσ
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

end CFSG.Quasithin.SBd19F
