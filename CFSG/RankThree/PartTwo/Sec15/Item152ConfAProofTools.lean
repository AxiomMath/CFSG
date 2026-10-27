module

import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXCover
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.Quasithin.SteinbergCBAlternatingFiveAut
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.StronglyEmbedded.Catalog
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof152ConfA

set_option maxRecDepth 100000 in
theorem alt5_pow_three_of_commute : ∀ x y : alternatingGroup (Fin 5), x ≠ 1 → x ^ 3 = 1 →
    y * x = x * y → y ^ 3 = 1 := by
  decide

theorem pow_three_of_commute_of_mulEquiv {Γ : Type*} [Group Γ]
    (e : Γ ≃* alternatingGroup (Fin 5)) {x y : Γ} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxy : y * x = x * y) : y ^ 3 = 1 := by
  have h := alt5_pow_three_of_commute (e x) (e y) (by simpa using hx1)
    (by rw [← map_pow, hx3, map_one]) (by rw [← map_mul, hxy, map_mul])
  exact e.injective (by rw [map_pow, h, map_one])

noncomputable def mulAutCongr {Γ Δ : Type*} [Group Γ] [Group Δ] (e : Γ ≃* Δ) :
    MulAut Γ ≃* MulAut Δ where
  toFun σ := (e.symm.trans σ).trans e
  invFun τ := (e.trans τ).trans e.symm
  left_inv σ := by
    ext x
    simp
  right_inv τ := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp [MulAut.mul_apply]

theorem card_dvd_three_of_mulEquiv {Γ : Type*} [Group Γ] [Finite Γ]
    (e : Γ ≃* alternatingGroup (Fin 5)) {H : Subgroup (MulAut Γ)} (hH : IsPGroup 3 H) :
    Nat.card H ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, -, hodd⟩ := CFSG.Quasithin.SteinbergCB.A7_A5_odd_automorphism_subgroups_inner
  set H' := H.map (mulAutCongr e).toMonoidHom with hH'
  have hcard : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective (mulAutCongr e).injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hH'odd : Odd (Nat.card H') := by
    rw [hcard, hk]
    exact Odd.pow (by decide)
  have hle := hodd H' hH'odd
  have hinj : Function.Injective
      (MulAut.conj : alternatingGroup (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
    refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
    have hgZ : g ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun σ : MulAut (alternatingGroup (Fin 5)) => σ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc h * g = g * h * g⁻¹ * g := by rw [this]
        _ = g * h := by group
    rw [hZ] at hgZ
    exact Subgroup.mem_bot.mp hgZ
  have hrange : Nat.card (MulAut.conj : alternatingGroup (Fin 5) →*
      MulAut (alternatingGroup (Fin 5))).range = 60 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card H ∣ 60 := by
    rw [← hcard, ← hrange]
    exact Subgroup.card_dvd_of_le hle
  rw [hk] at h60 ⊢
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    have := this.trans h60
    norm_num at this
  interval_cases k <;> norm_num

theorem exists_sylow_three_fixed {Γ : Type*} [Group Γ] [Finite Γ] {S : Subgroup (MulAut Γ)}
    (hS : IsPGroup 3 S) :
    ∃ P : Sylow 3 Γ, ∀ α ∈ S, (P : Subgroup Γ).map α.toMonoidHom = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 Γ) := by
    have h := card_sylow_modEq_one 3 Γ
    rintro ⟨k, hk⟩
    unfold Nat.ModEq at h
    rw [hk] at h
    omega
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 Γ) hnd
  refine ⟨P, fun α hα => ?_⟩
  have h2 : α • P = P := hP ⟨α, hα⟩
  have h3 := congrArg (fun Q : Sylow 3 Γ => (Q : Subgroup Γ)) h2
  simp only [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h3
  exact h3

theorem eq_of_pow_three_eq_one {Γ : Type*} [Group Γ] {σ : MulAut Γ} (hσ : σ ^ 3 = 1) {r : Γ}
    (hr : orderOf r = 3) (hσr : σ r ∈ Subgroup.zpowers r) : σ r = r := by
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr
    omega
  have hr3 : r ^ 3 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσr
  have hk' : r ^ (k % 3) = σ r := by
    rw [← hk, show (3 : ℤ) = (orderOf r : ℤ) by rw [hr]; rfl, zpow_mod_orderOf]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k % 3 = j := ⟨(k % 3).toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [hj, zpow_natCast] at hk'
  have hjr : r ^ j = σ r := hk'
  have hj3 : j < 3 := by omega
  have hσ3 : ∀ x : Γ, σ (σ (σ x)) = x := by
    intro x
    have := congrArg (fun τ : MulAut Γ => τ x) hσ
    simpa [pow_succ, MulAut.mul_apply] using this
  interval_cases j
  · exfalso
    rw [pow_zero] at hjr
    exact hr1 (σ.injective (by rw [← hjr, map_one]))
  · rw [← hjr, pow_one]
  · exfalso
    have h1 : σ (σ r) = r := by
      rw [← hjr, map_pow, ← hjr, ← pow_mul,
        show r ^ (2 * 2) = r ^ 3 * r by group, hr3, one_mul]
    have h2 := hσ3 r
    rw [h1, ← hjr] at h2
    apply hr1
    calc r = r ^ 2 * r⁻¹ := by group
      _ = 1 := by rw [h2]; group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_theta_quot_eq_bot {X : Subgroup G}
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60) :
    Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) = ⊥ := by
  rcases (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)).normal_of_characteristic
      |>.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥X ⧸ aschbacherSolvableCore 3 ↥X)
    rw [hX60] at hp
    norm_num at hp

theorem exists_mem_inf_not_mem_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    ∃ x ∈ A, x ∈ X ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ x ∉ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  set φ : ↥A →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hctx.norm_x)
    with hφ
  have hS : IsPGroup 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hA.isPGroup.of_equiv Subgroup.topEquiv.symm).map φ
  obtain ⟨R, hR⟩ := exists_sylow_three_fixed hS
  have hRcard : Nat.card (R : Subgroup ↥X) = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have hX : Nat.card ↥X = 60 * Nat.card θ := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
      rwa [hX60] at this
    have h60 : Nat.factorization 60 3 = 1 := by
      rw [show (60 : ℕ) = 3 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hX, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h60,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero, pow_one]
  have hRnt : Nontrivial (R : Subgroup ↥X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hRcard]
    norm_num
  obtain ⟨⟨r, hrR⟩, hr1⟩ := exists_ne (1 : (R : Subgroup ↥X))
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrord : orderOf r = 3 := by
    have h := orderOf_dvd_natCard (⟨r, hrR⟩ : (R : Subgroup ↥X))
    rw [hRcard, Subgroup.orderOf_mk] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hr1'
    · exact h1
  have hRz : (R : Subgroup ↥X) = Subgroup.zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrR) ?_).symm
    rw [Nat.card_zpowers, hrord, hRcard]
  have hrA : ∀ a ∈ A, a * (r : G) * a⁻¹ = r := by
    intro a ha
    have hσ : (φ ⟨a, ha⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := Subtype.ext (hA.1.2 a ha)
      rw [this, map_one]
    have hmem : φ ⟨a, ha⟩ r ∈ Subgroup.zpowers r := by
      rw [← hRz, ← hR (φ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩]
      exact ⟨r, hrR, rfl⟩
    have h := eq_of_pow_three_eq_one hσ hrord hmem
    have h' := congrArg Subtype.val h
    rwa [hφ, MonoidHom.comp_apply, Sec4.normalizerMonoidHom_apply_coe] at h'
  have hr3 : (r : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hrord, pow_orderOf_eq_one, Subgroup.coe_one]
  have hrAm : (r : G) ∈ A := by
    refine mem_of_mem_partTwoF hAF hr3 fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (r : G) = a * r * a⁻¹ * a := by group
      _ = r * a := by rw [hrA a ha]
  refine ⟨r, hrAm, r.2, hr3, fun h => hr1' (Subtype.ext h), ?_⟩
  rintro ⟨t, ht, htr⟩
  have htr' : t = r := Subtype.ext htr
  rw [htr'] at ht
  have h := orderOf_dvd_natCard (⟨r, ht⟩ : θ)
  rw [Subgroup.orderOf_mk, hrord] at h
  exact hθ3 h

theorem exists_not_mem_thetaQuotCentralizer
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    ∃ a ∈ A, a ∉ Sec4.thetaQuotCentralizer X := by
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨x, hxA, hxX, -, -, hxθ⟩ := exists_mem_inf_not_mem_theta hctx hAF hA
  refine ⟨x, hxA, fun hxC => hxθ ?_⟩
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hZ := center_theta_quot_eq_bot hXs hX60
  have hcen : (QuotientGroup.mk' θ ⟨x, hxX⟩ : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hxC
    obtain ⟨t, ht, hte⟩ := hl l l.2
    have hte' : (t : G) = (l : G)⁻¹ * (x * l * x⁻¹) := hte
    have h1 : (QuotientGroup.mk' θ l : ↥X ⧸ θ) =
        QuotientGroup.mk' θ (⟨x, hxX⟩ * l * (⟨x, hxX⟩ : ↥X)⁻¹) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : l⁻¹ * (⟨x, hxX⟩ * l * (⟨x, hxX⟩ : ↥X)⁻¹) = t :=
        Subtype.ext (by rw [hte']; simp)
      rw [this]
      exact ht
    rw [map_mul, map_mul, map_inv] at h1
    calc QuotientGroup.mk' θ l * QuotientGroup.mk' θ ⟨x, hxX⟩ =
        QuotientGroup.mk' θ ⟨x, hxX⟩ * QuotientGroup.mk' θ l *
          (QuotientGroup.mk' θ ⟨x, hxX⟩)⁻¹ * QuotientGroup.mk' θ ⟨x, hxX⟩ := by
          rw [← h1]
      _ = QuotientGroup.mk' θ ⟨x, hxX⟩ * QuotientGroup.mk' θ l := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  exact ⟨_, hcen, rfl⟩

theorem card_inf_thetaQuotCentralizer
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  have hmul := Sec13.card_inf_mul_card_autThetaQuot hctx.norm_x
  rw [hA.2] at hmul
  have hH27 : Nat.card (Sec4.autThetaQuot A X) ∣ 3 ^ 3 :=
    Dvd.intro_left _ (hmul.trans (by norm_num))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hH27
  have hH3 : Nat.card (Sec4.autThetaQuot A X) ∣ 3 :=
    card_dvd_three_of_mulEquiv e (IsPGroup.of_card hk)
  obtain ⟨a, haA, haC⟩ := exists_not_mem_thetaQuotCentralizer hctx hAF hA
  have hne : Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) ≠ 27 := by
    intro h27
    have hle : A ≤ A ⊓ Sec4.thetaQuotCentralizer X :=
      (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hA.2])).symm.le
    exact haC (hle haA).2
  rcases (Nat.dvd_prime Nat.prime_three).mp hH3 with h1 | h1
  · rw [h1, mul_one] at hmul
    exact absurd hmul hne
  · rw [h1] at hmul
    omega

theorem inf_centralizer_le_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A)
    {Q : Subgroup G} (hQ : Q ∈ collectionIn (scriptQ A LB) X) :
    Q ⊓ Subgroup.centralizer (A : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hX60
  obtain ⟨x, hxA, hxX, hx3, -, hxθ⟩ := exists_mem_inf_not_mem_theta hctx hAF hA
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hx1 : π ⟨x, hxX⟩ ≠ 1 := fun h => hxθ ⟨_, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
  have hx3' : (π ⟨x, hxX⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
  intro y hy
  have hyX : y ∈ X := hQ.2 hy.1
  have hyx : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hy.2 x hxA).symm
  have hy3 : (π ⟨y, hyX⟩) ^ 3 = 1 := by
    refine pow_three_of_commute_of_mulEquiv e hx1 hx3' ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyx
  have hyo : (π ⟨y, hyX⟩) ^ orderOf y = 1 := by
    rw [← map_pow]
    have : (⟨y, hyX⟩ : ↥X) ^ orderOf y = 1 := Subtype.ext (pow_orderOf_eq_one y)
    rw [this, map_one]
  have hcop : Nat.Coprime (orderOf y) 3 := by
    have h1 : orderOf y ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨y, hy.1⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3).symm
  have h1 : π ⟨y, hyX⟩ = 1 := by
    have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyo) (orderOf_dvd_of_pow_eq_one hy3)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact h2
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem le_deltaZero_sup_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    X ≤ deltaZero A LB X ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hctx.delta_x.le.trans (sSup_le fun Q hQ => ?_)
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A Q hA.isPGroup hQ3 hAQ
  refine (le_of_eq hfac).trans (sup_le (le_sup_of_le_left ?_)
    (le_sup_of_le_right (inf_centralizer_le_theta hctx hAF hA hQ)))
  have hcQ : ⁅Q, A⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ
  refine le_deltaZero ⟨mem_scriptQ_of_le hQ.1 hcQ (Subgroup.normalizer_commutator_ge_right Q A),
    (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A Q
      hA.isPGroup hQ3 hAQ).symm⟩ ?_
  exact (Subgroup.commutator_mono hQ.2 le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hctx.norm_x)

theorem pPrimeCoreOf_deltaZero_le_theta
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) :
    pPrimeCoreOf 3 (deltaZero A LB X) ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  set D0 := deltaZero A LB X with hD0
  set N := pPrimeCoreOf 3 D0 with hN
  have hD0X : D0 ≤ X := deltaZero_le X
  have hNX : N ≤ X := (pPrimeCoreOf_le 3 D0).trans hD0X
  have hcov : (D0.subgroupOf X).map (QuotientGroup.mk' θ) = ⊤ :=
    Proof152Gen.map_subgroupOf_eq_top_of_le_sup hD0X (le_deltaZero_sup_theta hctx hAF hA)
  have hn := Proof152Gen.map_subgroupOf_normal_of_le_normalizer
    (le_normalizer_pPrimeCoreOf 3 D0) hcov
  rcases hn.eq_bot_or_eq_top with h | h
  · intro n hn'
    have hmem : QuotientGroup.mk' θ ⟨n, hNX hn'⟩ ∈ (N.subgroupOf X).map (QuotientGroup.mk' θ) :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hn', rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩
  · exfalso
    have h1 : Nat.card ((N.subgroupOf X).map (QuotientGroup.mk' θ)) = 60 := by
      rw [h, Subgroup.card_top, hX60]
    have h2 : Nat.card ((N.subgroupOf X).map (QuotientGroup.mk' θ)) ∣ Nat.card N := by
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    rw [h1] at h2
    have h3 := coprime_card_pPrimeCoreOf 3 D0
    rw [← hN] at h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3
      ((by norm_num : 3 ∣ 60).trans h2)

omit [Finite G] in
theorem deltaZero_inf_normalizer_le_centralizer {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {X : Subgroup G} {c' : G} (hc'A : c' ∈ A)
    (hc'3 : orderOf c' = 3) :
    deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ≤
      Subgroup.centralizer ({c'} : Set G) :=
  sSup_le fun _ hQ => Sec14.le_centralizer_of_mem_invariantPiSubgroups hc'A hc'3
    ⟨hQ.2.trans inf_le_right, hQ.1.1.1.2.1, hQ.1.1.1.2.2⟩

theorem mem_thetaQuotCentralizer_of_dec
    {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G}
    (hctx : Ctx152 A LB Y M X) (hAF : A ∈ partTwoF G) (hA : Late.IsE27 A) {c' : G}
    (hc'A : c' ∈ A) (hc'3 : orderOf c' = 3)
    (hdec : deltaZero A LB X = pPrimeCoreOf 3 (deltaZero A LB X) ⊔
      deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))) :
    c' ∈ Sec4.thetaQuotCentralizer X := by
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hcov : X ≤ (X ⊓ Subgroup.centralizer ({c'} : Set G)) ⊔ θX := by
    refine (le_deltaZero_sup_theta hctx hAF hA).trans (sup_le ?_ le_sup_right)
    refine (le_of_eq hdec).trans (sup_le ?_ ?_)
    · exact (pPrimeCoreOf_deltaZero_le_theta hctx hAF hA).trans le_sup_right
    · exact le_sup_of_le_left (le_inf ((deltaZero_le _).trans inf_le_left)
        (deltaZero_inf_normalizer_le_centralizer hc'A hc'3))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hctx.norm_x hc'A, fun l hl => ?_⟩
  have hl' : l ∈ ((X ⊓ Subgroup.centralizer ({c'} : Set G) ⊔ θX : Subgroup G) : Set G) := hcov hl
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (inf_le_left.trans (Sec6.le_normalizer_theta X))] at hl'
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hl'
  have hyc : y * c' = c' * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have he : c' * (y * t) * c'⁻¹ = y * (c' * t * c'⁻¹) := by
    calc c' * (y * t) * c'⁻¹ = (c' * y) * t * c'⁻¹ := by group
      _ = (y * c') * t * c'⁻¹ := by rw [hyc]
      _ = y * (c' * t * c'⁻¹) := by group
  rw [he, show (y * t)⁻¹ * (y * (c' * t * c'⁻¹)) = t⁻¹ * (c' * t * c'⁻¹) by group]
  exact mul_mem (inv_mem ht) ((Subgroup.mem_normalizer_iff.mp
    (Sec6.normalizer_le_normalizer_theta X (hctx.norm_x hc'A)) t).mp ht)

end Proof152ConfA

end CFSG.RankThree.PartTwo.Sec15
