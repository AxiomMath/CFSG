module

public import CFSG.RankThree.PartTwo.KFacts.KS222SL3Bar
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G]

theorem exists_fixed_lift_thetaQuot {H : Type*} [Group H] [Finite H] {σ : MulAut H}
    (hσ : σ ^ 3 = 1) {z : H ⧸ aschbacherSolvableCore 3 H}
    (hz : Sec4.thetaQuotMulAut H σ z = z) :
    ∃ x : H, σ x = x ∧ (x : H ⧸ aschbacherSolvableCore 3 H) = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 (Subgroup.zpowers σ) :=
    IsPGroup.of_card_dvd_pow (n := 1)
      (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one hσ)
  have hfix : ∀ a : Subgroup.zpowers σ, Sec4.thetaQuotMulAut H a z = z := by
    rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hst : Sec4.thetaQuotMulAut H σ ∈
        MulAction.stabilizer (MulAut (H ⧸ aschbacherSolvableCore 3 H)) z := hz
    have h := (MulAction.stabilizer (MulAut (H ⧸ aschbacherSolvableCore 3 H)) z).zpow_mem hst k
    rw [← map_zpow] at h
    exact h
  let F := {x : H // (x : H ⧸ aschbacherSolvableCore 3 H) = z}
  let _ : MulAction (Subgroup.zpowers σ) F :=
    { smul := fun a x => ⟨(a : MulAut H) x.1, by
        rw [← Sec4.thetaQuotMulAut_mk, x.2]
        exact hfix a⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun a b x => Subtype.ext rfl }
  have hcard : Nat.card F = Nat.card (aschbacherSolvableCore 3 H) := by
    have h := Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 H)) z)
    rw [QuotientGroup.ker_mk'] at h
    exact h
  have h3 : ¬ 3 ∣ Nat.card F := by
    rw [hcard]
    exact (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
  obtain ⟨x, hx⟩ := hSp.nonempty_fixed_point_of_prime_not_dvd_card F h3
  exact ⟨x.1, congrArg Subtype.val (hx ⟨σ, Subgroup.mem_zpowers σ⟩), x.2⟩

theorem map_fixedSubgroupOf_eq_thetaQuot {H : Type*} [Group H] [Finite H] {σ : MulAut H}
    (hσ : σ ^ 3 = 1) :
    (fixedSubgroupOf σ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) =
      fixedSubgroupOf (Sec4.thetaQuotMulAut H σ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact congrArg (QuotientGroup.mk' (aschbacherSolvableCore 3 H))
      ((mem_fixedSubgroupOf σ x).mp hx)
  · intro hz
    obtain ⟨x, hx, rfl⟩ := exists_fixed_lift_thetaQuot hσ hz
    exact ⟨x, hx, rfl⟩

theorem isSolvable_fixedSubgroupOf_thetaQuot {H : Type*} [Group H] [Finite H] {σ : MulAut H}
    (hσ : σ ^ 3 = 1) (hs : Group.IsSolvable (fixedSubgroupOf σ)) :
    Group.IsSolvable (fixedSubgroupOf (Sec4.thetaQuotMulAut H σ)) := by
  rw [← map_fixedSubgroupOf_eq_thetaQuot hσ]
  exact Group.isSolvable_of_surjective ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem map_fixedSubgroupOf_normalizerMonoidHom {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    (fixedSubgroupOf (L.normalizerMonoidHom ⟨b, hb⟩)).map L.subtype =
      L ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h : b * (x : G) * b⁻¹ = x := congrArg Subtype.val ((mem_fixedSubgroupOf _ x).mp hx)
    show (x : G) * b = b * x
    calc (x : G) * b = b * x * b⁻¹ * b := by rw [h]
      _ = b * x := by group
  · intro hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    show L.normalizerMonoidHom ⟨b, hb⟩ ⟨x, hxL⟩ = ⟨x, hxL⟩
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    show b * x * b⁻¹ = x
    calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [hxC]
      _ = x := by group

theorem inSubgroup_perfectResidual_eq_bot_iff {H : Type*} [Group H] [Finite H]
    (X : Subgroup H) : inSubgroup perfectResidual X = ⊥ ↔ Group.IsSolvable X := by
  rw [inSubgroup, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  exact (perfect_residual_characterization (G := X)).2.2.2.2.2

theorem even_card_fixedSubgroupOf_thetaQuot [Finite G] {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) {t : G} (htL : t ∈ L)
    (htN : t ∈ Subgroup.normalizer (A : Set G)) (htb : t * b = b * t)
    (ht2 : orderOf (A.normalizerMonoidHom ⟨t, htN⟩) = 2) :
    Even (Nat.card (fixedSubgroupOf (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩)))) := by
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hz : ((⟨t, htL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      fixedSubgroupOf (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩)) := by
    show Sec4.thetaQuotMulAut L _ ((⟨t, htL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    show b * t * b⁻¹ = t
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [htb]
      _ = t := by group
  have h2 : 2 ∣ orderOf ((⟨t, htL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    by_contra hodd
    obtain ⟨k, hk⟩ : ∃ k, k = orderOf ((⟨t, htL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
      ⟨_, rfl⟩
    rw [← hk] at hodd
    have hxk : (⟨t, htL⟩ : L) ^ k ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hk, pow_orderOf_eq_one]
    have htk : (((⟨t, htL⟩ : L) ^ k : L) : G) = t ^ k := by
      rw [Subgroup.coe_pow]
    have htkN : t ^ k ∈ Subgroup.normalizer (A : Set G) := (Subgroup.normalizer _).pow_mem htN k
    have hcomm : ∀ a ∈ A, t ^ k * a * (t ^ k)⁻¹ = a := by
      intro a ha
      have hσa : L.normalizerMonoidHom ⟨a, hAL ha⟩ ((⟨t, htL⟩ : L) ^ k)⁻¹ ∈
          aschbacherSolvableCore 3 L := by
        have h : L.normalizerMonoidHom ⟨a, hAL ha⟩ ((⟨t, htL⟩ : L) ^ k)⁻¹ ∈
            (aschbacherSolvableCore 3 L).map
              (L.normalizerMonoidHom ⟨a, hAL ha⟩ : L →* L) :=
          ⟨_, (aschbacherSolvableCore 3 L).inv_mem hxk, rfl⟩
        rwa [Sec4.map_aschbacherSolvableCore] at h
      set w : L := (⟨t, htL⟩ : L) ^ k * L.normalizerMonoidHom ⟨a, hAL ha⟩ ((⟨t, htL⟩ : L) ^ k)⁻¹
        with hw
      have hwθ : w ∈ aschbacherSolvableCore 3 L :=
        (aschbacherSolvableCore 3 L).mul_mem hxk hσa
      have hwG : (w : G) = t ^ k * a * (t ^ k)⁻¹ * a⁻¹ := by
        rw [hw, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe, Subgroup.coe_inv, htk]
        group
      have hwA : (w : G) ∈ A := by
        rw [hwG]
        exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp htkN a).mp ha) (A.inv_mem ha)
      have hw3 : orderOf w ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hAe.2 _ hwA))
      have hwo : orderOf w ∣ Nat.card (aschbacherSolvableCore 3 L) := by
        rw [← Subgroup.orderOf_mk w hwθ]
        exact orderOf_dvd_natCard _
      have hcop : Nat.gcd 3 (Nat.card (aschbacherSolvableCore 3 L)) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
      have hw1 : w = 1 :=
        orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hw3 hwo))
      have h1 : t ^ k * a * (t ^ k)⁻¹ * a⁻¹ = 1 := by
        rw [← hwG, hw1, Subgroup.coe_one]
      calc t ^ k * a * (t ^ k)⁻¹ = t ^ k * a * (t ^ k)⁻¹ * a⁻¹ * a := by group
        _ = a := by rw [h1, one_mul]
    have hpow : A.normalizerMonoidHom ⟨t, htN⟩ ^ k = 1 := by
      rw [← map_pow]
      ext a
      rw [MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe, SubmonoidClass.coe_pow]
      exact hcomm a a.2
    have := orderOf_dvd_of_pow_eq_one hpow
    rw [ht2] at this
    exact hodd this
  have hdvd : orderOf ((⟨t, htL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∣
      Nat.card (fixedSubgroupOf (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩))) := by
    rw [← Subgroup.orderOf_mk _ hz]
    exact orderOf_dvd_natCard _
  exact even_iff_two_dvd.mpr (h2.trans hdvd)

theorem inSubgroup_perfectResidual_ne_bot_of_lBar [Finite G]
    {A L : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hLp : Group.IsPerfect L) {n : ℕ} (hn : 0 < n)
    (he : Even n) (eB : lBar L ≃* SL3 n) (hC : IsTypeCOnBarSL A L) {φ : MulAut A}
    (hφL : φ ∈ starOf A L) (hφ2 : orderOf φ = 2) {b : G} (hbA : b ∈ A)
    (heq : L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) =
      L ⊓ Subgroup.centralizer ({b} : Set G)) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≠ ⊥ := by
  have hSL3B := ks222SL3Bar
  intro hbot
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hAL hbA
  have hsol : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    (inSubgroup_perfectResidual_eq_bot_iff _).mp hbot
  rw [← map_fixedSubgroupOf_normalizerMonoidHom hb] at hsol
  have hsolσ : Group.IsSolvable (fixedSubgroupOf (L.normalizerMonoidHom ⟨b, hb⟩)) :=
    Group.isSolvable_of_surjective
      (f := ((fixedSubgroupOf (L.normalizerMonoidHom ⟨b, hb⟩)).equivMapOfInjective
        _ L.subtype_injective).symm.toMonoidHom) (MulEquiv.surjective _)
  have hσ3 : L.normalizerMonoidHom ⟨b, hb⟩ ^ 3 = 1 := by
    have h1 : (⟨b, hb⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hAe.2 b hbA)
    rw [← map_pow, h1, map_one]
  have hsolτ := isSolvable_fixedSubgroupOf_thetaQuot hσ3 hsolσ
  by_cases htriv : ∀ z : lBar L, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) z = z
  ·
    have htop : fixedSubgroupOf (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩)) = ⊤ :=
      eq_top_iff.mpr fun z _ => htriv z
    rw [htop] at hsolτ
    have hsL : Group.IsSolvable (lBar L) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup (lBar L)) ≃* _).toMonoidHom)
        (MulEquiv.surjective _)
    have : Group.IsPerfect L := hLp
    have h1 : 1 < Nat.card (lBar L) := by
      rw [Nat.card_congr eB.toEquiv]
      calc 1 < 3 := by norm_num
        _ = Nat.card (Subgroup.center (SL3 n)) := (card_center_SL3 hn he).symm
        _ ≤ Nat.card (SL3 n) := Subgroup.card_le_card_group _
    have : Nontrivial (lBar L) := Finite.one_lt_card_iff_nontrivial.mp h1
    exact Group.IsPerfect.not_isSolvable (lBar L) hsL
  · push Not at htriv
    obtain ⟨⟨t, htN⟩, htL, htφ⟩ := hφL
    have htL' : t ∈ L := Subgroup.mem_subgroupOf.mp htL
    have htC : t ∈ L ⊓ Subgroup.centralizer (fixedInG A φ : Set G) := by
      refine ⟨htL', Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      have h1 : φ a = a := ha
      rw [← htφ] at h1
      have h2 : t * a * t⁻¹ = a := congrArg Subtype.val h1
      show (a : G) * t = t * a
      calc (a : G) * t = t * a * t⁻¹ * t := by rw [h2]
        _ = t * a := by group
    rw [heq] at htC
    have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.mp htC.2
    have hev := even_card_fixedSubgroupOf_thetaQuot hAe hAL hb htL' htN htb (htφ ▸ hφ2)
    have hτA : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) ∈ Sec4.autThetaQuot A L :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨b, hb, hbA, rfl⟩
    obtain ⟨e₁⟩ := hSL3B G L A n hn he ⟨eB⟩ hC _ hτA htriv hev
    have h3 := three_dvd_card_of_mulEquiv_projSL e₁
    rw [(inSubgroup_perfectResidual_eq_bot_iff _).mpr hsolτ, Subgroup.card_bot] at h3
    norm_num at h3

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
