module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofHess
import CFSG.RankThree.PartTwo.Sec10.Item101
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof1413Res7

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_inf_centralizer {Θ : Subgroup G} {r : G} (hr2 : r ^ 2 = 1)
    (hrΘ : r ∈ Subgroup.normalizer (Θ : Set G)) (h2 : 2 ∣ Nat.card Θ) :
    2 ∣ Nat.card ↥(Θ ⊓ Subgroup.centralizer ({r} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Subgroup.zpowers r with hR
  have hR2 : IsPGroup 2 R := by
    have h : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one hr2
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have : Subgroup.Normalizes R Θ := ⟨Subgroup.zpowers_le.mpr hrΘ⟩
  have hmod := hR2.card_modEq_card_fixedPoints (↥Θ)
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints R ↥Θ) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h2))
  have hcomm : ∀ x : MulAction.fixedPoints R ↥Θ,
      ((x : ↥Θ) : G) ∈ Subgroup.centralizer ({r} : Set G) := by
    intro x
    have h1 : (⟨r, Subgroup.mem_zpowers r⟩ : R) • (x : ↥Θ) = x := x.2 _
    have h2 : r * ((x : ↥Θ) : G) * r⁻¹ = ((x : ↥Θ) : G) := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((x : ↥Θ) : G) * r = r * ((x : ↥Θ) : G) * r⁻¹ * r := by rw [h2]
      _ = r * ((x : ↥Θ) : G) := by group
  have hfixed : ∀ y : ↥(Θ ⊓ Subgroup.centralizer ({r} : Set G)),
      (⟨(y : G), y.2.1⟩ : ↥Θ) ∈ MulAction.fixedPoints R ↥Θ := by
    intro y b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hyr : Commute (y : G) r := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, ← hk,
      (hyr.zpow_right k).symm.eq, mul_inv_cancel_right]
  have e : ↥(MulAction.fixedPoints R ↥Θ) ≃ ↥(Θ ⊓ Subgroup.centralizer ({r} : Set G)) :=
    { toFun := fun x => ⟨((x : ↥Θ) : G), (x : ↥Θ).2, hcomm x⟩
      invFun := fun y => ⟨⟨(y : G), y.2.1⟩, hfixed y⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [← Nat.card_congr e]
  exact hfix

@[expose] noncomputable def thetaPre (L : Subgroup G)
    (eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L) : Subgroup G :=
  ((Res8Hess.thetaC eb).comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map L.subtype

omit [Finite G] in
theorem mem_thetaPre_iff {L : Subgroup G} {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L} {x : G} :
    x ∈ thetaPre L eb ↔ ∃ hx : x ∈ L,
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨x, hx⟩ ∈ Res8Hess.thetaC eb := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem thetaPre_le (L : Subgroup G) (eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    thetaPre L eb ≤ L :=
  Subgroup.map_subtype_le _

theorem not_three_dvd_card_thetaPre (L : Subgroup G) (eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    ¬ 3 ∣ Nat.card (thetaPre L eb) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hθC3 : ¬ 3 ∣ Nat.card (Res8Hess.thetaC eb) :=
    (Sec6.theta_solvable_and_not_dvd
      (Subgroup.centralizer ({eb} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))).2
  intro h3
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(thetaPre L eb)) 3 h3
  obtain ⟨hyL, hyθ⟩ := mem_thetaPre_iff.mp y.2
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have hπy : π ⟨y, hyL⟩ = 1 := by
    have h1 : orderOf (π ⟨y, hyL⟩) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_mk, ← hy3, pow_orderOf_eq_one, OneMemClass.coe_one])
      rw [this, map_one]
    have h2 : orderOf (π ⟨y, hyL⟩) ∣ Nat.card (Res8Hess.thetaC eb) := by
      rw [show orderOf (π ⟨y, hyL⟩) = orderOf (⟨π ⟨y, hyL⟩, hyθ⟩ : ↥(Res8Hess.thetaC eb))
        from (Subgroup.orderOf_mk _ _).symm]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (Nat.card (Res8Hess.thetaC eb)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθC3
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hyθL : (y : G) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    ⟨⟨y, hyL⟩, (QuotientGroup.eq_one_iff _).mp hπy, rfl⟩
  have hθ3 := (Sec6.theta_solvable_and_not_dvd L).2
  have h4 := Subgroup.orderOf_dvd_natCard _ hyθL
  rw [hy3] at h4
  exact hθ3 h4

omit [Finite G] in
theorem two_dvd_card_thetaPre {L : Subgroup G} {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hz : ∃ z ∈ Res8Hess.thetaC eb, orderOf z = 2) : 2 ∣ Nat.card (thetaPre L eb) := by
  obtain ⟨z, hz, hz2⟩ := hz
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) z
  have hlΘ : (l : G) ∈ thetaPre L eb := mem_thetaPre_iff.mpr ⟨l.2, hz⟩
  have h1 : 2 ∣ orderOf l := hz2 ▸ orderOf_map_dvd _ l
  rw [← Subgroup.orderOf_coe] at h1
  exact h1.trans (Subgroup.orderOf_dvd_natCard _ hlΘ)

theorem le_normalizer_thetaPre {A L : Subgroup G} {a : G} (hD : Sec13Data G A a L)
    (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ L)) {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (heb : eb ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) :
    A ≤ Subgroup.normalizer (thetaPre L eb : Set G) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hLaC : L ≤ Subgroup.centralizer ({a} : Set G) := hD.le_centralizer
  have hcomA : ∀ z ∈ A ⊓ L, z * a = a * z := fun z hz => hD.commute hz.1 hD.mem_A
  obtain ⟨b, hb, rfl⟩ := heb
  intro y hy
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [hAa] at hy
  obtain ⟨i, d, hd, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers hcomA hy
  obtain ⟨hvL, hvθ⟩ := mem_thetaPre_iff.mp hv
  have hdvL : d * v * d⁻¹ ∈ L := mul_mem (mul_mem hd.2 hvL) (inv_mem hd.2)
  have hcomm : Commute (a ^ i) (d * v * d⁻¹) :=
    (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLaC hdvL)).symm i)
  have heq : a ^ i * d * v * (a ^ i * d)⁻¹ = d * v * d⁻¹ := by
    calc a ^ i * d * v * (a ^ i * d)⁻¹ = a ^ i * (d * v * d⁻¹) * (a ^ i)⁻¹ := by group
      _ = d * v * d⁻¹ := by rw [hcomm.eq, mul_inv_cancel_right]
  rw [SetLike.mem_coe, heq]
  refine mem_thetaPre_iff.mpr ⟨hdvL, ?_⟩
  have hbd : (b : G) * d = d * b :=
    hD.commute (Subgroup.mem_subgroupOf.mp hb) hd.1
  have hdC : π ⟨d, hd.2⟩ ∈
      Subgroup.centralizer ({π b} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbd.symm
  have hdN := Sec6.normalizer_le_normalizer_theta
    (Subgroup.centralizer ({π b} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (Subgroup.le_normalizer hdC)
  have h1 := (Subgroup.mem_normalizer_iff.mp hdN _).mp hvθ
  have h2 : π ⟨d * v * d⁻¹, hdvL⟩ = π ⟨d, hd.2⟩ * π ⟨v, hvL⟩ * (π ⟨d, hd.2⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h2]
  exact h1

theorem mem_normalizer_thetaPre {L : Subgroup G} {eb : ↥L ⧸ aschbacherSolvableCore 3 ↥L} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hfix : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) eb = eb) :
    x ∈ Subgroup.normalizer (thetaPre L eb : Set G) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set α := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hα
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  obtain ⟨hvL, hvθ⟩ := mem_thetaPre_iff.mp hv
  have hxvL : x * v * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvL
  refine mem_thetaPre_iff.mpr ⟨hxvL, ?_⟩
  have h1 : α (π ⟨v, hvL⟩) ∈ Res8Hess.thetaC eb := by
    have h2 := Res8Hess.thetaC_map_equiv α eb
    rw [hfix] at h2
    rw [← h2]
    exact ⟨_, hvθ, rfl⟩
  have h3 : α (π ⟨v, hvL⟩) = π ⟨x * v * x⁻¹, hxvL⟩ := by
    rw [hα, hπ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    rfl
  rw [h3] at h1
  exact h1

theorem mem_zpowers_of_types {A L T : Subgroup G} {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hp3 : 3 < p) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hEe : CFSG.Assembly.IsElemAbelian 3
      ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))))
    (hE9 : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9)
    (htr : ∀ y₀ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      y₀ ≠ 1 → ∀ y₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
        y₁ ≠ 1 → ∃ w ∈ Subgroup.normalizer
          (((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
            Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
              Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)), w * y₀ * w⁻¹ = y₁)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hT2 : IsPGroup 2 T) {a₁ a₂ : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (ha₁ : a₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    (ha₁1 : a₁ ≠ 1)
    (ha₂ : a₂ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    {s₁ s₂ : ↥L} (hs₁ : (s₁ : G) ∈ T) (hs₂ : (s₂ : G) ∈ T)
    (h₁ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₁ ∈ Res8Hess.thetaC a₁)
    (h₁1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₁ ≠ 1)
    (h₂ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₂ ∈ Res8Hess.thetaC a₂)
    (h₂1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s₂ ≠ 1) :
    a₂ ∈ Subgroup.zpowers a₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Ebar := (A.subgroupOf L).map π with hEbar
  set V := T ⊓ L with hV
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := le_normalizer_inf hAT hAL
  set W := (V.subgroupOf L).map π with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    refine Proof1413Res5.not_three_dvd_of_two hT2 (h3.trans ((Subgroup.card_map_dvd _ _).trans ?_))
    rw [show Nat.card (V.subgroupOf L) = Nat.card V from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hEW : Ebar ≤ Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    have hrV : (r : G) ∈ V := Subgroup.mem_subgroupOf.mp hr
    have h1 : (b : G) * r * (b : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV (Subgroup.mem_subgroupOf.mp hb)) _).mp hrV
    refine ⟨b * r * b⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨eb, heb, heb1, hWe⟩ := Res8Hess.le_thetaC_of_transitive he hp3 hiso hEe hE9 htr hW3 hEW
  have hmemW : ∀ s : ↥L, (s : G) ∈ T → π s ∈ W := fun s hs =>
    ⟨s, Subgroup.mem_subgroupOf.mpr ⟨hs, s.2⟩, rfl⟩
  have key : ∀ (a' : ↥L ⧸ aschbacherSolvableCore 3 ↥L) (s : ↥L), a' ∈ Ebar → (s : G) ∈ T →
      π s ∈ Res8Hess.thetaC a' → π s ≠ 1 → a' ∈ Subgroup.zpowers eb := by
    intro a' s ha' hs hsθ hs1
    have hsC : π s ∈ Subgroup.centralizer ({a'} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
      Res8Hess.inSubgroup_theta_le _ hsθ
    exact mem_zpowers_of_mem_thetaC he hiso hEe hE9 htr heb heb1 (hWe (hmemW s hs)) hs1 ha'
      (Subgroup.mem_centralizer_singleton_iff.mp hsC)
  have h1 := key a₁ s₁ ha₁ hs₁ h₁ h₁1
  have h2 := key a₂ s₂ ha₂ hs₂ h₂ h₂1
  have hord : ∀ y ∈ Ebar, y ≠ 1 → orderOf y = 3 := fun y hy hy1 =>
    orderOf_eq_prime (hEe.2 y hy) hy1
  have hle : Subgroup.zpowers a₁ ≤ Subgroup.zpowers eb := Subgroup.zpowers_le.mpr h1
  have heq : Subgroup.zpowers a₁ = Subgroup.zpowers eb :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hord a₁ ha₁ ha₁1, hord eb heb heb1])
  rw [heq]
  exact h2

theorem conj_mem_thetaC {A L : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.centralizer (A : Set G)) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    {ab : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hab : ab ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    {s : ↥L} (hs : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ∈ Res8Hess.thetaC ab)
    (hs1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ≠ 1) :
    ∃ s' : ↥L, (s' : G) = x * s * x⁻¹ ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s' ∈ Res8Hess.thetaC ab ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s' ≠ 1 := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set α := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hα
  have hxsL : x * (s : G) * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN s).mp s.2
  have h3 : α (π s) = π ⟨x * s * x⁻¹, hxsL⟩ := by
    rw [hα, hπ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    rfl
  refine ⟨⟨x * s * x⁻¹, hxsL⟩, rfl, ?_, ?_⟩
  · have h2 := Res8Hess.thetaC_map_equiv α ab
    rw [Proof1413Res6.aut_fix_of_mem hxA hxN ab hab] at h2
    rw [← h3, ← h2]
    exact ⟨_, hs, rfl⟩
  · rw [← h3]
    intro h
    exact hs1 (α.injective (h.trans (map_one α).symm))

theorem mem_scriptQ_of_point (h142 : Item142AllS14) {A L : Subgroup G} {a : G}
    (h' : Sec14Std G A a L) {V : Subgroup G}
    (hVH : V ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) (hV3 : ¬ 3 ∣ Nat.card V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) : V ∈ scriptQ A (lB A) := by
  have hD := h'.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G))
      A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({a} : Set G)) ∧ _ :=
    h142 G A a L h'
  obtain ⟨Q, hQ, hVQ⟩ := exists_le_mem_maxInvariantPiSubgroups
    ⟨hVH, (isPiSubgroup_piCompl_iff Nat.prime_three V).mpr hV3, hAV⟩
  exact mem_scriptQ_of_le (h142' Q hQ).1.1 hVQ hAV

end Proof1413Res7

end CFSG.RankThree.PartTwo.Sec14
