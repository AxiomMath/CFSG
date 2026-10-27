module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLFinal
import CFSG.RankThree.PartTwo.Sec4.T444.Step452Residual
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


section Certs


@[expose] def Item4_44_3Diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L : Subgroup G),
    Ctx4443 G A M H s → L ∈ thetaComponents 3 G → 3 ∣ Nat.card L → ¬ L ≤ M →
    inSubgroup perfectResidual H ≤ Subgroup.normalizer (L : Set G) →
    (inSubgroup perfectResidual H).map (starQuot G) ≤ L.map (starQuot G) ⊔
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) →
    ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) →
    s ∈ Subgroup.normalizer (L : Set G) →
    ¬ (Subgroup.zpowers s).map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) →
    Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      projSL 3 (GaloisField 2 2)) →
    ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤ L.map (starQuot G) →
    Concl4443 M H

end Certs

namespace Res4443

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCore_le_pCoreOf_L34 {I : Subgroup G}
    (eI : I ⧸ CFSG.pCore 2 I ≃* projSL 3 (GaloisField 2 2)) :
    I ⊓ CFSG.pPrimeCore 3 G ≤ CFSG.Open.pCoreOf 2 I := by
  set P := CFSG.pPrimeCore 3 G with hP
  set D : Subgroup I := P.subgroupOf I with hD
  have hDn : D.Normal := normal_subgroupOf
  set φ := QuotientGroup.mk' (CFSG.pCore 2 I) with hφ
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have : IsSimpleGroup (I ⧸ CFSG.pCore 2 I) := eI.isSimpleGroup
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3
    apply not_three_dvd_card_pPrimeCore (G := G)
    rw [← card_map_of_injective I.subtype_injective] at h3
    refine h3.trans (card_dvd_of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp hx
  have hDφ3 : ¬ 3 ∣ Nat.card (D.map φ) := fun h3 => hD3 (h3.trans (card_map_dvd D φ))
  have hle : D ≤ CFSG.pCore 2 I := by
    have : (D.map φ).Normal := hDn.map φ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map φ) with hbot | htop
    · rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    · exfalso
      apply hDφ3
      rw [htop, card_top, Nat.card_congr eI.toEquiv, KFacts.L34.card_projSL]
      norm_num
  intro x hx
  have hxD : (⟨x, hx.1⟩ : I) ∈ D := mem_subgroupOf.mpr hx.2
  have := hle hxD
  rw [Sec18.mem_pCore_iff_mem_pCoreOf] at this
  exact this

theorem nonempty_quotient_map_equiv_L34 {I : Subgroup G}
    (eI : I ⧸ CFSG.pCore 2 I ≃* projSL 3 (GaloisField 2 2))
    [((CFSG.Open.pCoreOf 2 I).map (starQuot G)).subgroupOf (I.map (starQuot G)) |>.Normal] :
    Nonempty (↥(I.map (starQuot G)) ⧸
      ((CFSG.Open.pCoreOf 2 I).map (starQuot G)).subgroupOf (I.map (starQuot G)) ≃*
        projSL 3 (GaloisField 2 2)) := by
  set π := starQuot G with hπ
  set T := (CFSG.Open.pCoreOf 2 I).map π with hT
  set ψ : I →* ↥(I.map π) ⧸ T.subgroupOf (I.map π) :=
    (QuotientGroup.mk' _).comp (π.subgroupMap I) with hψ
  have hsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective I)
  have hker : ψ.ker = CFSG.pCore 2 I := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, MonoidHom.subgroupMap_apply_coe,
      Sec18.mem_pCore_iff_mem_pCoreOf]
    constructor
    · rintro ⟨t, ht, hte⟩
      rw [hπ, starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hte
      have h1 : t⁻¹ * x ∈ I ⊓ CFSG.pPrimeCore 3 G :=
        ⟨I.mul_mem (I.inv_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 I ht)) x.2, hte⟩
      have h2 := inf_pPrimeCore_le_pCoreOf_L34 eI h1
      have h3 : (x : G) = t * (t⁻¹ * x) := by group
      rw [h3]
      exact mul_mem ht h2
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans eI)⟩

theorem le_of_forall_pow_mem_L34 {I N : Subgroup G} (hIp : Group.IsPerfect I)
    (eI : I ⧸ CFSG.pCore 2 I ≃* projSL 3 (GaloisField 2 2))
    (hNI : N ≤ I) (hIN : I ≤ normalizer (N : Set G))
    (hpow : ∀ x ∈ I, ∃ m : ℕ, ¬ 3 ∣ m ∧ x ^ m ∈ N) : I ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' : Subgroup I := N.subgroupOf I with hN'
  have hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNI).mpr hIN
  set φ := QuotientGroup.mk' (CFSG.pCore 2 I) with hφ
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have : IsSimpleGroup (I ⧸ CFSG.pCore 2 I) := eI.isSimpleGroup
  have hN'φ : (N'.map φ).Normal := hN'n.map φ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map φ) with hbot | htop
  ·
    exfalso
    have h3 : 3 ∣ Nat.card (I ⧸ CFSG.pCore 2 I) := by
      rw [Nat.card_congr eI.toEquiv, KFacts.L34.card_projSL]
      norm_num
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 I) z
    obtain ⟨m, hm3, hxm⟩ := hpow x x.2
    have hm : (φ x) ^ m = 1 := by
      have h1 : φ (x ^ m) ∈ N'.map φ :=
        mem_map_of_mem φ (mem_subgroupOf.mpr (by simpa using hxm))
      rw [hbot, mem_bot] at h1
      rw [← map_pow]
      exact h1
    exact hm3 (hz ▸ orderOf_dvd_of_pow_eq_one hm)
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp (CFSG.pCore 2 I).subtype) := by
      intro qq
      obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective N' qq
      have hi : φ i ∈ N'.map φ := htop ▸ mem_top _
      obtain ⟨d, hd, hdi⟩ := hi
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdi
      refine ⟨⟨d⁻¹ * i, hdi⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      change (d⁻¹ * i)⁻¹ * i ∈ N'
      rw [show (d⁻¹ * i)⁻¹ * i = i⁻¹ * d * i by group]
      have := hN'n.conj_mem d hd i⁻¹
      simpa [mul_assoc] using this
    have hTs : Group.IsNilpotent (CFSG.pCore 2 I) := CFSG.pCore_isPGroup.isNilpotent
    have hsolv : Group.IsSolvable (I ⧸ N') := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (I ⧸ N') :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N')
    have hsub : Subsingleton (I ⧸ N') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable _ hsolv
    intro x hx
    have h1 : (QuotientGroup.mk' N' ⟨x, hx⟩ : I ⧸ N') = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_subgroupOf.mp h1

theorem le_of_map_starQuot_le_L34 {I L : Subgroup G} (hIp : Group.IsPerfect I)
    (eI : I ⧸ CFSG.pCore 2 I ≃* projSL 3 (GaloisField 2 2))
    (hIL : I ≤ normalizer (L : Set G)) (hle : I.map (starQuot G) ≤ L.map (starQuot G)) :
    I ≤ L := by
  have hIN : I ≤ normalizer ((I ⊓ L : Subgroup G) : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hx, hIL hx⟩
  refine (le_of_forall_pow_mem_L34 hIp eI inf_le_left hIN fun x hx => ?_).trans inf_le_right
  obtain ⟨l, hl, hlx⟩ := hle (mem_map_of_mem _ hx)
  rw [starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
  set p := l⁻¹ * x with hp
  have hpN : p ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (le_normalizer hl)) (hIL hx)
  refine ⟨orderOf p, not_three_dvd_orderOf_of_mem hlx not_three_dvd_card_pPrimeCore,
    pow_mem hx _, ?_⟩
  have h1 := Item4443SL.mul_pow_mul_inv_mem hl hpN (orderOf p)
  rwa [pow_orderOf_eq_one, inv_one, mul_one, show l * p = x by rw [hp]; group] at h1

section Certs


theorem nonempty_equiv_of_concl4442 {A M H : Subgroup G} {s : G} (hc : Concl4442 A M H s) :
    Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        projSL 3 (GaloisField 2 2)) ∨
      Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsS, -, -, hsH, X, hXn, hX, hXt, -⟩ := hc
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  set Lb : Subgroup (H ⧸ Q) := (perfectResidual H).map π with hLb
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQ, hRdef, CFSG.Open.pCoreOf]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [Subtype.ext hyx] at hy
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ X) := by
    have h1 := ht2.map (QuotientGroup.mk' X)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' X) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' X)
        (QuotientGroup.mk'_surjective X), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self X), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ X) := by
    have := hq2.isNilpotent
    infer_instance
  have hLbeq : ⁅⁅X, X⁆, ⁅X, X⁆⁆ = ⁅X, X⁆ → Lb = ⁅X, X⁆ := fun hp => by
    rw [hLb, Sec18.map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
    exact Sec18.perfectResidual_eq_commutator hqs hp
  set φ : L →* H ⧸ Q := π.comp (Subgroup.inclusion hLH) with hφ
  have hrange : φ.range = Lb := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Subgroup.inclusion hLH x, ?_, rfl⟩
      obtain ⟨z, hz, hzx⟩ := x.2
      have : Subgroup.inclusion hLH x = z := Subtype.ext hzx.symm
      rw [this]
      exact hz
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), ⟨x, hx, rfl⟩⟩, rfl⟩
  have hker : φ.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, ?_⟩
      have himg : φ.ker.map L.subtype ≤ R := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hmemR _).mp hx
      exact (hR2.to_le himg).of_equiv (φ.ker.equivMapOfInjective _ L.subtype_injective).symm
    · intro x hx
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hmemR]
      have hO : CFSG.Open.pCoreOf 2 L ≤ R :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
          ((Sec18.le_normalizer_inSubgroup_perfectResidual H).trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      exact hO ((Sec18.mem_pCore_iff_mem_pCoreOf x).mp hx)
  have hLiso : L ⧸ CFSG.pCore 2 L ≃* Lb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
  ·
    obtain ⟨e⟩ := he
    set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
      (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
    have hcomm := KFacts.KS18.commutator_eq_range e'
    have hperf : Group.IsPerfect (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 2)) := KFacts.KS18.isPerfect_projectiveSL _
    have hrp : ⁅(KFacts.KS18.inrY e').range, (KFacts.KS18.inrY e').range⁆ =
        (KFacts.KS18.inrY e').range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have hLbr : Lb = (KFacts.KS18.inrY e').range := by
      rw [hLbeq (by rw [hcomm, hrp]), hcomm]
    set ι := MonoidHom.ofInjective (KFacts.KS18.inrY_injective e') with hι
    exact Or.inl ⟨hLiso.trans ((MulEquiv.subgroupCongr hLbr).trans
      (ι.symm.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm))⟩
  ·
    have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
    have hXX : ⁅X, X⁆ = V.map X.subtype := by
      rw [← Subgroup.map_subtype_commutator, hcomm]
    have hVp : Group.IsPerfect V := by
      have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
        CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
      exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVmp : ⁅V.map X.subtype, V.map X.subtype⁆ = V.map X.subtype := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
        Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hLbV : Lb = V.map X.subtype := by
      rw [hLbeq (by rw [hXX, hVmp]), hXX]
    exact Or.inr ⟨hLiso.trans ((MulEquiv.subgroupCongr hLbV).trans
      ((V.equivMapOfInjective _ X.subtype_injective).symm.trans eV))⟩

end Certs

theorem eq_of_le_of_quotient_L34 {Y : Type} [Group Y] [Finite Y] {I L T : Subgroup Y}
    (hIL : I ≤ L) (hLp : Group.IsPerfect L) [(T.subgroupOf I).Normal]
    (hT2 : IsPGroup 2 T) (eI : I ⧸ T.subgroupOf I ≃* projSL 3 (GaloisField 2 2))
    (hLcard : Nat.card L = 20160 * Nat.card (L ⊓ centralizer (L : Set Y) : Subgroup Y))
    (hZL : Nat.card (L ⊓ centralizer (L : Set Y) : Subgroup Y) ∣ 3) : I = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := L ⊓ centralizer (L : Set Y) with hC
  set T' := T.subgroupOf I with hT'
  have hmul := card_eq_card_quotient_mul_card_subgroup T'
  rw [Nat.card_congr eI.toEquiv, KFacts.L34.card_projSL] at hmul
  have hT'2 : IsPGroup 2 T' := hT2.comap_subtype
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT'2
  have hdvd : Nat.card I ∣ Nat.card L := Subgroup.card_dvd_of_le hIL
  rw [hmul, hk, hLcard] at hdvd
  have h2k : 2 ^ k ∣ Nat.card C := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans (h2k.trans hZL)
    omega
  rw [hk, hk0, pow_zero, mul_one] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hZL with h1 | h3
  · exact Subgroup.eq_of_le_of_card_ge hIL (by rw [hLcard, h1, hmul])
  · exfalso
    have hT'bot : T' = ⊥ := by
      rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
    have hcen : ∀ x ∈ I, (∀ y ∈ I, y * x = x * y) → x = 1 := by
      intro x hx hxc
      set q := QuotientGroup.mk' T' with hq
      have hz : ∀ w : projSL 3 (GaloisField 2 2), w * eI (q ⟨x, hx⟩) = eI (q ⟨x, hx⟩) * w := by
        intro w
        obtain ⟨u, rfl⟩ := eI.surjective w
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T' u
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
        congr 2
        exact Subtype.ext (hxc y y.2)
      have h1 : eI (q ⟨x, hx⟩) ∈ center (projSL 3 (GaloisField 2 2)) :=
        mem_center_iff.mpr hz
      rw [center_projSL_eq_bot, mem_bot, MulEquiv.map_eq_one_iff, hq, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hT'bot, mem_bot] at h1
      exact congrArg Subtype.val h1
    have hCI : I ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hcen x hx.1 fun y hy => mem_centralizer_iff.mp hx.2.2 y (hIL hy)
    have hIC : I ≤ normalizer (C : Set Y) := by
      intro i hi
      rw [mem_normalizer_iff]
      intro c
      constructor
      · intro hc
        have h1 : i * c = c * i := mem_centralizer_iff.mp hc.2 i (hIL hi)
        rw [h1, mul_inv_cancel_right]
        exact hc
      · intro hc
        have h1 : i * (i * c * i⁻¹) = (i * c * i⁻¹) * i :=
          mem_centralizer_iff.mp hc.2 i (hIL hi)
        have h2 : c = i * c * i⁻¹ := by
          have h3 : i * (i * c * i⁻¹) = i * c := by rw [h1]; group
          exact (mul_left_cancel h3).symm
        rw [h2]
        exact hc
    have hcard := Item4443SL.card_sup_mul_card_inf hIC
    rw [hCI, card_bot, mul_one, hmul, h3] at hcard
    have hsupL : I ⊔ C = L := Subgroup.eq_of_le_of_card_ge (sup_le hIL inf_le_left)
      (by rw [hcard, hLcard, h3])
    have hLI : L ≤ I := by
      have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLp
      rw [← hLL, ← hsupL, Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I C hIC] at hx hy
      obtain ⟨i, hi, c, hc, rfl⟩ := hx
      obtain ⟨i', hi', c', hc', rfl⟩ := hy
      have e1 : c * i' = i' * c := (mem_centralizer_iff.mp hc.2 i' (hIL hi')).symm
      have e2 : c * c' * c⁻¹ = c' := by
        rw [(mem_centralizer_iff.mp hc.2 c' hc'.1).symm, mul_inv_cancel_right]
      have e3 : c' * i⁻¹ = i⁻¹ * c' :=
        (mem_centralizer_iff.mp hc'.2 i⁻¹ (L.inv_mem (hIL hi))).symm
      have heq : i * c * (i' * c') * (i * c)⁻¹ * (i' * c')⁻¹ = i * i' * i⁻¹ * i'⁻¹ := by
        calc i * c * (i' * c') * (i * c)⁻¹ * (i' * c')⁻¹
            = i * (c * i') * c' * c⁻¹ * i⁻¹ * c'⁻¹ * i'⁻¹ := by group
          _ = i * (i' * c) * c' * c⁻¹ * i⁻¹ * c'⁻¹ * i'⁻¹ := by rw [e1]
          _ = i * i' * (c * c' * c⁻¹) * i⁻¹ * c'⁻¹ * i'⁻¹ := by group
          _ = i * i' * c' * i⁻¹ * c'⁻¹ * i'⁻¹ := by rw [e2]
          _ = i * i' * (c' * i⁻¹) * c'⁻¹ * i'⁻¹ := by group
          _ = i * i' * (i⁻¹ * c') * c'⁻¹ * i'⁻¹ := by rw [e3]
          _ = i * i' * i⁻¹ * i'⁻¹ := by group
      rw [heq]
      exact I.mul_mem (I.mul_mem (I.mul_mem hi hi') (I.inv_mem hi)) (I.inv_mem hi')
    have hle := Subgroup.card_le_of_le hLI
    rw [hLcard, h3, hmul] at hle
    norm_num at hle

section Certs


theorem item4_44_3_of_inputs (h434 : Item4_34Sec) (h45 : Item4_5) (h442 : Item4_44_2)
    (hSL : Item4_44_3SL) (hSz : KFacts.KPSz)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hres : Item4_52Residual) (hmult : KFacts.L34CenterThreePrimeTwo) (hD : Item4_44_3Diag) :
    Item4_44_3 := by
  intro G _ _ A M h H hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := Item4443SL.exists_ctx4443 h442 h hH
  set I := inSubgroup perfectResidual H with hI
  set π := starQuot G with hπ
  rcases nonempty_equiv_of_concl4442 hs.concl4442 with heI | hSLI
  swap
  · obtain ⟨L, hL, hLM, hi⟩ := hSL G A M h H hH hSLI
    exact ⟨L, hL, hLM, Or.inl hi⟩
  obtain ⟨eI⟩ := heI
  obtain ⟨L, hL, h3, hLM, hIL, hIC, hIs, hsL, hss⟩ :=
    Item4443SL.Ctx4443.exists_mem_thetaComponents_of_commutator_eq hSz hS h45 hs
      (Item4443SL.Ctx4443.commutator_A_eq_general hs)
      (Item4443SL.Ctx4443.isQuasisimple_quotient hs)
  by_cases hIsL : I.map π ≤ L.map π
  swap
  · exact hD G A M H s L hs hL h3 hLM hIL hIC hIs hsL hss ⟨eI⟩ hIsL
  have hIp : ⁅I, I⁆ = I := Sec18.commutator_inSubgroup_perfectResidual H
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map π) :=
    Item4443SL.Ctx4443.isZ3L34OrHeisSL34_map h434 h45 hs hL hLM hsL hss
  have hILe : I ≤ L := le_of_map_starQuot_le_L34 (Subgroup.isPerfect_iff.mpr hIp) eI hIL hIsL
  have hLq := (isComponent_map_starQuot hL h3).1
  have hAL' : A.map π ≤ normalizer (L.map π : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (map_mono hAL).trans (le_normalizer_map π)
  obtain ⟨hshape, -, -⟩ := Item4443SL.shape_sup (Item4443SL.isE27_map_starQuot h.isE27) hAL'
    hLq.1 (by rw [← Subgroup.map_sup]; exact hZ)
  obtain ⟨hLcard, hZL⟩ := Item4443SL.card_of_shape hshape
  have hTn := Item4443SL.map_pCoreOf_subgroupOf_normal (G := G) I
  obtain ⟨eIs⟩ := nonempty_quotient_map_equiv_L34 eI
  have hIsEq : I.map π = L.map π :=
    eq_of_le_of_quotient_L34 hIsL hLq.1
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).map π) eIs hLcard hZL
  obtain ⟨K, _, hKs, h9, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL h.isE27.isPGroup hL h3 hAL hZ
  have : Group.IsPerfect L := hL.1
  have hq := quasisimple_of_residual hres (sectionFourHyp_subgroup h.sectionFourHyp L) hKs h9 ψ
  have hθ2 := isPGroup_two_aschbacherSolvableCore hmult hq ψ
  have hθO : aschbacherSolvableCore 3 L ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, hθ2⟩
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  refine ⟨L, ⟨hL.1, hL.2.1, hq⟩, hLM,
    Or.inl (le_antisymm (fun l hl => ?_) (sup_le hILe (map_subtype_le _)))⟩
  have hl' : π l ∈ I.map π := hIsEq ▸ mem_map_of_mem π hl
  obtain ⟨x, hx, hxl⟩ := hl'
  rw [hπ, starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxl
  have hmem : x⁻¹ * l ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨L.mul_mem (L.inv_mem (hILe hx)) hl, hxl⟩
  rw [hθL] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have h1 : l = x * (x⁻¹ * l) := by group
  rw [h1, ← hte]
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨t, hθO ht, rfl⟩)

end Certs

theorem item4_44_3_of
    (h434 : Item4_34Sec) (h45 : Item4_5) (hD : Item4_44_3Diag) : Item4_44_3 :=
  item4_44_3_of_inputs h434 h45 (rank3II_4_44_2_of h45 h434) (Item4443SL.item4_44_3SL_of h434 h45)
    KFacts.kpSz PartOne.TCB.schreierFor_inCatalog_holds rank3II_4_52_residual
    KFacts.l34CenterThreePrimeTwo hD

end Res4443

end CFSG.RankThree.PartTwo.Sec4
