module

public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofPL
import CFSG.LocalAnalysis.ComponentInitial.OddCoreFreeInvolutionLayer
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.GH74.GLS.Stage2.Bender.Thm1.QpExists

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof1418Res3

open Subgroup
open scoped commutatorElement

@[expose] def ActsTrivOnLayer3 {G : Type*} [Group G] (X R : Subgroup G) : Prop :=
  (R.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) ≤
    centralizer (CFSG.layer (↥X ⧸ CFSG.pPrimeCore 3 ↥X) : Set (↥X ⧸ CFSG.pPrimeCore 3 ↥X))

theorem actsTrivOnLayer3_of_layer_eq_bot {G : Type*} [Group G] {X R : Subgroup G}
    (h : CFSG.layer (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = ⊥) : ActsTrivOnLayer3 X R := by
  intro z _
  rw [h]
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]

theorem eq_one_of_two_pow_of_mem {Q : Type*} [Group Q] {P : Subgroup Q} (hP : IsPGroup 3 P)
    {r : Q} {k : ℕ} (hr : r ^ 2 ^ k = 1) (hrP : r ∈ P) : r = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨r, hrP⟩
  have hj' : r ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hr
  have h2 : orderOf r ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hcop : Nat.Coprime (2 ^ k) (3 ^ j) := Nat.Coprime.pow k j (by norm_num)
  have h := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rwa [orderOf_eq_one_iff] at h

theorem eq_one_of_mem_centralizer_layer {Q : Type*} [Group Q] [Finite Q]
    (hcore : CFSG.pPrimeCore 3 Q = ⊥) {r : Q} {k : ℕ} (hr : r ^ 2 ^ k = 1)
    (hrE : r ∈ centralizer (CFSG.layer Q : Set Q))
    (hrP : r ∈ centralizer (CFSG.pCore 3 Q : Set Q)) : r = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : CFSG.fittingSubgroup Q ≤ CFSG.pCore 3 Q :=
    CFSG.LocalAnalysis.ComponentInitial.fittingSubgroup_le_pCore_of_pPrimeCore_eq_bot hcore
  have hrF : r ∈ centralizer (CFSG.generalizedFitting Q : Set Q) := by
    have hle : CFSG.generalizedFitting Q ≤ centralizer ({r} : Set Q) := by
      refine sup_le (fun f hf => ?_) (fun e he => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp hrP f (hF hf)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp hrE e he
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hle hh)
  set C := centralizer (CFSG.generalizedFitting Q : Set Q) with hCdef
  have hCF : C ≤ CFSG.generalizedFitting Q := CFSG.centralizer_generalizedFitting_le Q
  have : (CFSG.generalizedFitting Q).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Q)).2
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCcomm : IsMulCommutative C :=
    ⟨⟨fun x y => Subtype.ext (mem_centralizer_iff.mp y.2 x (hCF x.2))⟩⟩
  let _ : CommGroup C := IsMulCommutative.instCommGroup
  have hCnil : Group.IsNilpotent C := inferInstance
  have hCFit : C ≤ CFSG.fittingSubgroup Q :=
    le_sSup (show C ∈ {N : Subgroup Q | N.Normal ∧ Group.IsNilpotent N} from ⟨hCn, hCnil⟩)
  exact eq_one_of_two_pow_of_mem CFSG.pCore_isPGroup hr (hF (hCFit hrF))

theorem mem_map_of_commute {G : Type*} [Group G] [Finite G] {X A : Subgroup G} (hAX : A ≤ X)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (hAmax : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A)
    {y : ↥X} (hy3 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X) y) ^ 3 = 1)
    (hyA : ∀ ab ∈ (A.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)),
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X) y * ab = ab * QuotientGroup.mk' _ y) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X) y ∈
      (A.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπdef
  set YX : Subgroup ↥X := (zpowers (π y)).comap π with hYXdef
  set YG : Subgroup G := YX.map X.subtype with hYGdef
  have hYX : YG ≤ X := Subgroup.map_subtype_le _
  have hyYX : y ∈ YX := mem_comap.mpr (mem_zpowers _)
  have hcommA : ∀ a ∈ A, ∀ (haX : a ∈ X), ∀ w ∈ zpowers (π y), π ⟨a, haX⟩ * w = w * π ⟨a, haX⟩ := by
    intro a ha haX w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have h := hyA (π ⟨a, haX⟩) ⟨⟨a, haX⟩, mem_subgroupOf.mpr ha, rfl⟩
    exact ((Commute.zpow_left h k).symm).eq
  let hom : ↥YG →* (↥X ⧸ N) := π.comp (Subgroup.inclusion hYX)
  have hconj : ∀ (a : G) (ha : a ∈ A), ∀ x ∈ YG, a * x * a⁻¹ ∈ YG ∧
      ∀ (hx : x ∈ X), π ⟨a * x * a⁻¹, mul_mem (mul_mem (hAX ha) hx) (inv_mem (hAX ha))⟩ =
        π ⟨x, hx⟩ := by
    intro a ha x hx
    have haX := hAX ha
    obtain ⟨x', hx', rfl⟩ := hx
    have hmem : π x' ∈ zpowers (π y) := mem_comap.mp hx'
    have hc := hcommA a ha haX _ hmem
    have hval : π (⟨a, haX⟩ * x' * ⟨a, haX⟩⁻¹) = π x' := by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    refine ⟨⟨⟨a, haX⟩ * x' * ⟨a, haX⟩⁻¹, mem_comap.mpr (hval ▸ hmem), rfl⟩, fun _ => ?_⟩
    exact hval
  have hAY : A ≤ normalizer (YG : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun x hx => (hconj a ha x hx).1
  have hA3' : IsPGroup 3 A := isPGroup_three_of_exp hA3
  have hker : ¬ 3 ∣ Nat.card hom.ker := by
    have hle : (hom.ker).map (Subgroup.inclusion hYX) ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hcard : Nat.card hom.ker ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYX)]
      exact Subgroup.card_dvd_of_le hle
    exact fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      CFSG.pPrimeCore_coprime_card (h.trans hcard)
  have htriv : ∀ (a : A) (x : YG), hom ⟨(a : G) * x * (a : G)⁻¹,
      Subgroup.le_normalizer_iff.mp hAY a a.2 x x.2⟩ = hom x := by
    rintro ⟨a, ha⟩ ⟨x, hx⟩
    exact (hconj a ha x hx).2 (hYX hx)
  have hyYG : (y : G) ∈ YG := ⟨y, hyYX, rfl⟩
  open CFSG.RankThreeEvenClassification.Helpers in
  obtain ⟨y', hy'A, hy'⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three A YG hA3' hAY hom hker htriv ⟨y, hyYG⟩
  set y'X : ↥X := Subgroup.inclusion hYX y' with hy'Xdef
  have hπy' : π y'X = π y := hy'
  set n := Nat.card N with hndef
  have hn3 : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    CFSG.pPrimeCore_coprime_card
  have hy'3 : y'X ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change π (y'X ^ 3) = 1
    rw [map_pow, hπy']
    exact hy3
  have hy'n : (y'X ^ 3) ^ n = 1 := by
    have h := pow_card_eq_one' (G := N) (x := ⟨y'X ^ 3, hy'3⟩)
    exact congrArg Subtype.val h
  have hy''3 : ((y' : G) ^ n) ^ 3 = 1 := by
    have h := congrArg Subtype.val hy'n
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h
    rw [← pow_mul, mul_comm, pow_mul]
    have e : ((y'X : ↥X) : G) = (y' : G) := rfl
    rw [← e]
    exact h
  have hy''A : (y' : G) ^ n ∈ A := by
    refine hAmax _ hy''3 fun a ha => ?_
    have hc := mem_centralizer_iff.mp (pow_mem hy'A n) a ha
    exact hc
  have hmemA : π (y'X ^ n) ∈ (A.subgroupOf X).map π := by
    refine ⟨y'X ^ n, mem_subgroupOf.mpr ?_, rfl⟩
    have e : ((y'X : ↥X) : G) = (y' : G) := rfl
    rw [Subgroup.coe_pow, e]
    exact hy''A
  rw [map_pow, hπy'] at hmemA
  have hnn : n * n % 3 = 1 := by
    have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h1 with h | h <;> simp [Nat.mul_mod, h]
  have hpow : π y = (π y ^ n) ^ n := by
    rw [← pow_mul]
    have e : n * n = 3 * (n * n / 3) + 1 := by omega
    rw [e, pow_add, pow_mul, hy3, one_pow, one_mul, pow_one]
  rw [hpow]
  exact pow_mem hmemA n

theorem le_pPrimeCoreOf_of_centralizes_layer {G : Type} [Group G] [Finite G]
    {A E R : Subgroup G} {b : G} (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAmax : ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A)
    (hEA : E ≤ A) (hbA : b ∈ A) (hAEb : A = E ⊔ zpowers b)
    (hRE : R ≤ centralizer (E : Set G)) (hR2 : IsPGroup 2 R)
    (hbR : b ∈ normalizer (R : Set G)) (hRb : ⁅R, zpowers b⁆ = R)
    (hlayer : ActsTrivOnLayer3 (centralizer (E : Set G)) R) :
    R ≤ CFSG.GH74.GLS.pPrimeCoreOf 3 (centralizer (E : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer (E : Set G) with hXdef
  set N := CFSG.pPrimeCore 3 ↥X with hNdef
  set π := QuotientGroup.mk' N with hπdef
  have hAX : A ≤ X := fun a ha => mem_centralizer_iff.mpr fun e he => hAab e (hEA he) a ha
  have hRX : R ≤ X := hRE
  have hbX : b ∈ X := hAX hbA
  have hEc : ∀ e ∈ E, ∀ (heX : e ∈ X) (x : ↥X), (⟨e, heX⟩ : ↥X) * x = x * ⟨e, heX⟩ := by
    intro e he heX x
    exact Subtype.ext (mem_centralizer_iff.mp x.2 e he)
  set Rb := (R.subgroupOf X).map π with hRbdef
  set Ab := (A.subgroupOf X).map π with hAbdef
  set Pb := CFSG.pCore 3 (↥X ⧸ N) with hPbdef
  have hPb3 : IsPGroup 3 Pb := CFSG.pCore_isPGroup
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hRb2 : IsPGroup 2 Rb :=
    (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm).map π
  have hc3 : π ⟨b, hbX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hA3 b hbA)
    rw [this, map_one]
  have hAR : A ≤ normalizer (R : Set G) := by
    rw [hAEb]
    refine sup_le ?_ (zpowers_le.mpr hbR)
    intro e he
    refine mem_normalizer_of_conj_mem fun r hr => ?_
    have h := mem_centralizer_iff.mp (hRE hr) e he
    rw [h, mul_inv_cancel_right]
    exact hr
  have hAbR : ∀ a ∈ Ab, a ∈ normalizer (Rb : Set (↥X ⧸ N)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨r, hr, rfl⟩ := hz
    refine ⟨a * r * a⁻¹, mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
    have := (mem_normalizer_iff.mp (hAR (mem_subgroupOf.mp ha)) r).mp (mem_subgroupOf.mp hr)
    simpa using this
  have hcAb : π ⟨b, hbX⟩ ∈ Ab := ⟨⟨b, hbX⟩, mem_subgroupOf.mpr hbA, rfl⟩
  have hcR : π ⟨b, hbX⟩ ∈ normalizer (Rb : Set (↥X ⧸ N)) := hAbR _ hcAb
  have hgen : ⁅Rb, zpowers (π ⟨b, hbX⟩)⁆ = Rb := by
    have hX : ⁅R.subgroupOf X, zpowers (⟨b, hbX⟩ : ↥X)⁆ = R.subgroupOf X := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hRX]
      exact hRb
    calc ⁅Rb, zpowers (π ⟨b, hbX⟩)⁆
        = (⁅R.subgroupOf X, zpowers (⟨b, hbX⟩ : ↥X)⁆).map π := by
          rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      _ = Rb := by rw [hX]
  by_contra hRN
  have hRb1 : Rb ≠ ⊥ := by
    intro h
    apply hRN
    intro r hr
    have hmem : π ⟨r, hRX hr⟩ ∈ Rb := ⟨⟨r, hRX hr⟩, mem_subgroupOf.mpr hr, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ⟨⟨r, hRX hr⟩, (QuotientGroup.eq_one_iff _).mp hmem, rfl⟩
  have hfaith : ∀ r ∈ Rb, r ∈ centralizer (Pb : Set (↥X ⧸ N)) → r = 1 := by
    intro r hr hrP
    obtain ⟨k, hk⟩ := hRb2 ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact eq_one_of_mem_centralizer_layer (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) hk'
      (hlayer hr) hrP
  have h2 : 2 ∣ Nat.card Rb := by
    obtain ⟨k, hk⟩ := hRb2.exists_card_eq
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      apply hRb1
      rw [← Subgroup.card_eq_one, hk, h0, pow_zero]
    · rw [hk]
      exact dvd_pow_self 2 hpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Rb) 2 h2
  have hz2 : orderOf (z : ↥X ⧸ N) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hzP : ¬ Pb ≤ centralizer ({(z : ↥X ⧸ N)} : Set (↥X ⧸ N)) := by
    intro h
    have hz1 := hfaith z z.2 (mem_centralizer_iff.mpr fun q hq =>
      mem_centralizer_singleton_iff.mp (h hq))
    rw [hz1, orderOf_one] at hz2
    omega
  have hzN : (z : ↥X ⧸ N) ∈ normalizer (Pb : Set (↥X ⧸ N)) := by
    rw [normalizer_eq_top_iff.mpr hPbn]
    exact mem_top _
  obtain ⟨Q₀, hQ₀P, hQ₀char, hQ₀exp, -, -, hQ₀z⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.qp_exists_thm (↥X ⧸ N) z 3 Pb Nat.prime_three
      (by norm_num) hz2 hPb3 hzN hzP
  have hnormQ : ∀ g : ↥X ⧸ N, g ∈ normalizer (Q₀ : Set (↥X ⧸ N)) := by
    intro g
    have := hQ₀char
    have hH : (⊤ : Subgroup (↥X ⧸ N)) ≤ normalizer (Pb : Set (↥X ⧸ N)) := by
      rw [normalizer_eq_top_iff.mpr hPbn]
    have h := CFSG.GH74.GLS.Stage2.Bender.Thm1.le_normalizer_of_characteristic hH
      (Q₀.subgroupOf Pb)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ₀P] at h
    exact h (mem_top g)
  have hfix : ∀ x ∈ Q₀, x * π ⟨b, hbX⟩ = π ⟨b, hbX⟩ * x → ∀ r ∈ Rb, x * r = r * x := by
    intro x hx hxc r hr
    have hxP : x ∈ Pb := hQ₀P hx
    have hx3 : x ^ 3 = 1 := hQ₀exp x hx
    obtain ⟨y, hy⟩ : ∃ y, π y = x := QuotientGroup.mk'_surjective N x
    rw [← hy] at hx3 hxc hxP ⊢
    have hxA : ∀ ab ∈ Ab, π y * ab = ab * π y := by
      have hAS : A ≤ ((centralizer ({π y} : Set (↥X ⧸ N))).comap π).map X.subtype := by
        rw [hAEb]
        refine sup_le (fun e he => ⟨⟨e, hAX (hEA he)⟩, ?_, rfl⟩)
          (zpowers_le.mpr ⟨⟨b, hbX⟩, ?_, rfl⟩)
        · rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
            hEc e he _ y]
        · rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
          exact hxc.symm
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨a', ha', ha'eq⟩ := hAS (mem_subgroupOf.mp ha)
      have : a' = a := Subtype.ext ha'eq
      subst this
      exact (mem_centralizer_singleton_iff.mp (mem_comap.mp ha')).symm
    have hxAb : π y ∈ Ab := mem_map_of_commute hAX hA3 hAmax hx3 hxA
    have hxR := hAbR _ hxAb
    have h1 : ⁅π y, r⁆ ∈ Rb := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp hxR r).mp hr) (inv_mem hr)
    have h2' : ⁅π y, r⁆ ∈ Pb := by
      have hr' : r * (π y)⁻¹ * r⁻¹ ∈ Pb := hPbn.conj_mem _ (inv_mem hxP) r
      rw [commutatorElement_def,
        show π y * r * (π y)⁻¹ * r⁻¹ = π y * (r * (π y)⁻¹ * r⁻¹) by group]
      exact mul_mem hxP hr'
    obtain ⟨k, hk⟩ := hRb2 ⟨_, h1⟩
    have hk' : ⁅π y, r⁆ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 := eq_one_of_two_pow_of_mem hPb3 hk' h2'
    rwa [commutatorElement_eq_one_iff_mul_comm] at h3
  have hfin := commutator_eq_bot_of_fix hc3 Rb Q₀ hQ₀exp hRb2 (fun g _ => hnormQ g)
    (hnormQ _) hcR hgen hfix
  apply hQ₀z
  intro q hq
  have hqR := commutator_eq_bot_iff_le_centralizer.mp hfin hq
  show q ∈ centralizer ({(z : ↥X ⧸ N)} : Set (↥X ⧸ N))
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hqR z z.2).symm

end CFSG.RankThree.PartTwo.Sec14.Proof1418Res3
