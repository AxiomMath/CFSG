module

public import CFSG.Walter.ReeOrder.JT.Cited
import CFSG.Walter.W67.Section4.Prop41A
import CFSG.Walter.W67.Section4.Prop41B
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.W2Cor32A
import CFSG.Walter.W67.W2Lemma26B
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_of_inf_normalizer_le {ℓ : ℕ} [Fact ℓ.Prime] {P R : Subgroup G}
    (hR : IsPGroup ℓ R) (hPR : P ≤ R) (h : R ⊓ Subgroup.normalizer (P : Set G) ≤ P) : P = R := by
  by_contra hne
  have hlt : P.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hPR fun x hx => ?_)
    have : (⟨x, hx⟩ : R) ∈ P.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact this
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (P.subgroupOf R) hlt)
  have hyNP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp hyN ⟨x, hPR hx⟩).mp hx
  exact hyP (h ⟨y.2, hyNP⟩)

omit [Finite G] in
theorem mem_centralizer_of_inv {P : Subgroup G} {J z : G} (hJP : P ≤ Subgroup.centralizer {J})
    (hJ2 : J * J = 1) (hz : J * z * J⁻¹ = z⁻¹) (hzN : z ∈ Subgroup.normalizer (P : Set G))
    (hodd : Odd (orderOf z)) : z ∈ Subgroup.centralizer (P : Set G) := by
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ2
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hw : z * a * z⁻¹ * a⁻¹ ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN a).mp ha) (P.inv_mem ha)
  have hJa : J * a = a * J := (Subgroup.mem_centralizer_singleton_iff.mp (hJP ha)).symm
  have hJw : J * (z * a * z⁻¹ * a⁻¹) = (z * a * z⁻¹ * a⁻¹) * J :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hJP hw)).symm
  have hzinv : J * z⁻¹ * J⁻¹ = z := by
    rw [show J * z⁻¹ * J⁻¹ = (J * z * J⁻¹)⁻¹ by group, hz, inv_inv]
  have h1 : J * (z * a * z⁻¹ * a⁻¹) * J⁻¹ = z⁻¹ * a * z * a⁻¹ := by
    have e : J * (z * a * z⁻¹ * a⁻¹) * J⁻¹ =
        (J * z * J⁻¹) * (J * a * J⁻¹) * (J * z⁻¹ * J⁻¹) * (J * a * J⁻¹)⁻¹ := by group
    rw [e, hz, hzinv, show J * a * J⁻¹ = a by rw [hJa, mul_inv_cancel_right]]
  have h2 : J * (z * a * z⁻¹ * a⁻¹) * J⁻¹ = z * a * z⁻¹ * a⁻¹ := by
    rw [hJw, mul_inv_cancel_right]
  have h3 : z⁻¹ * a * z = z * a * z⁻¹ := by
    have := h1.symm.trans h2
    have := congrArg (· * a) this
    simpa using this
  have h4 : (z * z) * a = a * (z * z) := by
    calc (z * z) * a = z * (z * a * z⁻¹) * z := by group
      _ = z * (z⁻¹ * a * z) * z := by rw [h3]
      _ = a * (z * z) := by group
  obtain ⟨k, hk⟩ := hodd
  have hzz : z = (z * z) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  rw [hzz]
  exact ((Commute.pow_left h4 (k + 1))).eq.symm

namespace Std

variable (s : Std G)

theorem card_H :
    Nat.card s.H = 2 * (Nat.card s.K * Nat.card s.fr.E) := by
  have hIDP := s.fr.isInternalDirectProduct_H
  have hc : ∀ x ∈ Subgroup.zpowers s.J, ∀ y ∈ s.K ⊔ s.fr.E, x * y = y * x := by
    intro x hx y hy
    have hyH : y ∈ s.H := (sup_le s.K_le_H s.fr.E_le_H) hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (s.commute_J hyH).symm n)).eq
  obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hIDP.1, disjoint_iff.mp hIDP.2.1, Subgroup.card_bot, mul_one, s.card_zpowers_J] at h1
  have hEN : s.fr.E ≤ Subgroup.normalizer (s.K : Set G) := s.fr.E_le_H.trans s.H_le_normalizer
  have h2 := card_sup_mul_card_inf_of_le_normalizer hEN
  rw [s.fr.K_inf_E, Subgroup.card_bot, mul_one] at h2
  rw [h1, h2]

theorem factorization_card_H
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    (Nat.card s.H).factorization ℓ =
      (Nat.card s.K).factorization ℓ + (Nat.card s.fr.E).factorization ℓ := by
  rw [s.card_H, Nat.factorization_mul (by norm_num) (Nat.mul_ne_zero Nat.card_pos.ne'
    Nat.card_pos.ne'), Finsupp.add_apply, Nat.factorization_mul Nat.card_pos.ne'
    Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ
      Nat.prime_two).mp h)), zero_add]

theorem card_inf_K
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {P : Subgroup G} (hPH : P ≤ s.H)
    (hPℓ : IsPGroup ℓ P) (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ) :
    Nat.card (P ⊓ s.K : Subgroup G) = ℓ ^ (Nat.card s.K).factorization ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  have hPN : P ≤ Subgroup.normalizer (s.K : Set G) := hPH.trans s.H_le_normalizer
  have hc := card_sup_mul_card_inf_of_le_normalizer hPN
  have hdvd : Nat.card (s.K ⊔ P : Subgroup G) ∣ Nat.card s.H :=
    Subgroup.card_dvd_of_le (sup_le s.K_le_H hPH)
  obtain ⟨m, hm⟩ := (hPℓ.to_le (inf_le_left : P ⊓ s.K ≤ P)).exists_card_eq
  have hm' : Nat.card (s.K ⊓ P : Subgroup G) = ℓ ^ m := by rw [inf_comm]; exact hm
  rw [hm'] at hc
  have hKne := (Nat.card_pos (α := s.K)).ne'
  have hle1 : m ≤ (Nat.card s.K).factorization ℓ :=
    (hℓ.pow_dvd_iff_le_factorization hKne).mp (hm ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hle2 : (Nat.card s.K).factorization ℓ ≤ m := by
    have h1 : Nat.card (s.K ⊔ P : Subgroup G) * ℓ ^ m = Nat.card s.K * ℓ ^
        (Nat.card s.H).factorization ℓ := by rw [hc, hPcard]
    have h2 := (Nat.factorization_le_iff_dvd (Nat.card_pos (α := (s.K ⊔ P : Subgroup G))).ne'
      (Nat.card_pos (α := s.H)).ne').mpr hdvd ℓ
    have h3 := congrArg (fun n => n.factorization ℓ) h1
    rw [Nat.factorization_mul (Nat.card_pos (α := (s.K ⊔ P : Subgroup G))).ne'
      (pow_ne_zero _ hℓ.ne_zero), Nat.factorization_mul hKne (pow_ne_zero _ hℓ.ne_zero),
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow_self hℓ,
      Nat.factorization_pow_self hℓ] at h3
    rw [s.factorization_card_H hℓ hℓ2] at h2 h3
    omega
  rw [hm, le_antisymm hle1 hle2]

theorem five_lt_q' : 5 < s.q := by
  have h3 := s.three_lt_q
  have h8 := s.mod_eight
  by_contra h
  have hq5 : s.q = 5 := by omega
  have hpf : s.p ^ s.f = 5 := hq5
  obtain ⟨hp5, hf1⟩ := (Nat.prime_five.pow_eq_iff).mp hpf
  obtain ⟨hdvd, -, -⟩ := lemma_2_6_i G s.toHyp s.fr le_rfl s.E_ne_bot
  rw [s.eX_eq, hf1] at hdvd
  apply s.E_ne_bot
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

theorem psl2Facts_K :
    JT.PSL2Facts s.K s.p s.f :=
  JT.psl2Facts s.K s.iso s.p_ne_two s.five_lt_q'

theorem card_K : Nat.card s.K = s.q * (s.q ^ 2 - 1) / 2 :=
  PSL2Sub.card_eq s.iso s.odd_p s.f_pos

theorem sup_eq
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {P₀ P : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    (hP₀card : Nat.card P₀ = ℓ ^ (Nat.card s.fr.E).factorization ℓ) (hPH : P ≤ s.H)
    (hPℓ : IsPGroup ℓ P) (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ)
    (hP₀P : P₀ ≤ P) : (P ⊓ s.K) ⊔ P₀ = P := by
  have hℓ : ℓ.Prime := Fact.out
  have hP₀N : P₀ ≤ Subgroup.normalizer ((P ⊓ s.K : Subgroup G) : Set G) := fun x hx =>
    normalizer_inf_normalizer_le P s.K ⟨Subgroup.le_normalizer (hP₀P hx),
      s.H_le_normalizer (hPH (hP₀P hx))⟩
  have hc := card_sup_mul_card_inf_of_le_normalizer hP₀N
  have hinf : (P ⊓ s.K) ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ s.K ⊓ s.fr.E := ⟨hx.1.2, hP₀E hx.2⟩
    rwa [s.fr.K_inf_E] at this
  rw [hinf, Subgroup.card_bot, mul_one, s.card_inf_K hℓ2 hPH hPℓ hPcard, hP₀card] at hc
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hP₀P) ?_
  rw [hc, hPcard, s.factorization_card_H hℓ hℓ2, pow_add]

theorem isMetacyclic
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ s.p) {P₀ P : Subgroup G}
    (hP₀E : P₀ ≤ s.fr.E) (hP₀card : Nat.card P₀ = ℓ ^ (Nat.card s.fr.E).factorization ℓ)
    (hPH : P ≤ s.H) (hPℓ : IsPGroup ℓ P)
    (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ) (hP₀P : P₀ ≤ P) :
    JT.IsMetacyclic P := by
  have hℓ : ℓ.Prime := Fact.out
  have hsup := s.sup_eq hℓ2 hP₀E hP₀card hPH hPℓ hPcard hP₀P
  have hP₁P : P ⊓ s.K ≤ P := inf_le_left
  set C : Subgroup P := (P ⊓ s.K).subgroupOf P with hC
  have hCn : C.Normal := by
    refine normal_subgroupOf_of_le_normalizer fun x hx => ?_
    exact normalizer_inf_normalizer_le P s.K ⟨Subgroup.le_normalizer hx,
      s.H_le_normalizer (hPH hx)⟩
  have hcycK : IsCyclic (P ⊓ s.K : Subgroup G) :=
    s.psl2Facts_K.cyclic ℓ hℓ hℓ2 hℓp _ inf_le_right (hPℓ.to_le inf_le_left)
  have hcycC : IsCyclic C :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP₁P).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP₁P).symm.surjective
  have hcycE : IsCyclic s.fr.E := by
    obtain ⟨g, hg⟩ := s.exists_E_eq_zpowers
    rw [hg]
    infer_instance
  have hcyc0 : IsCyclic P₀ := Subgroup.isCyclic_of_le hP₀E
  set f : P₀ →* P ⧸ C := (QuotientGroup.mk' C).comp (Subgroup.inclusion hP₀P)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hxP : (x : G) ∈ (P ⊓ s.K) ⊔ P₀ := by rw [hsup]; exact x.2
    have hN : P₀ ≤ Subgroup.normalizer ((P ⊓ s.K : Subgroup G) : Set G) := fun z hz =>
      normalizer_inf_normalizer_le P s.K ⟨Subgroup.le_normalizer (hP₀P hz),
        s.H_le_normalizer (hPH (hP₀P hz))⟩
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_le_normalizer hN).mp hxP
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' C) (Subgroup.inclusion hP₀P ⟨b, hb⟩) = QuotientGroup.mk' C x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    change (⟨b, hP₀P hb⟩ : P)⁻¹ * x ∈ C
    rw [hC, Subgroup.mem_subgroupOf]
    have : ((⟨b, hP₀P hb⟩ : P)⁻¹ * x : P) = b⁻¹ * a * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hab]
      group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp (hN (P₀.inv_mem hb)) a).mp ha |> fun h => by
      simpa [mul_assoc] using h
  exact ⟨C, hCn, hcycC, isCyclic_of_surjective f hf⟩

theorem not_pow_dvd_card_KX
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ s.p)
    (hℓK : ℓ ∣ Nat.card s.K) {Ω : Subgroup G} (hΩE : Ω ≤ s.fr.E) (hΩcard : Nat.card Ω = ℓ) :
    ¬ ℓ ^ (Nat.card s.K).factorization ℓ ∣ Nat.card (s.KX Ω) := by
  intro h1
  have hℓ : ℓ.Prime := Fact.out
  have hΩne : Ω ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hΩcard
    exact hℓ.one_lt.ne hΩcard
  obtain ⟨hdvd, ⟨eK⟩, -⟩ := lemma_2_6_i G s.toHyp s.fr hΩE hΩne
  have heΩ : s.eX Ω = ℓ := by rw [s.eX_eq, hΩcard]
  have hfe : 0 < s.f / s.eX Ω := by
    rw [heΩ]
    exact Nat.div_pos (Nat.le_of_dvd s.f_pos (heΩ ▸ hdvd)) hℓ.pos
  have hKΩ' := PSL2Sub.card_eq eK s.odd_p hfe
  rw [heΩ] at hKΩ' hdvd
  set r := s.p ^ (s.f / ℓ) with hr
  have hKΩ : Nat.card (s.KX Ω) = r * (r ^ 2 - 1) / 2 := hKΩ'
  set v := (Nat.card s.K).factorization ℓ with hv
  have hv1 : 1 ≤ v := (hℓ.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hℓK
  rw [hKΩ] at h1
  have hcopr : Nat.Coprime (ℓ ^ v) r := by
    apply Nat.Coprime.pow_left
    rw [hr]
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes hℓ Fact.out).mpr hℓp
  have h2 : ℓ ^ v ∣ r ^ 2 - 1 :=
    hcopr.dvd_of_dvd_mul_left (h1.trans (Nat.div_dvd_of_dvd ((by
      have hodd : Odd r := s.odd_p.pow
      have : Even (r ^ 2 - 1) := by
        rw [Nat.even_sub (Nat.one_le_pow _ _ hodd.pos)]
        simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hodd]
      exact (even_iff_two_dvd.mp this).mul_left _ : 2 ∣ r * (r ^ 2 - 1)))))
  have h3 := pow_succ_dvd_pow_sub_one hℓ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _
    (Nat.Prime.pos Fact.out))) hv1 h2
  have hq : (r ^ 2) ^ ℓ = s.q ^ 2 := by
    have h1 : r ^ ℓ = s.q := by
      rw [hr, ← pow_mul, Nat.div_mul_cancel hdvd]
      rfl
    rw [← pow_mul, mul_comm, pow_mul, h1]
  rw [hq] at h3
  have h4 : ℓ ^ (v + 1) ∣ Nat.card s.K := by
    rw [s.card_K]
    have h2' : 2 ∣ s.q * (s.q ^ 2 - 1) := by
      have hodd : Odd s.q := s.odd_p.pow
      have : Even (s.q ^ 2 - 1) := by
        rw [Nat.even_sub (Nat.one_le_pow _ _ hodd.pos)]
        simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hodd]
      exact (even_iff_two_dvd.mp this).mul_left _
    obtain ⟨c, hc⟩ := h2'
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
    have h5 : ℓ ^ (v + 1) ∣ 2 * c := hc ▸ h3.mul_left s.q
    exact (Nat.Coprime.pow_left (v + 1) ((Nat.coprime_primes hℓ Nat.prime_two).mpr
      hℓ2)).dvd_of_dvd_mul_left h5
  have := (hℓ.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h4
  omega

theorem not_isMulCommutative
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ s.p)
    (hℓK : ℓ ∣ Nat.card s.K) {P₀ P : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    (hP₀ℓ : IsPGroup ℓ P₀) (hP₀ne : P₀ ≠ ⊥) (hPH : P ≤ s.H) (hPℓ : IsPGroup ℓ P)
    (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ) (hP₀P : P₀ ≤ P) :
    ¬ IsMulCommutative P := by
  intro hab
  have hℓ : ℓ.Prime := Fact.out
  have hℓP₀ : ℓ ∣ Nat.card P₀ := by
    obtain ⟨k, hk⟩ := hP₀ℓ.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      exact hP₀ne (Subgroup.card_eq_one.mp hk)
    rw [hk]
    exact dvd_pow_self ℓ hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P₀) ℓ hℓP₀
  set Ω := Subgroup.zpowers (x : G) with hΩ
  have hΩE : Ω ≤ s.fr.E := Subgroup.zpowers_le.mpr (hP₀E x.2)
  have hΩcard : Nat.card Ω = ℓ := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hP₁ : P ⊓ s.K ≤ s.KX Ω := by
    intro y hy
    refine ⟨hy.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hwP : w ∈ P := hP₀P ((Subgroup.zpowers_le.mpr x.2) hw)
    exact congrArg Subtype.val (hab.is_comm.comm ⟨w, hwP⟩ ⟨y, hy.1⟩)
  refine s.not_pow_dvd_card_KX hℓ2 hℓp hℓK hΩE hΩcard ?_
  rw [← s.card_inf_K hℓ2 hPH hPℓ hPcard]
  exact Subgroup.card_dvd_of_le hP₁

theorem eq_of_mem_normalizer_J {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) {P₀ P R : Subgroup G}
    (hPH : P ≤ s.H) (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ)
    (hP₀P : P₀ ≤ P)
    (hsyl : (Nat.card (Subgroup.normalizer (P₀ : Set G))).factorization ℓ ≤
      (Nat.card (P ⊓ Subgroup.centralizer (P₀ : Set G) : Subgroup G)).factorization ℓ)
    (hR : IsPGroup ℓ R) (hPR : P ≤ R) (hJR : s.J ∈ Subgroup.normalizer (R : Set G)) :
    P = R := by
  have hℓ : ℓ.Prime := Fact.out
  have hJ2 : s.J * s.J = 1 := s.J_mul_J
  have hJinv : s.J⁻¹ = s.J := s.J_inv
  have hPC : P ≤ Subgroup.centralizer ({s.J} : Set G) := hPH
  have hJP : s.J ∈ Subgroup.normalizer (P : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC ha)
    rw [show s.J * a * s.J⁻¹ = a by rw [← h1, mul_inv_cancel_right]]
    exact ha
  have hRH : R ⊓ s.H = P := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hPR hPH) ?_).symm
    obtain ⟨k, hk⟩ := (hR.to_le (inf_le_left : R ⊓ s.H ≤ R)).exists_card_eq
    have h1 : ℓ ^ k ∣ Nat.card s.H := hk ▸ Subgroup.card_dvd_of_le inf_le_right
    have h2 := (hℓ.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
    rw [hk, hPcard]
    exact Nat.pow_le_pow_right hℓ.pos h2
  have hRC : R ⊓ Subgroup.centralizer (P₀ : Set G) ≤ P := by
    have hle : P ⊓ Subgroup.centralizer (P₀ : Set G) ≤ R ⊓ Subgroup.centralizer (P₀ : Set G) :=
      inf_le_inf_right _ hPR
    have heq : P ⊓ Subgroup.centralizer (P₀ : Set G) =
        R ⊓ Subgroup.centralizer (P₀ : Set G) := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      obtain ⟨k, hk⟩ := (hR.to_le (inf_le_left : R ⊓ Subgroup.centralizer (P₀ : Set G) ≤ R)
        ).exists_card_eq
      obtain ⟨m, hm⟩ := ((hR.to_le hPR).to_le
        (inf_le_left : P ⊓ Subgroup.centralizer (P₀ : Set G) ≤ P)).exists_card_eq
      have h1 : ℓ ^ k ∣ Nat.card (Subgroup.normalizer (P₀ : Set G)) :=
        hk ▸ Subgroup.card_dvd_of_le (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
      have h2 := (hℓ.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
      rw [hm, Nat.factorization_pow_self hℓ] at hsyl
      rw [hk, hm]
      exact Nat.pow_le_pow_right hℓ.pos (h2.trans hsyl)
    rw [← heq]
    exact inf_le_left
  apply eq_of_le_of_inf_normalizer_le hR hPR
  rintro x ⟨hxR, hxN⟩
  have hJxR : s.J * x * s.J⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hJR x).mp hxR
  have hJxN : s.J * x * s.J⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hJP hxN) (Subgroup.inv_mem _ hJP)
  set y := (s.J * x * s.J⁻¹)⁻¹ * x with hy
  have hyR : y ∈ R := R.mul_mem (R.inv_mem hJxR) hxR
  have hyN : y ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hJxN) hxN
  have hJy : s.J * y * s.J⁻¹ = y⁻¹ := by
    rw [hy]
    have e1 : s.J * ((s.J * x * s.J⁻¹)⁻¹ * x) * s.J⁻¹ =
        (s.J * s.J) * x⁻¹ * s.J⁻¹ * x * s.J⁻¹ := by group
    have e2 : ((s.J * x * s.J⁻¹)⁻¹ * x)⁻¹ = x⁻¹ * s.J * x * s.J⁻¹ := by group
    rw [e1, e2, hJ2, one_mul, hJinv]
  have hyodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨y, hyR⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨k, hk⟩ := hyodd
  set z := y ^ (k + 1) with hz
  have hzz : z * z = y := by
    rw [hz, ← pow_two, ← pow_mul, show (k + 1) * 2 = 2 * k + 1 + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  have hzR : z ∈ R := R.pow_mem hyR _
  have hzN : z ∈ Subgroup.normalizer (P : Set G) := Subgroup.pow_mem _ hyN _
  have hJz : s.J * z * s.J⁻¹ = z⁻¹ := by rw [hz, ← conj_pow, hJy, inv_pow]
  have hzodd : Odd (orderOf z) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨z, hzR⟩
    rw [Subgroup.orderOf_mk] at hm
    rw [hm]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have hc : s.J * (x * z⁻¹) * s.J⁻¹ = x * z⁻¹ := by
    have e1 : s.J * (x * z⁻¹) * s.J⁻¹ = (s.J * x * s.J⁻¹) * (s.J * z⁻¹ * s.J⁻¹) := by group
    have e2 : s.J * z⁻¹ * s.J⁻¹ = z := by
      rw [show s.J * z⁻¹ * s.J⁻¹ = (s.J * z * s.J⁻¹)⁻¹ by group, hJz, inv_inv]
    rw [e1, e2]
    have : x * z⁻¹ = (s.J * x * s.J⁻¹) * (z * z) * z⁻¹ := by
      rw [hzz, hy]; group
    rw [this]
    group
  have hcP : x * z⁻¹ ∈ P := by
    rw [← hRH]
    refine ⟨R.mul_mem hxR (R.inv_mem hzR), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * z⁻¹ * s.J = (s.J * (x * z⁻¹) * s.J⁻¹) * s.J := by rw [hc]
      _ = s.J * (x * z⁻¹) := by group
  have hzC := mem_centralizer_of_inv hPC hJ2 hJz hzN hzodd
  have hzP : z ∈ P := hRC ⟨hzR, Subgroup.centralizer_le hP₀P hzC⟩
  have : x = (x * z⁻¹) * z := by group
  rw [this]
  exact P.mul_mem hcP hzP

end Std

end CFSG.Walter.W67
