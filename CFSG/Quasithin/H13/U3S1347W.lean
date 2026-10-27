module

public import CFSG.Quasithin.Background.F6Cyclic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6 CFSG.LieType.BorelTits

theorem gl2_core {F : Type*} [Field F] {o₁ o₂ κ₁ κ₂ : GL (Fin 2) F}
    (h12 : o₁ * o₂ = o₂ * o₁) (h1 : o₁ * κ₁ = κ₁ * o₁) (h2 : o₂ * κ₁ * o₂⁻¹ = κ₁⁻¹)
    (h4 : o₁ * κ₂ * o₁⁻¹ = κ₂⁻¹) (hκ₁ : κ₁ * κ₁ ≠ 1)
    (hκ₂ : κ₂ * κ₂ ≠ 1) : False := by
  have hinv : ∀ {o κ : GL (Fin 2) F}, o * κ = κ * o → o * κ * o⁻¹ = κ⁻¹ → κ * κ = 1 := by
    intro o κ hc hi
    rw [hc, mul_inv_cancel_right] at hi
    have e : κ * κ = κ * κ⁻¹ := congrArg (κ * ·) hi
    rw [e, mul_inv_cancel]
  by_cases hs : ∃ c : F, (o₁ : Matrix (Fin 2) (Fin 2) F) = c • 1
  · obtain ⟨c, hc⟩ := hs
    have hcomm : o₁ * κ₂ = κ₂ * o₁ := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one])
    exact hκ₂ (hinv hcomm h4)
  · have hB : (o₁ : Matrix (Fin 2) (Fin 2) F) * κ₁ = κ₁ * o₁ := by
      rw [← Units.val_mul, ← Units.val_mul, h1]
    have hC : (o₁ : Matrix (Fin 2) (Fin 2) F) * o₂ = o₂ * o₁ := by
      rw [← Units.val_mul, ← Units.val_mul, h12]
    have hκo : (κ₁ : Matrix (Fin 2) (Fin 2) F) * o₂ = o₂ * κ₁ :=
      CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hs hB hC
    have hκo' : o₂ * κ₁ = κ₁ * o₂ := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hκo])
    exact hκ₁ (hinv hκo' h2)

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem perm_three_sq_of_two_pow (σ : Equiv.Perm (Fin 3)) {k : ℕ} (hk : σ ^ 2 ^ k = 1) :
    σ ^ 2 = 1 := by
  have h6 : orderOf σ ∣ 6 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have h4 : 4 ∣ orderOf σ := by
      rw [hj, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have := h4.trans h6
    omega
  have h2' : orderOf σ ∣ 2 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj1).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 h2'

omit [Finite D] in
theorem inv_mod_pCoreOf (h : IsGoldschmidtTriple G₁ G₂) {x s : D} (hx : x ∈ G₁)
    (hx3 : x ^ 3 = 1) (hs : s ∈ G₁ ⊓ G₂) (hsQ : s ∉ pCoreOf 2 G₁) :
    s * x * s⁻¹ * x ∈ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.quotient₁
  set σ := e (QuotientGroup.mk (⟨s, hs.1⟩ : ↥G₁)) with hσ
  set τ := e (QuotientGroup.mk (⟨x, hx⟩ : ↥G₁)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥G₁) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hsQ
    have h2 : (⟨s, hs.1⟩ : ↥G₁) ∈ Open.pCore 2 ↥G₁ := by
      rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
      exact h1
    exact ⟨_, h2, rfl⟩
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := h.isPGroup_inf ⟨s, hs⟩
    have hk' : (⟨s, hs.1⟩ : ↥G₁) ^ 2 ^ k = 1 := Subtype.ext (by
      simpa using congrArg Subtype.val hk)
    refine perm_three_sq_of_two_pow σ (k := k) ?_
    rw [hσ, ← map_pow, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one, map_one]
  have h1 : e (QuotientGroup.mk (⟨s, hs.1⟩ * ⟨x, hx⟩ * ⟨s, hs.1⟩⁻¹ * ⟨x, hx⟩ : ↥G₁)) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    exact perm_three_inv σ τ ⟨hσ2, hσ1, hτ3⟩
  have h2 : (⟨s, hs.1⟩ * ⟨x, hx⟩ * ⟨s, hs.1⟩⁻¹ * ⟨x, hx⟩ : ↥G₁) ∈ Open.pCore 2 ↥G₁ := by
    rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
    exact h1
  exact ⟨_, h2, rfl⟩

theorem ker_inf_le_pCoreOf {E : Type*} [Group E] (h : IsGoldschmidtTriple G₁ G₂) (ρ : D →* E)
    {x : D} (hx : x ∈ G₁) (hx3 : x ^ 3 = 1) (hρ : ρ x ≠ 1) : G₁ ⊓ ρ.ker ≤ pCoreOf 2 G₁ := by
  by_contra hle
  have hn : ((G₁ ⊓ ρ.ker).subgroupOf G₁).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).2 (le_normalizer_inf_of_normal G₁)
  have hL := twoResidual_le_of_isSubnormal h (A4.subnormal_of_normal inf_le_left hn) hle
  have hxL : x ∈ twoResidual G₁ := mem_twoResidual_of_odd hx (by
    have : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    exact Odd.of_dvd_nat (by decide) this)
  exact hρ (mem_inf.1 (hL hxL)).2

omit [Finite D] in
theorem sq_eq_one_of_card_le_two {E : Type*} [Group E] [Finite E] {X : Subgroup E}
    (hX : Nat.card ↥X ≤ 2) {o : E} (ho : o ∈ X) : o ^ 2 = 1 := by
  have h1 := pow_card_eq_one' (G := ↥X) (x := ⟨o, ho⟩)
  have hpos : 0 < Nat.card ↥X := Nat.card_pos
  interval_cases hc : Nat.card ↥X
  · have := congrArg Subtype.val h1
    simp only [pow_one, OneMemClass.coe_one] at this
    rw [this, one_pow]
  · simpa using congrArg Subtype.val h1

omit [Finite D] in
theorem comm_of_card_le_two {E : Type*} [Group E] [Finite E] {X : Subgroup E}
    (hX : Nat.card ↥X ≤ 2) {o g : E} (ho : o ∈ X) (hg : g * o * g⁻¹ ∈ X) : g * o = o * g := by
  by_cases ho1 : o = 1
  · rw [ho1, mul_one, one_mul]
  have ho2 : o ^ 2 = 1 := sq_eq_one_of_card_le_two hX ho
  have hord : orderOf o = 2 := orderOf_eq_prime ho2 ho1
  have hZX : zpowers o ≤ X := zpowers_le.2 ho
  have hXZ : X = zpowers o := by
    refine (eq_of_le_of_card_ge hZX ?_).symm
    rw [Nat.card_zpowers, hord]
    exact hX
  rw [hXZ] at hg
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg
  have hk' : o ^ k = o ^ (k % 2) := by
    rw [show (2 : ℤ) = ((orderOf o : ℕ) : ℤ) by rw [hord]; rfl, zpow_mod_orderOf]
  have hne : g * o * g⁻¹ ≠ 1 := fun h1 => ho1 (by
    have := congrArg (fun y => g⁻¹ * y * g) h1
    simpa [mul_assoc] using this)
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [hk', h0, zpow_zero] at hk
    exact absurd hk.symm hne
  · rw [hk', h0, zpow_one] at hk
    calc g * o = g * o * g⁻¹ * g := by group
      _ = o * g := by rw [← hk]

theorem pCoreOf_eq_of_gl2 {F : Type*} [Field F] [Finite F] (h : IsGoldschmidtTriple G₁ G₂)
    (ρ : D →* GL (Fin 2) F) (hT : Nat.card ↥((G₁ ⊓ G₂).map ρ) ≤ 4)
    {x₁ x₂ : D} (hx₁ : x₁ ∈ G₁) (hx₁3 : x₁ ^ 3 = 1) (hρ₁ : ρ x₁ ≠ 1)
    (hx₂ : x₂ ∈ G₂) (hx₂3 : x₂ ^ 3 = 1) (hρ₂ : ρ x₂ ≠ 1) :
    pCoreOf 2 G₁ = pCoreOf 2 G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ {G G' : Subgroup D}, IsGoldschmidtTriple G G' → ∀ {x : D}, x ∈ G → x ^ 3 = 1 →
      ρ x ≠ 1 → Nat.card ↥((G ⊓ G').map ρ) ≤ 4 →
      Nat.card ↥((G ⊓ G').map ρ) = 2 * Nat.card ↥((pCoreOf 2 G).map ρ) ∧
      (∀ o ∈ (pCoreOf 2 G).map ρ, ∀ g ∈ G, ρ g * o = o * ρ g) ∧
      (∀ s ∈ G ⊓ G', s ∉ pCoreOf 2 G → ρ s * ρ x * (ρ s)⁻¹ = (ρ x)⁻¹) ∧
      (∀ q ∈ G ⊓ G', ρ q ∈ (pCoreOf 2 G).map ρ → q ∈ pCoreOf 2 G) := by
    intro G G' hG x hx hx3 hρx hT'
    have hker := ker_inf_le_pCoreOf hG ρ hx hx3 hρx
    have hQT : pCoreOf 2 G ≤ G ⊓ G' := pCoreOf_le_inf_left hG
    have hkerT : ρ.ker ⊓ (G ⊓ G') = ρ.ker ⊓ pCoreOf 2 G :=
      le_antisymm (fun y hy => mem_inf.2 ⟨(mem_inf.1 hy).1,
          hker (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hy).2).1, (mem_inf.1 hy).1⟩)⟩)
        (inf_le_inf_left _ hQT)
    have hcard : Nat.card ↥((G ⊓ G').map ρ) = 2 * Nat.card ↥((pCoreOf 2 G).map ρ) := by
      have h1 := relIndex_mul_card ρ.ker (G ⊓ G')
      have h2 := relIndex_mul_card ρ.ker (pCoreOf 2 G)
      have h3 := relIndex_mul_card (pCoreOf 2 G) (G ⊓ G')
      rw [relIndex_ker] at h1 h2
      rw [relIndex_pCoreOf_left hG, inf_eq_left.2 hQT] at h3
      rw [hkerT] at h1
      have hpos : 0 < Nat.card ↥(ρ.ker ⊓ pCoreOf 2 G) := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [h1, mul_assoc, h2, h3]
    have hQ2 : Nat.card ↥((pCoreOf 2 G).map ρ) ≤ 2 := by omega
    have hcent : ∀ o ∈ (pCoreOf 2 G).map ρ, ∀ g ∈ G, ρ g * o = o * ρ g := by
      rintro _ ⟨q, hq, rfl⟩ g hg
      refine comm_of_card_le_two hQ2 ⟨q, hq, rfl⟩ ?_
      refine ⟨g * q * g⁻¹, (mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 G hg) q).1 hq, ?_⟩
      rw [map_mul, map_mul, map_inv]
    refine ⟨hcard, hcent, fun s hs hsQ => ?_, fun q hq hρq => ?_⟩
    · have hm := inv_mod_pCoreOf hG hx hx3 hs hsQ
      set o := ρ s * ρ x * (ρ s)⁻¹ * ρ x with ho
      have hoQ : o ∈ (pCoreOf 2 G).map ρ := ⟨_, hm, by rw [ho, map_mul, map_mul, map_mul,
        map_inv]⟩
      have hoc : ρ x * o = o * ρ x := hcent o hoQ x hx
      have ho2 : o ^ 2 = 1 := sq_eq_one_of_card_le_two hQ2 hoQ
      have hκ3 : ρ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
      have e1 : ρ s * ρ x * (ρ s)⁻¹ = o * (ρ x)⁻¹ := by rw [ho]; group
      have e2 : (ρ s * ρ x * (ρ s)⁻¹) ^ 3 = 1 := by
        rw [show ρ s * ρ x * (ρ s)⁻¹ = MulAut.conj (ρ s) (ρ x) from rfl, ← map_pow, hκ3,
          map_one]
      have hoc' : Commute o (ρ x)⁻¹ := Commute.inv_right (show Commute o (ρ x) from hoc.symm)
      have e3 : (o * (ρ x)⁻¹) ^ 3 = o := by
        rw [(Commute.mul_pow hoc'), inv_pow, hκ3, inv_one, mul_one, show 3 = 2 + 1 from rfl,
          pow_succ, ho2, one_mul]
      rw [e1] at e2 ⊢
      rw [e3] at e2
      rw [e2, one_mul]
    · obtain ⟨q', hq', hqq'⟩ := hρq
      have hk : q * q'⁻¹ ∈ G ⊓ ρ.ker :=
        mem_inf.2 ⟨mul_mem (mem_inf.1 hq).1 (inv_mem (hQT hq').1),
          by rw [MonoidHom.mem_ker, map_mul, map_inv, hqq', mul_inv_cancel]⟩
      have hq'' := mul_mem (hker hk) hq'
      rwa [inv_mul_cancel_right] at hq''
  have hT' : Nat.card ↥((G₂ ⊓ G₁).map ρ) ≤ 4 := by rwa [inf_comm]
  obtain ⟨c₁, z₁, i₁, p₁⟩ := key h hx₁ hx₁3 hρ₁ hT
  obtain ⟨c₂, z₂, i₂, p₂⟩ := key h.symm hx₂ hx₂3 hρ₂ hT'
  rw [inf_comm] at c₂ i₂ p₂
  by_contra hne
  have hO : (pCoreOf 2 G₁).map ρ ≠ (pCoreOf 2 G₂).map ρ := by
    intro hO
    apply hne
    refine le_antisymm (fun q hq => p₂ q (pCoreOf_le_inf_left h hq) ?_)
      (fun q hq => p₁ q (pCoreOf_le_inf_right h hq) ?_)
    · rw [← hO]; exact mem_map_of_mem _ hq
    · rw [hO]; exact mem_map_of_mem _ hq
  have hcardO : Nat.card ↥((pCoreOf 2 G₁).map ρ) = Nat.card ↥((pCoreOf 2 G₂).map ρ) := by omega
  have hex : ∀ {A B : Subgroup D}, Nat.card ↥(A.map ρ) = Nat.card ↥(B.map ρ) →
      A.map ρ ≠ B.map ρ → ∃ a ∈ A, ρ a ∉ B.map ρ := by
    intro A B hAB hne'
    by_contra hall
    have hall' : ∀ a ∈ A, ρ a ∈ B.map ρ := fun a ha => by
      by_contra hna
      exact hall ⟨a, ha, hna⟩
    exact hne' (eq_of_le_of_card_ge (fun _ ⟨a, ha, hae⟩ => hae ▸ hall' a ha) hAB.ge)
  obtain ⟨q₁, hq₁, hq₁'⟩ := hex hcardO hO
  obtain ⟨q₂, hq₂, hq₂'⟩ := hex hcardO.symm (Ne.symm hO)
  have hq₁T := pCoreOf_le_inf_left h hq₁
  have hq₂T := pCoreOf_le_inf_right h hq₂
  have hq₁Q₂ : q₁ ∉ pCoreOf 2 G₂ := fun hq => hq₁' (mem_map_of_mem _ hq)
  have hq₂Q₁ : q₂ ∉ pCoreOf 2 G₁ := fun hq => hq₂' (mem_map_of_mem _ hq)
  have hsq : ∀ {κ : GL (Fin 2) F}, κ ^ 3 = 1 → κ ≠ 1 → κ * κ ≠ 1 := by
    intro κ h3 h1 h2
    apply h1
    calc κ = κ ^ 3 * (κ * κ)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  exact gl2_core (o₁ := ρ q₁) (o₂ := ρ q₂) (κ₁ := ρ x₁) (κ₂ := ρ x₂)
    (z₁ _ (mem_map_of_mem _ hq₁) q₂ hq₂T.1).symm
    (z₁ _ (mem_map_of_mem _ hq₁) x₁ hx₁).symm
    (i₁ q₂ hq₂T hq₂Q₁) (i₂ q₁ hq₁T hq₁Q₂)
    (hsq (by rw [← map_pow, hx₁3, map_one]) hρ₁) (hsq (by rw [← map_pow, hx₂3, map_one]) hρ₂)

theorem exists_normalPComplement_of_central {C : Type*} [Group C] [Finite C] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hcen : ∀ x : C, x ^ p = 1 → x ∈ center C) :
    ∃ M : Subgroup C, CFSG.GroupTheory.IsNormalPComplement p M := by
  refine (CFSG.GroupTheory.frobenius_normal_p_complement (G := C) p).1.2 fun Q hQ => ?_
  rintro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  set α := Q.normalizerMonoidHom g with hα
  have hm : orderOf α ≠ 0 := (orderOf_pos α).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.one_lt.ne'
  obtain ⟨X, hX, hfaith⟩ := exists_isSupercritical_faithful hp2 hQ
  have hβ : α ^ p ^ a = 1 := by
    refine hfaith _ ?_ fun x hx => ?_
    · rw [orderOf_pow' α (pow_ne_zero a hp.out.ne_zero), hab,
        Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos a)]
      exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
    · have hxp : (((x : ↥Q) : C)) ^ p = 1 := by
        have := hX.pow_eq_one x hx
        simpa using congrArg (fun z : ↥Q => (z : C)) this
      have hxc := hcen _ hxp
      have hfix : (α ^ p ^ a) x = x := by
        rw [← map_pow]
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_apply_coe]
        have := mem_center_iff.1 hxc ((g ^ p ^ a : ↥(normalizer (Q : Set C))) : C)
        rw [this, mul_inv_cancel_right]
      rw [hfix, inv_mul_cancel]
      exact one_mem _
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← normalizerMonoidHom_ker,
    MonoidHom.mem_ker, map_pow]
  exact hβ

open scoped IsMulCommutative in
theorem mem_of_centralizes_elem {p : ℕ} [hp : Fact p.Prime] {E : Subgroup D}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hr : ∀ A : Subgroup D, IsElemAbelian p A → Nat.card A ≤ p ^ 2) {x : D} (hx : x ^ p = 1)
    (hxE : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  by_contra hxn
  have := hE.1
  have hcomm : ((E : Set D) ∪ {x}).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
    · rw [Set.mem_singleton_iff.1 hb]
      exact (hxE a ha).symm
    · rw [Set.mem_singleton_iff.1 ha]
      exact hxE b hb
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  set A := closure ((E : Set D) ∪ {x}) with hA
  have hAc : IsMulCommutative ↥A := isMulCommutative_closure hcomm
  have hAp : ∀ a ∈ A, a ^ p = 1 := by
    intro a ha
    induction ha using closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact hE.2 a ha
      · rw [Set.mem_singleton_iff.1 ha]; exact hx
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
      have hc : Commute a b := congrArg Subtype.val (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [hc.mul_pow, iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  have hEA : E ≤ A := fun e he => subset_closure (Or.inl he)
  have hxA : x ∈ A := subset_closure (Or.inr rfl)
  have hAp' : IsPGroup p ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAp a a.2)⟩
  obtain ⟨n, hn⟩ := hAp'.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card A := card_dvd_of_le hEA
  have hne : Nat.card E ≠ Nat.card A := fun h' => hxn ((eq_of_le_of_card_ge hEA h'.ge) ▸ hxA)
  rw [hEc, hn] at hdvd hne
  have h2n : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd
  have hle := hr A ⟨hAc, hAp⟩
  rw [hn] at hle
  have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  have : n = 2 := by omega
  exact hne (by rw [this])

theorem isCyclic_pCore_of_goldschmidt (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) ≤ 4) (hQ : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hr : ∀ A : Subgroup D, IsElemAbelian p A → Nat.card A ≤ p ^ 2) :
    IsCyclic ↥(Open.pCore p D) := by
  by_contra hnc
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  set R := Open.pCore p D with hRdef
  have hRn : R.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hRp : IsPGroup p ↥R := CFSG.LieType.BorelTits.pCore_isPGroup p
  have : Fact (IsPGroup p ↥R) := ⟨hRp⟩
  obtain ⟨E₀, -, hE₀c, hE₀e⟩ := CFSG.lemma_4_5_a hp2 hnc
  set E := E₀.map R.subtype with hEdef
  have hER : E ≤ R := map_subtype_le E₀
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      apply Subtype.ext
      show (a : D) * b = b * a
      rw [← hae, ← hbe]
      exact congrArg (fun z : ↥R => (z : D))
        (congrArg Subtype.val (hE₀e.toIsMulCommutative.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · obtain ⟨x', hx', rfl⟩ := hx
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E₀) x' hx'
      simpa using congrArg Subtype.val this
  have hEc : Nat.card E = p ^ 2 := by rw [card_map_of_injective R.subtype_injective, hE₀c]
  set C := centralizer (R : Set D) with hCdef
  have hCp : ∀ x ∈ C, x ^ p = 1 → x ∈ E := fun x hx hxp =>
    mem_of_centralizes_elem hEe hEc hr hxp fun e he => (mem_centralizer_iff.1 hx e (hER he)).symm
  obtain ⟨M, hMn, hMc, k, hMk⟩ := exists_normalPComplement_of_central (C := ↥C) hp2 fun x hx => by
    rw [mem_center_iff]
    intro y
    have hxE := hCp x x.2 (by simpa using congrArg Subtype.val hx)
    exact Subtype.ext (mem_centralizer_iff.1 y.2 x (hER hxE)).symm
  have hM3 : ∀ c : ↥C, c ^ 3 = 1 → c ∈ M := by
    intro c hc
    have h1 : orderOf (QuotientGroup.mk c : ↥C ⧸ M) ∣ p ^ k := by
      rw [← hMk]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk c : ↥C ⧸ M) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hc, QuotientGroup.mk_one])
    have hcop : Nat.Coprime 3 (p ^ k) := Nat.Coprime.pow_right k
      ((Nat.coprime_primes Nat.prime_three hp.out).2 (Ne.symm hp3))
    have h3 : orderOf (QuotientGroup.mk c : ↥C ⧸ M) = 1 :=
      Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥R) ≤ 2 := by
    refine csSup_le' fun n hn => ?_
    obtain ⟨A, _, hA, hAc⟩ := hn
    have hA' : IsElemAbelian p (A.map R.subtype) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨a', ha', hae⟩ := a.2
        obtain ⟨b', hb', hbe⟩ := b.2
        apply Subtype.ext
        show (a : D) * b = b * a
        rw [← hae, ← hbe]
        exact congrArg (fun z : ↥R => (z : D))
          (congrArg Subtype.val (hA.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
      · obtain ⟨x', hx', rfl⟩ := hx
        simpa using congrArg Subtype.val (hA.2 x' hx')
    have h1 := hr _ hA'
    rw [card_map_of_injective R.subtype_injective, hAc] at h1
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h1
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut hp2 hRp hrk
  set ρ : D →* GL (Fin 2) (ZMod p) := φ.comp (MulAut.conjNormal (H := R)) with hρdef
  have hρ3 : ∀ y : D, y ^ 3 = 1 → ρ y = 1 → y ∈ C := by
    intro y hy3 hy
    have hmem : MulAut.conjNormal (H := R) y ∈ φ.ker := hy
    rw [hφ] at hmem
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := MulAut ↥R) p) ⟨_, hmem⟩
    have hj' : (MulAut.conjNormal (H := R) y) ^ p ^ j = 1 := by
      simpa using congrArg Subtype.val hj
    have h3 : (MulAut.conjNormal (H := R) y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hcop : Nat.Coprime 3 (p ^ j) := Nat.Coprime.pow_right j
      ((Nat.coprime_primes Nat.prime_three hp.out).2 (Ne.symm hp3))
    have h1 : orderOf (MulAut.conjNormal (H := R) y) = 1 :=
      Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3)
        (orderOf_dvd_of_pow_eq_one hj'))
    rw [orderOf_eq_one_iff] at h1
    rw [mem_centralizer_iff]
    intro r hr
    have := congrArg (fun α : MulAut ↥R => ((α ⟨r, hr⟩ : ↥R) : D)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc r * y = y * r * y⁻¹ * y := by rw [this]
      _ = y * r := by group
  have hTρ : Nat.card ↥((G₁ ⊓ G₂).map ρ) ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (card_map_dvd _ ρ)).trans hT
  have hfrob : ∀ {G G' : Subgroup D}, IsGoldschmidtTriple G G' →
      (∀ x ∈ G, x ^ 3 = 1 → x ∈ C) → False := by
    intro G G' hG hGC
    set N := normalClosure {x | x ∈ G ∧ x ^ 3 = 1} with hNdef
    have hNM : N ≤ M.map C.subtype := by
      rw [hNdef, normalClosure, closure_le]
      intro y hy
      obtain ⟨x, ⟨hxG, hx3⟩, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
      have hyC : c * x * c⁻¹ ∈ C := (normal_centralizer (H := R)).conj_mem x (hGC x hxG hx3) c
      refine ⟨⟨_, hyC⟩, hM3 _ (Subtype.ext ?_), rfl⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hNp : Nat.Coprime (Nat.card ↥N) p := by
      have h1 : Nat.card ↥N ∣ Nat.card ↥M := by
        have := card_dvd_of_le hNM
        rwa [card_map_of_injective C.subtype_injective] at this
      exact Nat.Coprime.coprime_dvd_left h1 hMc
    have hLN : twoResidual G ≤ N := by
      rw [twoResidual_eq_oTwoUpper]
      refine (closure_le _).2 fun x hx => subset_normalClosure ⟨hx.1, ?_⟩
      exact orderOf_dvd_iff_pow_eq_one.1 (orderOf_dvd_three_of_odd hG hx.1 hx.2)
    have hRL : R ≤ twoResidual G' ⊔ N := by
      intro r hr
      have hro : Odd (orderOf r) := by
        obtain ⟨j, hj⟩ := hRp ⟨r, hr⟩
        have hj' : r ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hj')
        rw [hi]
        exact Odd.pow (hp.out.odd_of_ne_two hp2)
      have h1 : r ∈ twoResidual (⊤ : Subgroup D) := mem_twoResidual_of_odd (mem_top r) hro
      rw [twoResidual_top_eq hG] at h1
      exact (sup_le (hLN.trans le_sup_right) le_sup_left) h1
    apply hnc
    have hRbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      rw [mem_bot]
      obtain ⟨l, hl, n, hn, hln⟩ := mem_sup_of_normal_right.1 (hRL hr)
      obtain ⟨j, hj⟩ := hRp ⟨r, hr⟩
      have hj' : r ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
      obtain ⟨a, ha⟩ := exists_card_inf_eq hG
      have hcopG : Nat.Coprime (3 * 2 ^ a) (p ^ j) := Nat.Coprime.pow_right j
        (Nat.coprime_mul_iff_left.2 ⟨(Nat.coprime_primes Nat.prime_three hp.out).2 (Ne.symm hp3),
          Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))⟩)
      have hmk : (QuotientGroup.mk r : D ⧸ N) = 1 := by
        have hl' : l ∈ G' := twoResidual_le G' hl
        have hdl : orderOf l ∣ 3 * 2 ^ a := by
          have := orderOf_dvd_natCard (⟨l, hl'⟩ : ↥G')
          rwa [Subgroup.orderOf_mk, card_right hG, ha] at this
        have heq : (QuotientGroup.mk r : D ⧸ N) = QuotientGroup.mk l := by
          rw [← hln, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, mul_one]
        have h1 : orderOf (QuotientGroup.mk r : D ⧸ N) ∣ p ^ j :=
          orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hj', QuotientGroup.mk_one])
        have h2 : orderOf (QuotientGroup.mk r : D ⧸ N) ∣ 3 * 2 ^ a := by
          rw [heq]
          have := orderOf_map_dvd (QuotientGroup.mk' N) l
          rw [QuotientGroup.mk'_apply] at this
          exact this.trans hdl
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcopG.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
      have hrN : r ∈ N := (QuotientGroup.eq_one_iff r).1 hmk
      have h1 : orderOf r ∣ Nat.card ↥N := by
        have := orderOf_dvd_natCard (⟨r, hrN⟩ : ↥N)
        rwa [Subgroup.orderOf_mk] at this
      have h2 : orderOf r ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj'
      have hcop : Nat.Coprime (Nat.card ↥N) (p ^ j) := Nat.Coprime.pow_right j hNp
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
    rw [hRbot]
    infer_instance
  by_cases h₁ : ∃ x ∈ G₁, x ^ 3 = 1 ∧ ρ x ≠ 1
  · by_cases h₂ : ∃ x ∈ G₂, x ^ 3 = 1 ∧ ρ x ≠ 1
    · obtain ⟨x₁, hx₁, hx₁3, hρ₁⟩ := h₁
      obtain ⟨x₂, hx₂, hx₂3, hρ₂⟩ := h₂
      exact hQ (pCoreOf_eq_of_gl2 h ρ hTρ hx₁ hx₁3 hρ₁ hx₂ hx₂3 hρ₂)
    · exact hfrob h.symm fun x hx hx3 => hρ3 x hx3 (by
        by_contra hne
        exact h₂ ⟨x, hx, hx3, hne⟩)
  · exact hfrob h fun x hx hx3 => hρ3 x hx3 (by
      by_contra hne
      exact h₁ ⟨x, hx, hx3, hne⟩)


end CFSG.Quasithin.H13.U3
