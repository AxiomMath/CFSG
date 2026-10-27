module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.KS16ProofSecCore
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.Sporadic.Fi22.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16.KS1619SecProof

open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism quotientAutomorphism_apply
  prime_order_frattini_kernel_trivial)

section Exponent

variable {G : Type} [Group G] [Finite G]

theorem exists_generator {X : Subgroup G} (hX : Nat.card X = 13) :
    ∃ x₀ ∈ X, orderOf x₀ = 13 ∧ Subgroup.zpowers x₀ = X := by
  have hne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hX
    norm_num at hX
  obtain ⟨⟨x₀, hx₀⟩, hx₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx₁' : x₀ ≠ 1 := fun h => hx₁ (Subtype.ext h)
  have hdvd : orderOf x₀ ∣ 13 := hX ▸ Subgroup.orderOf_dvd_natCard X hx₀
  have h13 : orderOf x₀ = 13 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx₁'
    · exact h
  refine ⟨x₀, hx₀, h13, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₀) ?_
  rw [hX, Nat.card_zpowers, h13]

theorem zmod13_cube : ∀ a : ZMod 13, a ^ 3 = 1 → a ≠ 1 → a = 3 ∨ a = 9 := by decide

theorem conj_eq_pow_three_or_nine {x₀ c : G} (hx₀ : orderOf x₀ = 13) (hc3 : c ^ 3 = 1)
    (hcX : c ∈ Subgroup.normalizer (Subgroup.zpowers x₀ : Set G)) (hfree : c * x₀ * c⁻¹ ≠ x₀) :
    c * x₀ * c⁻¹ = x₀ ^ 3 ∨ c * x₀ * c⁻¹ = x₀ ^ 9 := by
  have hmem : c * x₀ * c⁻¹ ∈ Subgroup.zpowers x₀ :=
    (Subgroup.mem_normalizer_iff.mp hcX x₀).mp (Subgroup.mem_zpowers x₀)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  have hiter : ∀ j : ℕ, (MulAut.conj c ^ j) x₀ = x₀ ^ k ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow, MulAut.conj_apply, ← hk, ← pow_mul,
        pow_succ', mul_comm]
  have h3 : x₀ ^ k ^ 3 = x₀ ^ 1 := by
    rw [← hiter 3, ← map_pow, hc3, map_one, pow_one]
    rfl
  have hcube : (k : ZMod 13) ^ 3 = 1 := by
    have h := (pow_eq_pow_iff_modEq.mp h3)
    rw [hx₀] at h
    have h' := (ZMod.natCast_eq_natCast_iff (k ^ 3) 1 13).mpr h
    rwa [Nat.cast_pow, Nat.cast_one] at h'
  have hne : (k : ZMod 13) ≠ 1 := by
    intro h1
    apply hfree
    rw [← hk]
    have h := (ZMod.natCast_eq_natCast_iff k 1 13).mp (by rw [h1, Nat.cast_one])
    rw [← hx₀] at h
    rw [pow_eq_pow_iff_modEq.mpr h, pow_one]
  rcases zmod13_cube _ hcube hne with h | h
  · left
    rw [← hk]
    have h' := (ZMod.natCast_eq_natCast_iff k 3 13).mp (by rw [h]; rfl)
    rw [← hx₀] at h'
    exact pow_eq_pow_iff_modEq.mpr h'
  · right
    rw [← hk]
    have h' := (ZMod.natCast_eq_natCast_iff k 9 13).mp (by rw [h]; rfl)
    rw [← hx₀] at h'
    exact pow_eq_pow_iff_modEq.mpr h'

end Exponent

section Linear

variable {P : Type*} [Group P]

abbrev commGroupOf (h : ∀ a b : P, a * b = b * a) : CommGroup P :=
  { (inferInstance : Group P) with mul_comm := h }

variable (h : ∀ a b : P, a * b = b * a) (h2 : ∀ a : P, a ^ 2 = 1)

abbrev moduleOf : letI := commGroupOf h; Module (ZMod 2) (Additive P) :=
  letI := commGroupOf h
  AddCommMonoid.zmodModule (n := 2) fun v => by
    change Additive.ofMul ((Additive.toMul v) ^ 2) = Additive.ofMul 1
    rw [h2]

@[expose] noncomputable def linOf : letI := commGroupOf h; letI := moduleOf h h2;
    MulAut P →* Module.End (ZMod 2) (Additive P) :=
  letI := commGroupOf h
  letI := moduleOf h h2
  { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap 2
    map_one' := LinearMap.ext fun _ => rfl
    map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }

end Linear

theorem isElementaryAbelian_two_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hcomm : ∀ a b : B, a * b = b * a) (hsq : ∀ b : B, b ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 A :=
  { toIsMulCommutative := ⟨⟨fun a a' => e.injective (by rw [map_mul, map_mul, hcomm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      e.injective (by rw [map_pow, hsq, map_one]) }

section Coset

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset {p : ℕ} [Fact p.Prime] {B N : Subgroup G} (hB : IsPGroup p B)
    (hN : ¬ p ∣ Nat.card N) (hBN : B ≤ Subgroup.normalizer (N : Set G)) {k : G}
    (hk : ∀ b ∈ B, k⁻¹ * (b * k * b⁻¹) ∈ N) :
    ∃ y : G, k⁻¹ * y ∈ N ∧ ∀ b ∈ B, b * y = y * b := by
  set α : B →* MulAut G := MulAut.conj.comp B.subtype
  obtain ⟨y, hy, hyfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hB α N
    hN k).2 (by
      intro a x hx
      change k⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ N
      have h1 := hk a a.2
      have h2 : (a : G) * (k⁻¹ * x) * (a : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hBN a.2) _).mp hx
      have h3 := N.mul_mem h1 h2
      rwa [show k⁻¹ * ((a : G) * k * (a : G)⁻¹) * ((a : G) * (k⁻¹ * x) * (a : G)⁻¹) =
        k⁻¹ * ((a : G) * x * (a : G)⁻¹) by group] at h3)
  refine ⟨y, hy, fun b hb => ?_⟩
  have h1 : b * y * b⁻¹ = y := hyfix ⟨b, hb⟩
  calc b * y = (b * y * b⁻¹) * b := by group
    _ = y * b := by rw [h1]

end Coset

section Main

variable {G : Type} [Group G] [Finite G]

theorem not_thirteen_dvd {Q : Subgroup G} (hQ : IsPGroup 2 Q) : ¬ 13 ∣ Nat.card Q := by
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  rw [hm]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((by norm_num : Nat.Prime 13).dvd_of_dvd_pow h)
  omega

theorem mem_centralizer_of_quotient_trivial {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x₀ : G}
    (hx₀ : orderOf x₀ = 13) (hxQ : x₀ ∈ Subgroup.normalizer (Q : Set G))
    (htriv : quotientAutomorphism (frattini Q) (Q.normalizerMonoidHom ⟨x₀, hxQ⟩) = 1) :
    x₀ ∈ Subgroup.centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set ψ := Q.normalizerMonoidHom ⟨x₀, hxQ⟩ with hψ
  have hψ13 : ψ ^ 13 = 1 := by
    rw [hψ, ← map_pow]
    have : (⟨x₀, hxQ⟩ : Subgroup.normalizer (Q : Set G)) ^ 13 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hx₀, pow_orderOf_eq_one]; rfl)
    rw [this, map_one]
  have hψ1 : ψ = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp (orderOf_dvd_of_pow_eq_one hψ13)
      with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact prime_order_frattini_kernel_trivial 13 ψ h (not_thirteen_dvd hQ) htriv
  have hker : (⟨x₀, hxQ⟩ : Subgroup.normalizer (Q : Set G)) ∈ Q.normalizerMonoidHom.ker := hψ1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

end Main

end CFSG.RankThree.PartTwo.Sec16.KS1619SecProof

namespace CFSG.RankThree.PartTwo.Sec16

open KS1619SecProof
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism quotientAutomorphism_apply)

theorem ks1619Sec : KS1619Sec := by
  intro G _ _ Q X c hQ hX13 hXQ hcQ hcX hc3 hfree hXC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, hx₀X, hx₀, hzX⟩ := exists_generator hX13
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx₀
    norm_num at hx₀
  have hcx₀ : c * x₀ * c⁻¹ = x₀ ^ 3 ∨ c * x₀ * c⁻¹ = x₀ ^ 9 :=
    conj_eq_pow_three_or_nine hx₀ hc3 (hzX ▸ hcX) fun h => hx₀1 (hfree x₀ hx₀X h)
  have hxQ : x₀ ∈ Subgroup.normalizer (Q : Set G) := hXQ hx₀X
  obtain ⟨-, hcomm, hsq⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary (p := 2) hQ
  set V := ↥Q ⧸ frattini ↥Q with hV
  let _ : CommGroup V := commGroupOf hcomm
  let _ : Module (ZMod 2) (Additive V) := moduleOf hcomm hsq
  set τ : Subgroup.normalizer (Q : Set G) →* MulAut V :=
    (quotientAutomorphism (frattini ↥Q)).comp Q.normalizerMonoidHom with hτ
  set ρ : Subgroup.normalizer (Q : Set G) →* Module.End (ZMod 2) (Additive V) :=
    (linOf hcomm hsq).comp τ with hρ
  set gx : Subgroup.normalizer (Q : Set G) := ⟨x₀, hxQ⟩ with hgx
  set gc : Subgroup.normalizer (Q : Set G) := ⟨c, hcQ⟩ with hgc
  have hx13 : ρ gx ^ 13 = 1 := by
    rw [← map_pow]
    have : gx ^ 13 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hx₀, pow_orderOf_eq_one]; rfl)
    rw [this, map_one]
  have hc3' : ρ gc ^ 3 = 1 := by
    rw [← map_pow]
    have : gc ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hc3]; rfl)
    rw [this, map_one]
  have hcx : ρ gc * ρ gx = ρ gx ^ 3 * ρ gc ∨ ρ gc * ρ gx = ρ gx ^ 9 * ρ gc := by
    rcases hcx₀ with h | h
    · left
      rw [← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by
        change c * x₀ = x₀ ^ 3 * c
        rw [← h, inv_mul_cancel_right])
    · right
      rw [← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by
        change c * x₀ = x₀ ^ 9 * c
        rw [← h, inv_mul_cancel_right])
  have hx1 : ρ gx ≠ 1 := by
    intro h1
    have hτ1 : τ gx = 1 := by
      ext v
      have h := congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) h1
      exact h
    have hcen := mem_centralizer_of_quotient_trivial hQ hx₀ hxQ hτ1
    have hbot : x₀ ∈ X ⊓ Subgroup.centralizer (Q : Set G) := ⟨hx₀X, hcen⟩
    rw [hXC, Subgroup.mem_bot] at hbot
    exact hx₀1 hbot
  have h16 := sixteen_le_card_fixed' hx13 hc3' hcx hx1
  set F : Subgroup V := MonoidHom.eqLocus (τ gc).toMonoidHom (MonoidHom.id V) with hF
  have hcardF : Nat.card {v : Additive V // ρ gc v = v} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => Iff.rfl)
  have h16F : 16 ≤ Nat.card F := hcardF ▸ h16
  have hVp : IsPGroup 2 V := hQ.to_quotient _
  obtain ⟨m, hm⟩ := (hVp.to_subgroup F).exists_card_eq
  rw [hm] at h16F
  have hm4 : 4 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 4 ∣ Nat.card F := hm ▸ Nat.pow_dvd_pow 2 hm4
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set W : Subgroup V := H.map F.subtype with hW
  have hWF : W ≤ F := Subgroup.map_subtype_le H
  have hWcard : Nat.card W = 2 ^ 4 := by
    rw [hW, Subgroup.card_map_of_injective F.subtype_injective, hH]
  set π := QuotientGroup.mk' (frattini ↥Q) with hπ
  set E : Subgroup G := (W.comap π).map Q.subtype ⊓ Subgroup.centralizer ({c} : Set G) with hE
  set Nn : Subgroup G := (frattini ↥Q).map Q.subtype ⊓ Subgroup.centralizer ({c} : Set G)
    with hNn
  have hEQ : E ≤ Q := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hNE : Nn ≤ E := by
    rintro g ⟨⟨q, hq, rfl⟩, hgc⟩
    refine ⟨⟨q, ?_, rfl⟩, hgc⟩
    change π q ∈ W
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff q).mpr hq]
    exact W.one_mem
  have hEQc : E ≤ Q ⊓ Subgroup.centralizer ({c} : Set G) := le_inf hEQ inf_le_right
  have hπW : ∀ e : E, π (Subgroup.inclusion hEQ e) ∈ W := by
    intro e
    obtain ⟨q, hq, hqe⟩ := e.2.1
    have h : Subgroup.inclusion hEQ e = q := Subtype.ext hqe.symm
    rw [h]
    exact hq
  set ψ : E →* W := (π.comp (Subgroup.inclusion hEQ)).codRestrict W hπW with hψ
  have hNf : ¬ 3 ∣ Nat.card ((frattini ↥Q).map Q.subtype) := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective]
    obtain ⟨j, hj⟩ := (hQ.to_subgroup (frattini ↥Q)).exists_card_eq
    rw [hj]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hBp : IsPGroup 3 (Subgroup.zpowers c) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hcNf : c ∈ Subgroup.normalizer (((frattini ↥Q).map Q.subtype : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨q, hq, rfl⟩ := hg
    refine ⟨Q.normalizerMonoidHom gc q, ?_, rfl⟩
    exact (Subgroup.characteristic_iff_le_comap.mp inferInstance (Q.normalizerMonoidHom gc)) hq
  have hsurj : Function.Surjective ψ := by
    rintro ⟨w, hwW⟩
    have hwF : τ gc w = w := hWF hwW
    obtain ⟨q₀, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥Q) w
    have hpowfix : ∀ n : ℕ, (τ gc ^ n) (π q₀) = π q₀ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hwF, ih]
    have hk : ∀ b ∈ Subgroup.zpowers c,
        (q₀ : G)⁻¹ * (b * q₀ * b⁻¹) ∈ (frattini ↥Q).map Q.subtype := by
      intro b hb
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hb)
      have h1 : τ (gc ^ n) (π q₀) = π q₀ := by rw [map_pow, hpowfix]
      rw [hτ, MonoidHom.comp_apply, hπ, quotientAutomorphism_apply, eq_comm,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      refine ⟨_, h1, ?_⟩
      rfl
    obtain ⟨y, hy, hyc⟩ := exists_fixed_mem_coset hBp hNf (Subgroup.zpowers_le.mpr hcNf) hk
    obtain ⟨φ, hφ, hφy⟩ := hy
    have hyQ : y ∈ Q := by
      have h1 : y = (q₀ : G) * ((q₀ : G)⁻¹ * y) := by group
      rw [h1, ← hφy]
      exact Q.mul_mem q₀.2 φ.2
    have hycen : y ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hyc c (Subgroup.mem_zpowers c)).symm
    have hπy : π ⟨y, hyQ⟩ = π q₀ := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
      have h1 : q₀⁻¹ * ⟨y, hyQ⟩ = φ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hφy.symm)
      rw [h1]
      exact hφ
    refine ⟨⟨y, ⟨⟨y, hyQ⟩, ?_, rfl⟩, hycen⟩, ?_⟩
    · change π ⟨y, hyQ⟩ ∈ W
      rw [hπy]
      exact hwW
    · apply Subtype.ext
      exact hπy
  have hker : ψ.ker = Nn.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      have h1 : π (Subgroup.inclusion hEQ e) = 1 := congrArg Subtype.val he
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨⟨_, h1, rfl⟩, e.2.2⟩
    · rintro ⟨⟨φ, hφ, hφe⟩, -⟩
      apply Subtype.ext
      change π (Subgroup.inclusion hEQ e) = 1
      have h1 : Subgroup.inclusion hEQ e = φ := Subtype.ext hφe.symm
      rw [h1, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hφ
  have hnormal : (Nn.subgroupOf E).Normal := hker ▸ ψ.normal_ker
  refine ⟨E, Nn, hNE, hEQc, hnormal, ?_⟩
  let e : ↥E ⧸ Nn.subgroupOf E ≃* W :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  refine ⟨isElementaryAbelian_two_of_mulEquiv e (fun a b => Subtype.ext (hcomm a b))
    (fun b => Subtype.ext (hsq b)), ?_⟩
  rw [Nat.card_congr e.toEquiv, hWcard]

end CFSG.RankThree.PartTwo.Sec16
