module

public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c2
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Outer

theorem comm_of_card_commutator_eq_one {A : Type*} [Group A] (h : Nat.card (commutator A) = 1) :
    ∀ a b : A, a * b = b * a := by
  intro a b
  have hbot : commutator A = ⊥ := Subgroup.card_eq_one.1 h
  have hm : ⁅a, b⁆ ∈ commutator A := by
    change ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hbot, Subgroup.mem_bot] at hm
  exact commutatorElement_eq_one_iff_mul_comm.1 hm

theorem outer_comm_of_rankOneConcl {J : Type} [Group J] [Group.IsPerfect J]
    (h : RankOneConcl (J ⧸ Subgroup.center J)) : ∀ a b : Outer J, a * b = b * a := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h⟩ | h
  · exact (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
      J 2 2 n h).2.2.2 rfl
  · obtain ⟨-, hd, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.OuterDerived.unitary_perfect_cover_outer_derived_diagonal_bound
        J 3 2 m h
    have h1 : Nat.gcd 3 (2 ^ m + 1) = 1 := by
      have := R3c.two_pow_mod_three_of_even hm
      have h3 : ¬ 3 ∣ 2 ^ m + 1 := by omega
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)).symm
    rw [h1] at hd
    exact comm_of_card_commutator_eq_one (Nat.dvd_one.1 hd)
  · obtain ⟨-, hd, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
        J 3 2 1 h
    have h1 : Nat.gcd 3 (2 ^ 1 - 1) = 1 := by norm_num
    rw [h1] at hd
    exact comm_of_card_commutator_eq_one (Nat.dvd_one.1 hd)

end Outer

section S3S3

theorem exists_commutator_perm_three : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    ∃ a b : Equiv.Perm (Fin 3), σ = a * b * a⁻¹ * b⁻¹ := by
  decide +kernel

theorem exists_commutator_perm_three_prod {g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)}
    (hg : g ^ 3 = 1) : ∃ a b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), g = a * b * a⁻¹ * b⁻¹ := by
  have h1 : g.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hg
  have h2 : g.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hg
  obtain ⟨a₁, b₁, hab₁⟩ := exists_commutator_perm_three g.1 h1
  obtain ⟨a₂, b₂, hab₂⟩ := exists_commutator_perm_three g.2 h2
  exact ⟨(a₁, a₂), (b₁, b₂), Prod.ext (by simpa using hab₁) (by simpa using hab₂)⟩

theorem pow_three_eq_one_of_odd_orderOf {g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)}
    (hg : Odd (orderOf g)) : g ^ 3 = 1 := by
  have h6 : g ^ 6 = 1 := by
    have : ∀ x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), x ^ 6 = 1 := by decide +kernel
    exact this g
  have hm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hgcd := pow_gcd_eq_one.2 ⟨hm, h6⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd (orderOf g) 6 := ⟨_, rfl⟩
  rw [← hd] at hgcd
  have hd1 : d ∣ 6 := hd ▸ Nat.gcd_dvd_right _ _
  have hd2 : Odd d := hd ▸ hg.of_dvd_nat (Nat.gcd_dvd_left _ _)
  have hd3 : d ∣ 3 := by
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd1
    rw [Nat.odd_iff] at hd2
    interval_cases d <;> omega
  obtain ⟨k, hk⟩ := hd3
  have h3 : g ^ 3 = g ^ (d * k) := congrArg (fun n => g ^ n) hk
  rw [pow_mul, hgcd, one_pow] at h3
  exact h3

end S3S3

section Core

variable {G : Type} [Group G] [Finite G]

theorem rho_eq_one_of_s3s3 {H Y S : Subgroup G} {A : Type} [Group A] (hA : ∀ a b : A, a * b = b * a)
    (hYH : Y ≤ H) (hSH : S ≤ H) (hHYS : H ≤ Y ⊔ S) (hY : oTwoUpper Y = Y) (hS : IsPGroup 2 ↥S)
    (ψ : ↥H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (oTwoPhi H).subgroupOf H) (ρ : ↥H →* A) :
    ∀ (y : G) (hy : y ∈ Y), ρ ⟨y, hYH hy⟩ = 1 := by
  classical
  have hK'H : (ρ.ker).map H.subtype ⊔ S ≤ H := sup_le (Subgroup.map_subtype_le _) hSH
  have hodd : ∀ y : G, y ∈ Y → Odd (orderOf y) → y ∈ ((ρ.ker).map H.subtype ⊔ S) ⊔ oTwoPhi H := by
    intro y hy hyo
    have hyH : y ∈ H := hYH hy
    have hord : Odd (orderOf (⟨y, hyH⟩ : ↥H)) := by
      have : orderOf (⟨y, hyH⟩ : ↥H) = orderOf y := Subgroup.orderOf_mk _ _
      rwa [this]
    have hψ3 : ψ ⟨y, hyH⟩ ^ 3 = 1 := by
      refine pow_three_eq_one_of_odd_orderOf (hord.of_dvd_nat ?_)
      exact orderOf_map_dvd ψ _
    obtain ⟨a, b, hab⟩ := exists_commutator_perm_three_prod hψ3
    obtain ⟨a', rfl⟩ := hψs a
    obtain ⟨b', rfl⟩ := hψs b
    obtain ⟨k, hkdef⟩ : ∃ k : ↥H, k = a' * b' * a'⁻¹ * b'⁻¹ := ⟨_, rfl⟩
    have hρk : ρ k = 1 := by
      rw [hkdef, map_mul, map_mul, map_mul, map_inv, map_inv, hA (ρ a') (ρ b')]
      group
    have hkK : k ∈ ρ.ker := hρk
    have hr : k⁻¹ * ⟨y, hyH⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkdef, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← hab]
      group
    rw [hψk, Subgroup.mem_subgroupOf] at hr
    have hyk : y = (k : G) * ((k⁻¹ * ⟨y, hyH⟩ : ↥H) : G) := by
      change y = (k : G) * ((k : G)⁻¹ * y)
      exact (mul_inv_cancel_left (k : G) y).symm
    rw [hyk]
    exact Subgroup.mul_mem_sup (Subgroup.mem_sup_left ⟨k, hkK, rfl⟩) hr
  have hYle : Y ≤ ((ρ.ker).map H.subtype ⊔ S) ⊔ oTwoPhi H := by
    rw [← hY]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hy, hyo⟩
    exact hodd y hy hyo
  have hHle : H ≤ ((ρ.ker).map H.subtype ⊔ S) ⊔ oTwoPhi H :=
    hHYS.trans (sup_le hYle (le_sup_of_le_left le_sup_right))
  have hng := B2F.exists_mul_of_le_sup_oTwoPhi hK'H hHle
  have hO2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hO2H : CFSG.Open.pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.card S * Nat.card (CFSG.Open.pCoreOf 2 H) := ⟨_, rfl⟩
  let Z : Subgroup ↥H :=
    { carrier := {h | ρ h ^ M = 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a ^ M = 1 := ha
        have hb' : ρ b ^ M = 1 := hb
        show ρ (a * b) ^ M = 1
        rw [map_mul, (show Commute (ρ a) (ρ b) from hA _ _).mul_pow, ha', hb', mul_one]
      inv_mem' := by
        intro a ha
        have ha' : ρ a ^ M = 1 := ha
        show ρ a⁻¹ ^ M = 1
        rw [map_inv, inv_pow, ha', inv_one] }
  have hKZ : ρ.ker ≤ Z := fun h hh => by
    show ρ h ^ M = 1
    rw [hh, one_pow]
  have hSZ : ∀ (x : G) (hx : x ∈ S), (⟨x, hSH hx⟩ : ↥H) ∈ Z := by
    intro x hx
    show ρ ⟨x, hSH hx⟩ ^ M = 1
    rw [← map_pow]
    have : (⟨x, hSH hx⟩ : ↥H) ^ M = 1 := by
      apply Subtype.ext
      have h1 : x ^ Nat.card S = 1 := by
        have := pow_card_eq_one' (G := ↥S) (x := ⟨x, hx⟩)
        exact congrArg Subtype.val this
      change x ^ M = 1
      rw [hM, pow_mul, h1, one_pow]
    rw [this, map_one]
  have hOZ : ∀ (x : G) (hx : x ∈ CFSG.Open.pCoreOf 2 H), (⟨x, hO2H hx⟩ : ↥H) ∈ Z := by
    intro x hx
    show ρ ⟨x, hO2H hx⟩ ^ M = 1
    rw [← map_pow]
    have : (⟨x, hO2H hx⟩ : ↥H) ^ M = 1 := by
      apply Subtype.ext
      have h1 : x ^ Nat.card (CFSG.Open.pCoreOf 2 H) = 1 := by
        have := pow_card_eq_one' (G := ↥(CFSG.Open.pCoreOf 2 H)) (x := ⟨x, hx⟩)
        exact congrArg Subtype.val this
      change x ^ M = 1
      rw [hM, mul_comm, pow_mul, h1, one_pow]
    rw [this, map_one]
  have hK'Z : (ρ.ker).map H.subtype ⊔ S ≤ Z.map H.subtype := by
    refine sup_le ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, hKZ hk, rfl⟩
    · intro x hx
      exact ⟨⟨x, hSH hx⟩, hSZ x hx, rfl⟩
  have hyodd : ∀ (y : G) (hy : y ∈ Y), Odd (orderOf y) → ρ ⟨y, hYH hy⟩ = 1 := by
    intro y hy hyo
    obtain ⟨k, hk, o, ho, hko⟩ := hng y (hYH hy)
    obtain ⟨kz, hkz, hkzk⟩ := hK'Z hk
    have hoZ := hOZ o ho
    have hyZ : (⟨y, hYH hy⟩ : ↥H) ∈ Z := by
      have : (⟨y, hYH hy⟩ : ↥H) = kz * ⟨o, hO2H ho⟩ := by
        apply Subtype.ext
        change y = (kz : G) * o
        have hkzk' : (kz : G) = k := hkzk
        rw [hkzk']
        exact hko
      rw [this]
      exact Z.mul_mem hkz hoZ
    obtain ⟨c, hc⟩ : ∃ c : ℕ, M = 2 ^ c := by
      obtain ⟨a, ha⟩ := hS.exists_card_eq
      obtain ⟨b, hb⟩ := hO2.exists_card_eq
      exact ⟨a + b, by rw [hM, ha, hb, pow_add]⟩
    have h1 : ρ ⟨y, hYH hy⟩ ^ 2 ^ c = 1 := by
      have : ρ ⟨y, hYH hy⟩ ^ M = 1 := hyZ
      rwa [hc] at this
    have hordy : Odd (orderOf (ρ ⟨y, hYH hy⟩)) := by
      refine hyo.of_dvd_nat ?_
      refine (orderOf_map_dvd ρ _).trans ?_
      rw [Subgroup.orderOf_mk]
    have h3 : orderOf (ρ ⟨y, hYH hy⟩) ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one h1
    have hcop : Nat.Coprime (orderOf (ρ ⟨y, hYH hy⟩)) (2 ^ c) :=
      Nat.Coprime.pow_right c (Nat.coprime_two_left.2 hordy).symm
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h3)
  intro y hy
  have hYk : Y ≤ (ρ.ker).map H.subtype := by
    rw [← hY]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hy, hyo⟩
    exact ⟨⟨y, hYH hy⟩, hyodd y hy hyo, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hYk hy
  have : z = ⟨y, hYH hy⟩ := Subtype.ext hzy
  rw [← this]
  exact hz

end Core

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_conjAct_apply' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : ↥V) :
    ((conjAct V g x : ↥V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

theorem input15337OneInner_of_facts (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Input15337OneInner := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hrk hconcl
  have hLc : L ∈ cComp I := c.c33.mem
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  have hOut : ∀ a b : Outer ↥L, a * b = b * a := outer_comm_of_rankOneConcl hconcl
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hLc
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L (Sgp153 T V₁)
    rwa [← hL0] at this
  have hHN : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYN hSN
  let ρ : ↥(Yp ⊔ Sgp153 T V₁) →* Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp ((conjAct L).comp (Subgroup.inclusion hHN))
  obtain ⟨ψ, hψs, hψk⟩ := c.s3s3
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts11.sylow.2.1
  have hYodd : oTwoUpper Yp = Yp := c.hyp.oTwoUpper_eq
  have key := rho_eq_one_of_s3s3 hOut (le_sup_left : Yp ≤ Yp ⊔ Sgp153 T V₁) le_sup_right le_rfl
    hYodd hS2 ψ hψs hψk ρ
  intro y hy
  have h1 : ρ ⟨y, (le_sup_left : Yp ≤ Yp ⊔ Sgp153 T V₁) hy⟩ = 1 := key y hy
  have hmem : conjAct L ⟨y, hYN hy⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨l, hl⟩ := hmem
  refine ⟨(l : G), l.2, fun x hx => ?_⟩
  have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨x, hx⟩ : ↥L) : G)) hl
  simp only [MulAut.conj_apply, coe_conjAct_apply'] at h2
  have h3 : y * x * y⁻¹ = (l : G) * x * (l : G)⁻¹ := h2.symm
  rw [h3, mul_inv_cancel]
  exact (CFSG.Open.pCoreOf 2 L).one_mem

end Main

end CFSG.Quasithin.R3c3
