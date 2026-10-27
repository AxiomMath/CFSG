module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofA7Z3
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofOneTwoLinAlg
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CritProof
open scoped IsMulCommutative

@[expose] def perm012 : Equiv.Perm (Fin 7) := Equiv.swap 0 2 * Equiv.swap 0 1

@[expose] def perm465 : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 4 6

@[expose] def permG₁ : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 4 * Equiv.swap 1 6 * Equiv.swap 1 2 * Equiv.swap 1 5

@[expose] def permG₂ : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 5 6

theorem perm012_mem : perm012 ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign perm012 = 1
  rw [perm012, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1)]
  norm_num

theorem perm465_mem : perm465 ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign perm465 = 1
  rw [perm465, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5),
    Equiv.Perm.sign_swap (by decide : (4 : Fin 7) ≠ 6)]
  norm_num

theorem permG₁_mem : permG₁ ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign permG₁ = 1
  rw [permG₁, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 4),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 6),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 7) ≠ 5)]
  norm_num

theorem permG₂_mem : permG₂ ∈ alternatingGroup (Fin 7) := by
  change Equiv.Perm.sign permG₂ = 1
  rw [permG₂, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (5 : Fin 7) ≠ 6)]
  norm_num

@[expose] def a7w : alternatingGroup (Fin 7) := ⟨perm012, perm012_mem⟩

@[expose] def a7c : alternatingGroup (Fin 7) := ⟨perm465, perm465_mem⟩

@[expose] def a7g₁ : alternatingGroup (Fin 7) := ⟨permG₁, permG₁_mem⟩

@[expose] def a7g₂ : alternatingGroup (Fin 7) := ⟨permG₂, permG₂_mem⟩

theorem a7w_cube : a7w ^ 3 = 1 := Subtype.ext (by decide)

theorem a7c_cube : a7c ^ 3 = 1 := Subtype.ext (by decide)

theorem a7w_c : a7w * a7c = a7c * a7w := Subtype.ext (by decide)

theorem a7c_a : a7c * a7a = a7a * a7c := Subtype.ext (by decide)

theorem a7c_b : a7c * a7b = a7b * a7c := Subtype.ext (by decide)

theorem a7w_a : a7w * a7a * a7w⁻¹ = a7a * a7b := Subtype.ext (by decide)

theorem a7w_b : a7w * a7b * a7w⁻¹ = a7a := Subtype.ext (by decide)

theorem a7w_inv_a : a7w⁻¹ * a7a * a7w = a7b := Subtype.ext (by decide)

theorem a7w_inv_b : a7w⁻¹ * a7b * a7w = a7a * a7b := Subtype.ext (by decide)

theorem a7g₁_conj : a7g₁ * a7c * a7g₁⁻¹ = a7w := Subtype.ext (by decide)

theorem a7g₂_conj : a7g₂ * a7c * a7g₂⁻¹ = a7c⁻¹ := Subtype.ext (by decide)

section Lift

variable {X : Type} [Group X] [Finite X] {T : Type*} [Group T] (ψ : X →* T) {O : Subgroup X}

omit [Finite X] in
theorem isPGroup_zpowers_of_pow {p : ℕ} {b : X} (hb : b ^ p = 1) :
    IsPGroup p (Subgroup.zpowers b) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [pow_one, Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hb, one_zpow, OneMemClass.coe_one]

omit [Finite X] in
theorem eq_one_of_three_pow {x : X} {r : ℕ} (hx : x ^ 3 ^ r = 1) (hxO : x ∈ O)
    (hO3 : ¬ 3 ∣ Nat.card O) : x = 1 := by
  have h1 : orderOf x ∣ 3 ^ r := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk x hxO]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ r) (Nat.card O) :=
    Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hO3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_three_part {a : T} (ha : a ^ 3 = 1) (y' : X) (hy' : ψ y' = a) :
    ∃ y ∈ Subgroup.zpowers y', (∃ r : ℕ, y ^ 3 ^ r = 1) ∧ ψ y = a := by
  obtain ⟨r, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y').ne' 3 (by norm_num)
  refine ⟨y' ^ (m * m), Subgroup.pow_mem _ (Subgroup.mem_zpowers y') _, ⟨r, ?_⟩, ?_⟩
  · rw [← pow_mul, show m * m * 3 ^ r = (3 ^ r * m) * m by ring, ← hn, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · have hmm : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, hy', ← Nat.div_add_mod (m * m) 3, hmm, pow_add, pow_mul, ha, one_pow, one_mul,
      pow_one]

omit [Finite X] in
theorem exists_lift_commute (hker : ∀ x, ψ x = 1 ↔ x ∈ O) (hO3 : ¬ 3 ∣ Nat.card O) {b : X}
    (hb : b ^ 3 = 1) (l : X) (hl : ψ l * ψ b = ψ b * ψ l) :
    ∃ l' : X, l' * b = b * l' ∧ ψ l' = ψ l := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON : O.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [← hker] at hn ⊢
    rw [map_mul, map_mul, hn, mul_one, map_inv, mul_inv_cancel]
  have hU := isPGroup_zpowers_of_pow hb
  have hNtop : Subgroup.normalizer (O : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hON
  obtain ⟨v, hv, hfix⟩ := PartOne.Sec159.exists_fixed_in_coset hU hO3
    (fun u _ => hNtop ▸ Subgroup.mem_top u) (hNtop ▸ Subgroup.mem_top l)
    (fun u hu => by
      rw [← hker]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hc : ψ l * ψ (b ^ k) = ψ (b ^ k) * ψ l := by
        rw [map_zpow]
        exact (Commute.zpow_right hl k)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group)
  refine ⟨l * v, ?_, ?_⟩
  · have := hfix b (Subgroup.mem_zpowers b)
    calc l * v * b = b * (l * v) * b⁻¹ * b := by rw [this]
      _ = b * (l * v) := by group
  · rw [map_mul, (hker v).mpr hv, mul_one]

theorem exists_conj_of_three (hker : ∀ x, ψ x = 1 ↔ x ∈ O) (hO3 : ¬ 3 ∣ Nat.card O) {x y : X}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : ψ x = ψ y) : ∃ h ∈ O, h * x * h⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ h ∈ O, y * h * x⁻¹ ∈ O := fun h hh => by
    rw [← hker] at hh ⊢
    rw [map_mul, map_mul, hh, mul_one, map_inv, hxy, mul_inv_cancel]
  have hmem' : ∀ h ∈ O, y⁻¹ * h * x ∈ O := fun h hh => by
    rw [← hker] at hh ⊢
    rw [map_mul, map_mul, hh, mul_one, map_inv, hxy, inv_mul_cancel]
  let σ : Equiv.Perm O :=
    { toFun := fun h => ⟨y * h * x⁻¹, hmem h h.2⟩
      invFun := fun h => ⟨y⁻¹ * h * x, hmem' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext h
    simp only [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq]
    change y * (y * (y * h * x⁻¹) * x⁻¹) * x⁻¹ = h
    have hx' : x⁻¹ * x⁻¹ * x⁻¹ = 1 := by rw [← pow_three', inv_pow, hx, inv_one]
    have hy' : y * y * y = 1 := by rw [← pow_three', hy]
    calc y * (y * (y * (h : X) * x⁻¹) * x⁻¹) * x⁻¹ = (y * y * y) * h * (x⁻¹ * x⁻¹ * x⁻¹) := by
          group
      _ = h := by rw [hx', hy', one_mul, mul_one]
  have : Fintype O := Fintype.ofFinite O
  have hcard : ¬ 3 ∣ Fintype.card O := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨h, hh⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  have h1 : y * (h : X) * x⁻¹ = h := congrArg Subtype.val hh
  refine ⟨h, h.2, ?_⟩
  calc (h : X) * x * (h : X)⁻¹ = y * (h : X) * x⁻¹ * x * (h : X)⁻¹ := by rw [h1]
    _ = y := by group

end Lift

theorem finrank_eigenspace_conj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A P Q : Module.End K V) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (μ : K) : Module.finrank K (Module.End.eigenspace (P * A * Q) μ) =
      Module.finrank K (Module.End.eigenspace A μ) := by
  have hPinj : Function.Injective P := fun v w h => by
    have := congrArg Q h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hQP, Module.End.one_apply,
      Module.End.one_apply] at this
  have hQinj : Function.Injective Q := fun v w h => by
    have := congrArg P h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hPQ, Module.End.one_apply,
      Module.End.one_apply] at this
  apply le_antisymm
  · refine A4Data.finrank_le_of_mapsTo hQinj fun v hv => ?_
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have := congrArg Q hv
    rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply Q P,
      hQP, Module.End.one_apply, map_smul] at this
  · refine A4Data.finrank_le_of_mapsTo hPinj fun v hv => ?_
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply Q P, hQP,
      Module.End.one_apply, hv, map_smul]

theorem false_of_alt7_local {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ}
    {C : Subgroup (CFSG.pCore p L)} (hcrit : Crit135 L p C) (ψL : L →* alternatingGroup (Fin 7))
    (hψ : Function.Surjective ψL) (hker : ∀ x, ψL x = 1 ↔ x ∈ CFSG.oddCore L)
    (hO3 : ¬ 3 ∣ Nat.card (CFSG.oddCore L)) : False := by
  classical
  have : Fact p.Prime := ⟨hcrit.prime⟩
  set Dg := (omegaOneCore p C).map L.subtype with hDg
  have hDD : DData p Dg := dData_of_crit135 hcrit
  have := hDD.isElementaryAbelian
  have hDn : (omegaOneCore p C).Normal := hcrit.criticalAt.normal
  have hLN : L ≤ Subgroup.normalizer (Dg : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨l, hl⟩ * d * ⟨l, hl⟩⁻¹, hDn.conj_mem d hd _, rfl⟩
    · rintro ⟨d, hd, hdg⟩
      refine ⟨⟨l, hl⟩⁻¹ * d * ⟨l, hl⟩⁻¹⁻¹, hDn.conj_mem d hd _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hdg ⊢
      rw [hdg]
      group
  set O := CFSG.oddCore L with hOdef
  have hOodd : Odd (Nat.card O) := CFSG.ABGDGroups.odd_card_oddCore L
  set ρ : L →* Module.End (ZMod p) (Additive (Dg ⧸ frattini Dg)) :=
    (frattiniLinN p Dg).comp (Subgroup.inclusion hLN) with hρ
  have hρconj : ∀ (k x : L) (μ : ZMod p),
      Module.finrank (ZMod p) (Module.End.eigenspace (ρ (k * x * k⁻¹)) μ) =
        Module.finrank (ZMod p) (Module.End.eigenspace (ρ x) μ) := by
    intro k x μ
    rw [map_mul, map_mul]
    exact finrank_eigenspace_conj _ _ _ (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one]) μ
  obtain ⟨b', hb'⟩ := hψ a7c
  obtain ⟨b, -, ⟨r, hbr⟩, hψb⟩ := exists_three_part ψL a7c_cube b' hb'
  have hb3 : b ^ 3 = 1 := by
    refine eq_one_of_three_pow (r := r) ?_ ((hker _).mp (by rw [map_pow, hψb, a7c_cube])) hO3
    rw [← pow_mul, mul_comm, pow_mul, hbr, one_pow]
  obtain ⟨w', hw'⟩ := hψ a7w
  obtain ⟨w'', hw''b, hψw''⟩ := exists_lift_commute ψL hker hO3 hb3 w'
    (by rw [hw', hψb, a7w_c])
  obtain ⟨ω, hωz, ⟨r', hωr⟩, hψω⟩ := exists_three_part ψL a7w_cube w'' (hψw''.trans hw')
  have hω3 : ω ^ 3 = 1 := by
    refine eq_one_of_three_pow (r := r') ?_ ((hker _).mp (by rw [map_pow, hψω, a7w_cube])) hO3
    rw [← pow_mul, mul_comm, pow_mul, hωr, one_pow]
  have hωb : ω * b = b * ω := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hωz
    exact (Commute.zpow_left hw''b k)
  set P : Subgroup L := Subgroup.centralizer ({b} : Set L) ⊓ kleinA7.comap ψL with hP
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 h3
    have hxk : ψL (x : L) ∈ kleinA7 := (Subgroup.mem_inf.mp x.2).2
    have hx3 : (x : L) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, OneMemClass.coe_one]
    have hψx : ψL (x : L) = 1 := by
      obtain ⟨k, hk⟩ := isPGroup_kleinA7 ⟨ψL x, hxk⟩
      have h1 : orderOf (ψL (x : L)) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx3,
        map_one])
      have h2 : orderOf (ψL (x : L)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        simpa using congrArg Subtype.val hk)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k
        (by norm_num)) h1 h2)
    have h1 := eq_one_of_three_pow (r := 1) (by rw [pow_one, hx3]) ((hker _).mp hψx) hO3
    have h2 : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [hx] at h2
    exact absurd h2 (by norm_num)
  have hωP : ω ∈ Subgroup.normalizer (P : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hP, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap]
    have hωinv : ω⁻¹ * b = b * ω⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hωb, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : ∀ k ∈ kleinA7, ψL ω * k * (ψL ω)⁻¹ ∈ kleinA7 := by
      intro k hk
      rw [hψω]
      rcases mem_kleinA7 hk with rfl | rfl | rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [a7w_a]
        exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      · rw [a7w_b]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [show a7w * (a7a * a7b) * a7w⁻¹ = (a7w * a7a * a7w⁻¹) * (a7w * a7b * a7w⁻¹) by group,
          a7w_a, a7w_b, ab_mul_a7a]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hconj' : ∀ k ∈ kleinA7, (ψL ω)⁻¹ * k * ψL ω ∈ kleinA7 := by
      intro k hk
      rw [hψω]
      rcases mem_kleinA7 hk with rfl | rfl | rfl | rfl
      · rw [mul_one, inv_mul_cancel]
        exact Subgroup.one_mem _
      · rw [a7w_inv_a]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [a7w_inv_b]
        exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      · rw [show a7w⁻¹ * (a7a * a7b) * a7w = (a7w⁻¹ * a7a * a7w) * (a7w⁻¹ * a7b * a7w) by group,
          a7w_inv_a, a7w_inv_b, a7b_mul_ab]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
    constructor
    · rintro ⟨hxb, hxk⟩
      refine ⟨?_, ?_⟩
      · calc ω * x * ω⁻¹ * b = ω * x * (ω⁻¹ * b) := by group
          _ = ω * (x * b) * ω⁻¹ := by rw [hωinv]; group
          _ = ω * b * x * ω⁻¹ := by rw [hxb]; group
          _ = b * (ω * x * ω⁻¹) := by rw [hωb]; group
      · rw [map_mul, map_mul, map_inv]
        exact hconj _ hxk
    · rintro ⟨hxb, hxk⟩
      refine ⟨?_, ?_⟩
      · have h1 : x = ω⁻¹ * (ω * x * ω⁻¹) * ω := by group
        rw [h1]
        calc ω⁻¹ * (ω * x * ω⁻¹) * ω * b = ω⁻¹ * (ω * x * ω⁻¹) * (ω * b) := by group
          _ = ω⁻¹ * ((ω * x * ω⁻¹) * b) * ω := by rw [hωb]; group
          _ = ω⁻¹ * b * (ω * x * ω⁻¹) * ω := by rw [hxb]; group
          _ = b * (ω⁻¹ * (ω * x * ω⁻¹) * ω) := by rw [hωinv]; group
      · rw [map_mul, map_mul, map_inv] at hxk
        have := hconj' _ hxk
        rwa [show (ψL ω)⁻¹ * (ψL ω * ψL x * (ψL ω)⁻¹) * ψL ω = ψL x by group] at this
  have hUω : IsPGroup 3 (Subgroup.zpowers ω) := isPGroup_zpowers_of_pow hω3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SP, hSP⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 2
    hUω hP3 (P.normalizerMonoidHom.comp (Subgroup.inclusion
      ((Subgroup.zpowers_le).mpr hωP)))
  set S : Subgroup L := (SP : Subgroup P).map P.subtype with hS
  have hS2 : IsPGroup 2 S := SP.isPGroup'.map _
  have hSP' : S ≤ P := Subgroup.map_subtype_le _
  have hSO : ∀ x ∈ S, x ∈ O → x = 1 := fun x hxS hxO =>
    eq_one_of_two_of_odd hS2 hOodd hxS hxO
  have hinjS : ∀ x ∈ S, ∀ y ∈ S, ψL x = ψL y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y = 1 := hSO _ (mul_mem (inv_mem hx) hy)
      ((hker _).mp (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    rwa [inv_mul_eq_one] at h1
  have hωS : ∀ x ∈ S, ω * x * ω⁻¹ ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hSP ⟨ω, Subgroup.mem_zpowers ω⟩
    have h2 : (P.normalizerMonoidHom ⟨ω, hωP⟩ x : P) ∈ (SP : Subgroup P) := by
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    exact ⟨_, h2, rfl⟩
  set ψP : P →* kleinA7 :=
    (ψL.comp P.subtype).codRestrict kleinA7 (fun x => (Subgroup.mem_inf.mp x.2).2) with hψP
  have hψPs : Function.Surjective ψP := by
    rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := hψ k
    have hcomm : ψL l * ψL b = ψL b * ψL l := by
      rw [hl, hψb]
      rcases mem_kleinA7 hk with rfl | rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · exact a7c_a.symm
      · exact a7c_b.symm
      · rw [mul_assoc, ← a7c_b, ← mul_assoc, ← a7c_a, mul_assoc]
    obtain ⟨l', hl'b, hl'⟩ := exists_lift_commute ψL hker hO3 hb3 l hcomm
    refine ⟨⟨l', Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hl'b, ?_⟩⟩,
      Subtype.ext ?_⟩
    · rw [Subgroup.mem_comap, hl', hl]
      exact hk
    · change ψL l' = k
      rw [hl', hl]
  have hSmap : (SP : Subgroup P).map ψP = ⊤ := by
    have h1 := (SP.mapSurjective hψPs).is_maximal' (Q := ⊤)
      (isPGroup_kleinA7.of_equiv Subgroup.topEquiv.symm) le_top
    rw [Sylow.coe_mapSurjective] at h1
    exact h1.symm
  have hlift : ∀ k ∈ kleinA7, ∃ x ∈ S, ψL x = k := by
    intro k hk
    have : (⟨k, hk⟩ : kleinA7) ∈ (SP : Subgroup P).map ψP := hSmap ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsk⟩ := this
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsk⟩
  obtain ⟨f₁, hf₁S, hψf₁⟩ := hlift a7a (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨f₂, hf₂S, hψf₂⟩ := hlift a7b (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hf₁2 : f₁ * f₁ = 1 := hinjS _ (mul_mem hf₁S hf₁S) _ (Subgroup.one_mem _)
    (by rw [map_mul, hψf₁, a7a_sq, map_one])
  have hf₂2 : f₂ * f₂ = 1 := hinjS _ (mul_mem hf₂S hf₂S) _ (Subgroup.one_mem _)
    (by rw [map_mul, hψf₂, a7b_sq, map_one])
  have hf₁₂ : f₁ * f₂ = f₂ * f₁ := hinjS _ (mul_mem hf₁S hf₂S) _ (mul_mem hf₂S hf₁S)
    (by rw [map_mul, map_mul, hψf₁, hψf₂, a7ab_comm])
  have hf₁1 : f₁ ≠ 1 := fun h => a7a_ne_one (by rw [← hψf₁, h, map_one])
  have hbf : ∀ x ∈ S, b * x = x * b := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hSP' hx)).1).symm
  have hωf₁ : ω * f₁ * ω⁻¹ = f₁ * f₂ := hinjS _ (hωS _ hf₁S) _ (mul_mem hf₁S hf₂S)
    (by rw [map_mul, map_mul, map_inv, map_mul, hψω, hψf₁, hψf₂, a7w_a])
  have hωf₂ : ω * f₂ * ω⁻¹ = f₁ := hinjS _ (hωS _ hf₂S) _ hf₁S
    (by rw [map_mul, map_mul, map_inv, hψω, hψf₂, hψf₁, a7w_b])
  have hA4 : A4Data (ρ f₁) (ρ f₂) (ρ b) (ρ ω) :=
    { a₁ := by rw [← map_mul, hf₁2, map_one]
      a₂ := by rw [← map_mul, hf₂2, map_one]
      a₁₂ := by rw [← map_mul, ← map_mul, hf₁₂]
      b₁ := by rw [← map_mul, ← map_mul, hbf f₁ hf₁S]
      b₂ := by rw [← map_mul, ← map_mul, hbf f₂ hf₂S]
      b₃ := by rw [← map_mul, ← map_mul, ← pow_three', hb3, map_one]
      o₁ := by
        rw [← map_mul, ← map_mul, ← map_mul, ← hωf₁]
        group
      o₂ := by
        rw [← map_mul, ← map_mul, ← hωf₂]
        group
      o₃ := by rw [← map_mul, ← map_mul, ← pow_three', hω3, map_one]
      bo := by rw [← map_mul, ← map_mul, ← hωb] }
  obtain ⟨g₁, hg₁⟩ := hψ a7g₁
  obtain ⟨h₁, -, hh₁⟩ := exists_conj_of_three ψL hker hO3 (x := g₁ * b * g₁⁻¹) (y := ω)
    (by rw [conj_pow, hb3, mul_one, mul_inv_cancel]) hω3
    (by rw [map_mul, map_mul, map_inv, hg₁, hψb, a7g₁_conj, hψω])
  obtain ⟨g₂, hg₂⟩ := hψ a7g₂
  obtain ⟨h₂, -, hh₂⟩ := exists_conj_of_three ψL hker hO3 (x := g₂ * b * g₂⁻¹) (y := b⁻¹)
    (by rw [conj_pow, hb3, mul_one, mul_inv_cancel]) (by rw [inv_pow, hb3, inv_one])
    (by rw [map_mul, map_mul, map_inv, hg₂, hψb, a7g₂_conj, map_inv, hψb])
  have hBΩ : Module.finrank (ZMod p) (Module.End.eigenspace (ρ b) 1) =
      Module.finrank (ZMod p) (Module.End.eigenspace (ρ ω) 1) := by
    rw [← hh₁, show h₁ * (g₁ * b * g₁⁻¹) * h₁⁻¹ = (h₁ * g₁) * b * (h₁ * g₁)⁻¹ by group, hρconj]
  have hBinv : ∀ μ : ZMod p, Module.finrank (ZMod p) (Module.End.eigenspace (ρ b) μ) =
      Module.finrank (ZMod p) (Module.End.eigenspace (ρ b * ρ b) μ) := by
    intro μ
    have hbinv : b * b = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_three', hb3]
    rw [← map_mul, hbinv, ← hh₂, show h₂ * (g₂ * b * g₂⁻¹) * h₂⁻¹ = (h₂ * g₂) * b * (h₂ * g₂)⁻¹ by
      group, hρconj]
  have hf₁o : orderOf ((f₁ : L) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hf₁2]) hf₁1
  have hd : Module.finrank (ZMod p) (Module.End.eigenspace (ρ f₁) 1) ≤ 2 :=
    hDD.finrank_fixed (hLN f₁.2) hf₁o
  have hA₁1 : ρ f₁ ≠ 1 := by
    intro h1
    refine false_of_frattiniLinN_eq_one Dg hDD.pgroup hDD.ne_two hDD.odd (y := Subgroup.inclusion
      hLN f₁) ?_ h1
    rw [← Subgroup.orderOf_coe]
    exact hf₁o
  exact hA4.false_of_A4_three hDD.two_ne_zero' hA₁1 hd hBΩ hBinv

theorem false_of_center_one {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ}
    {C : Subgroup (CFSG.pCore p L)} (hcrit : Crit135 L p C)
    (hodd : OddCoreAlt7 L (aschbacherSolvableCore 3 L))
    (hZ : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 1) : False := by
  obtain ⟨e⟩ := hodd.quotient_center
  set O := CFSG.oddCore L with hOdef
  have hZbot : Subgroup.center (L ⧸ O) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  set ψL : L →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (L ⧸ O))).comp (QuotientGroup.mk' O)) with hψL
  have hψs : Function.Surjective ψL :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker : ∀ x, ψL x = 1 ↔ x ∈ O := by
    intro x
    rw [hψL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZbot,
      Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hθ : aschbacherSolvableCore 3 L = O := by
    rw [← hodd.comap_center, hZbot, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hO3 : ¬ 3 ∣ Nat.card O := by
    rw [← hθ]
    exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  exact false_of_alt7_local hcrit ψL hψs hker hO3

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
