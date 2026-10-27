module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.S4Free.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AS3Rec
import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.S4Free

open Subgroup

@[expose] def IsSym3Free (X : Type*) [Group X] : Prop :=
  ∀ (H : Subgroup X) (K : Subgroup H) [K.Normal], IsEmpty (H ⧸ K ≃* Equiv.Perm (Fin 3))

theorem isSym3Free_iff (X : Type*) [Group X] :
    IsSym3Free X ↔ ∀ (H : Subgroup X) (φ : H →* Equiv.Perm (Fin 3)), ¬ Function.Surjective φ := by
  constructor
  · intro h H φ hφ
    exact (h H φ.ker).false (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  · intro h H K _
    exact ⟨fun e => h H (e.toMonoidHom.comp (QuotientGroup.mk' K))
      (e.surjective.comp (QuotientGroup.mk'_surjective K))⟩

theorem IsSym3Free.subgroup {X : Type*} [Group X] (hX : IsSym3Free X) (Y : Subgroup X) :
    IsSym3Free Y := by
  rw [isSym3Free_iff] at hX ⊢
  intro H φ hφ
  let e : H ≃* H.map Y.subtype := H.equivMapOfInjective Y.subtype Y.subtype_injective
  exact hX _ (φ.comp e.symm.toMonoidHom) (hφ.comp e.symm.surjective)

theorem IsSym3Free.quotient {X : Type*} [Group X] (hX : IsSym3Free X) (N : Subgroup X)
    [N.Normal] : IsSym3Free (X ⧸ N) := by
  rw [isSym3Free_iff] at hX ⊢
  intro H φ hφ
  let r : H.comap (QuotientGroup.mk' N) →* H :=
    { toFun := fun x => ⟨QuotientGroup.mk' N x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hr : Function.Surjective r := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hX _ (φ.comp r) (hφ.comp hr)

theorem IsSym3Free.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : IsSym3Free X) : IsSym3Free Y := by
  rw [isSym3Free_iff] at hX ⊢
  intro H φ hφ
  let e' : H.comap e.toMonoidHom ≃* H :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [mem_comap]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }
  exact hX _ (φ.comp e'.toMonoidHom) (hφ.comp e'.surjective)

theorem IsSym3Free.eq_one_of_inv {X : Type*} [Group X] [Finite X] (hX : IsSym3Free X)
    {a y : X} (ha : a ^ 2 = 1) (hy : y ^ 3 = 1) (hay : a * y * a⁻¹ = y⁻¹) : y = 1 := by
  by_contra hy1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.OddStandard.SmallF3.HarrisU33.S4A.nonempty_closure_mulEquiv_perm_three
    (orderOf_eq_prime hy hy1) (by rwa [← pow_two]) hay
  exact (isSym3Free_iff X).1 hX _ e.toMonoidHom e.surjective

theorem isPGroup_oTwo (X : Type*) [Group X] [Finite X] : IsPGroup 2 (oTwo X) :=
  CFSG.isPGroup_of_isPiSubgroup_singleton (CFSG.LocalCores.piCore_isPiSubgroup _)

private theorem eq_one_of_pow_three {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {x : G} (hx : x ∈ P) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have : x ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨hk', hx3⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

private theorem eq_bot_of_normal_of_isPGroup_two {M : Subgroup (Equiv.Perm (Fin 3))}
    (hM : M.Normal) (h2 : IsPGroup 2 M) : M = ⊥ := by
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 ≠ 1 → ∃ τ : Equiv.Perm (Fin 3),
      (σ * (τ * σ * τ⁻¹)) ^ 3 = 1 ∧ σ * (τ * σ * τ⁻¹) ≠ 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_bot]
  by_cases hσ3 : σ ^ 3 = 1
  · exact eq_one_of_pow_three h2 hσ hσ3
  · obtain ⟨τ, hc3, hc1⟩ := key σ hσ3
    exact absurd (eq_one_of_pow_three h2 (M.mul_mem hσ (hM.conj_mem σ hσ τ)) hc3) hc1

theorem IsAdmissibleHost.restrict {S : Type*} [Group S] {X : Type*} [Group X] {ι : S →* X}
    (h : IsAdmissibleHost ι) {K : Subgroup X} (hK : ι.range ≤ K) :
    IsAdmissibleHost (ι.codRestrict K fun s => hK ⟨s, rfl⟩) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.sylow
  have hQK : oTwo X ≤ K := ((isPGroup_oTwo X).le_sylow_of_normal P).trans (hP.le.trans hK)
  have hle : (oTwo X).subgroupOf K ≤ oTwo K :=
    CFSG.LocalCores.le_piCore_of_normal inferInstance
      (CFSG.isPiSubgroup_singleton_of_isPGroup (q := ⟨2, Nat.prime_two⟩)
        ((isPGroup_oTwo X).comap_subtype (K := K)))
  refine ⟨inferInstance, h.sym4Free.subgroup K,
    fun a b hab => h.injective (congrArg Subtype.val hab),
    ⟨P.subtype (hP.le.trans hK), ?_⟩, ?_⟩
  · rw [Sylow.coe_subtype, hP]
    exact MonoidHom.subgroupOf_range_eq_of_le ι hK
  · intro k hk
    have hkX : (k : X) ∈ centralizer (oTwo X : Set X) := by
      rw [mem_centralizer_iff] at hk ⊢
      intro x hx
      have := hk ⟨x, hQK hx⟩ (hle (by simpa [mem_subgroupOf] using hx))
      simpa using congrArg Subtype.val this
    exact hle (by simpa [mem_subgroupOf] using h.centralizer_le hkX)

private theorem isPGroup_zpowers {G : Type*} [Group G] {p k : ℕ} {g : G} (hg : g ^ p ^ k = 1) :
    IsPGroup p (zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

private theorem two_dvd_card {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) : 2 ∣ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
  obtain ⟨n, hn, hcard⟩ := hQ.nontrivial_iff_card.1 this
  rw [hcard]
  exact dvd_pow_self 2 hn.ne'

private theorem exists_ne_one_conj_eq {X : Type*} [Group X] [Finite X] {Q : Subgroup X}
    [Q.Normal] (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) {g : X} {k : ℕ} (hg : g ^ 2 ^ k = 1) :
    ∃ q ∈ Q, q ≠ 1 ∧ g * q * g⁻¹ = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction (zpowers g) Q :=
    MulAction.compHom Q ((MulAut.conjNormal (H := Q)).comp (zpowers g).subtype)
  have hfix : (1 : Q) ∈ MulAction.fixedPoints (zpowers g) Q := fun h =>
    show MulAut.conjNormal (h : X) (1 : Q) = 1 from map_one _
  obtain ⟨b, hb, hne⟩ := (isPGroup_zpowers hg).exists_fixed_point_of_prime_dvd_card_of_fixed_point
    Q (two_dvd_card hQ hQ1) hfix
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), ?_⟩
  have h1 : MulAut.conjNormal g b = b := hb ⟨g, mem_zpowers g⟩
  rw [← MulAut.conjNormal_apply, h1]

private theorem commute_of_conj_mem {G : Type*} [Group G] {N : Subgroup G} (hN : IsPGroup 2 N)
    {y q : G} (hy3 : y ^ 3 = 1) (hyN : ∀ n ∈ N, y * n = n * y)
    (hq : y * q * y⁻¹ * q⁻¹ ∈ N) : y * q = q * y := by
  set n := y * q * y⁻¹ * q⁻¹ with hn
  have h1 : y * q = n * q * y := by rw [hn]; group
  have hyn : Commute y n := hyN n hq
  have key : ∀ j : ℕ, y ^ j * q = n ^ j * q * y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * q = y * (y ^ j * q) := by rw [pow_succ', mul_assoc]
        _ = (y * n ^ j) * q * y ^ j := by rw [ih]; group
        _ = n ^ j * (y * q) * y ^ j := by rw [(hyn.pow_right j).eq]; group
        _ = n ^ (j + 1) * q * y ^ (j + 1) := by rw [h1]; group
  have hn3 : n ^ 3 = 1 := by
    have h3 := key 3
    rw [hy3, one_mul, mul_one] at h3
    calc n ^ 3 = n ^ 3 * q * q⁻¹ := by group
      _ = 1 := by rw [← h3, mul_inv_cancel]
  rw [h1, eq_one_of_pow_three hN hq hn3, one_mul]

private theorem normal_of_conj {X : Type*} [Group X] {Q : Subgroup X} [Q.Normal]
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {y t : X}
    (hQH : Q ⊔ closure ({y, t} : Set X) = ⊤) {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hy : y ^ m₁ = 1)
    (hm₂ : 0 < m₂) (ht : t ^ m₂ = 1) {U : Subgroup X} (hUQ : U ≤ Q)
    (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) (htU : ∀ u ∈ U, t * u * t⁻¹ ∈ U) : U.Normal := by
  have Tmul : ∀ a b : X, (∀ u ∈ U, a * u * a⁻¹ ∈ U) → (∀ u ∈ U, b * u * b⁻¹ ∈ U) →
      ∀ u ∈ U, a * b * u * (a * b)⁻¹ ∈ U := by
    intro a b ha hb u hu
    have := ha _ (hb u hu)
    rwa [show a * (b * u * b⁻¹) * a⁻¹ = a * b * u * (a * b)⁻¹ by group] at this
  have Tpow : ∀ g : X, (∀ u ∈ U, g * u * g⁻¹ ∈ U) → ∀ j : ℕ, ∀ u ∈ U,
      g ^ j * u * (g ^ j)⁻¹ ∈ U := by
    intro g hg j
    induction j with
    | zero => intro u hu; simpa using hu
    | succ j ih => intro u hu; rw [pow_succ]; exact Tmul _ _ ih hg u hu
  have Tinv : ∀ g : X, ∀ m : ℕ, 0 < m → g ^ m = 1 → (∀ u ∈ U, g * u * g⁻¹ ∈ U) →
      ∀ u ∈ U, g⁻¹ * u * g⁻¹⁻¹ ∈ U := by
    intro g m hm hgm hg u hu
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt hm
    have : g⁻¹ = g ^ m' := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; simpa using hgm)
    rw [this]
    exact Tpow g hg m' u hu
  have TH : ∀ h ∈ closure ({y, t} : Set X),
      (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧ (∀ u ∈ U, h⁻¹ * u * h⁻¹⁻¹ ∈ U) := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨hyU, Tinv _ m₁ hm₁ hy hyU⟩
      · exact ⟨htU, Tinv _ m₂ hm₂ ht htU⟩
    | one => exact ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩
    | mul a b _ _ ha hb =>
      refine ⟨Tmul a b ha.1 hb.1, ?_⟩
      rw [mul_inv_rev]
      exact Tmul _ _ hb.2 ha.2
    | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
  refine ⟨fun u hu g => ?_⟩
  have hg : g ∈ ((Q ⊔ closure ({y, t} : Set X) : Subgroup X) : Set X) := by
    rw [hQH]; trivial
  rw [Subgroup.normal_mul] at hg
  obtain ⟨q, hq, h, hh, rfl⟩ := hg
  have h1 := (TH h hh).1 u hu
  rw [show q * h * u * (q * h)⁻¹ = q * (h * u * h⁻¹) * q⁻¹ by group,
    hab q hq _ (hUQ h1), mul_inv_cancel_right]
  exact h1

private theorem exists_inverted_of_surjective {A : Type*} [Group A] [Finite A]
    (φ : A →* Equiv.Perm (Fin 3)) (hφ : Function.Surjective φ) :
    ∃ y t : A, y ≠ 1 ∧ y ^ 3 = 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧ t * y * t⁻¹ = y⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 A) := inferInstance
  have hP3 : ∀ x ∈ (P : Subgroup A), ∃ j : ℕ, x ^ 3 ^ j = 1 := fun x hx => by
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨x, hx⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  let B := (Equiv.Perm.sign.comp φ).ker
  have hsign3 : ∀ x : A, (∃ j : ℕ, x ^ 3 ^ j = 1) → Equiv.Perm.sign (φ x) = 1 := by
    rintro x ⟨j, hj⟩
    have h1 : Equiv.Perm.sign (φ x) ^ 3 ^ j = 1 := by
      rw [← map_pow, ← map_pow, hj, map_one, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φ x)) with h | h
    · exact h
    · rw [h, Odd.neg_one_pow (Odd.pow (by decide : Odd 3))] at h1
      exact absurd h1 (by decide)
  have hPB : (P : Subgroup A) ≤ B := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact hsign3 x (hP3 x hx)
  obtain ⟨g, hgN, hgB⟩ : ∃ g ∈ normalizer (P : Set A), g ∉ B := by
    by_contra h
    push Not at h
    have hle : normalizer (P : Set A) ⊔ B ≤ B := sup_le h le_rfl
    rw [Sylow.normalizer_sup_eq_top' P hPB] at hle
    obtain ⟨a, ha⟩ := hφ (Equiv.swap 0 1)
    have := hle (mem_top a)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ha, Equiv.Perm.sign_swap (by decide)] at this
    exact absurd this (by decide)
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have htN : g ^ m ∈ normalizer (P : Set A) := pow_mem hgN m
  have ht2 : (g ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hgm, pow_orderOf_eq_one]
  have hsg : Equiv.Perm.sign (φ g) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (φ g)) with h | h
    · exact absurd (by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h]) hgB
    · exact h
  have hst : Equiv.Perm.sign (φ (g ^ m)) = -1 := by
    rw [map_pow, map_pow, hsg, hm.neg_one_pow]
  obtain ⟨x₀, hx₀P, hx₀⟩ : ∃ x₀ ∈ (P : Subgroup A), φ x₀ ≠ 1 := by
    by_contra h
    push Not at h
    have hle : (P : Subgroup A) ≤ φ.ker := fun x hx => h x hx
    have h6 : φ.ker.index = 6 := by
      rw [Subgroup.index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, Nat.card_perm,
        Nat.card_fin]
      rfl
    have := Subgroup.index_dvd_of_le hle
    rw [h6] at this
    exact P.not_dvd_index ((by norm_num : (3 : ℕ) ∣ 6).trans this)
  have hc : Equiv.Perm.sign (φ x₀) = 1 := hsign3 x₀ (hP3 x₀ hx₀P)
  have hinv : φ (g ^ m) * φ x₀ * (φ (g ^ m))⁻¹ = (φ x₀)⁻¹ := by
    have key : ∀ ρ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign ρ = -1 → Equiv.Perm.sign σ = 1 →
        ρ * σ * ρ⁻¹ = σ⁻¹ := by
      decide +kernel
    exact key _ _ hst hc
  set t := g ^ m with ht
  clear_value t
  set c := φ x₀ with hcdef
  let Ω := {x : A // x ∈ (P : Subgroup A) ∧ φ x = c}
  have hmem : ∀ x : Ω, (t * x.1 * t⁻¹)⁻¹ ∈ (P : Subgroup A) ∧ φ (t * x.1 * t⁻¹)⁻¹ = c := by
    rintro ⟨x, hxP, hxc⟩
    refine ⟨P.inv_mem ((mem_normalizer_iff.1 htN x).1 hxP), ?_⟩
    rw [map_inv, map_mul, map_mul, map_inv, hxc, hinv, inv_inv]
  have hmem' : ∀ x : Ω, t⁻¹ * x.1⁻¹ * t ∈ (P : Subgroup A) ∧ φ (t⁻¹ * x.1⁻¹ * t) = c := by
    rintro ⟨x, hxP, hxc⟩
    refine ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem htN) x⁻¹).1 (P.inv_mem hxP)
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv, map_inv, hxc]
      calc (φ t)⁻¹ * c⁻¹ * φ t = (φ t)⁻¹ * (φ t * c * (φ t)⁻¹) * φ t := by rw [hinv]
        _ = c := by group
  let σ : Equiv.Perm Ω :=
    { toFun := fun x => ⟨(t * x.1 * t⁻¹)⁻¹, hmem x⟩
      invFun := fun x => ⟨t⁻¹ * x.1⁻¹ * t, hmem' x⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  have hσ2 : ∀ x : Ω, ((σ ^ 2) x).1 = t ^ 2 * x.1 * (t ^ 2)⁻¹ := by
    intro x
    rw [pow_two, Equiv.Perm.mul_apply]
    show (t * (t * x.1 * t⁻¹)⁻¹ * t⁻¹)⁻¹ = _
    group
  have hσpow : ∀ j : ℕ, ∀ x : Ω, (((σ ^ 2) ^ j) x).1 = t ^ (2 * j) * x.1 * (t ^ (2 * j))⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, hσ2, ih]
      group
  have ht2' : t ^ (2 * 2 ^ a) = 1 := by rw [mul_comm, pow_mul, ht2, one_pow]
  have hσord : σ ^ 2 ^ (a + 1) = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_succ', pow_mul, hσpow, ht2']
    simp
  have hΩ : ¬ 2 ∣ Nat.card Ω := by
    let K := (P : Subgroup A) ⊓ φ.ker
    let e : Ω ≃ K :=
      { toFun := fun x => ⟨x₀⁻¹ * x.1, Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem hx₀P) x.2.1,
          MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, x.2.2, inv_mul_cancel])⟩⟩
        invFun := fun k => ⟨x₀ * k.1, P.mul_mem hx₀P (Subgroup.mem_inf.1 k.2).1, by
          rw [map_mul, MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 k.2).2, mul_one]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
    rw [Nat.card_congr e]
    obtain ⟨n, hn⟩ := (P.isPGroup'.to_le (inf_le_left : K ≤ P)).exists_card_eq
    rw [hn]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  obtain ⟨x, hx⟩ := (isPGroup_zpowers hσord).nonempty_fixed_point_of_prime_not_dvd_card Ω hΩ
  have hσx : σ x = x := hx ⟨σ, mem_zpowers σ⟩
  have htx : t * x.1 * t⁻¹ = x.1⁻¹ := by
    have h1 : (t * x.1 * t⁻¹)⁻¹ = x.1 := congrArg Subtype.val hσx
    calc t * x.1 * t⁻¹ = ((t * x.1 * t⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ = x.1⁻¹ := by rw [h1]
  have hx1 : x.1 ≠ 1 := fun h => hx₀ (by rw [← x.2.2, h, map_one])
  have hx3 : ∃ j : ℕ, x.1 ^ 3 ^ j = 1 := hP3 x.1 x.2.1
  have hj₀ : x.1 ^ 3 ^ Nat.find hx3 = 1 := Nat.find_spec hx3
  have hj₀pos : Nat.find hx3 ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hj₀
    exact hx1 hj₀
  refine ⟨x.1 ^ 3 ^ (Nat.find hx3 - 1), t, ?_, ?_, ⟨a, ht2⟩, ?_⟩
  · exact Nat.find_min hx3 (Nat.sub_lt (Nat.pos_of_ne_zero hj₀pos) one_pos)
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj₀pos), hj₀]
  · rw [← conj_pow, htx, inv_pow]

universe u in
private theorem commute_of_isSym4Free (n : ℕ) : ∀ (X : Type u) [Group X] [Finite X]
    (Q : Subgroup X) [Q.Normal], Nat.card X + Nat.card Q = n → IsSym4Free X → IsPGroup 2 Q →
    ∀ y t : X, y ^ 3 = 1 → (∃ k : ℕ, t ^ 2 ^ k = 1) → t * y * t⁻¹ = y⁻¹ →
    ∀ q ∈ Q, y * q = q * y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ Q _ hn h4 hQ y t hy3 ⟨k, hk⟩ hty
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have ihS : ∀ G₀ : Subgroup X, G₀ ≠ ⊤ → Q ≤ G₀ → y ∈ G₀ → t ∈ G₀ →
      ∀ q ∈ Q, y * q = q * y := by
    intro G₀ hG₀ hQG hyG htG q hq
    have hlt : Nat.card G₀ < Nat.card X :=
      lt_of_le_of_ne (Subgroup.card_le_card_group G₀) fun h =>
        hG₀ ((Subgroup.card_eq_iff_eq_top G₀).1 h)
    have hcard : Nat.card (Q.subgroupOf G₀) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQG).toEquiv
    have h := ih _ (by omega) G₀ (Q.subgroupOf G₀) rfl (h4.subgroup G₀) hQ.comap_subtype
      ⟨y, hyG⟩ ⟨t, htG⟩ (Subtype.ext (by simp [hy3])) ⟨k, Subtype.ext (by simp [hk])⟩
      (Subtype.ext (by simp [hty])) ⟨q, hQG hq⟩ (by simpa [Subgroup.mem_subgroupOf] using hq)
    simpa using congrArg Subtype.val h
  have ihN : ∀ N : Subgroup X, N.Normal → N < Q → ∀ q ∈ N, y * q = q * y := by
    intro N _ hNQ
    have := Subgroup.card_lt_of_lt hNQ
    exact ih _ (by omega) X N rfl h4 (hQ.to_le hNQ.le) y t hy3 ⟨k, hk⟩ hty
  have ihq : ∀ N : Subgroup X, N.Normal → N ≠ ⊥ → ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ N := by
    intro N _ hN q hq
    have hlt : Nat.card (X ⧸ N) < Nat.card X := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have h2 := (Subgroup.one_lt_card_iff_ne_bot N).2 hN
      have h3 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
      nlinarith
    have hle : Nat.card (Q.map (QuotientGroup.mk' N)) ≤ Nat.card Q :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd Q _)
    have : (Q.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    have h := ih _ (by omega) (X ⧸ N) (Q.map (QuotientGroup.mk' N)) rfl (h4.quotient N)
      (hQ.map _) (y : X ⧸ N) (t : X ⧸ N) (by simpa using congrArg (QuotientGroup.mk' N) hy3)
      ⟨k, by simpa using congrArg (QuotientGroup.mk' N) hk⟩
      (by simpa using congrArg (QuotientGroup.mk' N) hty) (q : X ⧸ N) ⟨q, hq, rfl⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have h' := (inferInstance : N.Normal).conj_mem _ (N.inv_mem h) (q * y)
    convert h' using 1
    group
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    exact hcon fun q hq => by rw [Subgroup.mem_bot.1 hq, mul_one, one_mul]
  set H : Subgroup X := closure ({y, t} : Set X) with hHdef
  have hyH : y ∈ H := subset_closure (Set.mem_insert y {t})
  have htH : t ∈ H := subset_closure (Set.mem_insert_of_mem y rfl)
  have hQH : Q ⊔ H = ⊤ := by
    by_contra hne
    exact hcon (ihS _ hne le_sup_left (le_sup_right (a := Q) hyH) (le_sup_right (a := Q) htH))
  have hmin : ∀ N : Subgroup X, N.Normal → N ≤ Q → N = ⊥ ∨ N = Q := by
    intro N hNn hNQ
    by_contra hc
    push Not at hc
    exact hcon fun q hq => commute_of_conj_mem (hQ.to_le hNQ) hy3
      (ihN N hNn (lt_of_le_of_ne hNQ hc.2)) (ihq N hNn hc.1 q hq)
  have hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have : (centralizer (Q : Set X)).Normal := Subgroup.normal_centralizer
    rcases hmin (Q ⊓ centralizer (Q : Set X)) inferInstance inf_le_left with h | h
    · exfalso
      have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
      have := hQ.center_nontrivial
      obtain ⟨z, hz⟩ := exists_ne (1 : center Q)
      have hzZ : ((z : Q) : X) ∈ Q ⊓ centralizer (Q : Set X) := by
        refine ⟨(z : Q).2, mem_centralizer_iff.2 fun b hb => ?_⟩
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨b, hb⟩)
      rw [h, Subgroup.mem_bot] at hzZ
      exact hz (Subtype.ext (Subtype.ext hzZ))
    · intro a ha b hb
      have hb' : b ∈ Q ⊓ centralizer (Q : Set X) := by rw [h]; exact hb
      exact mem_centralizer_iff.1 hb'.2 a ha
  have hexp : ∀ q ∈ Q, q * q = 1 := by
    let E : Subgroup X :=
      { carrier := {q | q ∈ Q ∧ q * q = 1}
        mul_mem' := by
          rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
          refine ⟨Q.mul_mem ha hb, ?_⟩
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab b hb a ha]
            _ = a * a * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
        one_mem' := ⟨Q.one_mem, mul_one 1⟩
        inv_mem' := by
          rintro a ⟨ha, ha2⟩
          exact ⟨Q.inv_mem ha, by rw [← mul_inv_rev, ha2, inv_one]⟩ }
    have hEn : E.Normal := ⟨fun q hq g => ⟨(inferInstance : Q.Normal).conj_mem q hq.1 g, by
      calc g * q * g⁻¹ * (g * q * g⁻¹) = g * (q * q) * g⁻¹ := by group
        _ = 1 := by rw [hq.2, mul_one, mul_inv_cancel]⟩⟩
    rcases hmin E hEn (fun q hq => hq.1) with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card hQ hQ1)
      have hxE : (x : X) ∈ E := ⟨x.2, by
        have := pow_orderOf_eq_one x
        rw [hx, pow_two] at this
        exact congrArg Subtype.val this⟩
      rw [h, Subgroup.mem_bot] at hxE
      have hx1 : x = 1 := Subtype.ext hxE
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · intro q hq
      have hqE : q ∈ E := by rw [h]; exact hq
      exact hqE.2
  have hnorm : ∀ U : Subgroup X, U ≤ Q → (∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      (∀ u ∈ U, t * u * t⁻¹ ∈ U) → U.Normal := fun U hUQ hyU htU =>
    normal_of_conj hab hQH (by norm_num : 0 < 3) hy3 (Nat.two_pow_pos k) hk hUQ hyU htU
  have h1 : t * y⁻¹ * t⁻¹ = y := by
    have := congrArg (·⁻¹) hty
    simpa [mul_assoc] using this
  have hty' : t * y = y⁻¹ * t := mul_inv_eq_iff_eq_mul.1 hty
  have h1' : t * y⁻¹ = y * t := mul_inv_eq_iff_eq_mul.1 h1
  have hct2y : Commute (t ^ 2) y := by
    show t ^ 2 * y = y * t ^ 2
    calc t ^ 2 * y = t * (t * y) := by rw [pow_two, mul_assoc]
      _ = t * (y⁻¹ * t) := by rw [hty']
      _ = t * y⁻¹ * t := by rw [mul_assoc]
      _ = y * t * t := by rw [h1']
      _ = y * t ^ 2 := by rw [pow_two, mul_assoc]
  have hct2t : Commute (t ^ 2) t := (Commute.self_pow t 2).symm
  have ht2Q : ∀ q ∈ Q, Commute (t ^ 2) q := by
    have hCn : (Q ⊓ centralizer ({t ^ 2} : Set X)).Normal := by
      refine hnorm _ inf_le_left ?_ ?_
      · intro u hu
        obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.1 hu
        rw [mem_centralizer_singleton_iff] at huC
        refine Subgroup.mem_inf.2 ⟨(inferInstance : Q.Normal).conj_mem u huQ y, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact ((hct2y.mul_right (huC : Commute u (t ^ 2)).symm).mul_right hct2y.inv_right).symm
      · intro u hu
        obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.1 hu
        rw [mem_centralizer_singleton_iff] at huC
        refine Subgroup.mem_inf.2 ⟨(inferInstance : Q.Normal).conj_mem u huQ t, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact ((hct2t.mul_right (huC : Commute u (t ^ 2)).symm).mul_right hct2t.inv_right).symm
    rcases hmin _ hCn inf_le_left with h | h
    · exfalso
      obtain ⟨q, hq, hq1, hqt⟩ := exists_ne_one_conj_eq hQ hQ1 (g := t ^ 2) (k := k)
        (by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
      have hqC : q ∈ Q ⊓ centralizer ({t ^ 2} : Set X) := Subgroup.mem_inf.2 ⟨hq, by
        rw [mem_centralizer_singleton_iff]
        calc q * t ^ 2 = t ^ 2 * q * (t ^ 2)⁻¹ * t ^ 2 := by rw [hqt]
          _ = t ^ 2 * q := by rw [inv_mul_cancel_right]⟩
      rw [h, Subgroup.mem_bot] at hqC
      exact hq1 hqC
    · intro q hq
      have hqC : q ∈ Q ⊓ centralizer ({t ^ 2} : Set X) := by rw [h]; exact hq
      exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hqC).2).symm
  have ht2c : ∀ g : X, Commute (t ^ 2) g := by
    have hle : Q ⊔ H ≤ centralizer ({t ^ 2} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.2 (ht2Q q hq).symm) ?_
      rw [hHdef, closure_le]
      rintro s (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 hct2y.symm
      · exact mem_centralizer_singleton_iff.2 hct2t.symm
    intro g
    have hg : g ∈ centralizer ({t ^ 2} : Set X) := hle (by rw [hQH]; trivial)
    exact (mem_centralizer_singleton_iff.1 hg).symm
  have htt : t * t = 1 := by
    have hNn : (zpowers (t ^ 2)).Normal := ⟨fun n hn g => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hn
      rw [← ((ht2c g).zpow_left m).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) m⟩
    by_contra hne
    have hN1 : zpowers (t ^ 2) ≠ ⊥ := fun h => hne (by
      have : t ^ 2 ∈ zpowers (t ^ 2) := mem_zpowers _
      rw [h, Subgroup.mem_bot, pow_two] at this
      exact this)
    rcases hmin (zpowers (t ^ 2) ⊓ Q) inferInstance inf_le_right with h | h
    · exact hcon fun q hq => by
        have h2 : y * q * y⁻¹ * q⁻¹ ∈ zpowers (t ^ 2) ⊓ Q := ⟨ihq _ hNn hN1 q hq,
          Q.mul_mem ((inferInstance : Q.Normal).conj_mem q hq y) (Q.inv_mem hq)⟩
        rw [h, Subgroup.mem_bot] at h2
        calc y * q = y * q * y⁻¹ * q⁻¹ * q * y := by group
          _ = q * y := by rw [h2, one_mul]
    · exact hcon fun q hq => by
        have hqN : q ∈ zpowers (t ^ 2) ⊓ Q := by rw [h]; exact hq
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hqN.1
        exact (hct2y.zpow_left m).symm.eq
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hcon fun q _ => by rw [one_mul, mul_one]
  obtain ⟨eH⟩ := CFSG.OddStandard.SmallF3.HarrisU33.S4A.nonempty_closure_mulEquiv_perm_three
    (orderOf_eq_prime hy3 hy1) htt hty
  have hQHbot : Q ⊓ H = ⊥ := by
    have hn : (Q ⊓ H).Normal := hnorm _ inf_le_left
      (fun u hu => ⟨(inferInstance : Q.Normal).conj_mem u hu.1 y,
        H.mul_mem (H.mul_mem hyH hu.2) (H.inv_mem hyH)⟩)
      (fun u hu => ⟨(inferInstance : Q.Normal).conj_mem u hu.1 t,
        H.mul_mem (H.mul_mem htH hu.2) (H.inv_mem htH)⟩)
    have h2 : IsPGroup 2 ((Q ⊓ H).subgroupOf H) := (hQ.to_le inf_le_left).comap_subtype
    have hbot := eq_bot_of_normal_of_isPGroup_two
      ((inferInstance : ((Q ⊓ H).subgroupOf H).Normal).map eH.toMonoidHom eH.surjective)
      (h2.map _)
    rw [eq_bot_iff]
    intro x hx
    have h3 : eH.toMonoidHom ⟨x, hx.2⟩ ∈ ((Q ⊓ H).subgroupOf H).map eH.toMonoidHom :=
      mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [hbot, Subgroup.mem_bot, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at h3
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)
  have hM : H ⊓ centralizer (Q : Set X) = ⊥ := by
    have hMn : (H ⊓ centralizer (Q : Set X)).Normal := by
      refine ⟨fun m hm g => ?_⟩
      have hg : g ∈ ((Q ⊔ H : Subgroup X) : Set X) := by rw [hQH]; trivial
      rw [Subgroup.normal_mul] at hg
      obtain ⟨q, hq, h, hh, rfl⟩ := hg
      have h1 : h * m * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hm.1) (H.inv_mem hh)
      have h2 : h * m * h⁻¹ ∈ centralizer (Q : Set X) :=
        (Subgroup.normal_centralizer (H := Q)).conj_mem m hm.2 h
      rw [show q * h * m * (q * h)⁻¹ = q * (h * m * h⁻¹) * q⁻¹ by group,
        mem_centralizer_iff.1 h2 q hq, mul_inv_cancel_right]
      exact ⟨h1, h2⟩
    by_contra hne
    exact hcon fun q hq => by
      have h3 : y * q * y⁻¹ * q⁻¹ ∈ Q ⊓ H := ⟨Q.mul_mem
        ((inferInstance : Q.Normal).conj_mem q hq y) (Q.inv_mem hq), (ihq _ hMn hne q hq).1⟩
      rw [hQHbot, Subgroup.mem_bot] at h3
      calc y * q = y * q * y⁻¹ * q⁻¹ * q * y := by group
        _ = q * y := by rw [h3, one_mul]
  have hfpf : ∀ q ∈ Q, y * q = q * y → q = 1 := by
    have hCn : (Q ⊓ centralizer ({y} : Set X)).Normal := by
      refine hnorm _ inf_le_left ?_ ?_
      · intro u hu
        obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.1 hu
        rw [mem_centralizer_singleton_iff] at huC
        refine Subgroup.mem_inf.2 ⟨(inferInstance : Q.Normal).conj_mem u huQ y, ?_⟩
        rw [mem_centralizer_singleton_iff,
          show y * u * y⁻¹ = u by rw [← huC, mul_inv_cancel_right]]
        exact huC
      · intro u hu
        obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.1 hu
        rw [mem_centralizer_singleton_iff] at huC
        refine Subgroup.mem_inf.2 ⟨(inferInstance : Q.Normal).conj_mem u huQ t, ?_⟩
        rw [mem_centralizer_singleton_iff]
        have h2 := (Commute.inv_right (huC : Commute u y)).map (MulAut.conj t)
        simp only [MulAut.conj_apply] at h2
        rw [h1] at h2
        exact h2
    rcases hmin _ hCn inf_le_left with h | h
    · intro q hq hqy
      have hqC : q ∈ Q ⊓ centralizer ({y} : Set X) :=
        Subgroup.mem_inf.2 ⟨hq, mem_centralizer_singleton_iff.2 hqy.symm⟩
      rw [h, Subgroup.mem_bot] at hqC
      exact hqC
    · exfalso
      exact hcon fun q hq => by
        have hqC : q ∈ Q ⊓ centralizer ({y} : Set X) := by rw [h]; exact hq
        exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hqC).2).symm
  obtain ⟨v, hvQ, hv1, hvt⟩ := exists_ne_one_conj_eq hQ hQ1 (g := t) hk
  set u := y * v * y⁻¹ with hu
  have huQ : u ∈ Q := (inferInstance : Q.Normal).conj_mem v hvQ y
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => (inferInstance : Q.Normal).conj_mem q hq y
  have hyu : y * u * y⁻¹ = v * u := by
    have hw : y * (v * u * (y * u * y⁻¹)) = v * u * (y * u * y⁻¹) * y := by
      have hyyy : y * y * y = 1 := by rw [← pow_three', hy3]
      have h2 : y * (y * u * y⁻¹) * y⁻¹ = v := by
        rw [hu]
        calc y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * v * (y * y * y)⁻¹ := by group
          _ = v := by rw [hyyy, one_mul, inv_one, mul_one]
      have h3 : y * (v * u * (y * u * y⁻¹)) * y⁻¹ = u * (y * u * y⁻¹) * v := by
        calc y * (v * u * (y * u * y⁻¹)) * y⁻¹
            = (y * v * y⁻¹) * (y * u * y⁻¹) * (y * (y * u * y⁻¹) * y⁻¹) := by group
          _ = u * (y * u * y⁻¹) * v := by rw [← hu, h2]
      rw [← mul_inv_eq_iff_eq_mul, h3, mul_assoc u, hab _ (hyQ u huQ) v hvQ, ← mul_assoc,
        hab u huQ v hvQ]
    have hw1 := hfpf _ (Q.mul_mem (Q.mul_mem hvQ huQ) (hyQ u huQ)) hw
    have hvu : (v * u) * (v * u) = 1 := hexp _ (Q.mul_mem hvQ huQ)
    calc y * u * y⁻¹ = (v * u) * (v * u) * (y * u * y⁻¹) := by rw [hvu, one_mul]
      _ = v * u * (v * u * (y * u * y⁻¹)) := by group
      _ = v * u := by rw [hw1, mul_one]
  have hvv : v * v = 1 := hexp v hvQ
  have huu : u * u = 1 := hexp u huQ
  have hcomm : u * v = v * u := hab u huQ v hvQ
  have p1 : v * (v * u) = u := by rw [← mul_assoc, hvv, one_mul]
  have p3 : u * (v * u) = v := by rw [← mul_assoc, hcomm, mul_assoc, huu, mul_one]
  have p4 : v * u * v = u := by rw [mul_assoc, hcomm, ← mul_assoc, hvv, one_mul]
  have p5 : v * u * u = v := by rw [mul_assoc, huu, mul_one]
  have p6 : v * u * (v * u) = 1 := hexp _ (Q.mul_mem hvQ huQ)
  let U : Subgroup X :=
    { carrier := {1, v, u, v * u}
      mul_mem' := by
        rintro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hvv, huu, hcomm, p1, p3, p4, p5, p6]
      one_mem' := by simp
      inv_mem' := by
        rintro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [inv_eq_of_mul_eq_one_right hvv]; simp
        · rw [inv_eq_of_mul_eq_one_right huu]; simp
        · rw [inv_eq_of_mul_eq_one_right p6]; simp }
  have hUQ : U ≤ Q := by
    rintro a (rfl | rfl | rfl | rfl)
    · exact Q.one_mem
    · exact hvQ
    · exact huQ
    · exact Q.mul_mem hvQ huQ
  have hyinv : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hy3)
  have htu : t * u * t⁻¹ = v * u := by
    calc t * u * t⁻¹ = (t * y * t⁻¹) * (t * v * t⁻¹) * (t * y * t⁻¹)⁻¹ := by rw [hu]; group
      _ = y⁻¹ * v * y := by rw [hty, hvt, inv_inv]
      _ = (y * y) * v * (y * y)⁻¹ := by rw [← hyinv, inv_inv]
      _ = y * (y * v * y⁻¹) * y⁻¹ := by group
      _ = v * u := hyu
  have hUn : U.Normal := by
    refine hnorm U hUQ ?_ ?_
    · rintro a (rfl | rfl | rfl | rfl)
      · simp
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rw [hyu]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [show y * (v * u) * y⁻¹ = (y * v * y⁻¹) * (y * u * y⁻¹) by group, hyu, ← hu, p3]
        exact Or.inr (Or.inl rfl)
    · rintro a (rfl | rfl | rfl | rfl)
      · simp
      · rw [hvt]; exact Or.inr (Or.inl rfl)
      · rw [htu]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [show t * (v * u) * t⁻¹ = (t * v * t⁻¹) * (t * u * t⁻¹) by group, hvt, htu, p1]
        exact Or.inr (Or.inr (Or.inl rfl))
  have hUeq : U = Q := (hmin U hUn hUQ).resolve_left fun h => hv1 (by
    have hvU : v ∈ U := Or.inr (Or.inl rfl)
    rw [h, Subgroup.mem_bot] at hvU
    exact hvU)
  have hu1 : u ≠ 1 := fun h => hv1 (by
    have : y⁻¹ * u * y = v := by rw [hu]; group
    rw [← this, h, mul_one, inv_mul_cancel])
  have hvu' : v ≠ u := fun h => hv1 (hfpf v hvQ (by
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [← hu, ← h]))
  have hvu1 : v * u ≠ 1 := fun h => hvu' (by
    calc v = v * u * u := p5.symm
      _ = u := by rw [h, one_mul])
  have hvvu : v ≠ v * u := fun h => hu1 (by
    calc u = v * (v * u) := p1.symm
      _ = 1 := by rw [← h, hvv])
  have huvu : u ≠ v * u := fun h => hv1 (by
    calc v = v * u * u := p5.symm
      _ = 1 := by rw [← h, huu])
  have hcardQ : Nat.card Q = 4 := by
    rw [← hUeq]
    show Nat.card ↑({1, v, u, v * u} : Set X) = 4
    have hn1 : (1 : X) ∉ ({v, u, v * u} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hv1, Ne.symm hu1, Ne.symm hvu1⟩
    have hn2 : v ∉ ({u, v * u} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hvu', hvvu⟩
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2,
      Set.ncard_pair huvu]
  have hcardH : Nat.card H = 6 := by
    rw [Nat.card_congr eH.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hcardX : Nat.card X = 24 := by
    have hquot : Nat.card (X ⧸ Q) = Nat.card H := by
      symm
      refine Nat.card_eq_of_bijective (fun h : H => ((h : X) : X ⧸ Q)) ⟨fun a b hab => ?_, ?_⟩
      · rw [QuotientGroup.eq] at hab
        have hmem : (a : X)⁻¹ * b ∈ Q ⊓ H := ⟨hab, H.mul_mem (H.inv_mem a.2) b.2⟩
        rw [hQHbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext (inv_mul_eq_one.1 hmem)
      · intro z
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
        have hg : g ∈ ((Q ⊔ H : Subgroup X) : Set X) := by rw [hQH]; trivial
        rw [Subgroup.normal_mul] at hg
        obtain ⟨q, hq, h, hh, rfl⟩ := hg
        refine ⟨⟨h, hh⟩, ?_⟩
        rw [QuotientGroup.eq]
        have := (inferInstance : Q.Normal).conj_mem q hq h⁻¹
        rwa [show h⁻¹ * q * h⁻¹⁻¹ = h⁻¹ * (q * h) by group] at this
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, hquot, hcardH, hcardQ]
  have hselfC : ∀ g : X, (∀ v ∈ Q, g * v = v * g) → g ∈ Q := by
    intro g hg
    have hg' : g ∈ ((Q ⊔ H : Subgroup X) : Set X) := by rw [hQH]; trivial
    rw [Subgroup.normal_mul] at hg'
    obtain ⟨q, hq, h, hh, rfl⟩ := hg'
    have hhC : h ∈ centralizer (Q : Set X) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h2 := hg a ha
      have h3 : q * (h * a) = q * (a * h) := by
        rw [← mul_assoc, h2, ← mul_assoc, ← hab q hq a ha, mul_assoc]
      exact (mul_left_cancel h3).symm
    have hh1 : h ∈ H ⊓ centralizer (Q : Set X) := ⟨hh, hhC⟩
    rw [hM, Subgroup.mem_bot] at hh1
    simpa [hh1] using hq
  obtain ⟨eX⟩ := CFSG.Quasithin.F6.GoldAmN.nonempty_mulEquiv_perm_four_of_normal Q hcardQ
    (fun v hv => by rw [pow_two]; exact hexp v hv) hselfC hcardX
  exact (isSym4Free_iff X).1 h4 ⊤ (eX.toMonoidHom.comp (⊤ : Subgroup X).subtype)
    (eX.surjective.comp fun x => ⟨⟨x, mem_top x⟩, rfl⟩)

universe u in
theorem isSym3Free_of_isSym4Free {X : Type u} [Group X] [Finite X] (h4 : IsSym4Free X)
    (hC : centralizer (oTwo X : Set X) ≤ oTwo X) : IsSym3Free X := by
  rw [isSym3Free_iff]
  intro A φ hφ
  obtain ⟨y, t, hy1, hy3, ⟨k, hk⟩, hty⟩ := exists_inverted_of_surjective φ hφ
  have hcomm := commute_of_isSym4Free _ X (oTwo X) rfl h4 (isPGroup_oTwo X) (y : X) (t : X)
    (by simpa using congrArg Subtype.val hy3) ⟨k, by simpa using congrArg Subtype.val hk⟩
    (by simpa using congrArg Subtype.val hty)
  have hyC : (y : X) ∈ centralizer (oTwo X : Set X) :=
    mem_centralizer_iff.2 fun q hq => (hcomm q hq).symm
  exact hy1 (Subtype.ext (eq_one_of_pow_three (isPGroup_oTwo X) (hC hyC)
    (by simpa using congrArg Subtype.val hy3)))

universe u in
theorem IsAdmissibleHost.isSym3Free {S : Type*} [Group S] {X : Type u} [Group X] {ι : S →* X}
    (h : IsAdmissibleHost ι) : IsSym3Free X :=
  have := h.finite
  isSym3Free_of_isSym4Free h.sym4Free h.centralizer_le

@[expose] def IsSzOrL2Three (E : Type*) [Group E] : Prop :=
  (∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
      Nonempty (E ≃* CFSG.Blueprint.suzukiGroup a K)) ∨
    ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 3 ^ m ∧
      Nonempty (E ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)

theorem IsSzOrL2Three.of_mulEquiv {E F : Type*} [Group E] [Group F] (e : E ≃* F)
    (hE : IsSzOrL2Three E) : IsSzOrL2Three F := by
  rcases hE with ⟨a, ha, K, _, _, hK, ⟨f⟩⟩ | ⟨m, hm, hm3, K, _, _, hK, ⟨f⟩⟩
  · exact Or.inl ⟨a, ha, K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨m, hm, hm3, K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩

@[expose] def SzL3Sections (X : Type*) [Group X] : Prop :=
  ∀ (H : Subgroup X) (K : Subgroup H) [K.Normal], IsSimpleGroup (H ⧸ K) →
    (∃ a b : H ⧸ K, a * b ≠ b * a) → IsSzOrL2Three (H ⧸ K)

theorem SzL3Sections.isSzOrL2Three {X : Type*} [Group X] (hX : SzL3Sections X)
    (H : Subgroup X) {E : Type*} [Group E] (φ : H →* E) (hφ : Function.Surjective φ)
    [IsSimpleGroup E] (hE : ∃ a b : E, a * b ≠ b * a) : IsSzOrL2Three E := by
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  refine (hX H φ.ker e.isSimpleGroup ?_).of_mulEquiv e
  obtain ⟨a, b, hab⟩ := hE
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem SzL3Sections.subgroup {X : Type*} [Group X] (hX : SzL3Sections X) (Y : Subgroup X) :
    SzL3Sections Y := by
  intro H K _ _ hna
  let e : H ≃* H.map Y.subtype := H.equivMapOfInjective Y.subtype Y.subtype_injective
  exact hX.isSzOrL2Three _ ((QuotientGroup.mk' K).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective K).comp e.symm.surjective) hna

theorem SzL3Sections.quotient {X : Type*} [Group X] (hX : SzL3Sections X) (N : Subgroup X)
    [N.Normal] : SzL3Sections (X ⧸ N) := by
  intro H K _ _ hna
  let r : H.comap (QuotientGroup.mk' N) →* H :=
    { toFun := fun x => ⟨QuotientGroup.mk' N x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hr : Function.Surjective r := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hX.isSzOrL2Three _ ((QuotientGroup.mk' K).comp r)
    ((QuotientGroup.mk'_surjective K).comp hr) hna

theorem SzL3Sections.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : SzL3Sections X) : SzL3Sections Y := by
  intro H K _ _ hna
  let e' : H.comap e.toMonoidHom ≃* H :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [mem_comap]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }
  exact hX.isSzOrL2Three _ ((QuotientGroup.mk' K).comp e'.toMonoidHom)
    ((QuotientGroup.mk'_surjective K).comp e'.surjective) hna

@[expose] def IsSzGroup (E : Type*) [Group E] : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
    Nonempty (E ≃* CFSG.Blueprint.suzukiGroup a K)

theorem IsSzGroup.of_mulEquiv {E F : Type*} [Group E] [Group F] (e : E ≃* F)
    (hE : IsSzGroup E) : IsSzGroup F := by
  obtain ⟨a, ha, K, _, _, hK, ⟨f⟩⟩ := hE
  exact ⟨a, ha, K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩

@[expose] def SzSections (X : Type*) [Group X] : Prop :=
  ∀ (H : Subgroup X) (K : Subgroup H) [K.Normal], IsSimpleGroup (H ⧸ K) →
    (∃ a b : H ⧸ K, a * b ≠ b * a) → IsSzGroup (H ⧸ K)

theorem SzSections.isSzGroup {X : Type*} [Group X] (hX : SzSections X) (H : Subgroup X)
    {E : Type*} [Group E] (φ : H →* E) (hφ : Function.Surjective φ) [IsSimpleGroup E]
    (hE : ∃ a b : E, a * b ≠ b * a) : IsSzGroup E := by
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  refine (hX H φ.ker e.isSimpleGroup ?_).of_mulEquiv e
  obtain ⟨a, b, hab⟩ := hE
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem SzSections.subgroup {X : Type*} [Group X] (hX : SzSections X) (Y : Subgroup X) :
    SzSections Y := by
  intro H K _ _ hna
  let e : H ≃* H.map Y.subtype := H.equivMapOfInjective Y.subtype Y.subtype_injective
  exact hX.isSzGroup _ ((QuotientGroup.mk' K).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective K).comp e.symm.surjective) hna

theorem SzSections.quotient {X : Type*} [Group X] (hX : SzSections X) (N : Subgroup X)
    [N.Normal] : SzSections (X ⧸ N) := by
  intro H K _ _ hna
  let r : H.comap (QuotientGroup.mk' N) →* H :=
    { toFun := fun x => ⟨QuotientGroup.mk' N x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hr : Function.Surjective r := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hX.isSzGroup _ ((QuotientGroup.mk' K).comp r)
    ((QuotientGroup.mk'_surjective K).comp hr) hna

theorem SzSections.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : SzSections X) : SzSections Y := by
  intro H K _ _ hna
  let e' : H.comap e.toMonoidHom ≃* H :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [mem_comap]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }
  exact hX.isSzGroup _ ((QuotientGroup.mk' K).comp e'.toMonoidHom)
    ((QuotientGroup.mk'_surjective K).comp e'.surjective) hna

theorem SzSections.of_isSolvable {X : Type*} [Group X] [Group.IsSolvable X] : SzSections X := by
  intro H K _ _ hna
  obtain ⟨a, b, hab⟩ := hna
  exact absurd ((IsSimpleGroup.comm_iff_isSolvable).2 inferInstance a b) hab

end CFSG.RankThree.S4Free
