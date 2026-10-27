module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Monster.Existence.StdOdd

open Subgroup

section Arith

theorem odd_dvd_of_dvd_two_pow_mul {n m : ℕ} (e : ℕ) (hn : Odd n) (h : n ∣ 2 ^ e * m) :
    n ∣ m :=
  Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right e hn.coprime_two_right) h

end Arith

section Counting

variable {G : Type*} [Group G]

theorem card_modEq_inf_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {P F : Subgroup G}
    (hP : IsPGroup p P) (hPF : P ≤ normalizer (F : Set G)) :
    Nat.card F ≡ Nat.card ↥(F ⊓ centralizer (P : Set G)) [MOD p] := by
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer P F hPF
  have h := hP.card_modEq_card_fixedPoints F
  have key : ∀ x : F, x ∈ MulAction.fixedPoints P F ↔ (x : G) ∈ centralizer (P : Set G) := by
    intro x
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx g hg
      have h1 := congrArg (fun z : F => (z : G)) (hx ⟨g, hg⟩)
      have h2 : g * (x : G) * g⁻¹ = (x : G) := h1
      exact mul_inv_eq_iff_eq_mul.1 h2
    · intro hx m
      apply Subtype.ext
      have h2 := hx (m : G) m.2
      show (m : G) * (x : G) * (m : G)⁻¹ = (x : G)
      rw [h2]
      group
  have hc : Nat.card (MulAction.fixedPoints P F) = Nat.card ↥(F ⊓ centralizer (P : Set G)) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, (key x.1).1 x.2⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩,
          (key _).2 (Subgroup.mem_inf.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hc] at h
  exact h

theorem card_modEq_zpowers [Finite G] {p : ℕ} [Fact p.Prime] {g : G} (hg : orderOf g = p)
    {F : Subgroup G} (hgF : g ∈ normalizer (F : Set G)) :
    Nat.card F ≡ Nat.card ↥(F ⊓ centralizer ({g} : Set G)) [MOD p] := by
  have hP : IsPGroup p (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := card_modEq_inf_centralizer hP (Subgroup.zpowers_le.2 hgF)
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem card_dvd_card_of_free {K Y : Type*} [Group K] [Finite K] [MulAction K Y] [Finite Y]
    (h : ∀ y : Y, ∀ k : K, k • y = y → k = 1) : Nat.card K ∣ Nat.card Y := by
  classical
  have : Fintype (Quotient (MulAction.orbitRel K Y)) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer K Y), Nat.card_sigma]
  have hst : ∀ ω : Quotient (MulAction.orbitRel K Y),
      Nat.card (K ⧸ MulAction.stabilizer K ω.out) = Nat.card K := by
    intro ω
    have hb : MulAction.stabilizer K ω.out = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 (fun k hk => h _ k hk)
    rw [hb]
    exact Nat.card_congr (QuotientGroup.quotientBot.toEquiv)
  simp only [hst, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

theorem card_modEq_of_free_outside {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    (S : Set X) (hS : ∀ k : K, ∀ x ∈ S, k • x ∈ S)
    (hfree : ∀ x ∉ S, ∀ k : K, k • x = x → k = 1) :
    Nat.card X ≡ Nat.card S [MOD Nat.card K] := by
  classical
  let _ : MulAction K ↥Sᶜ :=
    { smul := fun k y => ⟨k • (y : X), fun hmem => y.2 (by
        have := hS k⁻¹ _ hmem
        rwa [inv_smul_smul] at this)⟩
      one_smul := fun y => Subtype.ext (one_smul K (y : X))
      mul_smul := fun k l y => Subtype.ext (mul_smul k l (y : X)) }
  have hdvd : Nat.card K ∣ Nat.card ↥Sᶜ := by
    refine card_dvd_card_of_free (K := K) (Y := ↥Sᶜ) ?_
    intro y k hk
    exact hfree _ y.2 k (congrArg Subtype.val hk)
  have hsum : Nat.card X = Nat.card S + Nat.card ↥Sᶜ := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl S).symm
  rw [hsum]
  have h0 : Nat.card ↥Sᶜ ≡ 0 [MOD Nat.card K] := (Nat.modEq_zero_iff_dvd).2 hdvd
  simpa using Nat.ModEq.add_left (Nat.card S) h0

theorem exists_small_orbit {K X : Type*} [Group K] [Finite K] [MulAction K X]
    (hK : Odd (Nat.card K)) (Ω : Set X) (hfin : Ω.Finite)
    (hΩ : ∀ k : K, ∀ x ∈ Ω, k • x ∈ Ω)
    (hev : Even Ω.ncard) (hne : Ω.Nonempty) (hle : Ω.ncard ≤ 8) :
    ∃ x ∈ Ω, (MulAction.orbit K x).ncard ≤ 3 := by
  have hodd : ∀ x : X, Odd (MulAction.orbit K x).ncard := by
    intro x
    have h1 : (MulAction.stabilizer K x).index = (MulAction.orbit K x).ncard :=
      MulAction.index_stabilizer K x
    have h2 : (MulAction.stabilizer K x).index ∣ Nat.card K := Subgroup.index_dvd_card _
    rw [← h1]
    exact hK.of_dvd_nat h2
  have hsub : ∀ x ∈ Ω, MulAction.orbit K x ⊆ Ω := by
    rintro x hx _ ⟨k, rfl⟩
    exact hΩ k x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hne
  have h1 := hcon x₁ hx₁
  have hex : ∃ y ∈ Ω, y ∉ MulAction.orbit K x₁ := by
    by_contra h
    push Not at h
    have hsub' : Ω ⊆ MulAction.orbit K x₁ := h
    have hfin' : (MulAction.orbit K x₁).Finite := hfin.subset (hsub x₁ hx₁)
    have : Ω.ncard = (MulAction.orbit K x₁).ncard :=
      le_antisymm (Set.ncard_le_ncard hsub' hfin') (Set.ncard_le_ncard (hsub x₁ hx₁) hfin)
    rw [← this] at h1
    have h3 := hodd x₁
    rw [← this] at h3
    exact (Nat.not_even_iff_odd.2 h3) hev
  obtain ⟨y, hy, hyn⟩ := hex
  have hdisj : MulAction.orbit K y ⊆ Ω \ MulAction.orbit K x₁ := by
    intro z hz
    refine ⟨hsub y hy hz, fun hz' => hyn ?_⟩
    have e1 : MulAction.orbit K z = MulAction.orbit K y := MulAction.orbit_eq_iff.2 hz
    have e2 : MulAction.orbit K z = MulAction.orbit K x₁ := MulAction.orbit_eq_iff.2 hz'
    exact MulAction.orbit_eq_iff.1 (e1.symm.trans e2)
  have hfin2 : (Ω \ MulAction.orbit K x₁).Finite := hfin.sdiff
  have h4 := Set.ncard_le_ncard hdisj hfin2
  rw [Set.ncard_sdiff (hsub x₁ hx₁) (hfin.subset (hsub x₁ hx₁))] at h4
  have h5 := hcon y hy
  have h6 := hodd x₁
  obtain ⟨m, hm⟩ := h6
  omega

end Counting

section Lifting

variable {G : Type*} [Group G]

theorem exists_orderOf_eq_of_quotient {p : ℕ} [Fact p.Prime] [Finite G]
    (F : Subgroup G) [F.Normal] (hF : IsPGroup p F) {x : G ⧸ F} {n : ℕ}
    (hx : orderOf x = n) : ∃ g : G, orderOf g = n := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
  have hnm : n ∣ orderOf g₀ := by
    rw [← hx]
    exact orderOf_map_dvd (QuotientGroup.mk' F) g₀
  have hnpos : 0 < n := hx ▸ orderOf_pos _
  have hmem : g₀ ^ n ∈ F := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hx]
    exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ := hF ⟨g₀ ^ n, hmem⟩
  have hj' : (g₀ ^ n) ^ (p ^ j) = 1 := congrArg Subtype.val hj
  have hdvd : orderOf g₀ ∣ n * p ^ j := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul] at hj'
    exact hj'
  obtain ⟨t, ht⟩ := hnm
  have htj : t ∣ p ^ j := by
    rw [ht] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hnpos).1 hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 htj
  refine ⟨g₀ ^ (p ^ i), ?_⟩
  have hpi : p ^ i ∣ orderOf g₀ := by
    rw [ht, hi]
    exact dvd_mul_left _ _
  rw [orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hpi, ht, hi]
  exact Nat.mul_div_cancel n (pow_pos (Fact.out : p.Prime).pos i)

theorem exists_card_eq_mul_dvd_totient [Finite G] (P N : Subgroup G) [IsCyclic P]
    (hN : N ≤ normalizer (P : Set G)) :
    ∃ k : ℕ, Nat.card N = Nat.card ↥(N ⊓ centralizer (P : Set G)) * k ∧
      k ∣ Nat.totient (Nat.card P) := by
  let φ : N →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hker : φ.ker = (N ⊓ centralizer (P : Set G)).subgroupOf N := by
    ext n
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h1 : φ n = 1 ↔ (Subgroup.inclusion hN n) ∈ P.normalizerMonoidHom.ker := Iff.rfl
    rw [h1, normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨n.2, h⟩
    · intro h
      exact h.2
  refine ⟨Nat.card φ.range, ?_, ?_⟩
  · have h := Subgroup.card_ker_mul_card_range φ
    rw [hker] at h
    rw [← h]
    congr 1
    exact Nat.card_congr
      (subgroupOfEquivOfLe (inf_le_left : N ⊓ centralizer (P : Set G) ≤ N)).toEquiv
  · have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [IsCyclic.card_mulAut] at this

end Lifting

section Normalizers

variable {G : Type*} [Group G]

theorem mem_normalizer_inf {g : G} {K L : Subgroup G} (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) : g ∈ normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hK hL ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hK x, hL x]

theorem mem_normalizer_centralizer_of_commute {g z : G} (h : g * z = z * g) :
    g ∈ normalizer ((centralizer ({z} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  have hz : g * z * g⁻¹ = z := by
    rw [h]
    group
  have e1 : z * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by
    calc z * (g * x * g⁻¹) = (g * z * g⁻¹) * (g * x * g⁻¹) := by rw [hz]
      _ = g * (z * x) * g⁻¹ := by group
  have e2 : g * x * g⁻¹ * z = g * (x * z) * g⁻¹ := by
    calc g * x * g⁻¹ * z = (g * x * g⁻¹) * (g * z * g⁻¹) := by rw [hz]
      _ = g * (x * z) * g⁻¹ := by group
  constructor
  · intro hx
    rw [e1, e2, hx]
  · intro hx
    rw [e1, e2] at hx
    exact mul_left_cancel (mul_right_cancel hx)

theorem card_map_subtype_eq (F : Subgroup G) (K : Subgroup F) :
    Nat.card (K.map F.subtype) = Nat.card K :=
  Subgroup.card_map_of_injective F.subtype_injective

theorem mem_normalizer_of_normal {F : Subgroup G} [F.Normal] (g : G) :
    g ∈ normalizer (F : Set G) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

end Normalizers

end CFSG.Monster.Existence.StdOdd
