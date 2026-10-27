module

public import CFSG.Walter.ReeOrder.JT.Section7Q

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem le_centralizer_of_forall_pow_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {K L : Subgroup X} (hK : IsPGroup p K) (hL : Nat.Coprime (Nat.card L) (Nat.card K))
    (hLK : L ≤ Subgroup.normalizer (K : Set X))
    (hfix : ∀ y ∈ L, ∀ x ∈ K, x ^ p = 1 → y * x = x * y) :
    L ≤ Subgroup.centralizer (K : Set X) := by
  let := conjAct L K hLK
  have : Fact (IsPGroup p K) := ⟨hK⟩
  have hΩ : ActsTriviallyOnSubgroup (A := L) (G := K) (omega₁ (G := K) (p := p)) := by
    intro a x hx
    have hle : omega₁ (G := K) (p := p) ≤ fixedPointSubgroup (Subgroup.zpowers a) K := by
      rw [omega₁, omega, Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, FixedPoints.mem_subgroup]
      rintro ⟨b, hb⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hz' : (z : X) ^ p = 1 := by
        have : z ^ (p ^ 1) = 1 := hz
        rw [pow_one] at this
        simpa using congrArg Subtype.val this
      apply Subtype.ext
      change ((a ^ k : L) : X) * z * ((a ^ k : L) : X)⁻¹ = z
      have hc : ((a ^ k : L) : X) * z = z * ((a ^ k : L) : X) :=
        hfix _ (a ^ k).2 z z.2 hz'
      rw [hc, mul_inv_cancel_right]
    have := hle hx
    rw [FixedPoints.mem_subgroup] at this
    exact this ⟨a, Subgroup.mem_zpowers a⟩
  have htriv := theorem_1_11 (G := K) (A := L) hp2 hL hΩ
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg Subtype.val (htriv ⟨y, hy⟩ ⟨x, hx⟩)
  change y * x * y⁻¹ = x at this
  calc x * y = (y * x * y⁻¹) * y := by rw [this]
    _ = y * x := by group

theorem map_eq_top_of_isHallSubgroup {Y : Type*} [Group Y] [Finite Y] {f : X →* Y}
    (hf : Function.Surjective f) {π : Set Nat.Primes} {Z : Subgroup X}
    (hZ : IsHallSubgroup π Z) (hY : ∀ q : Nat.Primes, q.val ∣ Nat.card Y → q ∈ π) :
    Z.map f = ⊤ := by
  have hH := hZ.map_of_surjective f hf
  rw [← Subgroup.index_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have h1 := hH.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hqd
  exact h1 (hY ⟨q, hq⟩ (hqd.trans (Subgroup.index_dvd_card _)))

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem sylow_facts
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) :
    4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      ¬ 8 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      ¬ 9 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      Group.IsSolvable (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      ∀ x ∈ (P : Subgroup G), x ^ p = 1 → ∀ y ∈ (P : Subgroup G), x * y = y * x := by
  have hpC : p ∣ Nat.card c.C := by
    have := c.card_C
    have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
    rwa [hq] at hpq
  have hP1 : (P : Subgroup G) ≠ ⊥ :=
    P.ne_bot_of_dvd_card (hpC.trans (Subgroup.card_subgroup_dvd_card _))
  have hsolv := h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq P.isPGroup' hP1
  have h8 := h.not_eight_dvd_card_normalizer_of_pi hp3 hpq P.isPGroup' hP1
  obtain ⟨P₀, -, hT₀P₀⟩ := h.exists_sylow_invariant hp3 c hpq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hPmap : (P : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    have hle : c.T₀.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hPmap]
      exact conj_mem_normalizer_map (hT₀P₀ hx) g
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      c.isKleinFour_T₀.card_four] at this
  refine ⟨h4, h8, h.not_nine_dvd_card hp3 hsolv h4, hsolv, ?_⟩
  intro x hx hxp y hy
  by_cases hc : IsCyclic (P : Subgroup G)
  · exact congrArg Subtype.val (hc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  · obtain ⟨-, -, hΩ⟩ := h.lemma_7_8 hp3 c hpq P hc
    have hxZ : x ∈ omegaZ (P : Subgroup G) p := hΩ ▸ mem_omegaOne hx hxp
    exact hxZ.2.1 y hy

theorem ne_inv_of_mem_normalizer_sylow
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G) {y : G}
    (hyN : y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hy : orderOf y = 3) (g : G) :
    g * y * g⁻¹ ≠ y⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h4, h8, -, hsolv, -⟩ := h.sylow_facts hp3 c hpq P
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}
  have hyπ : IsPiSubgroup π ((Subgroup.zpowers y).subgroupOf N) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr hyN)).toEquiv,
      Nat.card_zpowers, hy] at hr
    right
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_three).mp hr)
  obtain ⟨H, hH, hyH⟩ := SolvableHall.solvable_hall_containment hsolv π _ hyπ
  set HG := H.map N.subtype
  have hHG : Nat.card HG = Nat.card H := Subgroup.card_map_of_injective N.subtype_injective
  have h4H : 4 ∣ Nat.card H := by
    have hcard := H.card_mul_index
    have h2 : Nat.Coprime 4 H.index := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      intro hd
      exact hH.p_in_pi_of_p_dvd_index ⟨2, Nat.prime_two⟩ hd (Or.inl rfl)
    exact h2.dvd_of_dvd_mul_right (hcard ▸ h4)
  obtain ⟨⟨V, hVn⟩, -⟩ := h.lemma_7_2 hp3 (H := HG) (fun r hr hrd => by
    rw [hHG] at hrd
    rcases hH.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1) (hHG ▸ h4H)
  set VG := (V : Subgroup HG).map HG.subtype
  have hVcard : Nat.card VG = 4 := by
    rw [Subgroup.card_map_of_injective HG.subtype_injective, V.card_eq_multiplicity, hHG]
    have hfac : (Nat.card H).factorization 2 = 2 := factorization_two_eq_two h4H (fun h8' =>
      h8 (h8'.trans (by
        have := Subgroup.card_dvd_of_le (Subgroup.map_subtype_le H : H.map N.subtype ≤ N)
        rwa [hHG] at this)))
    rw [hfac]
    norm_num
  have hVsq : ∀ x : VG, x * x = 1 := fun x => Subtype.ext
    (h.mul_self_of_isPGroup_two hp3 (V.isPGroup'.map HG.subtype) x.2)
  have hV : IsKleinFour VG := isKleinFour_of_card_four hVcard hVsq
  have hyHG : y ∈ HG := ⟨⟨y, hyN⟩, hyH (by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y), rfl⟩
  have hyV : y ∈ Subgroup.normalizer (VG : Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨⟨y, hyHG⟩ * v * ⟨y, hyHG⟩⁻¹, hVn.conj_mem v hv ⟨y, hyHG⟩, rfl⟩
  obtain ⟨u, hu, hyu⟩ := h.exists_commute_of_mem_normalizer_kleinFour hp3 hV hyV hy
  exact h.lemma_7_1_a hp3 hy hu hyu g

end JTHyp

end CFSG.Walter.JT
