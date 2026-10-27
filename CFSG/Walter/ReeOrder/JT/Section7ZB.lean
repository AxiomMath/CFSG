module

public import CFSG.Walter.ReeOrder.JT.Section7ZA
import CFSG.Walter.Transitivity.OddCore
public import CFSG.Walter.ReeOrder.JT.Section7X
public import CFSG.Walter.ReeOrder.JT.Section7Z

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG CFSG.Walter.Transitivity

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_card_eq_pow_mul_pow {r p : ℕ} (hr : r.Prime) {H : Subgroup X}
    (hH : ∀ d : ℕ, d.Prime → d ∣ Nat.card H → d = r ∨ d = p) :
    ∃ a b : ℕ, Nat.card H = r ^ a * p ^ b := by
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := H)).ne' r
    hr.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcard
    exact Nat.card_pos.ne' hcard
  have hmp : m = p ^ m.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdm => by
      rcases hH d hd (hcard ▸ Dvd.dvd.mul_left hdm _) with h1 | h1
      · exact absurd (h1 ▸ hdm) hm
      · exact h1)
  exact ⟨a, _, by rw [hcard, ← hmp]⟩

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem false_of_not_isCyclic_sylow
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P₀ : Sylow p G) (hCpP₀ : c.Cp p ≤ P₀)
    (hT₀P₀ : c.T₀ ≤ Subgroup.normalizer ((P₀ : Subgroup G) : Set G))
    (hnc₀ : ¬ IsCyclic (P₀ : Subgroup G)) : False := by
  classical
  have hS := CFSG.Walter.suzukiFourGroupTheorem
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp.out).mpr (Ne.symm hp3')
  obtain ⟨s, hsP, hsT, hs3, w₀, hw₀W, hw₀1, hw₀s⟩ :=
    h.exists_fixed_omegaZ hp3 c hpq P₀ hCpP₀ hT₀P₀ hnc₀
  have hw₀o : orderOf w₀ = p := orderOf_eq_prime (pow_eq_one_of_mem_omegaZ hw₀W) hw₀1
  set W₀ := Subgroup.zpowers w₀ with hW₀def
  have hW₀card : Nat.card W₀ = p := by rw [Nat.card_zpowers, hw₀o]
  have hW₀p : IsPGroup p W₀ := IsPGroup.of_card (by rw [hW₀card, pow_one] : Nat.card W₀ = p ^ 1)
  have hnotC : ∀ g : G, g * w₀ * g⁻¹ ∉ c.C := by
    intro g hg
    have hx1 : g * w₀ * g⁻¹ ≠ 1 := fun h0 => hw₀1 (by
      calc w₀ = g⁻¹ * (g * w₀ * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group)
    apply h.lemma_7_4 hp3 c.torus.le c.torus.cyclic c.card_C hg hx1
    have hmem : g * s * g⁻¹ ∈ Subgroup.centralizer ({g * w₀ * g⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * s * g⁻¹ * (g * w₀ * g⁻¹) = g * (s * w₀) * g⁻¹ := by group
        _ = g * (w₀ * s) * g⁻¹ := by rw [hw₀s]
        _ = g * w₀ * g⁻¹ * (g * s * g⁻¹) := by group
    have ho : orderOf (g * s * g⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs3]
    exact ho ▸ Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨u, hu2, hsu⟩ := h.exists_commute_of_mem_normalizer_kleinFour hp3 c.isKleinFour_T₀ hsT hs3
  have h9s := h.nine_dvd_card_centralizer_of_commute hp3 hs3 hu2 hsu
  set X := Subgroup.centralizer ({s} : Set G) with hXdef
  have hs2 : s ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs3] at this
    norm_num at this
  have hXs : Group.IsSolvable X := h.lemma_7_7_a hp3 hS hs2
  set π : Set Nat.Primes := {⟨3, Nat.prime_three⟩, ⟨p, hp.out⟩} with hπdef
  have hπ3 : (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ π := Or.inl rfl
  have hπp : (⟨p, hp.out⟩ : Nat.Primes) ∈ π := Or.inr rfl
  have hπprimes : ∀ {Z : Subgroup G}, IsPiSubgroup π Z →
      ∀ r : ℕ, r.Prime → r ∣ Nat.card Z → r = 3 ∨ r = p := by
    intro Z hZ r hr hrd
    rcases hZ ⟨r, hr⟩ hrd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  set SW := Subgroup.zpowers s ⊔ W₀ with hSWdef
  have hsX : s ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hw₀X : w₀ ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hw₀s
  have hSWX : SW ≤ X := sup_le ((Subgroup.zpowers_le).mpr hsX) ((Subgroup.zpowers_le).mpr hw₀X)
  have hSWcard : Nat.card SW = 3 * p := by
    have hN : Subgroup.zpowers s ≤ Subgroup.normalizer (W₀ : Set G) :=
      (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_commute hw₀s.symm)
    have hdisj : Disjoint (Subgroup.zpowers s) W₀ := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [Nat.card_zpowers, hs3, hW₀card]
      exact hcop3p
    rw [hSWdef, card_sup_eq_mul_of_disjoint hN hdisj, Nat.card_zpowers, hs3, hW₀card]
  have hSWπ : IsPiSubgroup π (SW.subgroupOf X) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSWX).toEquiv, hSWcard] at hr
    rcases (Nat.Prime.dvd_mul r.2).mp hr with h1 | h1
    · left
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_three).mp h1)
    · right
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 hp.out).mp h1)
  obtain ⟨Y', hY', hSWY'⟩ := SolvableHall.solvable_hall_containment hXs π _ hSWπ
  set Y := Y'.map X.subtype with hYdef
  have hYcard : Nat.card Y = Nat.card Y' := Subgroup.card_map_of_injective X.subtype_injective
  have hYπ : IsPiSubgroup π Y := fun q hq => hY'.p_in_pi_of_p_dvd_card q (hYcard ▸ hq)
  have hSWY : SW ≤ Y := fun y hy =>
    ⟨⟨y, hSWX hy⟩, hSWY' (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩
  have hY9 : 9 ∣ Nat.card Y := by
    have hidx : ¬ 3 ∣ Y'.index := fun hd => hY'.p_in_pi_of_p_dvd_index _ hd hπ3
    have h1 := Y'.card_mul_index
    have hcop : Nat.Coprime 9 Y'.index := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)
    rw [hYcard]
    exact hcop.dvd_of_dvd_mul_right (h1 ▸ h9s)
  have hW₀Y : W₀ ≤ Y := le_sup_right.trans hSWY
  set Fam : Set (Subgroup G) := {Z | IsPiSubgroup π Z ∧ Y ≤ Z} with hFamdef
  obtain ⟨Ys, ⟨hYsπ, hYYs⟩, hYsmax⟩ := (Set.toFinite Fam).exists_maximal ⟨Y, hYπ, le_rfl⟩
  have hmax : ∀ Z' : Subgroup G, IsPiSubgroup π Z' → Ys ≤ Z' → Z' ≤ Ys :=
    fun Z' hZ' hle => hYsmax ⟨hZ', hYYs.trans hle⟩ hle
  have hYs9 : 9 ∣ Nat.card Ys := hY9.trans (Subgroup.card_dvd_of_le hYYs)
  have hYsprimes := hπprimes hYsπ
  have hYss : Group.IsSolvable Ys :=
    isSolvable_of_prime_dvd Nat.prime_three hp.out (Ne.symm hp3') hYsprimes
  have hW₀Ys : W₀ ≤ Ys := hW₀Y.trans hYYs
  obtain ⟨a3, ap, hYscard⟩ := exists_card_eq_pow_mul_pow Nat.prime_three hYsprimes
  obtain ⟨Sg, hW₀Sg⟩ := (hW₀p.comap_subtype (K := Ys)).exists_le_sylow
  set SgG := (Sg : Subgroup Ys).map Ys.subtype with hSgGdef
  have hSgGcard : Nat.card SgG = p ^ (Nat.card Ys).factorization p := by
    rw [Subgroup.card_map_of_injective Ys.subtype_injective, Sg.card_eq_multiplicity]
  have hSgGp : IsPGroup p SgG := Sg.isPGroup'.map _
  have hSgGYs : SgG ≤ Ys := Subgroup.map_subtype_le _
  have hw₀Sg : w₀ ∈ SgG :=
    ⟨⟨w₀, hW₀Ys (Subgroup.mem_zpowers w₀)⟩, hW₀Sg (by
      rw [Subgroup.mem_comap]; exact Subgroup.mem_zpowers w₀), rfl⟩
  have hSgG1 : SgG ≠ ⊥ := fun h0 => hw₀1 (by rw [h0] at hw₀Sg; exact Subgroup.mem_bot.mp hw₀Sg)
  by_cases hSgc : IsCyclic SgG
  swap
  ·
    have hcore : pPrimeCore p Ys = ⊥ := by
      set K₀ := (pPrimeCore p Ys).map Ys.subtype with hK₀def
      have hK₀3 : IsPGroup 3 K₀ := by
        refine IsPGroup.of_card (n := (Nat.card K₀).primeFactorsList.length)
          (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdK => ?_)
        have hdYs : d ∣ Nat.card Ys :=
          hdK.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
        rcases hYsprimes d hd hdYs with h1 | h1
        · exact h1
        · exfalso
          have := coprime_card_map_pPrimeCore (p := p) Ys
          rw [h1] at hdK
          exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp this hdK
      have hSgK₀ : SgG ≤ Subgroup.normalizer (K₀ : Set G) :=
        hSgGYs.trans (le_normalizer_map_pPrimeCore Ys)
      have := h.eq_bot_of_le_normalizer_of_not_isCyclic hp3 c hpq hSgGp hSgc hK₀3 hSgK₀
      exact (Subgroup.map_eq_bot_iff_of_injective _ Ys.subtype_injective).mp this
    obtain ⟨P', hSgP'⟩ := hSgGp.exists_le_sylow
    have hP'nc : ¬ IsCyclic (P' : Subgroup G) := fun hc => hSgc (Subgroup.isCyclic_of_le hSgP')
    obtain ⟨-, -, hΩP'⟩ := h.lemma_7_8 hp3 c hpq P' hP'nc
    have hSgn := normal_sylow_of_pPrimeCore_eq_bot hp2 hYss hcore Sg (fun x hx hxp y hy => by
      have hx' : (x : G) ∈ omegaZ (P' : Subgroup G) p := hΩP' ▸ mem_omegaOne
        (hSgP' ⟨x, hx, rfl⟩) (by simpa using congrArg Subtype.val hxp)
      exact Subtype.ext (hx'.2.1 _ (hSgP' ⟨y, hy, rfl⟩)))
    have hYsN : Ys ≤ Subgroup.normalizer (SgG : Set G) := by
      intro g hg
      have hmem : (⟨g, hg⟩ : Ys) ∈ Subgroup.normalizer ((Sg : Subgroup Ys) : Set Ys) := by
        have := hSgn
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      exact Subgroup.le_normalizer_map Ys.subtype ⟨⟨g, hg⟩, hmem, rfl⟩
    have hSgsyl : Nat.card SgG = p ^ (Nat.card G).factorization p :=
      card_eq_of_isPiSubgroup_maximal hmax hYsπ hπp hYsN hSgGcard
        (h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq hSgGp hSgG1)
    let SgS : Sylow p G := Sylow.ofCard SgG hSgsyl
    have hSgS : (SgS : Subgroup G) = SgG := Sylow.coe_ofCard _ _
    obtain ⟨-, -, h9N, -, -⟩ := h.sylow_facts hp3 c hpq SgS
    rw [hSgS] at h9N
    exact h9N (hYs9.trans (Subgroup.card_dvd_of_le hYsN))
  have hSgcomm : ∀ x ∈ SgG, ∀ y ∈ SgG, x * y = y * x := by
    intro x hx y hy
    have := hSgc
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := SgG)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSgW₀ : ∀ x ∈ SgG, x ^ p = 1 → x ∈ W₀ := by
    intro x hx hxp
    by_cases hx1 : x = 1
    · rw [hx1]; exact W₀.one_mem
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    have heq := eq_of_le_of_isCyclic hSgc ((Subgroup.zpowers_le).mpr hx)
      ((Subgroup.zpowers_le).mpr hw₀Sg) (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hw₀o])
    rw [hW₀def, ← heq]
    exact Subgroup.mem_zpowers x
  have hp'SgG : ∀ {Z : Subgroup G}, IsPGroup p Z → Z ≤ Ys → Nat.card Z ≤ Nat.card SgG := by
    intro Z hZ hZYs
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm, hSgGcard]
    have h1 : p ^ m ∣ Nat.card Ys := hm ▸ Subgroup.card_dvd_of_le hZYs
    exact Nat.pow_le_pow_right hp.out.pos
      ((Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp h1)
  have hcen : ∀ n ∈ Ys, n ∈ Subgroup.normalizer (SgG : Set G) →
      n ∈ Subgroup.centralizer (SgG : Set G) := by
    intro n hnY hnN
    have hnord : n ^ (3 ^ a3 * p ^ ap) = 1 := by
      have := pow_card_eq_one' (G := Ys) (x := ⟨n, hnY⟩)
      rw [hYscard] at this
      simpa using congrArg Subtype.val this
    have hnp : n ^ 3 ^ a3 ∈ Subgroup.centralizer (SgG : Set G) := by
      set np := n ^ 3 ^ a3 with hnpdef
      have hnpp : IsPGroup p (Subgroup.zpowers np) := by
        refine IsPGroup.of_card (n := (orderOf np).primeFactorsList.length) ?_
        rw [Nat.card_zpowers]
        refine Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos np).ne' fun {d} hd hdo => ?_
        have h1 : orderOf np ∣ p ^ ap := orderOf_dvd_of_pow_eq_one (by
          rw [hnpdef, ← pow_mul, hnord])
        exact (Nat.prime_dvd_prime_iff_eq hd hp.out).mp (hd.dvd_of_dvd_pow (hdo.trans h1))
      have hnpN : Subgroup.zpowers np ≤ Subgroup.normalizer (SgG : Set G) :=
        (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hnN _)
      have hsup := hnpp.to_sup_of_normal_right' hSgGp hnpN
      have hsupYs : Subgroup.zpowers np ⊔ SgG ≤ Ys :=
        sup_le ((Subgroup.zpowers_le).mpr (Ys.pow_mem hnY _)) hSgGYs
      have heq : Subgroup.zpowers np ⊔ SgG = SgG :=
        (Subgroup.eq_of_le_of_card_ge le_sup_right (hp'SgG hsup hsupYs)).symm
      have hnpS : np ∈ SgG := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers np)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hSgcomm x hx np hnpS
    have hn3 : n ^ p ^ ap ∈ Subgroup.centralizer (SgG : Set G) := by
      set n3 := n ^ p ^ ap with hn3def
      have hn33 : IsPGroup 3 (Subgroup.zpowers n3) := by
        refine IsPGroup.of_card (n := (orderOf n3).primeFactorsList.length) ?_
        rw [Nat.card_zpowers]
        refine Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos n3).ne' fun {d} hd hdo => ?_
        have h1 : orderOf n3 ∣ 3 ^ a3 := orderOf_dvd_of_pow_eq_one (by
          rw [hn3def, ← pow_mul, mul_comm, hnord])
        exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow (hdo.trans h1))
      have hn3N : n3 ∈ Subgroup.normalizer (SgG : Set G) := Subgroup.pow_mem _ hnN _
      have hn3W₀ : n3 ∈ Subgroup.normalizer (W₀ : Set G) := by
        have hconj : n3 * w₀ * n3⁻¹ ∈ SgG := (Subgroup.mem_normalizer_iff.mp hn3N w₀).mp hw₀Sg
        have hconjo : orderOf (n3 * w₀ * n3⁻¹) = p := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw₀o]
        have heq := eq_of_le_of_isCyclic hSgc ((Subgroup.zpowers_le).mpr hconj)
          ((Subgroup.zpowers_le).mpr hw₀Sg)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hconjo, hw₀o])
        refine mem_normalizer_of_conj_mem fun x hx => ?_
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← conj_zpow, hW₀def, ← heq]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
      have hcomm := h.commute_of_mem_normalizer_zpowers hp3 c hpq P₀ hsP hs3 hw₀W hw₀s hn33 hn3W₀
      have hcopn : Nat.Coprime (Nat.card (Subgroup.zpowers n3)) (Nat.card SgG) := by
        obtain ⟨a, ha⟩ := hn33.exists_card_eq
        obtain ⟨b, hb⟩ := hSgGp.exists_card_eq
        rw [ha, hb]
        exact Nat.Coprime.pow _ _ hcop3p
      have hfix : ∀ y ∈ Subgroup.zpowers n3, ∀ x ∈ SgG, x ^ p = 1 → y * x = x * y := by
        intro y hy x hx hxp
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hSgW₀ x hx hxp)
        exact ((Commute.zpow_zpow (hcomm : Commute n3 w₀) k j)).eq
      exact le_centralizer_of_forall_pow_eq_one hp2 hSgGp hcopn
        ((Subgroup.zpowers_le).mpr hn3N) hfix (Subgroup.mem_zpowers n3)
    exact mem_of_pow_mem_of_coprime hnp hn3 (Nat.Coprime.pow _ _ hcop3p)
  have hSgc' : Subgroup.normalizer ((Sg : Subgroup Ys) : Set Ys) ≤
      Subgroup.centralizer ((Sg : Subgroup Ys) : Set Ys) := by
    intro m hm
    have hmG : (m : G) ∈ Subgroup.normalizer (SgG : Set G) :=
      Subgroup.le_normalizer_map Ys.subtype ⟨m, hm, rfl⟩
    have hmC := hcen m m.2 hmG
    rw [Subgroup.mem_centralizer_iff] at hmC ⊢
    intro x hx
    exact Subtype.ext (hmC x ⟨x, hx, rfl⟩)
  obtain ⟨K, hKn, hKp, -, hKcard⟩ := exists_normal_complement_of_le_centralizer Sg hSgc'
  set KG := K.map Ys.subtype with hKGdef
  have hKGcard' : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective Ys.subtype_injective
  have hK3 : ∃ c3 : ℕ, Nat.card K = 3 ^ c3 := by
    refine ⟨(Nat.card K).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdK => ?_⟩
    have hdYs : d ∣ Nat.card Ys := hdK.trans (Dvd.intro _ hKcard)
    rcases hYsprimes d hd hdYs with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hdK) hKp
  obtain ⟨c3, hc3⟩ := hK3
  have hKG3 : IsPGroup 3 KG := IsPGroup.of_card (by rw [hKGcard', hc3])
  have hKGcard : Nat.card KG = 3 ^ (Nat.card Ys).factorization 3 := by
    rw [hKGcard', hc3]
    congr 1
    rw [← hKcard, Sg.card_eq_multiplicity, hc3, Nat.factorization_mul (by positivity)
      (by positivity), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (Ne.symm hp3'), add_zero]
  have hYsKG : Ys ≤ Subgroup.normalizer (KG : Set G) := by
    intro g hg
    have hmem : (⟨g, hg⟩ : Ys) ∈ Subgroup.normalizer (K : Set Ys) := by
      have := hKn
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map Ys.subtype ⟨⟨g, hg⟩, hmem, rfl⟩
  have hKG1 : KG ≠ ⊥ := by
    intro h0
    have h1 : Nat.card KG = 1 := by rw [h0, Subgroup.card_bot]
    rw [hKGcard] at h1
    have h2 : 2 ≤ (Nat.card Ys).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp
        (by simpa using hYs9)
    have : 3 ^ 2 ≤ 3 ^ (Nat.card Ys).factorization 3 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hKGsyl : Nat.card KG = 3 ^ (Nat.card G).factorization 3 :=
    card_eq_of_isPiSubgroup_maximal hmax hYsπ hπ3 hYsKG hKGcard
      (h.isSolvable_normalizer_of_isPGroup_three hp3 hKG3 hKG1)
  let Ps : Sylow 3 G := Sylow.ofCard KG hKGsyl
  have hPs : (Ps : Subgroup G) = KG := Sylow.coe_ofCard _ _
  have hW₀N : W₀ ≤ Subgroup.normalizer ((Ps : Subgroup G) : Set G) := by
    rw [hPs]
    exact hW₀Ys.trans hYsKG
  obtain ⟨P₃, hCP₃, -, -⟩ := h.lemma_7_11_a hp3 c
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₃ Ps
  have hPsmap : (Ps : Subgroup G) = (P₃ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hpC : p ∣ Nat.card c.C := by
    have := c.card_C
    have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
    rwa [hq] at hpq
  obtain ⟨n₀, hn₀⟩ := (c.isPGroup_Cp p).exists_card_eq
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn₀
    exact c.Cp_ne_bot p hpC (Subgroup.card_eq_one.mp hn₀)
  obtain ⟨⟨c₁, hc₁Cp⟩, hc₁⟩ := exists_prime_orderOf_dvd_card' (G := c.Cp p) p
    (hn₀ ▸ dvd_pow_self p hn₀0)
  have hc₁o : orderOf c₁ = p := by rw [← hc₁, Subgroup.orderOf_mk]
  have hc₁C : c₁ ∈ c.C := c.Cp_le_C p hc₁Cp
  have hgc₁N : g * c₁ * g⁻¹ ∈ Subgroup.normalizer ((Ps : Subgroup G) : Set G) := by
    rw [hPsmap]
    exact conj_mem_normalizer_map (hCP₃ hc₁C) g
  set NPs := Subgroup.normalizer ((Ps : Subgroup G) : Set G) with hNPsdef
  have hgc₁p : IsPGroup p (Subgroup.zpowers (⟨g * c₁ * g⁻¹, hgc₁N⟩ : NPs)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hc₁o,
      pow_one]
  obtain ⟨Sg1, hSg1⟩ := hgc₁p.exists_le_sylow
  obtain ⟨Sg2, hSg2⟩ := (hW₀p.comap_subtype (K := NPs)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq NPs Sg1 Sg2
  set Sg2G := (Sg2 : Subgroup NPs).map NPs.subtype with hSg2Gdef
  have hSg2Gp : IsPGroup p Sg2G := Sg2.isPGroup'.map _
  have hSg2N : Sg2G ≤ NPs := Subgroup.map_subtype_le _
  by_cases hSg2c : IsCyclic Sg2G
  swap
  · have := h.eq_bot_of_le_normalizer_of_not_isCyclic hp3 c hpq hSg2Gp hSg2c Ps.isPGroup' hSg2N
    exact hKG1 (hPs ▸ this)
  have hw₀Sg2 : w₀ ∈ Sg2G :=
    ⟨⟨w₀, hW₀N (Subgroup.mem_zpowers w₀)⟩, hSg2 (by
      rw [Subgroup.mem_comap]; exact Subgroup.mem_zpowers w₀), rfl⟩
  have hc₁Sg2 : (k : G) * (g * c₁ * g⁻¹) * (k : G)⁻¹ ∈ Sg2G := by
    have hx : (⟨g * c₁ * g⁻¹, hgc₁N⟩ : NPs) ∈ (Sg1 : Subgroup NPs) :=
      hSg1 (Subgroup.mem_zpowers _)
    have hmem : k * ⟨g * c₁ * g⁻¹, hgc₁N⟩ * k⁻¹ ∈ (Sg2 : Subgroup NPs) := by
      rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hx, rfl⟩
    exact ⟨_, hmem, rfl⟩
  have hko : orderOf ((k : G) * (g * c₁ * g⁻¹) * (k : G)⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      hc₁o]
  have heq := eq_of_le_of_isCyclic hSg2c ((Subgroup.zpowers_le).mpr hw₀Sg2)
    ((Subgroup.zpowers_le).mpr hc₁Sg2) (by rw [Nat.card_zpowers, Nat.card_zpowers, hw₀o, hko])
  have hw₀mem : w₀ ∈ Subgroup.zpowers ((k : G) * (g * c₁ * g⁻¹) * (k : G)⁻¹) :=
    heq ▸ Subgroup.mem_zpowers w₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw₀mem
  apply hnotC ((k : G) * g)⁻¹
  rw [inv_inv, ← hj, show (k : G) * (g * c₁ * g⁻¹) * (k : G)⁻¹ =
    ((k : G) * g) * c₁ * ((k : G) * g)⁻¹ by group, conj_zpow]
  have : ((k : G) * g)⁻¹ * (((k : G) * g) * c₁ ^ j * ((k : G) * g)⁻¹) * ((k : G) * g) =
      c₁ ^ j := by group
  rw [this]
  exact c.C.zpow_mem hc₁C j

theorem lemma_7_15 :
    PiCyclic h := by
  classical
  intro p hp hpq P hP
  have : Fact p.Prime := ⟨hp⟩
  by_contra hPnc
  obtain ⟨c⟩ := h.nonempty_torusConf hp3
  obtain ⟨P₀, hCpP₀, hT₀P₀⟩ := h.exists_sylow_invariant hp3 c hpq
  have hnc₀ : ¬ IsCyclic (P₀ : Subgroup G) := by
    intro hc
    obtain ⟨P', hPP'⟩ := hP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P'
    have hP'map : (P' : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hc' : IsCyclic (P' : Subgroup G) := by
      rw [hP'map]
      exact isCyclic_of_surjective ((P₀ : Subgroup G).equivMapOfInjective _
        (MulAut.conj g).injective).toMonoidHom (MulEquiv.surjective _)
    exact hPnc (Subgroup.isCyclic_of_le hPP')
  exact h.false_of_not_isCyclic_sylow hp3 c hpq P₀ hCpP₀ hT₀P₀ hnc₀

theorem lemma_7_16 :
    Lemma716 h := h.lemma_7_16_of_piCyclic hp3 (h.lemma_7_15 hp3)

end JTHyp

end CFSG.Walter.JT
