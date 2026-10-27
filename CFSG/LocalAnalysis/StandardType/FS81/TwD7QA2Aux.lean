module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QSplit
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCountAux
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7M0Model
public import CFSG.LocalAnalysis.StandardType.FS81.D6MarkOfModel
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
public import CFSG.LocalAnalysis.StandardType.FS81.SplitEAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open
open Subgroup

theorem mem_E_of_three_element_centralizer_E_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    {x : G} (hxE : x ∈ Subgroup.centralizer (E : Set G)) {a : ℕ} (ha : 1 ≤ a)
    (hx3 : x ^ (3 ^ a) = 1) : x ∈ E := by
  obtain ⟨hA, hEmax, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨-, -, hsup, -, -, hself⟩ := hstd.2.2
  have hE : IsElemAbelian 3 E := hEmax.2.1
  obtain ⟨R₀, hR₀C, hR₀n, hR₀3, hCeq, hR₀E, hNR, hmin, hXcent⟩ :=
    exists_threePrime_core_twD7 hstd hB hrec
  have hxC : x ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxE b₀ hb₀E).symm
  obtain ⟨-, hKC, hKn, hKz, -, -, -, -⟩ := hA
  obtain ⟨hRow, -, -, -, hE1card, -⟩ := hstd.2.2
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hRow hKz
  have hK3 : 3 ∣ Nat.card K := by
    have h : 3 ∣ Nat.card ↥(E ⊓ K) := by rw [hE1card]; exact dvd_pow_self 3 (by decide)
    exact h.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hR₀K : R₀ ≤ Subgroup.centralizer (K : Set G) :=
    le_centralizer_of_normal_of_isSimple hKC hKn hKs hK3 hR₀C hR₀n hR₀3
  have hZK : Subgroup.zpowers b₀ ⊔ K ≤ Subgroup.centralizer (R₀ : Set G) := by
    refine sup_le ?_ ((Subgroup.le_centralizer_iff).mp hR₀K)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hR₀C hr)
  have hcommR : ∀ a ∈ R₀, ∀ b ∈ Subgroup.zpowers b₀ ⊔ K, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hZK hb) a ha
  have hzK : Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hcommK : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hzK ha) b hb).symm
  obtain ⟨r, hr, s, hs, rfl⟩ := fs81Sp_mem_sup_of_commute hcommR (hCeq ▸ hxC)
  obtain ⟨z, hz, k, hk, rfl⟩ := fs81Sp_mem_sup_of_commute hcommK hs
  have hsE : z * k ∈ Subgroup.centralizer (E : Set G) := by
    have : z * k = r⁻¹ * (r * (z * k)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hR₀E hr)) hxE
  have hzC : z ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hn]
    have hb₀y : Commute b₀ y := by
      rw [commute_iff_eq]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b₀, hb₀E⟩ ⟨y, hy.1⟩)
    exact (Commute.zpow_left hb₀y n).eq.symm
  have hkC : k ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
    have : k = z⁻¹ * (z * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzC) (Subgroup.centralizer_le inf_le_left hsE)
  have hkEK : k ∈ E ⊓ K := by
    rw [← hself]
    exact Subgroup.mem_inf.mpr ⟨hkC, hk⟩
  have hkE : k ∈ E := hkEK.1
  have hzE : z ∈ E := (Subgroup.zpowers_le.mpr hb₀E) hz
  have heE : z * k ∈ E := E.mul_mem hzE hkE
  have hrs : Commute r (z * k) := (Subgroup.mem_centralizer_iff.mp (hR₀E hr) (z * k) heE).symm
  have hxpow : (r * (z * k)) ^ (3 ^ a) = r ^ (3 ^ a) * (z * k) ^ (3 ^ a) := by
    rw [hrs.mul_pow]
  have he3a : (z * k) ^ (3 ^ a) = 1 := by
    have he3 : (z * k) ^ 3 = 1 := hE.2 (z * k) heE
    have hdvd : orderOf (z * k) ∣ 3 := orderOf_dvd_of_pow_eq_one he3
    have hdvd3a : orderOf (z * k) ∣ 3 ^ a :=
      hdvd.trans (dvd_pow_self 3 (Nat.one_le_iff_ne_zero.mp ha))
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd3a
  have hr3a : r ^ (3 ^ a) = 1 := by
    rw [hxpow, he3a, mul_one] at hx3
    exact hx3
  have hr_dvd_3a : orderOf r ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hr3a
  have hr_dvd_R : orderOf r ∣ Nat.card R₀ := Subgroup.orderOf_dvd_natCard R₀ hr
  have hcop : Nat.Coprime 3 (Nat.card R₀) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR₀3
  have hr1 : r = 1 := by
    have h1 : orderOf r ∣ Nat.gcd (3 ^ a) (Nat.card R₀) := Nat.dvd_gcd hr_dvd_3a hr_dvd_R
    have hcop' : Nat.Coprime (3 ^ a) (Nat.card R₀) := hcop.pow_left a
    rw [hcop'.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  rw [hr1, one_mul]
  exact heE

private theorem conj_pow_eq_pow_two_pow {X : Type} [Group X] {n z : X}
    (h : n * z * n⁻¹ = z ^ 2) : ∀ j : ℕ, n ^ j * z * (n ^ j)⁻¹ = z ^ (2 ^ j)
  | 0 => by simp
  | j + 1 => by
      have hj := conj_pow_eq_pow_two_pow h j
      calc n ^ (j + 1) * z * (n ^ (j + 1))⁻¹ = n * (n ^ j * z * (n ^ j)⁻¹) * n⁻¹ := by group
        _ = (n * z * n⁻¹) ^ (2 ^ j) := by rw [hj, conj_pow]
        _ = z ^ (2 ^ (j + 1)) := by rw [h, ← pow_mul, pow_succ, mul_comm]

private theorem conj_eq_of_mem_zpowers_of_pow_eq_one {X : Type} [Group X] {n z : X}
    (hz : orderOf z = 3) {k : ℕ} (hn : n ^ (3 ^ k) = 1) (h : n * z * n⁻¹ ∈ zpowers z) :
    n * z * n⁻¹ = z := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp h
  have hm' : z ^ (m % 3) = n * z * n⁻¹ := by
    rw [← hm, ← zpow_mod_orderOf z m, hz]
    norm_cast
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hm'
    exact absurd (by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [← hm']; group) hz1
  · rw [h1, zpow_one] at hm'
    exact hm'.symm
  · rw [h2] at hm'
    have hsq : n * z * n⁻¹ = z ^ 2 := by rw [← hm']; norm_cast
    have hpow := conj_pow_eq_pow_two_pow hsq (3 ^ k)
    rw [hn, one_mul, inv_one, mul_one] at hpow
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨t, ht⟩ := hodd
    have hmod : 2 ^ (3 ^ k) % 3 = 2 := by
      rw [ht, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hz2 : z = z ^ 2 := by
      rw [← pow_mod_orderOf, hz, hmod] at hpow
      exact hpow
    have h3 : z * z = z * 1 := by rw [mul_one, ← pow_two]; exact hz2.symm
    exact absurd (mul_left_cancel h3) hz1


open TwD7Q in
theorem card_zb_twD7 {G : Type} [Group G] (B : Basis3 G 8) :
    Nat.card ↥(zb (B.b 0 * B.b 1)) = 3 := by
  rw [zb, card_subgroupOf_eq (zpowers_le_cen _), Nat.card_zpowers]
  exact orderOf_b_mul_b B (by decide)

open TwD7Q in
theorem card_le_nine_of_isPGroup_centralizer_m0_inf_centralizer_beta_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    {S : Subgroup G}
    (hS : S ≤ centralizer (twD7M0 K B : Set G) ⊓ centralizer ({B.b 0 * B.b 1} : Set G))
    (h3 : IsPGroup 3 S) : Nat.card S ≤ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hspan, rfl, -⟩ := id hB
  obtain ⟨-, ⟨⟨-, hKC, -, -, -, -, -, -⟩, -, -, -, -, -⟩, -, -, hsup, -, -, -⟩ := id hstd
  have hM₀K : twD7M0 K B ≤ K := (commutator_le_self _).trans inf_le_right
  have hM₀C1 : twD7M0 K B ≤ centralizer ({B.b 1} : Set G) :=
    (commutator_le_self _).trans inf_le_left
  have hb₀M : B.b 0 ∈ centralizer (twD7M0 K B : Set G) := fun m hm =>
    mem_centralizer_singleton_iff.mp (hKC (hM₀K hm))
  have hb₁M : B.b 1 ∈ centralizer (twD7M0 K B : Set G) := fun m hm =>
    mem_centralizer_singleton_iff.mp (hM₀C1 hm)
  have hβM : B.b 0 * B.b 1 ∈ centralizer (twD7M0 K B : Set G) := mul_mem hb₀M hb₁M
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G, F = ((zpowers (B.twD7Quot.b 0)).comap
      (pr (B.b 0 * B.b 1))).map (cen (B.b 0 * B.b 1)).subtype := ⟨_, rfl⟩
  have hmemF : ∀ x : ↥(cen (B.b 0 * B.b 1)), (x : G) ∈ F ↔
      pr (B.b 0 * B.b 1) x ∈ zpowers (B.twD7Quot.b 0) := by
    intro x
    rw [hFdef, mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← Subtype.ext hyx]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hFcen : F ≤ cen (B.b 0 * B.b 1) := by
    rw [hFdef]; exact map_subtype_le _
  have hFcard : Nat.card F = 9 := by
    rw [hFdef, card_map_of_injective (cen _).subtype_injective]
    have h := QuotientGroup.card_preimage_mk (zb (B.b 0 * B.b 1))
      ((zpowers (B.twD7Quot.b 0) : Subgroup (Q (B.b 0 * B.b 1))) : Set (Q (B.b 0 * B.b 1)))
    rw [card_zb_twD7 B, SetLike.coe_sort_coe, Nat.card_zpowers,
      B.twD7Quot.ord 0] at h
    exact h
  have hF3 : IsPGroup 3 F := IsPGroup.of_card (n := 2) (by rw [hFcard]; norm_num)
  have hb₀F : B.b 0 ∈ F := by
    rw [show B.b 0 = ((⟨B.b 0, B.b_mem_cen_twD7 0⟩ : ↥(cen (B.b 0 * B.b 1))) : G) from rfl,
      hmemF, B.pr_b_zero_twD7Quot]
    exact mem_zpowers _
  have hb₁F : B.b 1 ∈ F := by
    rw [show B.b 1 = ((⟨B.b 1, B.b_mem_cen_twD7 1⟩ : ↥(cen (B.b 0 * B.b 1))) : G) from rfl,
      hmemF, B.pr_b_one_twD7Quot]
    exact inv_mem (mem_zpowers _)
  have hFC : F ≤ centralizer (twD7M0 K B : Set G) ⊓ centralizer ({B.b 0 * B.b 1} : Set G) := by
    intro x hx
    refine ⟨?_, hFcen hx⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp ((hmemF ⟨x, hFcen hx⟩).mp hx)
    have hpr : pr (B.b 0 * B.b 1) ((⟨B.b 0, B.b_mem_cen_twD7 0⟩ : ↥(cen (B.b 0 * B.b 1))) ^ i) =
        pr (B.b 0 * B.b 1) ⟨x, hFcen hx⟩ := by
      rw [map_zpow, B.pr_b_zero_twD7Quot]; exact hi
    rw [pr_eq_pr_iff, Subgroup.coe_zpow] at hpr
    have hxeq : x = B.b 0 ^ i * ((B.b 0 ^ i)⁻¹ * x) := by group
    rw [hxeq]
    exact mul_mem (zpow_mem hb₀M i) (zpowers_le.mpr hβM hpr)
  have key : ∀ g ∈ centralizer (twD7M0 K B : Set G) ⊓ centralizer ({B.b 0 * B.b 1} : Set G),
      ∀ k : ℕ, g ^ (3 ^ k) = 1 → g * B.b 0 * g⁻¹ ∈ F → g ∈ F := by
    intro g hg k hk hgF
    obtain ⟨hgM, hgβ⟩ := hg
    have hgβ' : g * (B.b 0 * B.b 1) = B.b 0 * B.b 1 * g := mem_centralizer_singleton_iff.mp hgβ
    have hconj : pr (B.b 0 * B.b 1) ⟨g, hgβ⟩ * B.twD7Quot.b 0 *
        (pr (B.b 0 * B.b 1) ⟨g, hgβ⟩)⁻¹ = B.twD7Quot.b 0 := by
      refine conj_eq_of_mem_zpowers_of_pow_eq_one (B.twD7Quot.ord 0) (k := k) ?_ ?_
      · rw [← map_pow]
        have : (⟨g, hgβ⟩ : ↥(cen (B.b 0 * B.b 1))) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
        rw [this, map_one]
      · have h := (hmemF ⟨g * B.b 0 * g⁻¹, hFcen hgF⟩).mp hgF
        have he : pr (B.b 0 * B.b 1) ⟨g * B.b 0 * g⁻¹, hFcen hgF⟩ =
            pr (B.b 0 * B.b 1) ⟨g, hgβ⟩ * B.twD7Quot.b 0 * (pr (B.b 0 * B.b 1) ⟨g, hgβ⟩)⁻¹ := by
          rw [← B.pr_b_zero_twD7Quot, ← map_inv, ← map_mul, ← map_mul]; rfl
        rw [← he]; exact h
    have hcl : (B.b 0)⁻¹ * (g * B.b 0 * g⁻¹) ∈ zpowers (B.b 0 * B.b 1) := by
      rw [← B.pr_b_zero_twD7Quot, ← map_inv, ← map_mul, ← map_mul] at hconj
      have h := (pr_eq_pr_iff _ _).mp hconj.symm
      simpa using h
    have hg0 : g * B.b 0 * g⁻¹ = B.b 0 := conj_b_zero_eq_of_mem_zpowers_twD7 hrec hgβ' hcl
    have hc0 : g * B.b 0 = B.b 0 * g := by
      calc g * B.b 0 = g * B.b 0 * g⁻¹ * g := by group
        _ = B.b 0 * g := by rw [hg0]
    have hgβc : g * (B.b 0 * B.b 1) * g⁻¹ = B.b 0 * B.b 1 := by rw [hgβ']; group
    have hc1 : g * B.b 1 = B.b 1 * g := by
      have h1 : g * B.b 1 * g⁻¹ = B.b 1 := by
        calc g * B.b 1 * g⁻¹ = (g * B.b 0 * g⁻¹)⁻¹ * (g * (B.b 0 * B.b 1) * g⁻¹) := by group
          _ = B.b 1 := by rw [hg0, hgβc]; group
      calc g * B.b 1 = g * B.b 1 * g⁻¹ * g := by group
        _ = B.b 1 * g := by rw [h1]
    have hcb : ∀ i : Fin 8, g * B.b i = B.b i * g := by
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact hc0
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j, rfl⟩
      · exact hc1
      · exact (mem_centralizer_iff.mp hgM _
          (tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec j)).symm
    have hgE : g ∈ centralizer (E : Set G) := by
      rw [← hspan]
      refine mem_centralizer_iff.mpr fun x hx => ?_
      have hle : B.span ≤ centralizer ({g} : Set G) := by
        rw [Basis3.span, closure_le]
        rintro y ⟨i, rfl⟩
        exact mem_centralizer_singleton_iff.mpr (hcb i).symm
      exact mem_centralizer_singleton_iff.mp (hle hx)
    have hgE' : g ∈ E := mem_E_of_three_element_centralizer_E_twD7 hstd hB hrec hgE
      (a := k + 1) (by omega) (by rw [pow_succ, pow_mul, hk, one_pow])
    have hb₀K : B.b 0 ∈ centralizer (K : Set G) := mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (hKC hx)
    have hcomm1 : ∀ a ∈ zpowers (B.b 0), ∀ b ∈ E ⊓ K, a * b = b * a := fun a ha b hb =>
      (mem_centralizer_iff.mp (zpowers_le.mpr hb₀K ha) b hb.2).symm
    obtain ⟨z, hz, y, hy, rfl⟩ := fs81Sp_mem_sup_of_commute hcomm1 (by rw [hsup]; exact hgE')
    have hzc : z ∈ centralizer ({B.b 1} : Set G) := by
      refine zpowers_le.mpr ?_ hz
      rw [mem_centralizer_singleton_iff]
      exact (B.comm 0 1).eq
    have hyc : y ∈ centralizer ({B.b 1} : Set G) := by
      have hyeq : y = z⁻¹ * (z * y) := by group
      rw [hyeq]
      exact mul_mem (inv_mem hzc) (mem_centralizer_singleton_iff.mpr hc1)
    obtain ⟨hCdec, -, -⟩ := centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec
    have hCdec' : centralizer ({B.b 1} : Set G) ⊓ K = zpowers (B.b 1) ⊔ twD7M0 K B := hCdec
    have hyCK : y ∈ centralizer ({B.b 1} : Set G) ⊓ K := ⟨hyc, hy.2⟩
    rw [hCdec'] at hyCK
    have hcomm2 : ∀ a ∈ zpowers (B.b 1), ∀ b ∈ twD7M0 K B, a * b = b * a := fun a ha b hb =>
      (mem_centralizer_iff.mp (zpowers_le.mpr hb₁M ha) b hb).symm
    obtain ⟨w, hw, m, hm, rfl⟩ := fs81Sp_mem_sup_of_commute hcomm2 hyCK
    have hmC : m ∈ centralizer (twD7M0 K B : Set G) := by
      have hmeq : m = w⁻¹ * (z⁻¹ * (z * (w * m))) := by group
      rw [hmeq]
      exact mul_mem (inv_mem (zpowers_le.mpr hb₁M hw))
        (mul_mem (inv_mem (zpowers_le.mpr hb₀M hz)) hgM)
    obtain ⟨e⟩ := nonempty_mulEquiv_om12_m0_twD7 hstd hB hrec
    obtain ⟨-, -, hZ, -⟩ := isRow_D6_of_mulEquiv_om12 e
    have hZ' : center ↥(twD7M0 K B) = ⊥ := hZ
    have hm1 : m = 1 := by
      have hmZ : (⟨m, hm⟩ : ↥(twD7M0 K B)) ∈ center ↥(twD7M0 K B) := by
        rw [mem_center_iff]
        intro x
        exact Subtype.ext (mem_centralizer_iff.mp hmC x x.2)
      rw [hZ', mem_bot] at hmZ
      exact congrArg Subtype.val hmZ
    rw [hm1, mul_one]
    exact mul_mem ((zpowers_le.mpr hb₀F) hz) ((zpowers_le.mpr hb₁F) hw)
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup G,
      C₁ = centralizer (twD7M0 K B : Set G) ⊓ centralizer ({B.b 0 * B.b 1} : Set G) := ⟨_, rfl⟩
  rw [← hC₁] at hS hFC key
  have hF'3 : IsPGroup 3 (F.subgroupOf C₁) :=
    hF3.comap_of_injective C₁.subtype C₁.subtype_injective
  obtain ⟨P, hFP⟩ := hF'3.exists_le_sylow
  have hPF : (P : Subgroup ↥C₁) ≤ F.subgroupOf C₁ := by
    haveI : Group.IsNilpotent ↥(P : Subgroup ↥C₁) := P.isPGroup'.isNilpotent
    have hself : normalizer (((F.subgroupOf C₁).subgroupOf P : Subgroup ↥(P : Subgroup ↥C₁)) :
        Set ↥(P : Subgroup ↥C₁)) = (F.subgroupOf C₁).subgroupOf P := by
      refine le_antisymm (fun x hx => ?_) le_normalizer
      rw [mem_subgroupOf, mem_subgroupOf]
      obtain ⟨k, hk⟩ := P.isPGroup' x
      refine key _ (x : ↥C₁).2 k ?_ ?_
      · have := congrArg (fun y : ↥(P : Subgroup ↥C₁) => ((y : ↥C₁) : G)) hk
        simpa using this
      · have hb : (⟨⟨B.b 0, hFC hb₀F⟩, hFP (mem_subgroupOf.mpr hb₀F)⟩ :
            ↥(P : Subgroup ↥C₁)) ∈ (F.subgroupOf C₁).subgroupOf P := by
          rw [mem_subgroupOf, mem_subgroupOf]; exact hb₀F
        have := (mem_normalizer_iff.mp hx _).mp hb
        rw [mem_subgroupOf, mem_subgroupOf] at this
        exact this
    have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup ↥C₁))) _ hself
    intro x hx
    have : (⟨x, hx⟩ : ↥(P : Subgroup ↥C₁)) ∈ (F.subgroupOf C₁).subgroupOf P := by
      rw [htop]; exact mem_top _
    exact mem_subgroupOf.mp this
  have hPcard : Nat.card ↥(P : Subgroup ↥C₁) ≤ 9 := by
    calc Nat.card ↥(P : Subgroup ↥C₁) ≤ Nat.card ↥(F.subgroupOf C₁) := card_le_of_le hPF
      _ = Nat.card F := card_subgroupOf_eq hFC
      _ = 9 := hFcard
  have hS'3 : IsPGroup 3 (S.subgroupOf C₁) :=
    h3.comap_of_injective C₁.subtype C₁.subtype_injective
  obtain ⟨P', hSP'⟩ := hS'3.exists_le_sylow
  calc Nat.card S = Nat.card ↥(S.subgroupOf C₁) := (card_subgroupOf_eq hS).symm
    _ ≤ Nat.card ↥(P' : Subgroup ↥C₁) := card_le_of_le hSP'
    _ = Nat.card ↥(P : Subgroup ↥C₁) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ ≤ 9 := hPcard


end CFSG.StandardType.FrameRoute.FS81
