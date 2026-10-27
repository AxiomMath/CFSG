module

public import CFSG.Walter.ReeOrder.JT.AuxTransitivity
public import CFSG.Walter.ReeOrder.JT.Section7R

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG CFSG.Walter.Transitivity

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem conjBy_mem_section7HFamily_top {A Q : Subgroup X} {π : Set Nat.Primes} {n : X}
    (hn : n ∈ Subgroup.normalizer (A : Set X)) (hQ : Q ∈ section7HFamily ⊤ A π) :
    Q.conjBy n ∈ section7HFamily ⊤ A π := by
  refine ⟨le_top, hQ.2.1.map (MulAut.conj n).toMonoidHom, fun a ha => ?_⟩
  have ha' : n⁻¹ * a * n ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) a).mp ha
    simpa using this
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (Subgroup.mem_normalizer_iff.mp (hQ.2.2 ha') y).mp hy
  refine ⟨(n⁻¹ * a * n) * y * (n⁻¹ * a * n)⁻¹, hy', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conjBy_mem_section7HStarFamily_top {A Q : Subgroup X} {π : Set Nat.Primes} {n : X}
    (hn : n ∈ Subgroup.normalizer (A : Set X)) (hQ : Q ∈ section7HStarFamily ⊤ A π) :
    Q.conjBy n ∈ section7HStarFamily ⊤ A π := by
  refine ⟨conjBy_mem_section7HFamily_top hn hQ.1, fun R hQR hR => ?_⟩
  have hR' : R.conjBy n⁻¹ ∈ section7HFamily ⊤ A π :=
    conjBy_mem_section7HFamily_top (Subgroup.inv_mem _ hn) hR
  have hle : Q ≤ R.conjBy n⁻¹ :=
    (Subgroup.conjBy_inv Q n).symm.le.trans (conjBy_mono n⁻¹ hQR)
  calc R = (R.conjBy n⁻¹).conjBy n := (Subgroup.conjBy_inv' R n).symm
    _ = Q.conjBy n := by rw [hQ.2 _ hle hR']

theorem normal_sylow_of_pPrimeCore_eq_bot {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hsolv : Group.IsSolvable X) (hcore : pPrimeCore p X = ⊥) (S : Sylow p X)
    (hS : ∀ x ∈ (S : Subgroup X), x ^ p = 1 → ∀ y ∈ (S : Subgroup X), x * y = y * x) :
    (S : Subgroup X).Normal := by
  classical
  set D := pCore p X with hDdef
  have hDn : D.Normal := pCore_normal
  have hDp : IsPGroup p D := pCore_isPGroup
  have hchar : Subgroup.centralizer (D : Set X) ≤ D := by
    rw [hDdef, ← Fitting_eq_pcore X p hcore]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  have hDS : D ≤ S := hDp.le_sylow_of_normal S
  set E : Set X := {x | x ∈ D ∧ x ^ p = 1} with hEdef
  set Y := Subgroup.centralizer E with hYdef
  have hSY : (S : Subgroup X) ≤ Y := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hS x (hDS hx.1) hx.2 y hy
  have hYn : Y.Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ E := by
      refine ⟨?_, ?_⟩
      · have := hDn.conj_mem x hx.1 g⁻¹
        simpa using this
      · rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hx.2]
        group
    have := hy _ hx'
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * x := by group
  have hp'1 : ∀ g ∈ Y, Nat.Coprime (orderOf g) p → g = 1 := by
    intro g hg hgp
    have hgD : Subgroup.zpowers g ≤ Subgroup.normalizer (D : Set X) := by
      rw [Subgroup.zpowers_le]
      have := hDn
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card D) := by
      obtain ⟨n, hn⟩ := hDp.exists_card_eq
      rw [hn, Nat.card_zpowers]
      exact Nat.Coprime.pow_right _ hgp
    have hfix : ∀ y ∈ Subgroup.zpowers g, ∀ x ∈ D, x ^ p = 1 → y * x = x * y := by
      intro y hy x hx hxp
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgx := Subgroup.mem_centralizer_iff.mp hg x ⟨hx, hxp⟩
      exact (Commute.zpow_left (hgx.symm : Commute g x) k).eq
    have hgC := le_centralizer_of_forall_pow_eq_one hp2 hDp hcop hgD hfix
      (Subgroup.mem_zpowers g)
    have hgD' : g ∈ D := hchar hgC
    obtain ⟨k, hk⟩ := hDp ⟨g, hgD'⟩
    have h1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hgp.pow_right k) dvd_rfl h1)
  have hYp : IsPGroup p Y := by
    intro y
    obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (y : X)).ne' p
      hp.out.ne_one
    refine ⟨a, ?_⟩
    have hdvd : p ^ a ∣ orderOf (y : X) := ⟨m, hom⟩
    have ho : orderOf ((y : X) ^ p ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) hdvd, hom,
        Nat.mul_div_cancel_left _ (pow_pos hp.out.pos a)]
    have h1 := hp'1 ((y : X) ^ p ^ a) (Y.pow_mem y.2 _) (by
      rw [ho]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)))
    exact Subtype.ext (by simpa using h1)
  have hYD : Y ≤ D := le_sSup ⟨hYn, hYp⟩
  have hSD : (S : Subgroup X) = D := le_antisymm (hSY.trans hYD) hDS
  rw [hSD]
  exact hDn

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem odd_card_centralizer_sylow
    {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) (hnc : ¬ IsCyclic (P : Subgroup G)) :
    Odd (Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨⟨u, huC⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer
    ((P : Subgroup G) : Set G)) 2 h2
  have hu' : orderOf u = 2 := by rw [← hu, Subgroup.orderOf_mk]
  have hPu : (P : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huC y hy)
  exact hnc (h.isCyclic_of_le_centralizer_pi hp3 hpq P.isPGroup' hu' hPu)

theorem lemma_7_13
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) (hnc : ¬ IsCyclic (P : Subgroup G)) {H : Subgroup G} (hH : IsPGroup 3 H)
    (hPH : (P : Subgroup G) ≤ Subgroup.normalizer (H : Set G)) : H = ⊥ := by
  classical
  have hS := CFSG.Walter.suzukiFourGroupTheorem
  have hp7 := h.seven_le_of_pi hp3 hpq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hWcard, -⟩ := h.lemma_7_8 hp3 c hpq P hnc
  obtain ⟨h4, -, -, -, -⟩ := h.sylow_facts hp3 c hpq P
  set W := omegaZ (P : Subgroup G) p with hWdef
  set q3 : Nat.Primes := ⟨3, Nat.prime_three⟩
  have hsolv : ∀ v ∈ W, v ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({v} : Set G)) := by
    intro v hv hv1
    refine h.lemma_7_7_a hp3 hS fun h2 => hv1 ?_
    have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h2' : orderOf v ∣ p := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_omegaZ hv)
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes this h1 h2')
  have htrans := thompson_transitivity_of_prime P (V := W) omegaZ_le
    (fun v hv y hy => (hv.2.1 y hy).symm)
    ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_omegaZ a.2 b.2)⟩⟩
    (fun x hx => pow_eq_one_of_mem_omegaZ hx) hWcard.symm.le hsolv (q := q3)
    (by change 3 ≠ p; omega) (le_top : (P : Subgroup G) ≤ ⊤)
  have hHF : H ∈ section7HFamily ⊤ (P : Subgroup G) ({q3} : Set Nat.Primes) :=
    ⟨le_top, isPiSubgroup_singleton_of_isPGroup (q := q3) hH, hPH⟩
  obtain ⟨H₀, hH₀, hHH₀⟩ := exists_mem_section7HStarFamily_of_mem_family hHF
  suffices hH₀1 : H₀ = ⊥ from le_bot_iff.mp (hH₀1 ▸ hHH₀)
  have hH₀3 : IsPGroup 3 H₀ := isPGroup_of_isPiSubgroup_singleton (q := q3) hH₀.1.2.1
  set NP := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNPdef
  set CP := Subgroup.centralizer ((P : Subgroup G) : Set G) with hCPdef
  set N₁ := NP ⊓ Subgroup.normalizer (H₀ : Set G) with hN₁def
  have hfrat : ∀ n ∈ NP, ∃ k ∈ CP, k⁻¹ * n ∈ Subgroup.normalizer (H₀ : Set G) := by
    intro n hn
    obtain ⟨k, hk⟩ := htrans H₀ hH₀ _ (conjBy_mem_section7HStarFamily_top hn hH₀)
    refine ⟨k, k.2.2, ?_⟩
    have h1 : H₀.conjBy ((k : G)⁻¹ * n) = H₀ := Subgroup.conjBy_inv_mul_cancel H₀ hk.symm
    exact (conj_smul_eq_iff (K := H₀)).mp h1
  have hCPN : CP ≤ NP := Subgroup.centralizer_le_normalizer _
  set K' := CP.subgroupOf NP with hK'def
  set H' := N₁.subgroupOf NP with hH'def
  have hK'n : K'.Normal := centralizer_subgroupOf_normalizer_normal (P : Subgroup G)
  have hsup : K' ⊔ H' = ⊤ := by
    refine eq_top_iff.mpr fun n _ => ?_
    obtain ⟨k, hkC, hkn⟩ := hfrat n n.2
    have hkN : k ∈ NP := hCPN hkC
    have h1 : (⟨k, hkN⟩ : NP) ∈ K' := hkC
    have h2 : (⟨k, hkN⟩ : NP)⁻¹ * n ∈ H' := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨NP.mul_mem (NP.inv_mem hkN) n.2, hkn⟩
    have : n = (⟨k, hkN⟩ : NP) * ((⟨k, hkN⟩ : NP)⁻¹ * n) := by group
    rw [this]
    exact Subgroup.mul_mem_sup h1 h2
  have hidx : K'.index ∣ Nat.card N₁ := by
    have h1 := Subgroup.relIndex_sup_left H' K'
    rw [hsup, Subgroup.relIndex_top_right] at h1
    rw [h1, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N₁ ≤ NP)).toEquiv]
    exact Subgroup.relIndex_dvd_card _ _
  have hK'card : Nat.card K' = Nat.card CP :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCPN).toEquiv
  have h4K : 4 ∣ K'.index := by
    have h1 := K'.card_mul_index
    rw [hK'card] at h1
    have hcop : Nat.Coprime 4 (Nat.card CP) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr
        (h.odd_card_centralizer_sylow hp3 hpq P hnc))
    exact hcop.dvd_of_dvd_mul_left (h1 ▸ h4)
  have h4N : 4 ∣ Nat.card N₁ := h4K.trans hidx
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := N₁) 2 (n := 2)
    (by norm_num; exact h4N)
  refine h.eq_bot_of_isPGroup_three_of_le_normalizer hp3 hH₀3 (W := V₀.map N₁.subtype)
    ((IsPGroup.of_card hV₀).map _) ?_ ?_
  · rw [Subgroup.card_map_of_injective N₁.subtype_injective, hV₀]
    norm_num
  · rintro _ ⟨v, -, rfl⟩
    exact v.2.2

end JTHyp

end CFSG.Walter.JT
