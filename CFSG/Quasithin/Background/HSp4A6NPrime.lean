module

public import CFSG.Quasithin.Background.HSp4A6Pair
public import CFSG.Quasithin.Background.HPairNPrime
public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.Background.HSL3NPrime

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4A6

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open scoped Pointwise

abbrev A6Aut : Type := MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2))

theorem card_stdMod : Nat.card (StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)) = 16 := by
  rw [Nat.card_congr (Multiplicative.toAdd : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) ≃ _), Nat.card_fun,
    Nat.card_sum, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem pairHom_injective :
    Function.Injective (pairHom Γ₆ tau₆) := by
  intro γ δ h
  rw [pairHom_apply, pairHom_apply] at h
  exact natAut_injective Γ₆ (pairAut_injective h).1

theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_Γ₆ : Nat.card ↥Γ₆ = 360 := by
  rw [← card_A6]
  exact (Nat.card_congr psiEquiv.toEquiv).symm

theorem card_pairImg : Nat.card (pairImg Γ₆ tau₆) = 360 := by
  rw [← card_Γ₆]
  exact (Nat.card_congr (MonoidHom.ofInjective pairHom_injective).toEquiv).symm

theorem isSimpleGroup_pairImg :
    IsSimpleGroup ↥(pairImg Γ₆ tau₆) := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : Nontrivial ↥(pairImg Γ₆ tau₆) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_pairImg]
    norm_num
  let f : alternatingGroup (Fin 6) →* ↥(pairImg Γ₆ tau₆) :=
    (MonoidHom.ofInjective pairHom_injective).toMonoidHom.comp psiEquiv.toMonoidHom
  refine IsSimpleGroup.isSimpleGroup_of_surjective f fun y => ?_
  obtain ⟨γ, hγ⟩ := (MonoidHom.ofInjective pairHom_injective).surjective y
  obtain ⟨σ, rfl⟩ := psiEquiv.surjective γ
  exact ⟨σ, hγ⟩

theorem natAut_eq_one_iff {γ : ↥Γ₆} :
    natAut Γ₆ γ = 1 ↔ γ = 1 :=
  ⟨fun h => natAut_injective Γ₆ (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

theorem orderOf_natAut (γ : ↥Γ₆) :
    orderOf (natAut Γ₆ γ) = orderOf γ :=
  orderOf_injective (natAut Γ₆) (natAut_injective Γ₆) γ

theorem orderOf_tau₆ (γ : ↥Γ₆) : orderOf (tau₆ γ) = orderOf γ :=
  orderOf_injective tau₆ (fun a b h => by rw [← tau₆_tau₆ a, h, tau₆_tau₆]) γ

theorem mem_pairImg_of_odd
    {x : MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2))} (hx : x ∈ pairNorm Γ₆ tau₆) {p : ℕ}
    (hp : Odd p) (hxp : x ^ p = 1) : x ∈ pairImg Γ₆ tau₆ := by
  have h1 := PairN.map_V₁_of_pow_odd isNatIrr tau₆_surjective not_isoMod hx hp hxp
  obtain ⟨B, rfl⟩ := mem_pairSp_of_map hx h1
  obtain ⟨σ, hσ⟩ := exists_psi_of_mem_statedSp B.2
  have hBp : B ^ p = 1 := by
    have h := hxp
    rw [← map_pow, pairHom_apply, ← pairAut_one] at h
    exact natAut_injective _ ((pairAut_injective h).1.trans (map_one _).symm)
  have hσp : σ ^ p = 1 := by
    apply psiHom_injective
    rw [map_pow, hσ, map_one]
    exact congrArg Subtype.val hBp
  have hsign : Perm.sign σ = 1 := by
    have h := congrArg Perm.sign hσp
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
    · exact hs
    · rw [hs, Odd.neg_one_pow hp] at h
      exact absurd h (by decide)
  have hγ : (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) ∈ Γ₆ := mem_Γ₆_iff.mpr ⟨σ, hsign, hσ⟩
  exact ⟨⟨B, hγ⟩, rfl⟩

theorem psiEquiv_conj (σ : alternatingGroup (Fin 6))
    (g : Perm (Fin 6)) :
    psiEquiv ⟨g * σ * g⁻¹, (alternatingGroup.normal (α := Fin 6)).conj_mem _ σ.2 g⟩ =
      conjB ⟨psiHom g, mem_statedSp_of_psi g⟩ (psiEquiv σ) := by
  apply Subtype.ext
  rw [coe_conjB]
  change psiHom (g * σ * g⁻¹) = psiHom g * psiHom σ * (psiHom g)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem card_fix_of_isConj {σ ρ : alternatingGroup (Fin 6)}
    (h : IsConj (σ : Perm (Fin 6)) ρ) :
    Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (psiEquiv σ) v = v} =
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (psiEquiv ρ) v = v} ∧
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
          natAut Γ₆ (tau₆ (psiEquiv σ)) v = v} =
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
          natAut Γ₆ (tau₆ (psiEquiv ρ)) v = v} := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hρ : ρ = ⟨g * σ * g⁻¹, (alternatingGroup.normal (α := Fin 6)).conj_mem _ σ.2 g⟩ :=
    Subtype.ext hg.symm
  rw [hρ, psiEquiv_conj, tau₆_conjB, card_fix_conjB, card_fix_conjB]
  exact ⟨rfl, rfl⟩

theorem isThreeCycle_cyc345 : (cyc345 : Perm (Fin 6)).IsThreeCycle := by
  rw [cyc345, Equiv.swap_comm]
  exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem cycleType_of_orderOf_three {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (h ▸ Nat.prime_three : (orderOf σ).Prime)
  rw [h] at hn
  have hsum := Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 6 := (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn1 : n ≤ 1 := by omega
  interval_cases n
  · left
    rw [hn]
    rfl
  · right
    rw [hn]
    rfl

theorem card_fix_of_orderOf_three {γ : ↥Γ₆}
    (h3 : orderOf γ = 3) :
    (Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ γ v = v} = 4 ∧
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (tau₆ γ) v = v} = 1) ∨
      (Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ γ v = v} = 1 ∧
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (tau₆ γ) v = v} = 4) := by
  set c : alternatingGroup (Fin 6) := ⟨cyc345, sign_cyc345⟩ with hcdef
  have hc : psiEquiv c = g₃ := Subtype.ext rfl
  have hord : ∀ σ : alternatingGroup (Fin 6), orderOf (σ : Perm (Fin 6)) =
      orderOf (psiEquiv σ) := fun σ => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hprof3 : ∀ σ : alternatingGroup (Fin 6), (σ : Perm (Fin 6)).cycleType = {3} →
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (psiEquiv σ) v = v} = 4 ∧
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
          natAut Γ₆ (tau₆ (psiEquiv σ)) v = v} = 1 := by
    intro σ hσ
    have hconj : IsConj (σ : Perm (Fin 6)) (c : Perm (Fin 6)) := by
      rw [Perm.isConj_iff_cycleType_eq, hσ]
      exact isThreeCycle_cyc345.symm
    obtain ⟨h1, h2⟩ := card_fix_of_isConj hconj
    rw [h1, h2, hc]
    exact ⟨card_fix_g₃, card_fix_tau_g₃⟩
  set σ₀ := psiEquiv.symm (tau₆ g₃) with hσ₀def
  have hσ₀ : psiEquiv σ₀ = tau₆ g₃ := MulEquiv.apply_symm_apply _ _
  have hprof₀ :
      Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (psiEquiv σ₀) v = v} = 1 ∧
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) //
          natAut Γ₆ (tau₆ (psiEquiv σ₀)) v = v} = 4 := by
    rw [hσ₀, tau₆_tau₆]
    exact ⟨card_fix_tau_g₃, card_fix_g₃⟩
  have hord₀ : orderOf (σ₀ : Perm (Fin 6)) = 3 := by
    rw [hord, hσ₀, orderOf_tau₆, ← hc, ← hord]
    exact isThreeCycle_cyc345.orderOf
  have hcyc₀ : (σ₀ : Perm (Fin 6)).cycleType = {3, 3} := by
    rcases cycleType_of_orderOf_three hord₀ with h | h
    · exfalso
      have h4 := (hprof3 σ₀ h).1
      rw [hprof₀.1] at h4
      exact absurd h4 (by norm_num)
    · exact h
  set σ := psiEquiv.symm γ with hσdef
  have hσ : psiEquiv σ = γ := MulEquiv.apply_symm_apply _ _
  have hordσ : orderOf (σ : Perm (Fin 6)) = 3 := by rw [hord, hσ, h3]
  rcases cycleType_of_orderOf_three hordσ with h | h
  · left
    rw [← hσ]
    exact hprof3 σ h
  · right
    have hconj : IsConj (σ : Perm (Fin 6)) (σ₀ : Perm (Fin 6)) := by
      rw [Perm.isConj_iff_cycleType_eq, h, hcyc₀]
    obtain ⟨h1, h2⟩ := card_fix_of_isConj hconj
    rw [← hσ, h1, h2]
    exact hprof₀

theorem not_commute_three_five {y z : ↥Γ₆} (hy : orderOf y = 3)
    (hz : orderOf z = 5) (hyz : y * z = z * y) : False := by
  have hz5 : ∀ w : ↥Γ₆, orderOf w = 5 → natAut Γ₆ w ^ 5 = 1 := fun w hw => by
    rw [← orderOf_natAut] at hw
    rw [← hw]
    exact pow_orderOf_eq_one _
  have hne : ∀ w : ↥Γ₆, orderOf w ≠ 1 → natAut Γ₆ w ≠ 1 := fun w hw h1 =>
    hw (by rw [natAut_eq_one_iff.mp h1, orderOf_one])
  have hc1 : natAut Γ₆ z * natAut Γ₆ y = natAut Γ₆ y * natAut Γ₆ z := by
    rw [← map_mul, ← map_mul, hyz]
  have hc2 : natAut Γ₆ (tau₆ z) * natAut Γ₆ (tau₆ y) =
      natAut Γ₆ (tau₆ y) * natAut Γ₆ (tau₆ z) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hyz]
  have h1 := (PairN.card_fix_of_commute_five card_stdMod (hz5 z hz) (hne z (by rw [hz]; norm_num))
    hc1).resolve_right (hne y (by rw [hy]; norm_num))
  have h2 := (PairN.card_fix_of_commute_five card_stdMod
    (hz5 (tau₆ z) (by rw [orderOf_tau₆, hz]))
    (hne (tau₆ z) (by rw [orderOf_tau₆, hz]; norm_num)) hc2).resolve_right
    (hne (tau₆ y) (by rw [orderOf_tau₆, hy]; norm_num))
  rcases card_fix_of_orderOf_three hy with ⟨h3, -⟩ | ⟨-, h4⟩
  · rw [h1] at h3
    exact absurd h3 (by norm_num)
  · rw [h2] at h4
    exact absurd h4 (by norm_num)

theorem eq_one_of_commute_five {t z : ↥Γ₆} (hz : orderOf z = 5)
    (htz : z * t = t * z) {k : ℕ} (ht : t ^ 2 ^ k = 1) : t = 1 := by
  have hz5 : natAut Γ₆ z ^ 5 = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have hz1 : natAut Γ₆ z ≠ 1 := fun h => by
    rw [natAut_eq_one_iff] at h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hcomm : natAut Γ₆ z * natAut Γ₆ t = natAut Γ₆ t * natAut Γ₆ z := by
    rw [← map_mul, ← map_mul, htz]
  have hpow : natAut Γ₆ t ^ 2 ^ k = 1 := by rw [← map_pow, ht, map_one]
  exact natAut_eq_one_iff.mp (PairN.eq_one_of_commute_five_of_two card_stdMod hz5 hz1 hcomm hpow)

theorem card_sylow_two_of_card {G : Type*} [Group G] [Finite G] {U L : Subgroup G}
    (hU : IsSylowIn 2 U L) (hL : Nat.card L = 360) : Nat.card U = 8 := by
  obtain ⟨k, hk⟩ := hU.isPGroup.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card (H := U) (K := L)
  rw [inf_eq_left.2 hU.le, hk, hL] at h1
  have h2 := hU.not_dvd_relIndex
  have hk9 : k < 9 := by
    by_contra hc
    push Not at hc
    have h3 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have h4 : 2 ^ k ≤ 360 := Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h1)
    omega
  rw [hk]
  interval_cases k <;> omega

theorem eq_eight_mul {r b s : ℕ} (hb : Odd b) (hbr : b ∣ r) (hrbs : r ∣ b * 2 ^ s)
    (h8 : 8 ∣ r) (hr : r ∣ 360) : r = 8 * b := by
  obtain ⟨q, rfl⟩ := hbr
  have hb0 : 0 < b := hb.pos
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (Nat.dvd_of_mul_dvd_mul_left hb0 hrbs)
  have hcop : Nat.Coprime 8 b := (Nat.coprime_comm.mp (Nat.coprime_two_right.mpr hb)).pow_left 3
  have h8' : 8 ∣ 2 ^ j := hcop.dvd_of_dvd_mul_left h8
  have h360 : 2 ^ j ∣ 360 := (Dvd.intro_left _ rfl).trans hr
  have hj9 : j < 9 := by
    by_contra hc
    push Not at hc
    have h3 : 2 ^ 9 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hc
    have h4 : 2 ^ j ≤ 360 := Nat.le_of_dvd (by norm_num) h360
    omega
  interval_cases j <;> omega

theorem eq_bot_of_permutes
    {X : Subgroup (A6Aut)}
    (hX1 : pairImg Γ₆ tau₆ ≤ X) (hX2 : X ≤ pairNorm Γ₆ tau₆)
    (hX3 : ∃ x ∈ X, x ∉ pairSub (Fin 2 ⊕ Fin 2) (ZMod 2))
    {B S : Subgroup (A6Aut)} (hBX : B ≤ X)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (A6Aut)) *
      (S : Set (A6Aut)) =
        (S : Set (A6Aut)) *
          (B : Set (A6Aut))) : B = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (A6Aut) := MulEquiv.finite_left
  set L := pairImg Γ₆ tau₆ with hL
  have hcardSub : ∀ {J K : Subgroup (A6Aut)}, J ≤ K →
      Nat.card (J.subgroupOf K) = Nat.card J := fun hJK =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJK).toEquiv
  have hBL : B ≤ L := fun b hb => mem_pairImg_of_odd (hX2 (hBX hb))
    (Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)) (pow_orderOf_eq_one b)
  obtain ⟨s, hsS, hs⟩ :=
    PairN.exists_swap_mem_sylow isNatIrr tau₆_surjective not_isoMod hX2 hX3 hS
  have hsX : s ∈ X := hS.le hsS
  obtain ⟨c, d, hcd⟩ := PairN.eq_swapAut_mul isNatIrr tau₆_surjective not_isoMod (hX2 hsX) hs
  set P := B ⊔ S with hPdef
  set R := P ⊓ L with hRdef
  have hsN : s ∈ Subgroup.normalizer (R : Set (A6Aut)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hRdef, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (le_sup_right (a := B) hsS)) y,
      Subgroup.mem_normalizer_iff.mp (hX2 hsX) y]
  have hBR : B ≤ R := le_inf le_sup_left hBL
  have hRL : R ≤ L := inf_le_right
  have hLnX : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  have hUR : S ⊓ L ≤ R := inf_le_inf_right L le_sup_right
  have hLc : Nat.card L = 360 := card_pairImg
  have hUc : Nat.card (S ⊓ L : Subgroup _) = 8 := card_sylow_two_of_card hU hLc
  obtain ⟨a, ha⟩ := hS.isPGroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by
    rw [ha]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hBodd)
  have hPc : Nat.card P = Nat.card B * Nat.card S :=
    SL3One.card_sup_of_permute hBS (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hRc : Nat.card R = 8 * Nat.card B := by
    refine eq_eight_mul (s := a) hBodd (Subgroup.card_dvd_of_le hBR) ?_ ?_ ?_
    · rw [← ha, ← hPc]
      exact Subgroup.card_dvd_of_le inf_le_left
    · rw [← hUc]
      exact Subgroup.card_dvd_of_le hUR
    · rw [← hLc]
      exact Subgroup.card_dvd_of_le hRL
  have hB45 : Nat.card B ∣ 45 := by
    have h1 : Nat.card R ∣ 360 := hLc ▸ Subgroup.card_dvd_of_le hRL
    rw [hRc, show (360 : ℕ) = 8 * 45 by norm_num] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hel : ∀ b ∈ B, ∃ β : ↥Γ₆, pairHom Γ₆ tau₆ β = b ∧ orderOf β = orderOf b :=
    fun b hb => by
      obtain ⟨β, hβ⟩ := hBL hb
      exact ⟨β, hβ, by rw [← hβ, orderOf_injective _ pairHom_injective]⟩
  by_contra hne
  have hB1 : Nat.card B ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hcases : Nat.card B = 3 ∨ Nat.card B = 5 ∨ Nat.card B = 9 ∨ Nat.card B = 15 ∨
      Nat.card B = 45 := by
    have key : ∀ m : ℕ, m ≤ 45 → m ∣ 45 → m ≠ 1 →
        m = 3 ∨ m = 5 ∨ m = 9 ∨ m = 15 ∨ m = 45 := by decide
    exact key _ (Nat.le_of_dvd (by norm_num) hB45) hB45 hB1
  have hex : ∀ p : ℕ, [Fact p.Prime] → p ∣ Nat.card B → ∃ b ∈ B, orderOf b = p := by
    intro p _ hp
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) p hp
    exact ⟨b, b.2, by rw [Subgroup.orderOf_coe, hb]⟩
  have h35 : ¬ (3 ∣ Nat.card B ∧ 5 ∣ Nat.card B) := by
    rintro ⟨h3, h5⟩
    obtain ⟨y, hyB, hy⟩ := hex 3 h3
    obtain ⟨z, hzB, hz⟩ := hex 5 h5
    obtain ⟨γ, hγ, hγo⟩ := hel y hyB
    obtain ⟨ζ, hζ, hζo⟩ := hel z hzB
    refine not_commute_three_five (hγo.trans hy) (hζo.trans hz) (pairHom_injective ?_)
    rw [map_mul, map_mul, hγ, hζ]
    exact hBab _ hyB _ hzB
  rcases hcases with h | h | h | h | h
  ·
    have hRc' : Nat.card R = 24 := by rw [hRc, h]
    set B₂ := B.map (MulAut.conj s).toMonoidHom with hB₂
    have hB₂R : B₂ ≤ R := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hsN b).mp (hBR hb)
    have hB₂c : Nat.card B₂ = 3 := by
      rw [hB₂, Subgroup.card_map_of_injective (MulAut.conj s).injective, h]
    have hsyl : ∀ {J : Subgroup (A6Aut)}, J ≤ R →
        Nat.card J = 3 → ∃ Q : Sylow 3 ↥R, (Q : Subgroup ↥R) = J.subgroupOf R := by
      intro J hJ hJc
      have hp : IsPGroup 3 (J.subgroupOf R) :=
        IsPGroup.of_card (n := 1) (by rw [hcardSub hJ, hJc, pow_one])
      have hidx : ¬ 3 ∣ (J.subgroupOf R).index := by
        have := (J.subgroupOf R).card_mul_index
        rw [hcardSub hJ, hJc, hRc'] at this
        omega
      exact ⟨hp.toSylow hidx, rfl⟩
    obtain ⟨Q₁, hQ₁⟩ := hsyl hBR h
    obtain ⟨Q₂, hQ₂⟩ := hsyl hB₂R hB₂c
    obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (↥R) Q₁ Q₂
    obtain ⟨b, hbB, hb1⟩ := (Subgroup.bot_or_exists_ne_one B).resolve_left hne
    have hsbR : s * (b : A6Aut) * s⁻¹ ∈ R := hB₂R ⟨b, hbB, rfl⟩
    have hsb : (⟨s * (b : A6Aut) * s⁻¹, hsbR⟩ : ↥R) ∈ (Q₂ : Subgroup ↥R) := by
      rw [hQ₂]
      exact ⟨b, hbB, rfl⟩
    rw [← hr, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hQ₁,
      Subgroup.mem_subgroupOf] at hsb
    have e : (((MulAut.conj r)⁻¹ • (⟨s * (b : A6Aut) * s⁻¹, hsbR⟩ : ↥R) : ↥R) :
        A6Aut) =
          (r : A6Aut)⁻¹ * (s * (b : A6Aut) * s⁻¹) * (r : A6Aut) := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      rfl
    rw [e] at hsb
    set b' := (r : A6Aut)⁻¹ * (s * (b : A6Aut) * s⁻¹) * (r : A6Aut)
      with hb'def
    have hbo : orderOf (b : A6Aut) = 3 := by
      have h1 : orderOf (b : A6Aut) ∣ 3 :=
        h ▸ Subgroup.orderOf_dvd_natCard B hbB
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hb1
      · exact h1
    have hzp : Subgroup.zpowers (b : A6Aut) = B :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hbB)
        (by rw [Nat.card_zpowers, hbo, h])
    have hb'1 : b' ≠ 1 := by
      intro h1
      apply hb1
      have h2 : s * (b : A6Aut) * s⁻¹ = 1 := by
        calc s * (b : A6Aut) * s⁻¹ = (r : A6Aut) * b' * (r : A6Aut)⁻¹ := by
              rw [hb'def]; group
          _ = 1 := by rw [h1]; group
      calc (b : A6Aut) = s⁻¹ * (s * b * s⁻¹) * s := by group
        _ = 1 := by rw [h2]; group
    have hbb' : b' = b ∨ b' = (b : A6Aut)⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ hsb)
      rw [← hk, ← zpow_mod_orderOf, hbo] at hb'1 ⊢
      have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
        omega
      rcases hk3 with h0 | h1 | h2
      · rw [h0, zpow_zero] at hb'1
        exact absurd rfl hb'1
      · left
        rw [h1, zpow_one]
      · right
        rw [h2]
        have h3 : (b : A6Aut) ^ 3 = 1 := by
          rw [← hbo]
          exact pow_orderOf_eq_one _
        rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
    obtain ⟨β, hβ, hβo⟩ := hel b hbB
    have hrL : (r : A6Aut) ∈ L := hRL r.2
    obtain ⟨ρ, hρ⟩ := hrL
    have hβ3 : orderOf β = 3 := hβo.trans hbo
    have hconj : s * (b : A6Aut) * s⁻¹ =
        (r : A6Aut) * b' * (r : A6Aut)⁻¹ := by
      rw [hb'def]; group
    have hfix' : ∃ β' : ↥Γ₆, pairHom Γ₆ tau₆ β' = b' ∧
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ β' v = v} =
          Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ β v = v} := by
      rcases hbb' with e1 | e1
      · exact ⟨β, by rw [hβ, e1], rfl⟩
      · refine ⟨β⁻¹, by rw [map_inv, hβ, e1], ?_⟩
        rw [map_inv]
        exact PairN.card_fix_inv _
    obtain ⟨β', hβ', hfixβ'⟩ := hfix'
    rw [← hβ, ← hβ', ← hρ, hcd, pairHom_apply, pairHom_apply, pairHom_apply,
      PairN.conj_swapAut_mul_pairAut, pairAut_inv, pairAut_mul, pairAut_mul] at hconj
    have h1 := (pairAut_injective hconj).1
    have h2 : Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ (tau₆ β) v = v} =
        Nat.card {v : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) // natAut Γ₆ β v = v} := by
      rw [← Sp4.card_fix_conj d (natAut Γ₆ (tau₆ β)), h1, Sp4.card_fix_conj, hfixβ']
    rcases card_fix_of_orderOf_three hβ3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3, h4] at h2
      exact absurd h2 (by norm_num)
    · rw [h3, h4] at h2
      exact absurd h2 (by norm_num)
  ·
    have hRc' : Nat.card R = 40 := by rw [hRc, h]
    obtain ⟨z, hzB, hz⟩ := hex 5 (by rw [h])
    have hBn : (B.subgroupOf R).Normal := by
      have hp : IsPGroup 5 (B.subgroupOf R) :=
        IsPGroup.of_card (n := 1) (by rw [hcardSub hBR, h, pow_one])
      have hidx : (B.subgroupOf R).index = 8 := by
        have := (B.subgroupOf R).card_mul_index
        rw [hcardSub hBR, h, hRc'] at this
        omega
      let Q : Sylow 5 ↥R := hp.toSylow (by rw [hidx]; norm_num)
      have hcard := card_sylow_modEq_one 5 ↥R
      have hdvd := Q.card_dvd_index
      have hQidx : (Q : Subgroup ↥R).index = 8 := hidx
      rw [hQidx] at hdvd
      have key : ∀ m : ℕ, m ≤ 8 → m ∣ 8 → m ≡ 1 [MOD 5] → m = 1 := by decide
      have h1 : Nat.card (Sylow 5 ↥R) = 1 := key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hcard
      have : Subsingleton (Sylow 5 ↥R) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact Q.normal_of_subsingleton
    have hconjB : ∀ t ∈ S ⊓ L, t * (z : A6Aut) * t⁻¹ ∈ B := by
      intro t ht
      have h1 := hBn.conj_mem ⟨z, hBR hzB⟩ hzB ⟨t, hUR ht⟩
      exact h1
    let f : ↥(S ⊓ L) → ↥B := fun t =>
      ⟨(t : A6Aut) * z * (t : A6Aut)⁻¹, hconjB t t.2⟩
    have hf : ¬ Function.Injective f := by
      intro hinj
      have h1 := Nat.card_le_card_of_injective f hinj
      rw [hUc, h] at h1
      omega
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨t₁, t₂, ht12, hne12⟩ := hf
    have heq : (t₁ : A6Aut) * z * (t₁ : A6Aut)⁻¹ =
        (t₂ : A6Aut) * z * (t₂ : A6Aut)⁻¹ := congrArg Subtype.val ht12
    set t := (t₂ : A6Aut)⁻¹ * (t₁ : A6Aut) with htdef
    have htU : t ∈ S ⊓ L := (S ⊓ L).mul_mem ((S ⊓ L).inv_mem t₂.2) t₁.2
    have ht1 : t ≠ 1 := by
      intro h1
      apply hne12
      apply Subtype.ext
      rw [htdef, inv_mul_eq_one] at h1
      exact h1.symm
    have htz : (z : A6Aut) * t = t * z := by
      rw [htdef]
      calc (z : A6Aut) * ((t₂ : A6Aut)⁻¹ * (t₁ : A6Aut)) =
            (t₂ : A6Aut)⁻¹ * ((t₂ : A6Aut) * z * (t₂ : A6Aut)⁻¹) * (t₁ : A6Aut) := by group
        _ = (t₂ : A6Aut)⁻¹ * ((t₁ : A6Aut) * z * (t₁ : A6Aut)⁻¹) * (t₁ : A6Aut) := by rw [heq]
        _ = (t₂ : A6Aut)⁻¹ * (t₁ : A6Aut) * z := by group
    obtain ⟨k, hk⟩ := hU.isPGroup ⟨t, htU⟩
    have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨τ', hτ'⟩ := hRL (hUR htU)
    obtain ⟨ζ, hζ, hζo⟩ := hel z hzB
    have hcomm' : ζ * τ' = τ' * ζ :=
      pairHom_injective (by rw [map_mul, map_mul, hζ, hτ']; exact htz)
    have hpow' : τ' ^ 2 ^ k = 1 := pairHom_injective (by rw [map_pow, hτ', hk', map_one])
    apply ht1
    rw [← hτ', eq_one_of_commute_five (hζo.trans hz) hcomm' hpow', map_one]
  ·
    have hRc' : Nat.card R = 72 := by rw [hRc, h]
    have : IsSimpleGroup ↥L := isSimpleGroup_pairImg
    have hidx : (R.subgroupOf L).index = 5 := by
      have := (R.subgroupOf L).card_mul_index
      rw [hcardSub hRL, hRc', hLc] at this
      omega
    have h1 := A7.index_eq_one_of_simple (R.subgroupOf L) (by rw [hidx, hLc]; decide)
    rw [hidx] at h1
    exact absurd h1 (by norm_num)
  · exact h35 ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩
  · exact h35 ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩

theorem nPrime_eq_one
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)))}
    (hX1 : pairImg Γ₆ tau₆ ≤ X) (hX2 : X ≤ pairNorm Γ₆ tau₆)
    (hX3 : ∃ x ∈ X, x ∉ pairSub (Fin 2 ⊕ Fin 2) (ZMod 2)) : E3.nPrime X = 1 := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2))) := MulEquiv.finite_left
  exact PairN.nPrime_eq_one_of fun B S hBX hBab hBodd hS hBS =>
    eq_bot_of_permutes hX1 hX2 hX3 hBX hBab hBodd hS hBS

theorem H7_A6Pair_nPrime
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : AlternatingNatural H V₁ ⊥ 6) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) (hφM : φ ∈ M) :
    E3.nPrime M = 1 := by
  obtain ⟨π, hπ⟩ := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_natural hπ
  set π' : ↥Γ₆ →* ↥H := π.comp psiEquiv.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp psiEquiv.symm.surjective
  have he₁' : ∀ (γ : ↥Γ₆) (u : ↥V₁) (hu : ((π' γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₁ u) := by
    intro γ u hu
    have h := he₁ (psiEquiv.symm γ) u hu
    have e : psiHom ((psiEquiv.symm γ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
        (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      have := congrArg Subtype.val (psiEquiv.apply_symm_apply γ)
      exact this
    rw [← e]
    exact h
  obtain ⟨e, he⟩ := PairG.exists_pair_model tau₆ π' hπ's hU e₁ he₁' hAut hφ hinf hsup hniso
  have h1 : pairImg Γ₆ tau₆ ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ pairNorm Γ₆ tau₆ := PairG.map_le_pairNorm tau₆ e he hMN
  have hV₁ : V₁ ≠ ⊥ := by
    intro h
    have hc := e₁.toEquiv
    rw [h] at hc
    have h3 := Nat.card_congr hc
    rw [Subgroup.card_bot, card_stdMod] at h3
    exact absurd h3 (by norm_num)
  have hX3 : ∃ x ∈ M.map (congrHom e), x ∉ pairSub (Fin 2 ⊕ Fin 2) (ZMod 2) :=
    ⟨congrHom e φ, ⟨φ, hφM, rfl⟩, PairN.congrHom_not_mem_pairSub isNatIrr tau₆_surjective
      not_isoMod (fun l hl w hw => hU ⟨l, hl⟩ w hw) hV₁ hinf e he (h2 ⟨φ, hφM, rfl⟩)⟩
  rw [← nPrime_map_congrHom e M]
  exact nPrime_eq_one h1 h2 hX3

end Sp4A6

end H

end CFSG.Quasithin
